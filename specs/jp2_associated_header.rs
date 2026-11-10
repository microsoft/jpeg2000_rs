//! Actual associated-header fallback, inherited owners and source override traversal.

use super::*;

verus! {

pub open spec fn part2_color_specification_clone(value: Part2ColorSpecification) -> Part2ColorSpecification {
    value
}

pub open spec fn part2_owned_palette_clone(value: Part2PaletteModel) -> Part2PaletteModel {
    value
}

pub open spec fn part2_optional_palette_clone(value: Option<Part2PaletteModel>) -> Option<Part2PaletteModel> {
    value
}

pub open spec fn part2_jp2_header_clone(value: Part2RawJp2Header) -> Part2RawJp2Header {
    value
}

pub open spec fn part2_optional_jp2_header_clone(value: Option<Part2RawJp2Header>) -> Option<Part2RawJp2Header> {
    value
}

pub type Part2RawCodestreamAssociation = (Part2BoxHeader, Seq<u8>, Option<Part2RawJp2Header>);

pub open spec fn part2_codestream_association_clone(value: Part2RawCodestreamAssociation) -> Part2RawCodestreamAssociation {
    value
}

pub struct Part2AssociatedHeaderState {
    pub header: Part2RawJp2Header,
    pub image_override: bool,
    pub color_override: bool,
    pub saw_bpcc: bool,
    pub palette_override: bool,
    pub mapping_override: bool,
    pub definition_override: bool,
    pub resolution_override: bool,
    pub nested: u32,
}

pub open spec fn part2_associated_header_finish(state: Part2AssociatedHeaderState, base: u64)
    -> Result<Part2RawJp2Header, crate::DecodeError>
{
    if state.image_override
        && matches!(state.header.image.bit_depth, crate::jp2::ComponentBitDepth::Variable) != state.saw_bpcc {
        Err(part2_raw_header_missing(base))
    } else if state.header.palette.is_some() && state.header.mappings.len() == 0 {
        Err(part2_raw_header_missing(base))
    } else { Ok(Part2RawJp2Header { nested_box_count: state.nested, ..state.header }) }
}

#[verifier::opaque]
pub open spec fn part2_associated_header_step(
    input: Part2BoxReference, state: Part2AssociatedHeaderState, limits: crate::ResourceLimits, base: u64,
) -> Result<Part2AssociatedHeaderState, crate::DecodeError> {
    let kind = input.0.0;
    let header = state.header;
    if kind == crate::jp2::BoxType::IMAGE_HEADER {
        if state.image_override { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else {
            match part2_parse_image_header(input, &limits, base) {
                Err(error) => Err(error),
                Ok(image) => Ok(Part2AssociatedHeaderState {
                    header: Part2RawJp2Header {
                        image, palette: None, mappings: Seq::empty(), definitions: Seq::empty(),
                        palette_entries: 0, palette_columns: 0, component_mapping_entries: 0,
                        channel_definitions: 0, ..header },
                    image_override: true, ..state }),
            }
        }
    } else if kind == crate::jp2::BoxType::BITS_PER_COMPONENT {
        if state.saw_bpcc { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else {
            match part2_validate_bpcc(input, header.image, base) {
                Err(error) => Err(error), Ok(()) => Ok(Part2AssociatedHeaderState { saw_bpcc: true, ..state }),
            }
        }
    } else if kind == crate::jp2::BoxType::COLOR_SPECIFICATION {
        if !state.color_override {
            match part2_parse_color_specification(input, base) {
                Err(error) => Err(error),
                Ok(color) => Ok(Part2AssociatedHeaderState {
                    header: Part2RawJp2Header { color, ..header }, color_override: true, ..state }),
            }
        } else {
            match part2_validate_color_specification_prefix(input, base) {
                Err(error) => Err(error), Ok(()) => Ok(state),
            }
        }
    } else if kind == crate::jp2::BoxType::PALETTE {
        if state.palette_override || state.mapping_override || state.definition_override {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
        } else {
            match part2_parse_palette(input, base) {
                Err(error) => Err(error),
                Ok(palette) => {
                    if palette.1.len() > u8::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                    else { Ok(Part2AssociatedHeaderState {
                        header: Part2RawJp2Header { palette: Some(palette), palette_entries: palette.0,
                            palette_columns: palette.1.len() as u8, ..header },
                        palette_override: true, ..state }) }
                },
            }
        }
    } else if kind == crate::jp2::BoxType::COMPONENT_MAPPING {
        if state.mapping_override || state.definition_override {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
        } else {
            let count = match header.palette { None => 0nat, Some(palette) => palette.1.len() };
            if count > u8::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
            else {
                match part2_parse_component_mapping(input, header.image.components, count as u8, &limits, base) {
                    Err(error) => Err(error),
                    Ok(mappings) => {
                        if mappings.len() > u16::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                        else { Ok(Part2AssociatedHeaderState {
                            header: Part2RawJp2Header { component_mapping_entries: mappings.len() as u16, mappings, ..header },
                            mapping_override: true, ..state }) }
                    },
                }
            }
        }
    } else if kind == crate::jp2::BoxType::CHANNEL_DEFINITION {
        if state.definition_override { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else {
            let count = if header.mappings.len() == 0 { header.image.components as nat } else { header.mappings.len() };
            if count > u16::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
            else {
                match part2_parse_channel_definition(input, count as u16, base) {
                    Err(error) => Err(error),
                    Ok(definitions) => {
                        if definitions.len() > u16::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                        else { Ok(Part2AssociatedHeaderState {
                            header: Part2RawJp2Header { channel_definitions: definitions.len() as u16, definitions, ..header },
                            definition_override: true, ..state }) }
                    },
                }
            }
        }
    } else if kind == crate::jp2::BoxType::RESOLUTION {
        if state.resolution_override { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else {
            match part2_box_payload_offset(input.0) {
                Err(error) => Err(error),
                Ok(relative) => match part2_box_add_offset(base, relative) {
                    Err(error) => Err(error),
                    Ok(nested_base) => match part2_parse_resolution_superbox(input.1, limits, nested_base) {
                        Err(error) => Err(error), Ok(pair) => Ok(Part2AssociatedHeaderState {
                            header: Part2RawJp2Header { capture: pair.0, display: pair.1, ..header },
                            resolution_override: true, ..state }),
                    },
                },
            }
        }
    } else { Ok(state) }
}

#[verifier::opaque]
pub open spec fn part2_associated_header_boxes(
    payload: Seq<u8>, reader: Part2BoxReaderState, state: Part2AssociatedHeaderState,
    limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawJp2Header, crate::DecodeError>
    decreases payload.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_associated_header_finish(state, base),
        Some(result) => {
            if next.1.position <= reader.position || next.1.position > payload.len() {
                Err(part2_resolution_progress_error(base, reader.position))
            } else {
                match result {
                    Err(error) => Err(part2_box_rebase_error(error, base)),
                    Ok(input) => if state.nested == u32::MAX { Err(part2_palette_arithmetic_error(base)) }
                    else {
                        match part2_associated_header_step(input, Part2AssociatedHeaderState {
                            nested: (state.nested + 1) as u32, ..state }, limits, base) {
                            Err(error) => Err(error),
                            Ok(updated) => part2_associated_header_boxes(payload, next.1, updated, limits, base),
                        }
                    },
                }
            }
        },
    }
}

pub open spec fn part2_parse_codestream_header(
    payload: Seq<u8>, defaults: Option<Part2RawJp2Header>, limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawJp2Header, crate::DecodeError> {
    match part2_parse_jp2_header(payload, limits, base) {
        Ok(header) => Ok(header),
        Err(_) => match defaults {
            None => Err(part2_raw_header_missing(base)),
            Some(header) => match part2_box_reader_from_input(payload, limits) {
                Err(error) => Err(error),
                Ok(reader) => part2_associated_header_boxes(payload, reader, Part2AssociatedHeaderState {
                    header, image_override: false, color_override: false, saw_bpcc: false,
                    palette_override: false, mapping_override: false, definition_override: false,
                    resolution_override: false, nested: 0,
                }, limits, base),
            },
        },
    }
}

}
