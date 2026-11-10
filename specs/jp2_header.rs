//! Complete actual raw JP2 header assembly, including all owned metadata projections.

use super::*;

verus! {

pub struct Part2RawHeaderState {
    pub image: crate::jp2::ImageHeader,
    pub color: Option<Part2ColorSpecification>,
    pub saw_bpcc: bool,
    pub palette: Option<Part2PaletteModel>,
    pub mappings: Seq<crate::jp2::ComponentMapping>,
    pub definitions: Seq<Part2ChannelRecord>,
    pub capture: Option<crate::jp2::Resolution>,
    pub display: Option<crate::jp2::Resolution>,
    pub nested: u32,
}

pub struct Part2RawJp2Header {
    pub image: crate::jp2::ImageHeader,
    pub color: Part2ColorSpecification,
    pub nested_box_count: u32,
    pub palette_entries: u16,
    pub palette_columns: u8,
    pub component_mapping_entries: u16,
    pub channel_definitions: u16,
    pub palette: Option<Part2PaletteModel>,
    pub mappings: Seq<crate::jp2::ComponentMapping>,
    pub definitions: Seq<Part2ChannelRecord>,
    pub capture: Option<crate::jp2::Resolution>,
    pub display: Option<crate::jp2::Resolution>,
}

pub open spec fn part2_raw_header_missing(base: u64) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::MissingRequiredStructure }
}

pub open spec fn part2_raw_header_finish(state: Part2RawHeaderState, base: u64)
    -> Result<Part2RawJp2Header, crate::DecodeError>
{
    if matches!(state.image.bit_depth, crate::jp2::ComponentBitDepth::Variable) != state.saw_bpcc
        || (state.palette.is_some() && state.mappings.len() == 0) {
        Err(part2_raw_header_missing(base))
    } else {
        match state.color {
            None => Err(part2_raw_header_missing(base)),
            Some(color) => {
                if state.mappings.len() > u16::MAX as nat || state.definitions.len() > u16::MAX as nat {
                    Err(part2_palette_arithmetic_error(base))
                } else {
                    Ok(Part2RawJp2Header {
                        image: state.image, color, nested_box_count: state.nested,
                        palette_entries: match state.palette { None => 0, Some(palette) => palette.0 },
                        palette_columns: match state.palette { None => 0, Some(palette) => palette.1.len() as u8 },
                        component_mapping_entries: state.mappings.len() as u16,
                        channel_definitions: state.definitions.len() as u16,
                        palette: state.palette, mappings: state.mappings, definitions: state.definitions,
                        capture: state.capture, display: state.display,
                    })
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_raw_header_step(
    input: Part2BoxReference, state: Part2RawHeaderState, limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawHeaderState, crate::DecodeError> {
    let kind = input.0.0;
    if kind == crate::jp2::BoxType::IMAGE_HEADER {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
    } else if kind == crate::jp2::BoxType::BITS_PER_COMPONENT {
        if state.saw_bpcc { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else { match part2_validate_bpcc(input, state.image, base) {
            Err(error) => Err(error), Ok(()) => Ok(Part2RawHeaderState { saw_bpcc: true, ..state }),
        } }
    } else if kind == crate::jp2::BoxType::COLOR_SPECIFICATION {
        if state.color.is_none() {
            match part2_parse_color_specification(input, base) {
                Err(error) => Err(error),
                Ok(parsed) => Ok(Part2RawHeaderState { color: Some(parsed), ..state }),
            }
        } else {
            match part2_validate_color_specification_prefix(input, base) {
                Err(error) => Err(error), Ok(()) => Ok(state),
            }
        }
    } else if kind == crate::jp2::BoxType::PALETTE {
        if state.palette.is_some() { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else { match part2_parse_palette(input, base) {
            Err(error) => Err(error), Ok(palette) => Ok(Part2RawHeaderState { palette: Some(palette), ..state }),
        } }
    } else if kind == crate::jp2::BoxType::COMPONENT_MAPPING {
        if state.mappings.len() > 0 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else {
            let count = match state.palette { None => 0nat, Some(palette) => palette.1.len() };
            if count > u8::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
            else { match part2_parse_component_mapping(input, state.image.components, count as u8, &limits, base) {
                Err(error) => Err(error), Ok(mappings) => Ok(Part2RawHeaderState { mappings, ..state }),
            } }
        }
    } else if kind == crate::jp2::BoxType::CHANNEL_DEFINITION {
        if state.definitions.len() > 0 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)) }
        else {
            let count = if state.mappings.len() == 0 { state.image.components as nat } else { state.mappings.len() };
            if count > u16::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
            else { match part2_parse_channel_definition(input, count as u16, base) {
                Err(error) => Err(error), Ok(definitions) => Ok(Part2RawHeaderState { definitions, ..state }),
            } }
        }
    } else if kind == crate::jp2::BoxType::RESOLUTION {
        match part2_box_payload_offset(input.0) {
            Err(error) => Err(error),
            Ok(relative) => match part2_box_add_offset(base, relative) {
                Err(error) => Err(error),
                Ok(nested_base) => match part2_parse_resolution_superbox(input.1, limits, nested_base) {
                    Err(error) => Err(error),
                    Ok(pair) => if state.capture.is_some() || state.display.is_some() {
                        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
                    } else { Ok(Part2RawHeaderState { capture: pair.0, display: pair.1, ..state }) },
                },
            },
        }
    } else { Ok(state) }
}

#[verifier::opaque]
pub open spec fn part2_raw_header_boxes(
    payload: Seq<u8>, reader: Part2BoxReaderState, state: Part2RawHeaderState,
    limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawJp2Header, crate::DecodeError>
    decreases payload.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_raw_header_finish(state, base),
        Some(result) => {
            if next.1.position <= reader.position || next.1.position > payload.len() {
                Err(part2_resolution_progress_error(base, reader.position))
            } else {
                match result {
                    Err(error) => Err(part2_box_rebase_error(error, base)),
                    Ok(input) => {
                        if state.nested == u32::MAX { Err(part2_palette_arithmetic_error(base)) }
                        else {
                            match part2_raw_header_step(input, Part2RawHeaderState {
                                nested: (state.nested + 1) as u32, ..state }, limits, base) {
                                Err(error) => Err(error),
                                Ok(updated) => part2_raw_header_boxes(payload, next.1, updated, limits, base),
                            }
                        }
                    },
                }
            }
        },
    }
}

pub open spec fn part2_parse_jp2_header(payload: Seq<u8>, limits: crate::ResourceLimits, base: u64)
    -> Result<Part2RawJp2Header, crate::DecodeError>
{
    match part2_box_reader_from_input(payload, limits) {
        Err(error) => Err(error),
        Ok(reader) => {
            let required = part2_box_reader_required(reader, 0);
            match required.0 {
                Err(error) => Err(part2_box_rebase_error(error, base)),
                Ok(input) => if input.0.0 != crate::jp2::BoxType::IMAGE_HEADER {
                    Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
                } else {
                    match part2_parse_image_header(input, &limits, base) {
                        Err(error) => Err(error),
                        Ok(image) => part2_raw_header_boxes(payload, required.1, Part2RawHeaderState {
                            image, color: None, saw_bpcc: false, palette: None,
                            mappings: Seq::empty(), definitions: Seq::empty(),
                            capture: None, display: None, nested: 1,
                        }, limits, base),
                    }
                },
            }
        },
    }
}

}
