//! Actual raw registration, full color-group metadata and layer-opacity producers.

use super::*;

verus! {

pub type Part2RawRegistration = (u16, u16, Seq<crate::jp2::CodestreamRegistration>);

pub open spec fn part2_registration_entry(input: Part2BoxReference, base: u64, index: nat)
    -> Result<crate::jp2::CodestreamRegistration, crate::DecodeError>
{
    let payload = input.1;
    let position = 4 + index * 6;
    if position + 6 > payload.len() {
        Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::InvalidBoxLength })
    } else {
        let horizontal = part2_box_u16([payload[0], payload[1]]);
        let vertical = part2_box_u16([payload[2], payload[3]]);
        let horizontal_subsampling = payload[position as int + 2];
        let vertical_subsampling = payload[position as int + 3];
        let horizontal_offset = payload[position as int + 4];
        let vertical_offset = payload[position as int + 5];
        if horizontal_subsampling == 0 || vertical_subsampling == 0
            || horizontal_offset as u16 >= horizontal || vertical_offset as u16 >= vertical {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else {
            Ok(crate::jp2::CodestreamRegistration {
                codestream_index: part2_box_u16([payload[position as int], payload[position as int + 1]]),
                horizontal_subsampling, vertical_subsampling,
                horizontal_offset: horizontal_offset as u32, vertical_offset: vertical_offset as u32,
            })
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_registration_prefix(input: Part2BoxReference, base: u64, count: nat)
    -> Result<Seq<crate::jp2::CodestreamRegistration>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_registration_prefix(input, base, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_registration_entry(input, base, (count - 1) as nat) {
                Err(error) => Err(error), Ok(value) => Ok(previous.push(value)),
            },
        }
    }
}

pub open spec fn part2_parse_codestream_registration(
    input: Part2BoxReference, base: u64, limits: &crate::ResourceLimits,
) -> Result<Part2RawRegistration, crate::DecodeError> {
    let payload = input.1;
    if payload.len() < 10 || (payload.len() - 4) % 6 != 0 {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else {
        let horizontal = part2_box_u16([payload[0], payload[1]]);
        let vertical = part2_box_u16([payload[2], payload[3]]);
        let count = ((payload.len() - 4) / 6) as nat;
        if horizontal == 0 || vertical == 0 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else if count as u64 > crate::limits::resource_codestream_limit(limits) as u64 {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Codestreams,
                limit: crate::limits::resource_codestream_limit(limits) as u64, actual: count as u64 })
        } else {
            match part2_registration_prefix(input, base, count) {
                Err(error) => Err(error), Ok(values) => Ok((horizontal, vertical, values)),
            }
        }
    }
}

pub(crate) proof fn part2_registration_step(input: Part2BoxReference, base: u64, count: nat)
    ensures part2_registration_prefix(input, base, count + 1)
        == match part2_registration_prefix(input, base, count) {
            Err(error) => Err(error),
            Ok(previous) => match part2_registration_entry(input, base, count) {
                Err(error) => Err(error), Ok(value) => Ok(previous.push(value)),
            },
        },
{
    reveal(part2_registration_prefix);
}

pub(crate) proof fn part2_registration_error(input: Part2BoxReference, base: u64, count: nat, total: nat)
    requires count <= total,
    ensures match part2_registration_prefix(input, base, count) {
        Err(error) => part2_registration_prefix(input, base, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_registration_prefix);
    if count < total { part2_registration_error(input, base, count, (total - 1) as nat); }
}

pub open spec fn part2_parse_layer_opacity(input: Part2BoxReference, base: u64)
    -> Result<Part2SourceOpacity, crate::DecodeError>
{
    match part2_box_add_offset(base, input.0.1) {
        Err(error) => Err(error),
        Ok(offset) => {
            let payload = input.1;
            if payload.len() == 0 {
                Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
            } else if payload[0] == 0 && payload.len() == 1 { Ok(Part2SourceOpacity::Straight) }
            else if payload[0] == 1 && payload.len() == 1 { Ok(Part2SourceOpacity::Premultiplied) }
            else if payload[0] == 2 {
                if payload.len() < 3 {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
                } else if payload[1] == 0 {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxContents })
                } else { Ok(Part2SourceOpacity::ChromaKey {
                    channels: payload[1], values: payload.subrange(2, payload.len() as int) }) }
            } else {
                Err(crate::DecodeError::MalformedInput { offset, kind: if payload[0] <= 2 {
                    crate::MalformedKind::InvalidBoxLength } else { crate::MalformedKind::InvalidBoxContents } })
            }
        },
    }
}

pub open spec fn part2_color_group_finish(colors: Seq<Part2ColorSpecification>, base: u64)
    -> Result<Seq<Part2ColorSpecification>, crate::DecodeError> {
    if colors.len() == 0 { Err(part2_raw_header_missing(base)) } else { Ok(colors) }
}

#[verifier::opaque]
pub open spec fn part2_color_group_boxes(
    payload: Seq<u8>, reader: Part2BoxReaderState, colors: Seq<Part2ColorSpecification>,
    limits: crate::ResourceLimits, base: u64,
) -> Result<Seq<Part2ColorSpecification>, crate::DecodeError>
    decreases payload.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_color_group_finish(colors, base),
        Some(result) => if next.1.position <= reader.position || next.1.position > payload.len() {
            Err(part2_resolution_progress_error(base, reader.position))
        } else {
            match result {
                Err(error) => Err(part2_box_rebase_error(error, base)),
                Ok(input) => if input.0.0 != crate::jp2::BoxType::COLOR_SPECIFICATION {
                    Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
                } else {
                    match part2_parse_color_specification(input, base) {
                        Err(error) => Err(error),
                        Ok(value) => {
                            let updated = colors.push(value);
                            if updated.len() as u64 > crate::limits::resource_component_limit(&limits) as u64 {
                                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Components,
                                    limit: crate::limits::resource_component_limit(&limits) as u64, actual: updated.len() as u64 })
                            } else { part2_color_group_boxes(payload, next.1, updated, limits, base) }
                        },
                    }
                },
            }
        },
    }
}

pub open spec fn part2_parse_color_group(input: Part2BoxReference, limits: crate::ResourceLimits, base: u64)
    -> Result<Seq<Part2ColorSpecification>, crate::DecodeError> {
    match part2_box_reader_from_input(input.1, limits) {
        Err(error) => Err(error),
        Ok(reader) => part2_color_group_boxes(input.1, reader, Seq::empty(), limits, base),
    }
}

pub struct Part2RawCompositingLayer {
    pub header: Part2BoxHeader,
    pub payload: Seq<u8>,
    pub horizontal: u16,
    pub vertical: u16,
    pub registrations: Seq<crate::jp2::CodestreamRegistration>,
    pub colors: Seq<Part2ColorSpecification>,
    pub definitions: Seq<Part2ChannelRecord>,
    pub opacity: Option<Part2SourceOpacity>,
    pub nested_metadata: u32,
}

pub struct Part2RawLayerState {
    pub layer: Part2RawCompositingLayer,
    pub has_registration: bool,
}

#[verifier::opaque]
pub open spec fn part2_raw_layer_step(
    input: Part2BoxReference, state: Part2RawLayerState, limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawLayerState, crate::DecodeError> {
    let kind = input.0.0;
    let layer = state.layer;
    if kind == crate::jp2::BoxType::CODESTREAM_REGISTRATION {
        if state.has_registration {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
        } else {
            match part2_parse_codestream_registration(input, base, &limits) {
                Err(error) => Err(error), Ok(value) => Ok(Part2RawLayerState {
                    layer: Part2RawCompositingLayer {
                        horizontal: value.0, vertical: value.1, registrations: value.2, ..layer },
                    has_registration: true }),
            }
        }
    } else if kind == crate::jp2::BoxType::COLOR_GROUP {
        if layer.colors.len() > 0 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
        } else {
            match part2_box_payload_offset(input.0) {
                Err(error) => Err(error),
                Ok(relative) => match part2_box_add_offset(base, relative) {
                    Err(error) => Err(error),
                    Ok(nested_base) => match part2_parse_color_group(input, limits, nested_base) {
                        Err(error) => Err(error), Ok(colors) => Ok(Part2RawLayerState {
                            layer: Part2RawCompositingLayer { colors, ..layer }, ..state }),
                    },
                },
            }
        }
    } else if kind == crate::jp2::BoxType::OPACITY {
        if layer.opacity.is_some() || layer.definitions.len() > 0 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
        } else {
            match part2_parse_layer_opacity(input, base) {
                Err(error) => Err(error), Ok(opacity) => Ok(Part2RawLayerState {
                    layer: Part2RawCompositingLayer { opacity: Some(opacity), ..layer }, ..state }),
            }
        }
    } else if kind == crate::jp2::BoxType::CHANNEL_DEFINITION {
        if layer.definitions.len() > 0 || layer.opacity.is_some() {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
        } else {
            match part2_parse_channel_definition(input, u16::MAX, base) {
                Err(error) => Err(error), Ok(definitions) => Ok(Part2RawLayerState {
                    layer: Part2RawCompositingLayer { definitions, ..layer }, ..state }),
            }
        }
    } else {
        match part2_inspect_metadata_box(input, limits, 1, (u32::MAX - 1) as u32) {
            Err(error) => Err(error),
            Ok(observed) => {
                let count = layer.nested_metadata as nat + observed.0 as nat;
                if count > u32::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                else { Ok(Part2RawLayerState {
                    layer: Part2RawCompositingLayer { nested_metadata: count as u32, ..layer }, ..state }) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_raw_layer_boxes(
    payload: Seq<u8>, reader: Part2BoxReaderState, state: Part2RawLayerState, limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawCompositingLayer, crate::DecodeError>
    decreases payload.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => Ok(state.layer),
        Some(result) => if next.1.position <= reader.position || next.1.position > payload.len() {
            Err(part2_resolution_progress_error(base, reader.position))
        } else {
            match result {
                Err(error) => Err(part2_box_rebase_error(error, base)),
                Ok(input) => match part2_raw_layer_step(input, state, limits, base) {
                    Err(error) => Err(error), Ok(updated) => part2_raw_layer_boxes(payload, next.1, updated, limits, base),
                },
            }
        },
    }
}

pub open spec fn part2_parse_compositing_layer(input: Part2BoxReference, limits: crate::ResourceLimits)
    -> Result<Part2RawCompositingLayer, crate::DecodeError> {
    match part2_box_payload_offset(input.0) {
        Err(error) => Err(error),
        Ok(base) => match part2_box_reader_from_input(input.1, limits) {
            Err(error) => Err(error),
            Ok(reader) => part2_raw_layer_boxes(input.1, reader, Part2RawLayerState {
                layer: Part2RawCompositingLayer {
                    header: input.0, payload: input.1, horizontal: 1, vertical: 1,
                    registrations: Seq::empty(), colors: Seq::empty(), definitions: Seq::empty(),
                    opacity: None, nested_metadata: 0 },
                has_registration: false,
            }, limits, base),
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_layer_registration_references(layer: Part2RawCompositingLayer, streams: usize, index: nat)
    -> Result<(), crate::DecodeError>
    decreases layer.registrations.len() - index,
{
    if index >= layer.registrations.len() { Ok(()) }
    else if layer.registrations[index as int].codestream_index as usize >= streams {
        Err(crate::DecodeError::MalformedInput { offset: layer.header.1, kind: crate::MalformedKind::InvalidBoxContents })
    } else { part2_layer_registration_references(layer, streams, index + 1) }
}

#[verifier::opaque]
pub open spec fn part2_any_layer_registration(layers: Seq<Part2RawCompositingLayer>, count: nat) -> bool
    decreases count,
{
    count > 0 && (layers[count as int - 1].registrations.len() != 0
        || part2_any_layer_registration(layers, (count - 1) as nat))
}

#[verifier::opaque]
pub open spec fn part2_layer_references(layers: Seq<Part2RawCompositingLayer>, streams: usize, index: nat)
    -> Result<(), crate::DecodeError>
    decreases layers.len() - index,
{
    if index >= layers.len() { Ok(()) }
    else {
        let layer = layers[index as int];
        if layer.registrations.len() == 0 {
            if part2_any_layer_registration(layers, layers.len()) || index >= streams as nat {
                Err(crate::DecodeError::MalformedInput { offset: layer.header.1, kind: crate::MalformedKind::InvalidBoxContents })
            } else { part2_layer_references(layers, streams, index + 1) }
        } else {
            match part2_layer_registration_references(layer, streams, 0) {
                Err(error) => Err(error), Ok(()) => part2_layer_references(layers, streams, index + 1),
            }
        }
    }
}

pub open spec fn part2_validate_layer_references(layers: Seq<Part2RawCompositingLayer>, streams: usize)
    -> Result<(), crate::DecodeError> {
    part2_layer_references(layers, streams, 0)
}

}
