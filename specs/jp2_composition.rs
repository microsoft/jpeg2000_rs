//! Actual raw composition cursor, dimensions and instruction record producers.

use super::*;

verus! {

pub open spec fn part2_read_composition_word(input: Seq<u8>, position: usize, offset: u64)
    -> (Result<u32, crate::DecodeError>, usize)
{
    let end = position as nat + 4;
    if end > usize::MAX as nat { (Err(part2_palette_arithmetic_error(offset)), position) }
    else if end > input.len() {
        (Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength }), position)
    } else {
        (Ok(part2_box_u32([input[position as int], input[position as int + 1],
            input[position as int + 2], input[position as int + 3]])), end as usize)
    }
}

pub open spec fn part2_validate_composition_dimensions(width: u32, height: u32, limits: &crate::ResourceLimits, offset: u64)
    -> Result<(), crate::DecodeError>
{
    if width == 0 || height == 0 {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidImageGeometry })
    } else if width > crate::limits::resource_width_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Width,
            limit: crate::limits::resource_width_limit(limits) as u64, actual: width as u64 })
    } else if height > crate::limits::resource_height_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Height,
            limit: crate::limits::resource_height_limit(limits) as u64, actual: height as u64 })
    } else {
        let pixels = width as nat * height as nat;
        if pixels > u64::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
        else if pixels > crate::limits::resource_pixel_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Pixels,
                limit: crate::limits::resource_pixel_limit(limits), actual: pixels as u64 })
        } else { Ok(()) }
    }
}

pub open spec fn part2_instruction_record_words(flags: u16) -> nat {
    (if flags & 1 != 0 { 2nat } else { 0nat })
    + (if flags & 2 != 0 { 2nat } else { 0nat })
    + (if flags & 4 != 0 { 2nat } else { 0nat })
    + (if flags & 32 != 0 { 4nat } else { 0nat })
}

pub open spec fn part2_composition_word_at(input: Seq<u8>, position: nat) -> u32 {
    part2_box_u32([input[position as int], input[position as int + 1], input[position as int + 2], input[position as int + 3]])
}

#[verifier::opaque]
pub open spec fn part2_instruction_record(
    input: Part2BoxReference, composition: (u32, u32, u8), offset: u64, flags: u16, tick: u32, position: nat,
) -> Result<crate::jp2::CompositionInstruction, crate::DecodeError>
{
    let words = part2_instruction_record_words(flags);
    let end = position + words * 4;
    if end > usize::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
    else if end > input.1.len() {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
    } else if words == 0 { Err(part2_palette_arithmetic_error(offset)) }
    else {
        let size_start = position + if flags & 1 != 0 { 8nat } else { 0nat };
        let life_start = size_start + if flags & 2 != 0 { 8nat } else { 0nat };
        let source_start = life_start + if flags & 4 != 0 { 8nat } else { 0nat };
        let target_x = if flags & 1 != 0 { part2_composition_word_at(input.1, position) } else { 0 };
        let target_y = if flags & 1 != 0 { part2_composition_word_at(input.1, position + 4) } else { 0 };
        let target_width = if flags & 2 != 0 { part2_composition_word_at(input.1, size_start) } else { composition.0 };
        let target_height = if flags & 2 != 0 { part2_composition_word_at(input.1, size_start + 4) } else { composition.1 };
        let encoded_life = if flags & 4 != 0 { part2_composition_word_at(input.1, life_start) } else { 0 };
        let persistent = if flags & 4 != 0 { encoded_life & 0x8000_0000u32 != 0 } else { true };
        let next_reuse = if flags & 4 != 0 { part2_composition_word_at(input.1, life_start + 4) } else { 0 };
        let source_x = if flags & 32 != 0 { part2_composition_word_at(input.1, source_start) } else { 0 };
        let source_y = if flags & 32 != 0 { part2_composition_word_at(input.1, source_start + 4) } else { 0 };
        let source_width = if flags & 32 != 0 { part2_composition_word_at(input.1, source_start + 8) } else { 0 };
        let source_height = if flags & 32 != 0 { part2_composition_word_at(input.1, source_start + 12) } else { 0 };
        if target_width == 0 || target_height == 0 || (flags & 32 != 0 && (source_width == 0 || source_height == 0)) {
            Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidImageGeometry })
        } else {
            let life_value = if flags & 4 != 0 { encoded_life & 0x7fff_ffffu32 } else { 0u32 };
            let life = life_value as nat * tick as nat;
            if life > u32::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
            else { Ok(crate::jp2::CompositionInstruction {
                target_x, target_y, target_width, target_height, life: life as u32, persistent, next_reuse,
                source_x, source_y, source_width, source_height,
            }) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_instruction_records(
    input: Part2BoxReference, composition: (u32, u32, u8), offset: u64, flags: u16, tick: u32,
    position: usize, records: Seq<crate::jp2::CompositionInstruction>,
) -> Result<Seq<crate::jp2::CompositionInstruction>, crate::DecodeError>
    decreases input.1.len() as int - position as int,
{
    if position >= input.1.len() { Ok(records) }
    else {
        let bytes = part2_instruction_record_words(flags) * 4;
        let end = position as nat + bytes;
        if bytes == 0 || end > usize::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
        else if end > input.1.len() {
            Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
        } else {
            match part2_instruction_record(input, composition, offset, flags, tick, position as nat) {
                Err(error) => Err(error),
                Ok(value) => part2_instruction_records(input, composition, offset, flags, tick, end as usize, records.push(value)),
            }
        }
    }
}

pub type Part2RawInstructionSet = (u16, u16, u32, Seq<crate::jp2::CompositionInstruction>);

pub open spec fn part2_instruction_result(flags: u16, repeat: u16, tick: u32,
    result: Result<Seq<crate::jp2::CompositionInstruction>, crate::DecodeError>)
    -> Result<Part2RawInstructionSet, crate::DecodeError> {
    match result { Err(error) => Err(error), Ok(values) => Ok((flags, repeat, tick, values)) }
}

#[verifier::opaque]
pub open spec fn part2_parse_instruction_set(
    input: Part2BoxReference, composition: (u32, u32, u8), base: u64, limits: &crate::ResourceLimits,
) -> Result<Part2RawInstructionSet, crate::DecodeError> {
    match part2_box_add_offset(base, input.0.1) {
        Err(error) => Err(error),
        Ok(offset) => {
            let payload = input.1;
            if payload.len() < 8 {
                Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
            } else {
                let flags = part2_box_u16([payload[0], payload[1]]);
                let repeat = part2_box_u16([payload[2], payload[3]]);
                let tick = part2_box_u32([payload[4], payload[5], payload[6], payload[7]]);
                let bytes = part2_instruction_record_words(flags) * 4;
                let remaining = (payload.len() - 8) as nat;
                if flags & !0x0027u16 != 0 {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxContents })
                } else if bytes == 0 {
                    if remaining != 0 {
                        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
                    } else { Ok((flags, repeat, tick, Seq::empty())) }
                } else if remaining % bytes != 0 {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
                } else {
                    let count = remaining / bytes;
                    if count as u64 > crate::limits::resource_work_limit(limits) {
                        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                            limit: crate::limits::resource_work_limit(limits), actual: count as u64 })
                    } else {
                        part2_instruction_result(flags, repeat, tick,
                            part2_instruction_records(input, composition, offset, flags, tick, 8, Seq::empty()))
                    }
                }
            }
        },
    }
}

pub type Part2RawComposition = (u32, u32, u8, Seq<Part2RawInstructionSet>, bool);

pub open spec fn part2_composition_finish(
    options: Option<(u32, u32, u8)>, sets: Seq<Part2RawInstructionSet>, unknown: bool, base: u64,
) -> Result<Part2RawComposition, crate::DecodeError> {
    match options {
        None => Err(part2_raw_header_missing(base)),
        Some(value) => Ok((value.0, value.1, if value.2 == u8::MAX { 0u8 } else { (value.2 + 1) as u8 }, sets, unknown)),
    }
}

#[verifier::opaque]
pub open spec fn part2_composition_boxes(
    payload: Seq<u8>, reader: Part2BoxReaderState, options: Option<(u32, u32, u8)>,
    sets: Seq<Part2RawInstructionSet>, unknown: bool, limits: crate::ResourceLimits, base: u64,
) -> Result<Part2RawComposition, crate::DecodeError>
    decreases payload.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_composition_finish(options, sets, unknown, base),
        Some(result) => if next.1.position <= reader.position || next.1.position > payload.len() {
            Err(part2_resolution_progress_error(base, reader.position))
        } else {
            match result {
                Err(error) => Err(part2_box_rebase_error(error, base)),
                Ok(input) => {
                    if input.0.0 == crate::jp2::BoxType::COMPOSITION_OPTIONS {
                        if options.is_some() || sets.len() > 0 {
                            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
                        } else if input.1.len() != 9 {
                            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
                        } else {
                            let height = part2_composition_word_at(input.1, 0);
                            let width = part2_composition_word_at(input.1, 4);
                            match part2_validate_composition_dimensions(width, height, &limits, base) {
                                Err(error) => Err(error),
                                Ok(()) => part2_composition_boxes(payload, next.1, Some((width, height, input.1[8])),
                                    sets, unknown, limits, base),
                            }
                        }
                    } else if input.0.0 == crate::jp2::BoxType::INSTRUCTION_SET {
                        match options {
                            None => Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder)),
                            Some(value) => match part2_parse_instruction_set(input, value, base, &limits) {
                                Err(error) => Err(error),
                                Ok(set) => {
                                    let count = sets.len() + 1;
                                    if count > usize::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                                    else if count as u64 > crate::limits::resource_layer_limit(&limits) as u64 {
                                        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Layers,
                                            limit: crate::limits::resource_layer_limit(&limits) as u64, actual: count as u64 })
                                    } else { part2_composition_boxes(payload, next.1, options, sets.push(set), unknown, limits, base) }
                                },
                            },
                        }
                    } else { part2_composition_boxes(payload, next.1, options, sets, true, limits, base) }
                },
            }
        },
    }
}

pub open spec fn part2_parse_composition(input: Part2BoxReference, limits: crate::ResourceLimits)
    -> Result<Part2RawComposition, crate::DecodeError> {
    match part2_box_payload_offset(input.0) {
        Err(error) => Err(error),
        Ok(base) => match part2_box_reader_from_input(input.1, limits) {
            Err(error) => Err(error),
            Ok(reader) => part2_composition_boxes(input.1, reader, None, Seq::empty(), false, limits, base),
        },
    }
}

}
