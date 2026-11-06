//! Actual resolution bytes and raw nested-box traversal, including native error priority.

use super::*;

verus! {

pub open spec fn part2_copy_metadata_bytes(input: Seq<u8>) -> Result<Seq<u8>, crate::DecodeError> {
    Ok(input)
}

pub open spec fn part2_parse_resolution(input: Part2BoxReference, base: u64)
    -> Result<crate::jp2::Resolution, crate::DecodeError>
{
    let payload = input.1;
    if payload.len() != 10 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
    else {
        let vertical_numerator = part2_box_u16([payload[0], payload[1]]);
        let vertical_denominator = part2_box_u16([payload[2], payload[3]]);
        let horizontal_numerator = part2_box_u16([payload[4], payload[5]]);
        let horizontal_denominator = part2_box_u16([payload[6], payload[7]]);
        if vertical_numerator == 0 || vertical_denominator == 0
            || horizontal_numerator == 0 || horizontal_denominator == 0 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else {
            Ok(crate::jp2::Resolution {
                vertical_numerator, vertical_denominator, horizontal_numerator, horizontal_denominator,
                vertical_exponent: payload[8] as i8, horizontal_exponent: payload[9] as i8,
            })
        }
    }
}

pub type Part2ResolutionPair = (Option<crate::jp2::Resolution>, Option<crate::jp2::Resolution>);

pub open spec fn part2_resolution_finish(base: u64, capture: Option<crate::jp2::Resolution>, display: Option<crate::jp2::Resolution>)
    -> Result<Part2ResolutionPair, crate::DecodeError>
{
    if capture.is_none() && display.is_none() {
        Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::MissingRequiredStructure })
    } else { Ok((capture, display)) }
}

pub open spec fn part2_resolution_progress_error(base: u64, position: usize) -> crate::DecodeError {
    match part2_box_add_offset(base, position as u64) {
        Err(error) => error,
        Ok(offset) => crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength },
    }
}

#[verifier::opaque]
pub open spec fn part2_resolution_boxes(
    payload: Seq<u8>, reader: Part2BoxReaderState, base: u64,
    capture: Option<crate::jp2::Resolution>, display: Option<crate::jp2::Resolution>,
) -> Result<Part2ResolutionPair, crate::DecodeError>
    decreases payload.len() as int - reader.position as int,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => part2_resolution_finish(base, capture, display),
        Some(result) => {
            if next.1.position <= reader.position || next.1.position > payload.len() {
                Err(part2_resolution_progress_error(base, reader.position))
            } else {
                match result {
                    Err(error) => Err(part2_box_rebase_error(error, base)),
                    Ok(input) => {
                        if input.0.0 == crate::jp2::BoxType::CAPTURE_RESOLUTION {
                            if capture.is_some() {
                                Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
                            } else {
                                match part2_parse_resolution(input, base) {
                                    Err(error) => Err(error),
                                    Ok(value) => part2_resolution_boxes(payload, next.1, base, Some(value), display),
                                }
                            }
                        } else if input.0.0 == crate::jp2::BoxType::DISPLAY_RESOLUTION {
                            if display.is_some() {
                                Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxOrder))
                            } else {
                                match part2_parse_resolution(input, base) {
                                    Err(error) => Err(error),
                                    Ok(value) => part2_resolution_boxes(payload, next.1, base, capture, Some(value)),
                                }
                            }
                        } else { part2_resolution_boxes(payload, next.1, base, capture, display) }
                    },
                }
            }
        },
    }
}

pub open spec fn part2_parse_resolution_superbox(payload: Seq<u8>, limits: crate::ResourceLimits, base: u64)
    -> Result<Part2ResolutionPair, crate::DecodeError>
{
    match part2_box_reader_from_input(payload, limits) {
        Err(error) => Err(error),
        Ok(reader) => part2_resolution_boxes(payload, reader, base, None, None),
    }
}

}
