//! Complete raw automatic tile-header normalization Results.

use super::*;

verus! {

/// Operation (0: byte-vector capacity, 1: byte extension), old length,
/// requested elements/additional bytes, and observed reservation success.
/// Physical capacity and allocator availability retain the existing vstd boundary.
pub type Part2JpipStorageEvent = (u8, usize, usize, bool);

pub open spec fn part2_jpip_storage_event(
    events: Seq<Part2JpipStorageEvent>, operation: u8, length: usize, requested: usize,
) -> Option<bool> {
    if events.len() == 0 || events[0].0 != operation
        || events[0].1 != length || events[0].2 != requested {
        None
    } else { Some(events[0].3) }
}

pub open spec fn part2_jpip_main_header_finish(
    result: Result<Seq<u8>, crate::DecodeError>, events: Seq<Part2JpipStorageEvent>,
) -> Option<Result<Seq<u8>, crate::DecodeError>> {
    if events.len() == 0 { Some(result) } else { None }
}

#[verifier::opaque]
pub open spec fn part2_jpip_main_header_scan(
    input: Seq<u8>, position: usize, remaining: usize, output: Seq<u8>,
    events: Seq<Part2JpipStorageEvent>,
) -> Option<Result<Seq<u8>, crate::DecodeError>>
    decreases remaining,
{
    if position as nat >= input.len() {
        part2_jpip_main_header_finish(Ok(output), events)
    } else if remaining == 0 {
        part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
            position as u64, crate::MalformedKind::InvalidMarkerLength)), events)
    } else {
        match part2_jpip_marker_segment(input, position) {
            Err(error) => part2_jpip_main_header_finish(Err(error), events),
            Ok((marker, _, end)) => if marker == 0xff90 || marker == 0xff93 || marker == 0xffd9 {
                part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
                    position as u64, crate::MalformedKind::InvalidMarkerOrder)), events)
            } else if part9_reframed_marker_removed(marker as nat, false) {
                part2_jpip_main_header_scan(input, end, (remaining - 1) as usize, output, events)
            } else if position > end || end as nat > input.len() {
                part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
                    position as u64, crate::MalformedKind::Truncated)), events)
            } else {
                let bytes = input.subrange(position as int, end as int);
                match part2_jpip_storage_event(events, 1, output.len() as usize, bytes.len() as usize) {
                    None => None,
                    Some(false) => part2_jpip_main_header_finish(
                        Err(crate::DecodeError::AllocationFailed), events.drop_first()),
                    Some(true) => part2_jpip_main_header_scan(input, end, (remaining - 1) as usize,
                        output + bytes, events.drop_first()),
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_normalize_main_header(
    input: Seq<u8>, events: Seq<Part2JpipStorageEvent>,
) -> Option<Result<Seq<u8>, crate::DecodeError>> {
    if input.len() < 2 || input[0] != 0xff || input[1] != 0x4f {
        part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
            0, crate::MalformedKind::MissingRequiredStructure)), events)
    } else {
        match part2_jpip_storage_event(events, 0, 0, 2) {
            None => None,
            Some(false) => part2_jpip_main_header_finish(
                Err(crate::DecodeError::AllocationFailed), events.drop_first()),
            Some(true) => match part2_jpip_storage_event(events.drop_first(), 1, 0, 2) {
                None => None,
                Some(false) => part2_jpip_main_header_finish(
                    Err(crate::DecodeError::AllocationFailed), events.drop_first().drop_first()),
                Some(true) => part2_jpip_main_header_scan(input, 2, input.len() as usize,
                    seq![0xffu8, 0x4fu8], events.drop_first().drop_first()),
            },
        }
    }
}

pub open spec fn part2_jpip_main_header_result(
    input: Seq<u8>, result: Result<Seq<u8>, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part2JpipStorageEvent>|
        part2_jpip_normalize_main_header(input, events) == Some(result)
}

#[verifier::opaque]
pub open spec fn part2_jpip_normalized_header_scan(
    source: Seq<u8>, position: usize, remaining: usize, output: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases remaining,
{
    if position as nat >= source.len() {
        if position as nat != source.len() {
            Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::MissingRequiredStructure))
        } else { Ok(output + seq![0xffu8, 0x93u8]) }
    } else if remaining == 0 {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidMarkerLength))
    } else if position as nat + 2 <= source.len()
        && source[position as int] == 0xff && source[position as int + 1] == 0x93 {
        let end = position as nat + 2;
        if end > usize::MAX as nat { Err(part2_jpip_range_overflow(position as u64)) }
        else if end != source.len() {
            Err(part2_jpip_cache_error(end as u64, crate::MalformedKind::MissingRequiredStructure))
        } else { Ok(output + seq![0xffu8, 0x93u8]) }
    } else {
        match part2_jpip_marker_segment(source, position) {
            Err(error) => Err(error),
            Ok((marker, _, end)) => if position > end || end as nat > source.len() {
                Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated))
            } else {
                part2_jpip_normalized_header_scan(source, end, (remaining - 1) as usize,
                    if part9_reframed_marker_removed(marker as nat, true) { output }
                    else { output + source.subrange(position as int, end as int) })
            },
        }
    }
}

pub open spec fn part2_jpip_normalized_header_after_start(
    source: Seq<u8>, tile: u16, index: usize, count: u8, start: usize,
) -> Result<Seq<u8>, crate::DecodeError> {
    if index > u8::MAX as usize { Err(part2_jpip_range_overflow(0)) }
    else {
        part2_jpip_normalized_header_scan(source, start, source.len() as usize,
            seq![0xffu8, 0x90u8, 0u8, 10u8, ((tile >> 8) & 0xff) as u8,
                (tile & 0xff) as u8, 0u8, 0u8, 0u8, 0u8, index as u8, count])
    }
}

pub open spec fn part2_jpip_normalize_tile_header(
    source: Seq<u8>, tile: u16, index: usize, count: u8,
) -> Result<Seq<u8>, crate::DecodeError> {
    if source.len() >= 2 && source[0] == 0xff && source[1] == 0x90 {
        match part2_jpip_marker_segment(source, 0) {
            Err(error) => Err(error),
            Ok((marker, _, end)) => if marker != 0xff90 || end != 12 {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
            } else { part2_jpip_normalized_header_after_start(source, tile, index, count, end) },
        }
    } else { part2_jpip_normalized_header_after_start(source, tile, index, count, 0) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_normalized_header_entries(
    entries: Seq<Part2JpipTransition>, tile: u16, position: nat, output: Seq<Seq<u8>>,
) -> Result<Seq<Seq<u8>>, crate::DecodeError>
    decreases if position < entries.len() { entries.len() - position } else { 0 },
{
    if position >= entries.len() { Ok(output) }
    else {
        match part2_jpip_normalize_tile_header(entries[position as int].5, tile,
            position as usize, entries.len() as u8) {
            Err(error) => Err(error),
            Ok(header) => part2_jpip_normalized_header_entries(entries, tile, position + 1, output.push(header)),
        }
    }
}

pub open spec fn part2_jpip_normalize_automatic_tile_headers(input: Seq<u8>, tile: u16)
    -> Result<Seq<Seq<u8>>, crate::DecodeError> {
    match part2_jpip_parse_transitions(input, tile) {
        Err(error) => Err(error),
        Ok(entries) => if entries.len() > u8::MAX as nat { Err(part2_jpip_range_overflow(0)) }
            else { part2_jpip_normalized_header_entries(entries, tile, 0, Seq::empty()) },
    }
}

}
