//! Complete raw automatic tile-header normalization Results.

use super::*;

verus! {

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
