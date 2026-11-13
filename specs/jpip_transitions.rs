//! Actual raw tile-part transition parsing and complete public cache reports.

use super::*;

verus! {

pub type Part2JpipTransition = (u16, u8, Option<u64>, Option<u64>, bool, Seq<u8>);
pub type Part2JpipSemanticNeed = (crate::jpip::JpipSemanticNeedKind, u64);
pub type Part2JpipTransitionReport = (
    crate::jpip::JpipAvailability, Seq<Part2JpipTransition>, Seq<Part2JpipSemanticNeed>, Seq<Part2JpipMissing>,
);

pub open spec fn part2_jpip_read_u16(input: Seq<u8>, position: usize) -> Result<u16, crate::DecodeError> {
    if position as nat + 2 > input.len() || position as nat + 2 > usize::MAX as nat {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated))
    }
    else { Ok(((input[position as int] as u16) << 8) | input[position as int + 1] as u16) }
}

pub open spec fn part2_jpip_read_u32(input: Seq<u8>, position: usize) -> Result<u32, crate::DecodeError> {
    if position as nat + 4 > input.len() || position as nat + 4 > usize::MAX as nat {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated))
    }
    else { Ok(((input[position as int] as u32) << 24) | ((input[position as int + 1] as u32) << 16)
        | ((input[position as int + 2] as u32) << 8) | input[position as int + 3] as u32) }
}

pub open spec fn part2_jpip_read_u64(input: Seq<u8>, position: usize) -> Result<u64, crate::DecodeError> {
    match part2_jpip_read_u32(input, position) {
        Err(error) => Err(error),
        Ok(high) => if position as nat + 4 > usize::MAX as nat {
            Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
        } else {
            match part2_jpip_read_u32(input, (position + 4) as usize) {
                Err(error) => Err(error),
                Ok(low) => Ok(((high as u64) << 32) | low as u64),
            }
        },
    }
}

pub open spec fn part2_jpip_marker_segment(input: Seq<u8>, position: usize)
    -> Result<(u16, usize, usize), crate::DecodeError> {
    match part2_jpip_read_u16(input, position) {
        Err(error) => Err(error),
        Ok(marker) => {
            let after_marker = position as nat + 2;
            if after_marker > usize::MAX as nat { Err(part2_jpip_range_overflow(position as u64)) }
            else if marker == 0xff4f || marker == 0xff93 || marker == 0xffd9 {
                Ok((marker, after_marker as usize, after_marker as usize))
            } else {
                match part2_jpip_read_u16(input, after_marker as usize) {
                    Err(error) => Err(error),
                    Ok(length) => if length < 2 {
                        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidMarkerLength))
                    } else {
                        let end = after_marker + length as nat;
                        if end > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                        else if end > input.len() {
                            Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated))
                        } else if position as nat + 4 > usize::MAX as nat { Err(part2_jpip_range_overflow(position as u64)) }
                        else { Ok((marker, (position + 4) as usize, end as usize)) }
                    },
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_plt_scan(payload: Seq<u8>, position: nat, count: u64, continuation: bool)
    -> Result<u64, crate::DecodeError>
    decreases if position < payload.len() { payload.len() - position } else { 0 },
{
    if position >= payload.len() {
        if continuation { Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidPacketLength)) } else { Ok(count) }
    } else {
        let next_continuation = payload[position as int] & 0x80 != 0;
        if !next_continuation && count == u64::MAX { Err(part2_jpip_range_overflow(0)) }
        else { part2_jpip_plt_scan(payload, position + 1, if next_continuation { count } else { (count + 1) as u64 }, next_continuation) }
    }
}

pub open spec fn part2_jpip_plt_count(payload: Seq<u8>) -> Result<u64, crate::DecodeError> {
    if payload.len() == 0 { Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidPacketLength)) }
    else { part2_jpip_plt_scan(payload, 1, 0, false) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_transition_scan(
    input: Seq<u8>, position: usize, remaining: usize, indexed: bool,
    functional: bool, packets: Option<u64>, next_plt: u16,
) -> Result<(usize, bool, Option<u64>, u16, bool), crate::DecodeError>
    decreases remaining,
{
    if position as nat >= input.len() { Ok((position, functional, packets, next_plt, false)) }
    else if remaining == 0 { Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidMarkerLength)) }
    else if position as nat + 2 <= input.len() && input[position as int] == 0xff && input[position as int + 1] == 0x93 {
        if indexed && position as nat + 2 > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { Ok((if indexed { (position + 2) as usize } else { position }, functional, packets, next_plt, true)) }
    } else {
        match part2_jpip_marker_segment(input, position) {
            Err(error) => Err(error),
            Ok((marker, start, end)) => if marker == 0xff58 {
                let payload = input.subrange(start as int, end as int);
                if indexed && (payload.len() == 0 || payload[0] as u16 != next_plt) {
                    Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidPacketLength))
                } else if indexed && next_plt == u16::MAX { Err(part2_jpip_range_overflow(0)) }
                else {
                    match part2_jpip_plt_count(payload) {
                        Err(error) => Err(error),
                        Ok(count) => {
                            let before = match packets { None => 0u64, Some(count) => count };
                            let total = before as nat + count as nat;
                            if total > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                            else { part2_jpip_transition_scan(input, end, (remaining - 1) as usize, indexed,
                                functional, Some(total as u64), if indexed { (next_plt + 1) as u16 } else { next_plt }) }
                        },
                    }
                }
            } else {
                part2_jpip_transition_scan(input, end, (remaining - 1) as usize, indexed,
                    if marker == 0xff61 || marker == 0xff64 { functional } else { true }, packets, next_plt)
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_transition_parts(
    input: Seq<u8>, tile: u16, position: usize, remaining: usize, transitions: Seq<Part2JpipTransition>,
) -> Result<Seq<Part2JpipTransition>, crate::DecodeError>
    decreases remaining,
{
    if position as nat >= input.len() { Ok(transitions) }
    else if remaining == 0 { Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidTilePart)) }
    else {
        match part2_jpip_marker_segment(input, position) {
            Err(error) => Err(error),
            Ok((marker, _, end)) => if marker != 0xff90 || end as nat != position as nat + 12 {
                Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidTilePart))
            } else {
                match part2_jpip_read_u16(input, (position + 4) as usize) {
                    Err(error) => Err(error),
                    Ok(actual_tile) => if actual_tile != tile {
                        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidTilePart))
                    } else {
                        let part = input[position as int + 10];
                        match part2_jpip_read_u32(input, (position + 6) as usize) {
                            Err(error) => Err(error),
                            Ok(length) => match part2_jpip_transition_scan(input, end, input.len() as usize, true, false, None, 0) {
                                Err(error) => Err(error),
                                Ok(scan) => if !scan.4 {
                                    Err(part2_jpip_cache_error(scan.0 as u64, crate::MalformedKind::MissingRequiredStructure))
                                } else if length == 0 && (scan.0 as nat) < input.len() {
                                    Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidTilePart))
                                } else {
                                    let header_length = scan.0 as nat - position as nat;
                                    if scan.0 < position { Err(part2_jpip_range_overflow(position as u64)) }
                                    else if length != 0 && length as nat > usize::MAX as nat {
                                        Err(part2_jpip_range_overflow(position as u64))
                                    } else if length != 0 && (length as nat) < header_length {
                                        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidTilePart))
                                    } else {
                                        let data = if length == 0 { None }
                                            else { Some((length as nat - header_length) as u64) };
                                        let transition = (actual_tile, part, scan.2, data, scan.1,
                                            input.subrange(position as int, scan.0 as int));
                                        part2_jpip_transition_parts(input, tile, scan.0, (remaining - 1) as usize, transitions.push(transition))
                                    }
                                },
                            },
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn part2_jpip_parse_transitions(input: Seq<u8>, tile: u16)
    -> Result<Seq<Part2JpipTransition>, crate::DecodeError> {
    if input.len() >= 2 && input[0] == 0xff && input[1] == 0x90 {
        part2_jpip_transition_parts(input, tile, 0, input.len() as usize, Seq::empty())
    } else {
        match part2_jpip_transition_scan(input, 0, input.len() as usize, false, false, None, 0) {
            Err(error) => Err(error),
            Ok(scan) => Ok(seq![(tile, 0u8, scan.2, None, scan.1, input)]),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_transition_needs(
    transitions: Seq<Part2JpipTransition>, position: nat, preceding_known: bool,
    needs: Seq<Part2JpipSemanticNeed>, tile: u16,
) -> Seq<Part2JpipSemanticNeed>
    decreases if position < transitions.len() { transitions.len() - position } else { 0 },
{
    if position >= transitions.len() { needs }
    else {
        let transition = transitions[position as int];
        let sufficient = jpip_tile_transition_sufficient(transition.4, preceding_known, transition.3.is_some());
        let next = if position > 0 && !sufficient {
            needs.push((crate::jpip::JpipSemanticNeedKind::TilePartTransition,
                ((tile as u64) << 8) | transition.1 as u64))
        } else { needs };
        part2_jpip_transition_needs(transitions, position + 1,
            preceding_known && (transition.2.is_some() || transition.3.is_some()), next, tile)
    }
}

pub open spec fn part2_jpip_transition_report(cache: Part2JpipCache, stream: u64, tile: u16)
    -> Result<Part2JpipTransitionReport, crate::DecodeError> {
    let id = (2u64, crate::jpip::DatabinClass::TileHeader, stream, tile as u64);
    if !part2_jpip_cache_complete(cache, id) {
        Ok((crate::jpip::JpipAvailability::Missing, Seq::empty(),
            seq![(crate::jpip::JpipSemanticNeedKind::TilePartTransition, tile as u64)], part2_jpip_complete_missing(cache, id)))
    } else {
        match part2_jpip_cache_view(cache, id) {
            Err(error) => Err(error),
            Ok(bytes) => match part2_jpip_parse_transitions(bytes, tile) {
                Err(error) => Err(error),
                Ok(transitions) => {
                    let needs = part2_jpip_transition_needs(transitions, 0, true, Seq::empty(), tile);
                    Ok((if needs.len() == 0 { crate::jpip::JpipAvailability::Available }
                        else { crate::jpip::JpipAvailability::Partial }, transitions, needs, Seq::empty()))
                },
            },
        }
    }
}

}
