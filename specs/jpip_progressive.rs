//! Actual caller-planned progressive availability and full/selected update Results.

use super::*;

verus! {

pub type Part2JpipProgressiveDecoder = (Part2JpipPlan, u16);
pub type Part2JpipProgressiveUpdate = (
    crate::jpip::JpipProgressiveStatus, u16, u16, Seq<Part2JpipMissing>, Option<Part1DecodedTypedImage>,
);

pub type Part2JpipAutomaticPacket = (Part2JpipDatabin, Option<Seq<u8>>, u64, bool, u16, u16);
pub type Part2JpipAutomaticTilePart = (Seq<u8>, Seq<Part2JpipAutomaticPacket>, bool, bool);

#[verifier::opaque]
pub open spec fn part2_jpip_partition_bytes(
    packets: Seq<Part2JpipAutomaticPacket>, target: u64, end: nat, consumed: u64,
) -> Result<Option<usize>, crate::DecodeError>
    decreases if end < packets.len() { packets.len() - end } else { 0 },
{
    if end < packets.len() && consumed < target {
        match packets[end as int].1 {
            None => Ok(None),
            Some(bytes) => {
                let next = consumed as nat + (bytes.len() as u64) as nat;
                if next > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                else { part2_jpip_partition_bytes(packets, target, end + 1, next as u64) }
            },
        }
    } else if consumed != target {
        Err(part2_jpip_cache_error(consumed, crate::MalformedKind::InvalidPacketLength))
    } else { Ok(Some(end as usize)) }
}

pub open spec fn part2_jpip_partition_end(
    packets: Seq<Part2JpipAutomaticPacket>, transition: Part2JpipTransition,
    part: nat, count: nat, start: usize,
) -> Result<Option<usize>, crate::DecodeError> {
    if part + 1 == count { Ok(Some(packets.len() as usize)) }
    else {
        match transition.2 {
            Some(packets_in_part) => if packets_in_part > usize::MAX as u64 {
                Err(part2_jpip_range_overflow(0))
            } else if start as nat + packets_in_part as nat > usize::MAX as nat {
                Err(part2_jpip_range_overflow(0))
            } else {
                let end = (start as nat + packets_in_part as nat) as usize;
                if end as nat > packets.len() {
                    Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidPacketLength))
                } else { Ok(Some(end)) }
            },
            None => match transition.3 {
                Some(target) => part2_jpip_partition_bytes(packets, target, start as nat, 0),
                None => Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_partition_parts(
    headers: Seq<Seq<u8>>, states: Seq<Part2OwnedTilePart>, transitions: Seq<Part2JpipTransition>,
    packets: Seq<Part2JpipAutomaticPacket>, part: nat, start: usize,
    output: Seq<Part2JpipAutomaticTilePart>,
) -> Result<Option<Seq<Part2JpipAutomaticTilePart>>, crate::DecodeError>
    decreases if part < headers.len() { headers.len() - part } else { 0 },
{
    if part >= headers.len() {
        if start as nat != packets.len() {
            Err(part2_jpip_cache_error(start as u64, crate::MalformedKind::InvalidPacketLength))
        } else { Ok(Some(output)) }
    } else if part >= transitions.len() || part >= states.len() {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
    } else {
        match part2_jpip_partition_end(packets, transitions[part as int], part, headers.len(), start) {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(end)) => if start > end || end as nat > packets.len() {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidPacketLength))
            } else {
                let state = states[part as int];
                part2_jpip_partition_parts(headers, states, transitions, packets, part + 1, end,
                    output.push((headers[part as int], packets.subrange(start as int, end as int),
                        state.coding_style.sop_markers, state.coding_style.eph_markers)))
            },
        }
    }
}

pub open spec fn part2_jpip_partition_automatic_tiles(
    headers: Seq<Seq<u8>>, states: Seq<Part2OwnedTilePart>, transitions: Seq<Part2JpipTransition>,
    packets: Seq<Part2JpipAutomaticPacket>,
) -> Result<Option<Seq<Part2JpipAutomaticTilePart>>, crate::DecodeError> {
    if headers.len() != states.len() || headers.len() != transitions.len() || headers.len() == 0 {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
    } else { part2_jpip_partition_parts(headers, states, transitions, packets, 0, 0, Seq::empty()) }
}

pub open spec fn part2_jpip_ordinal_matrix_write(
    before: Seq<Seq<Option<u16>>>, after: Seq<Seq<Option<u16>>>,
    execution: usize, layer: u16, sequence: u16,
) -> bool {
    (execution as nat) < before.len()
        && (layer as nat) < before[execution as int].len()
        && before[execution as int][layer as int].is_none()
        && after == before.update(execution as int,
            before[execution as int].update(layer as int, Some(sequence)))
}

pub open spec fn part2_jpip_packet_matrix_write(
    before: Seq<Seq<Option<Seq<u8>>>>, after: Seq<Seq<Option<Seq<u8>>>>,
    execution: usize, layer: u16, bytes: Seq<u8>,
) -> bool {
    (execution as nat) < before.len()
        && (layer as nat) < before[execution as int].len()
        && after == before.update(execution as int,
            before[execution as int].update(layer as int, Some(bytes)))
}

#[verifier::opaque]
pub open spec fn part2_jpip_progressive_layers(
    cache: Part2JpipCache, packets: Seq<Part2JpipPacket>, ends: Seq<usize>, layer: nat, start: usize,
) -> Result<(u16, Seq<Part2JpipMissing>), crate::DecodeError>
    decreases if layer < ends.len() { ends.len() - layer } else { 0 },
{
    if layer >= ends.len() {
        if layer > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { Ok((layer as u16, Seq::empty())) }
    } else {
        let end = ends[layer as int];
        if start > end || end as nat > packets.len() { Err(part2_jpip_range_overflow(0)) }
        else {
            let ranges = packets.subrange(start as int, end as int).map_values(|packet: Part2JpipPacket| packet.0);
            match part2_jpip_cache_availability(cache, ranges) {
                Err(error) => Err(error),
                Ok(report) => if report.0 != crate::jpip::JpipAvailability::Available {
                    if layer > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                    else { Ok((layer as u16, report.3)) }
                } else { part2_jpip_progressive_layers(cache, packets, ends, layer + 1, end) },
            }
        }
    }
}

pub open spec fn part2_jpip_progressive_availability(cache: Part2JpipCache, plan: Part2JpipPlan)
    -> Result<(u16, Seq<Part2JpipMissing>), crate::DecodeError> {
    let main = part2_jpip_append_complete_requirement(cache, plan.0,
        (crate::jpip::JpipAvailability::Available, 0, 0, Seq::empty()));
    match main.0 {
        Err(error) => Err(error),
        Ok(()) => {
            let tile = part2_jpip_append_complete_requirement(cache, plan.1, main.1);
            match tile.0 {
                Err(error) => Err(error),
                Ok(()) => if tile.1.3.len() != 0 { Ok((0, tile.1.3)) }
                else { part2_jpip_progressive_layers(cache, plan.2, plan.3, 0, 0) },
            }
        },
    }
}

pub open spec fn part2_jpip_progressive_update(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
) -> (Result<Part2JpipProgressiveUpdate, crate::DecodeError>, Part2JpipProgressiveDecoder) {
    let previous = decoder.1;
    let planned = decoder.0.3.len() as u16;
    match part2_jpip_progressive_availability(cache, decoder.0) {
        Err(error) => (Err(error), decoder),
        Ok((available, missing)) => {
            if !valid_jpip_progressive_update(previous as nat, available as nat, planned as nat) {
                (Err(part2_jpip_plan_invalid(0)), decoder)
            } else if available <= previous {
                (Ok((if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                    else { crate::jpip::JpipProgressiveStatus::WaitingForData }, previous, available, missing, None)), decoder)
            } else {
                match part2_jpip_transcode(cache, decoder.0, available) {
                    Err(error) => (Err(error), decoder),
                    Ok(transcoded) => match transcoded.2 {
                        None => (Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)), decoder),
                        Some(bytes) => match part2_decode_raw_codestream(
                            bytes, crate::options::decode_options_limits(options), selection) {
                            Err(error) => (Err(error), decoder),
                            Ok(image) => (Ok((
                                if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                                else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
                                previous, available, missing, Some(image),
                            )), (decoder.0, available)),
                        },
                    },
                }
            }
        },
    }
}

}
