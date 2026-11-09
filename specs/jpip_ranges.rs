//! Actual range requests, native-order availability and packet byte reads.

use super::*;

verus! {

pub type Part2JpipRange = (Part2JpipDatabin, u64, u64);
pub type Part2JpipMissing = (Part2JpipDatabin, u64, Option<u64>);
pub type Part2JpipAvailabilityReport = (crate::jpip::JpipAvailability, u64, u64, Seq<Part2JpipMissing>);
pub type Part2JpipPacket = (Part2JpipRange, u16);

pub open spec fn part2_jpip_range_overflow(offset: u64) -> crate::DecodeError {
    part2_jpip_cache_error(offset, crate::MalformedKind::ArithmeticOverflow)
}

pub open spec fn part2_jpip_range_new(
    id: Part2JpipDatabin, offset: u64, length: u64,
) -> Result<Part2JpipRange, crate::DecodeError> {
    if length == 0 { Err(part2_jpip_cache_error(offset, crate::MalformedKind::InvalidJpipFragment)) }
    else if offset as nat + length as nat > u64::MAX as nat { Err(part2_jpip_range_overflow(offset)) }
    else { Ok((id, offset, length)) }
}

pub open spec fn part2_jpip_complete_missing(cache: Part2JpipCache, id: Part2JpipDatabin) -> Seq<Part2JpipMissing> {
    match part2_jpip_cache_status(cache, id) {
        None => seq![(id, 0, None)],
        Some(status) => seq![(id, status.1, match status.0 {
            None => None,
            Some(length) => Some(part9_missing_length(length as nat, if status.1 < length { status.1 as nat } else { length as nat }) as u64),
        })],
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_missing_total(missing: Seq<Part2JpipMissing>, position: nat, total: u64)
    -> Result<u64, crate::DecodeError>
    decreases if position < missing.len() { missing.len() - position } else { 0 },
{
    if position >= missing.len() { Ok(total) }
    else {
        let length = match missing[position as int].2 { None => 0u64, Some(length) => length };
        let next = total as nat + length as nat;
        if next > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { part2_jpip_missing_total(missing, position + 1, next as u64) }
    }
}

pub open spec fn part2_jpip_availability_finish(required: u64, missing: Seq<Part2JpipMissing>)
    -> Result<Part2JpipAvailabilityReport, crate::DecodeError> {
    match part2_jpip_missing_total(missing, 0, 0) {
        Err(error) => Err(error),
        Ok(total) => if total > required { Err(part2_jpip_range_overflow(0)) }
        else {
            let available = (required - total) as u64;
            if part9_available_bytes(required as nat, total as nat) as u64 != available {
                Err(part2_jpip_range_overflow(0))
            } else {
                Ok((if complete_jpip_range(available as nat, required as nat) { crate::jpip::JpipAvailability::Available }
                    else if available == 0 { crate::jpip::JpipAvailability::Missing }
                    else { crate::jpip::JpipAvailability::Partial }, required, available, missing))
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_availability_fragments(
    fragments: Seq<Part2JpipStoredFragment>, requested: Part2JpipRange, end: u64,
    position: nat, cursor: u64, work: u64, missing: Seq<Part2JpipMissing>, work_limit: u64,
) -> Result<(u64, u64, Seq<Part2JpipMissing>), crate::DecodeError>
    decreases if position < fragments.len() { fragments.len() - position } else { 0 },
{
    if position >= fragments.len() || cursor >= end { Ok((cursor, work, missing)) }
    else {
        let next_work = work as nat + 1;
        if next_work > u64::MAX as nat { Err(part2_jpip_range_overflow(cursor)) }
        else if next_work > work_limit as nat {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                limit: work_limit, actual: next_work as u64 })
        } else {
            let fragment = fragments[position as int];
            let fragment_end = part2_jpip_stored_end(fragment);
            if fragment_end <= cursor {
                part2_jpip_availability_fragments(fragments, requested, end, position + 1, cursor, next_work as u64, missing, work_limit)
            } else if fragment.0 >= end { Ok((cursor, next_work as u64, missing)) }
            else {
                let gap_end = if fragment.0 < end { fragment.0 } else { end };
                let next_missing = if fragment.0 > cursor {
                    missing.push((requested.0, cursor, Some((gap_end - cursor) as u64)))
                } else { missing };
                let gap_cursor = if fragment.0 > cursor { gap_end } else { cursor };
                let next_cursor = if gap_cursor < end && fragment_end > gap_cursor {
                    if fragment_end < end { fragment_end } else { end }
                } else { gap_cursor };
                part2_jpip_availability_fragments(fragments, requested, end, position + 1, next_cursor, next_work as u64, next_missing, work_limit)
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_availability_request(
    cache: Part2JpipCache, requested: Part2JpipRange, required: u64, work: u64, missing: Seq<Part2JpipMissing>,
) -> Result<(u64, u64, Seq<Part2JpipMissing>), crate::DecodeError> {
    let end = requested.1 as nat + requested.2 as nat;
    let input_limit = crate::limits::resource_input_byte_limit(&cache.0);
    if end > u64::MAX as nat { Err(part2_jpip_range_overflow(requested.1)) }
    else if end > input_limit as nat {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes, limit: input_limit, actual: end as u64 })
    } else {
        let next_required = required as nat + requested.2 as nat;
        if next_required > u64::MAX as nat { Err(part2_jpip_range_overflow(requested.1)) }
        else if next_required > input_limit as nat {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes, limit: input_limit, actual: next_required as u64 })
        } else {
            match part2_jpip_find_databin(cache.1, requested.0, 0) {
                None => Ok((next_required as u64, work, missing.push((requested.0, requested.1, Some(requested.2))))),
                Some(index) => if index as nat >= cache.1.len() { Err(part2_jpip_range_overflow(requested.1)) }
                else {
                    match part2_jpip_availability_fragments(cache.1[index as int].1, requested, end as u64,
                        0, requested.1, work, missing, crate::limits::resource_work_limit(&cache.0)) {
                        Err(error) => Err(error),
                        Ok(scan) => Ok((next_required as u64, scan.1,
                            if scan.0 < end { scan.2.push((requested.0, scan.0, Some((end - scan.0) as u64))) }
                            else { scan.2 })),
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_availability_remaining(
    cache: Part2JpipCache, ranges: Seq<Part2JpipRange>, position: nat,
    required: u64, work: u64, missing: Seq<Part2JpipMissing>,
) -> Result<Part2JpipAvailabilityReport, crate::DecodeError>
    decreases if position < ranges.len() { ranges.len() - position } else { 0 },
{
    if position >= ranges.len() { part2_jpip_availability_finish(required, missing) }
    else {
        match part2_jpip_availability_request(cache, ranges[position as int], required, work, missing) {
            Err(error) => Err(error),
            Ok(next) => part2_jpip_availability_remaining(cache, ranges, position + 1, next.0, next.1, next.2),
        }
    }
}

pub open spec fn part2_jpip_cache_availability(cache: Part2JpipCache, ranges: Seq<Part2JpipRange>)
    -> Result<Part2JpipAvailabilityReport, crate::DecodeError> {
    if ranges.len() as u64 > crate::limits::resource_packet_limit(&cache.0) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Packets,
            limit: crate::limits::resource_packet_limit(&cache.0), actual: ranges.len() as u64 })
    } else { part2_jpip_availability_remaining(cache, ranges, 0, 0, 0, Seq::empty()) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_packet_total(packets: Seq<Part2JpipPacket>, position: nat, total: u64)
    -> Result<u64, crate::DecodeError>
    decreases if position < packets.len() { packets.len() - position } else { 0 },
{
    if position >= packets.len() { Ok(total) }
    else {
        let next = total as nat + packets[position as int].0.2 as nat;
        if next > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { part2_jpip_packet_total(packets, position + 1, next as u64) }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_packet_fragments(
    fragments: Seq<Part2JpipStoredFragment>, position: nat, cursor: u64, end: u64, output: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if position < fragments.len() { fragments.len() - position } else { 0 },
{
    if position >= fragments.len() || cursor >= end {
        if cursor != end { Err(part2_jpip_cache_error(cursor, crate::MalformedKind::MissingRequiredStructure)) } else { Ok(output) }
    } else {
        let fragment = fragments[position as int];
        let fragment_end = part2_jpip_stored_end(fragment);
        if fragment_end <= cursor { part2_jpip_packet_fragments(fragments, position + 1, cursor, end, output) }
        else if fragment.0 > cursor { Err(part2_jpip_cache_error(cursor, crate::MalformedKind::MissingRequiredStructure)) }
        else {
            let copy_end = if fragment_end < end { fragment_end } else { end };
            let start = cursor as nat - fragment.0 as nat;
            if start > usize::MAX as nat || copy_end < fragment.0 { Err(part2_jpip_range_overflow(cursor)) }
            else {
                let local_end = copy_end as nat - fragment.0 as nat;
                if local_end > usize::MAX as nat || start > local_end || local_end > fragment.1.len() {
                    Err(part2_jpip_range_overflow(cursor))
                } else {
                    part2_jpip_packet_fragments(fragments, position + 1, copy_end, end,
                        output + fragment.1.subrange(start as int, local_end as int))
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_packet_remaining(
    cache: Part2JpipCache, packets: Seq<Part2JpipPacket>, position: nat, output: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if position < packets.len() { packets.len() - position } else { 0 },
{
    if position >= packets.len() { Ok(output) }
    else {
        let range = packets[position as int].0;
        match part2_jpip_find_databin(cache.1, range.0, 0) {
            None => Err(part2_jpip_cache_error(range.1, crate::MalformedKind::MissingRequiredStructure)),
            Some(index) => if index as nat >= cache.1.len() { Err(part2_jpip_range_overflow(range.1)) }
            else {
                let end = range.1 as nat + range.2 as nat;
                if end > u64::MAX as nat { Err(part2_jpip_range_overflow(range.1)) }
                else {
                    match part2_jpip_packet_fragments(cache.1[index as int].1, 0, range.1, end as u64, output) {
                        Err(error) => Err(error),
                        Ok(bytes) => part2_jpip_packet_remaining(cache, packets, position + 1, bytes),
                    }
                }
            },
        }
    }
}

pub open spec fn part2_jpip_read_packets(cache: Part2JpipCache, packets: Seq<Part2JpipPacket>)
    -> Result<Seq<u8>, crate::DecodeError> {
    match part2_jpip_packet_total(packets, 0, 0) {
        Err(error) => Err(error),
        Ok(total) => if total > crate::limits::resource_input_byte_limit(&cache.0) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(&cache.0), actual: total })
        } else if total as nat > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { part2_jpip_packet_remaining(cache, packets, 0, Seq::empty()) },
    }
}

}
