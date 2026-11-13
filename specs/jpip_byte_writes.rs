//! Exact returned Results and byte frames for JPIP's saturating word writer.

use super::*;

verus! {

pub open spec fn part2_jpip_u32_bytes(value: u32) -> Seq<u8> {
    seq![((value >> 24) & 0xff) as u8, ((value >> 16) & 0xff) as u8,
        ((value >> 8) & 0xff) as u8, (value & 0xff) as u8]
}

pub open spec fn part2_jpip_write_u32_end(position: usize) -> nat {
    if position as nat + 4 > usize::MAX as nat { usize::MAX as nat } else { position as nat + 4 }
}

pub open spec fn part2_jpip_write_u32(
    before: Seq<u8>, position: usize, value: u32,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    let end = part2_jpip_write_u32_end(position);
    if position as nat > end || end > before.len() {
        (Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated)), before)
    } else {
        let count = end - position as nat;
        (if count == 4 { Ok(()) } else {
            Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated))
        }, before.subrange(0, position as int) + part2_jpip_u32_bytes(value).subrange(0, count as int)
            + before.subrange(end as int, before.len() as int))
    }
}

pub proof fn part2_jpip_write_u32_short_saturated_window(
    before: Seq<u8>, position: usize, value: u32,
)
    requires before.len() == usize::MAX as nat, position as nat + 4 > usize::MAX as nat,
    ensures part2_jpip_write_u32(before, position, value) == (
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated)),
        before.subrange(0, position as int) + part2_jpip_u32_bytes(value).subrange(
            0, usize::MAX as int - position as int),
    ),
{
    assert(before.subrange(usize::MAX as int, before.len() as int) =~= Seq::<u8>::empty());
}

pub open spec fn part2_jpip_empty_packet_bytes(sop: bool, eph: bool, sequence: u16) -> Seq<u8> {
    (if sop {
        seq![0xffu8, 0x91u8, 0u8, 4u8, ((sequence >> 8) & 0xff) as u8, (sequence & 0xff) as u8]
    } else { Seq::empty() }) + seq![0u8]
        + if eph { seq![0xffu8, 0x92u8] } else { Seq::empty() }
}

pub open spec fn part2_jpip_append_empty_packet(
    before: Seq<u8>, sop: bool, eph: bool, sequence: u16,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    (Ok(()), before + part2_jpip_empty_packet_bytes(sop, eph, sequence))
}

pub open spec fn part2_jpip_template_append(before: Seq<u8>, header: Seq<u8>)
    -> Result<Seq<u8>, crate::DecodeError> {
    if header.len() > u32::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else if before.len() + 6 > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else {
        let written = part2_jpip_write_u32(before + header,
            (before.len() + 6) as usize, header.len() as u32);
        match written.0 { Err(error) => Err(error), Ok(()) => Ok(written.1) }
    }
}

pub open spec fn part2_jpip_template_finish(output: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Seq<u8>, crate::DecodeError> {
    let bytes = output + seq![0xffu8, 0xd9u8];
    if bytes.len() as u64 > crate::limits::resource_input_byte_limit(limits) {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::InputBytes,
            limit: crate::limits::resource_input_byte_limit(limits), actual: bytes.len() as u64,
        })
    } else { Ok(bytes) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_transition_template_fold(
    headers: Seq<Seq<Seq<u8>>>, tile: nat, part: nat, output: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if tile < headers.len() { headers.len() - tile } else { 0 },
        if tile < headers.len() && part < headers[tile as int].len() {
            headers[tile as int].len() - part
        } else { 0 },
{
    if tile >= headers.len() { part2_jpip_template_finish(output, limits) }
    else if part >= headers[tile as int].len() {
        part2_jpip_transition_template_fold(headers, tile + 1, 0, output, limits)
    } else {
        match part2_jpip_template_append(output, headers[tile as int][part as int]) {
            Err(error) => Err(error),
            Ok(next) => part2_jpip_transition_template_fold(headers, tile, part + 1, next, limits),
        }
    }
}

pub open spec fn part2_jpip_transition_template(
    main: Seq<u8>, headers: Seq<Seq<Seq<u8>>>, limits: &crate::ResourceLimits,
) -> Result<Seq<u8>, crate::DecodeError> {
    part2_jpip_transition_template_fold(headers, 0, 0, main, limits)
}

#[verifier::opaque]
pub open spec fn part2_jpip_flat_template_fold(
    headers: Seq<Seq<u8>>, index: nat, output: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if index < headers.len() { headers.len() - index } else { 0 },
{
    if index >= headers.len() { part2_jpip_template_finish(output, limits) }
    else {
        match part2_jpip_template_append(output, headers[index as int]) {
            Err(error) => Err(error),
            Ok(next) => part2_jpip_flat_template_fold(headers, index + 1, next, limits),
        }
    }
}

pub open spec fn part2_jpip_flat_template(
    main: Seq<u8>, headers: Seq<Seq<u8>>, limits: &crate::ResourceLimits,
) -> Result<Seq<u8>, crate::DecodeError> {
    part2_jpip_flat_template_fold(headers, 0, main, limits)
}

}
