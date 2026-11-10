//! Automatic codestream header normalization and tile-part template construction.

use super::{
    AutomaticPacket, AutomaticTilePart, DecodeError, EOC, JpipTilePartTransition, MalformedKind,
    Resource, ResourceLimits, SOC, copy_bytes, parse_tile_part_transitions, read_u16_be,
    write_u32_be,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) fn normalize_main_header(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    if !input.starts_with(&SOC) {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    let mut output = vec![SOC[0], SOC[1]];
    let mut position = 2_usize;
    let mut remaining_markers = input.len();
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(decreases remaining_markers,)
    )]
    while position < input.len() {
        if remaining_markers == 0 {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerLength,
            ));
        }
        remaining_markers -= 1;
        let (marker, _, end) = marker_segment(input, position)?;
        if matches!(marker, 0xff90 | 0xff93 | 0xffd9) {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        if !crate::refinement::jpip_reframed_marker_removed(marker, false) {
            output.extend_from_slice(input.get(position..end).ok_or_else(|| {
                DecodeError::malformed(position as u64, MalformedKind::Truncated)
            })?);
        }
        position = end;
    }
    Ok(output)
}

pub(super) fn normalize_automatic_tile_headers(
    input: &[u8],
    tile: u16,
) -> Result<Vec<Vec<u8>>, DecodeError> {
    let transitions = parse_tile_part_transitions(input, tile)?;
    let count = u8::try_from(transitions.len())
        .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    let mut output = Vec::with_capacity(transitions.len());
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= transitions.len(),
            decreases transitions.len() - index,
        )
    )]
    while index < transitions.len() {
        let transition = transitions
            .get(index)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?;
        let source = transition.header_bytes();
        let marker_start = if source.starts_with(&[0xff, 0x90]) {
            let (marker, _, end) = marker_segment(source, 0)?;
            if marker != 0xff90 || end != 12 {
                return Err(DecodeError::malformed(0, MalformedKind::InvalidTilePart));
            }
            end
        } else {
            0
        };
        let mut header = vec![0xff, 0x90, 0, 10];
        header.push(
            u8::try_from((tile >> 8) & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        );
        header.push(
            u8::try_from(tile & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        );
        header.extend_from_slice(&[0, 0, 0, 0]);
        header.push(
            u8::try_from(index)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        );
        header.push(count);
        let mut position = marker_start;
        let mut found_sod = false;
        let mut remaining_markers = source.len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases remaining_markers,)
        )]
        while position < source.len() {
            if remaining_markers == 0 {
                return Err(DecodeError::malformed(
                    position as u64,
                    MalformedKind::InvalidMarkerLength,
                ));
            }
            remaining_markers -= 1;
            if source.get(position..position.saturating_add(2)) == Some(&[0xff, 0x93]) {
                position = position.checked_add(2).ok_or_else(|| {
                    DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
                })?;
                found_sod = true;
                break;
            }
            let (marker, _, end) = marker_segment(source, position)?;
            if !crate::refinement::jpip_reframed_marker_removed(marker, true) {
                header.extend_from_slice(source.get(position..end).ok_or_else(|| {
                    DecodeError::malformed(position as u64, MalformedKind::Truncated)
                })?);
            }
            position = end;
        }
        if !found_sod || position != source.len() {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        header.extend_from_slice(&[0xff, 0x93]);
        output.push(header);
        index += 1;
    }
    Ok(output)
}

pub(super) fn partition_automatic_tile_parts(
    headers: &[Vec<u8>],
    states: &[&crate::codestream::TilePartPayload<'_>],
    transitions: &[JpipTilePartTransition],
    packets: &[AutomaticPacket],
) -> Result<Option<Vec<AutomaticTilePart>>, DecodeError> {
    if headers.len() != states.len() || headers.len() != transitions.len() || headers.is_empty() {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidTilePart));
    }
    let mut output = Vec::with_capacity(headers.len());
    let mut packet_start = 0_usize;
    let mut part = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant part <= headers.len(),
            decreases headers.len() - part,
        )
    )]
    while part < headers.len() {
        let transition = transitions
            .get(part)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?;
        let mut packet_end = packet_start;
        if part + 1 == headers.len() {
            packet_end = packets.len();
        } else if let Some(count) = transition.packet_count() {
            let count = usize::try_from(count)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            packet_end = packet_start
                .checked_add(count)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            if packet_end > packets.len() {
                return Err(DecodeError::malformed(
                    0,
                    MalformedKind::InvalidPacketLength,
                ));
            }
        } else if let Some(target) = transition.data_length() {
            let mut consumed = 0_u64;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(decreases packets.len() - packet_end,)
            )]
            while packet_end < packets.len() && consumed < target {
                let packet = packets
                    .get(packet_end)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidPacketLength))?;
                let Some(bytes) = packet.bytes.as_ref() else {
                    return Ok(None);
                };
                consumed = consumed
                    .checked_add(bytes.len() as u64)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                packet_end += 1;
            }
            if consumed != target {
                return Err(DecodeError::malformed(
                    consumed,
                    MalformedKind::InvalidPacketLength,
                ));
            }
        } else {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidTilePart));
        }
        let state = states
            .get(part)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?;
        output.push(AutomaticTilePart {
            header: headers
                .get(part)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?
                .clone(),
            packets: packets
                .get(packet_start..packet_end)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidPacketLength))?
                .iter()
                .map(|packet| AutomaticPacket {
                    databin: packet.databin,
                    bytes: packet.bytes.clone(),
                    next_offset: packet.next_offset,
                    required: packet.required,
                    ordinal: packet.ordinal,
                    layer: packet.layer,
                })
                .collect(),
            sop: state.coding_style.sop_markers,
            eph: state.coding_style.eph_markers,
        });
        packet_start = packet_end;
        part += 1;
    }
    if packet_start != packets.len() {
        return Err(DecodeError::malformed(
            packet_start as u64,
            MalformedKind::InvalidPacketLength,
        ));
    }
    Ok(Some(output))
}

pub(super) fn build_automatic_transition_template(
    main: &[u8],
    tile_headers: &[Vec<Vec<u8>>],
    limits: &ResourceLimits,
) -> Result<Vec<u8>, DecodeError> {
    let mut output = copy_bytes(main);
    let mut tile = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant tile <= tile_headers.len(),
            decreases tile_headers.len() - tile,
        )
    )]
    while tile < tile_headers.len() {
        let parts = tile_headers
            .get(tile)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?;
        let mut part = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant part <= parts.len(),
                decreases parts.len() - part,
            )
        )]
        while part < parts.len() {
            let start = output.len();
            output.extend_from_slice(
                parts
                    .get(part)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?,
            );
            let length = u32::try_from(output.len() - start)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            let length_position = start
                .checked_add(6)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            write_u32_be(&mut output, length_position, length)?;
            part += 1;
        }
        tile += 1;
    }
    output.extend_from_slice(&EOC);
    if output.len() as u64 > limits.maximum_input_bytes() {
        return Err(DecodeError::limit(
            Resource::InputBytes,
            limits.maximum_input_bytes(),
            output.len() as u64,
        ));
    }
    Ok(output)
}

pub(super) fn build_automatic_template(
    main: &[u8],
    tile_headers: &[Vec<u8>],
    limits: &ResourceLimits,
) -> Result<Vec<u8>, DecodeError> {
    let mut output = copy_bytes(main);
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= tile_headers.len(),
            decreases tile_headers.len() - index,
        )
    )]
    while index < tile_headers.len() {
        let start = output.len();
        output.extend_from_slice(&tile_headers[index]);
        let length = u32::try_from(output.len() - start)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let length_position = start
            .checked_add(6)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        write_u32_be(&mut output, length_position, length)?;
        index += 1;
    }
    output.extend_from_slice(&EOC);
    if output.len() as u64 > limits.maximum_input_bytes() {
        return Err(DecodeError::limit(
            Resource::InputBytes,
            limits.maximum_input_bytes(),
            output.len() as u64,
        ));
    }
    Ok(output)
}

pub(super) fn automatic_tile_part<'a>(
    tile_parts: &'a [crate::codestream::TilePartPayload<'a>],
    tile: u16,
) -> Result<&'a crate::codestream::TilePartPayload<'a>, DecodeError> {
    let mut found = None;
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= tile_parts.len(),
            decreases tile_parts.len() - index,
        )
    )]
    while index < tile_parts.len() {
        if tile_parts[index].tile_index == tile {
            if found.is_some() {
                return Err(DecodeError::AmbiguousJpipMapping {
                    reason: crate::JpipMappingAmbiguity::TilePartBoundary,
                });
            }
            found = Some(&tile_parts[index]);
        }
        index += 1;
    }
    found.ok_or_else(|| DecodeError::malformed(0, MalformedKind::MissingRequiredStructure))
}

pub(super) fn append_empty_packet(
    output: &mut Vec<u8>,
    sop: bool,
    eph: bool,
    sequence: u16,
) -> Result<(), DecodeError> {
    let expected = crate::refinement::jpip_packet_reframed_length(1, sop, eph);
    let start = output.len();
    if sop {
        output.extend_from_slice(&[0xff, 0x91, 0, 4]);
        output.push(
            u8::try_from((sequence >> 8) & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        );
        output.push(
            u8::try_from(sequence & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        );
    }
    output.push(0);
    if eph {
        output.extend_from_slice(&[0xff, 0x92]);
    }
    if output.len().checked_sub(start) != Some(expected) {
        return Err(DecodeError::malformed(
            start as u64,
            MalformedKind::ArithmeticOverflow,
        ));
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_jpip_marker_segment(input@, position),
))]
pub(super) fn marker_segment(
    input: &[u8],
    position: usize,
) -> Result<(u16, usize, usize), DecodeError> {
    let marker = read_u16_be(input, position)?;
    if matches!(marker, 0xff4f | 0xff93 | 0xffd9) {
        let end = position.checked_add(2).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_range_overflow(position as u64),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
        )?;
        return Ok((marker, end, end));
    }
    let length_position = position.checked_add(2).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_range_overflow(position as u64),
        ))]
        || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
    )?;
    let length = usize::from(read_u16_be(input, length_position)?);
    if length < 2 {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::InvalidMarkerLength,
        ));
    }
    let end = position
        .checked_add(2)
        .and_then(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: (Option<usize>) =>
                ensures result == if value as nat + length as nat > usize::MAX as nat { None }
                    else { Some((value as nat + length as nat) as usize) },
            ))]
            |value: usize| value.checked_add(length),
        )
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_range_overflow(0),
            ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
    if end > input.len() {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::Truncated,
        ));
    }
    let payload = position.checked_add(4).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_range_overflow(position as u64),
        ))]
        || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
    )?;
    Ok((marker, payload, end))
}

pub(super) fn ceil_div_jpip(value: u64, divisor: u64) -> Result<u64, DecodeError> {
    if divisor == 0 {
        return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow));
    }
    value
        .checked_add(divisor - 1)
        .and_then(|sum| sum.checked_div(divisor))
        .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))
}
