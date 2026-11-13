//! Automatic codestream header normalization and tile-part template construction.

use super::{
    AutomaticPacket, AutomaticTilePart, DecodeError, EOC, JpipTilePartTransition, MalformedKind,
    Resource, ResourceLimits, SOC, copy_bytes, parse_tile_part_transitions, read_u16_be,
    write_u32_be,
};
#[cfg(verus_keep_ghost)]
use super::{
    jpip_normalized_headers_outcome, jpip_packet_bytes_outcome, jpip_transition_sequence_shapes,
    jpip_transition_view, jpip_transitions_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(test)]
#[path = "normalization_result_tests.rs"]
mod result_tests;

#[cfg(verus_keep_ghost)]
verus! {
    proof fn main_header_result_witness(
        input: Seq<u8>, events: Seq<crate::specs::Part2JpipStorageEvent>,
        result: Result<Seq<u8>, DecodeError>,
    )
        requires crate::specs::part2_jpip_normalize_main_header(input, events) == Some(result),
        ensures crate::specs::part2_jpip_main_header_result(input, result),
    {
    }

    proof fn main_header_storage_events_are_ordered() {
        reveal(crate::specs::part2_jpip_normalize_main_header);
        reveal_with_fuel(crate::specs::part2_jpip_main_header_scan, 3);
        assert(((0xffu16 << 8) | 0x64u16) == 0xff64u16) by (bit_vector);
        assert(((0xffu16 << 8) | 0x57u16) == 0xff57u16) by (bit_vector);
        assert(((0u16 << 8) | 1u16) == 1u16) by (bit_vector);
        assert(((0u16 << 8) | 3u16) == 3u16) by (bit_vector);
        let prefix = seq![(0u8, 0usize, 2usize, true), (1u8, 0usize, 2usize, true)];
        let soc = seq![0xffu8, 0x4fu8];
        let refusal = (1u8, 2usize, 5usize, false);
        assert(crate::specs::part2_jpip_normalize_main_header(soc, prefix) == Some(Ok(soc)));
        assert(crate::specs::part2_jpip_normalize_main_header(soc, prefix.push(refusal)) == None);
        assert(crate::specs::part2_jpip_normalize_main_header(Seq::empty(),
            seq![(0u8, 0usize, 2usize, false)]) == None);
        assert(crate::specs::part2_jpip_normalize_main_header(soc,
            seq![(0u8, 0usize, 3usize, false)]) == None);
        assert(crate::specs::part2_jpip_normalize_main_header(soc,
            seq![(0u8, 0usize, 2usize, false)])
            == Some(Err(DecodeError::AllocationFailed)));
        let invalid = soc + seq![0xffu8, 0x64u8, 0u8, 1u8];
        assert(crate::specs::part2_jpip_marker_segment(invalid, 2)
            == Err(crate::specs::part2_jpip_cache_error(2, MalformedKind::InvalidMarkerLength)));
        assert(crate::specs::part2_jpip_normalize_main_header(invalid, prefix)
            == Some(Err(crate::specs::part2_jpip_cache_error(2, MalformedKind::InvalidMarkerLength))));
        assert(crate::specs::part2_jpip_normalize_main_header(invalid, prefix.push(refusal)) == None);
        let retained = soc + seq![0xffu8, 0x64u8, 0u8, 3u8, 7u8];
        let input = retained + seq![0xffu8, 0x57u8, 0u8, 3u8, 0u8];
        assert(crate::specs::part2_jpip_marker_segment(input, 2) == Ok((0xff64u16, 6usize, 7usize)));
        assert(crate::specs::part2_jpip_marker_segment(input, 7) == Ok((0xff57u16, 11usize, 12usize)));
        assert(soc + input.subrange(2, 7) =~= retained);
        assert(crate::specs::part2_jpip_main_header_scan(input, 7, 11, retained, Seq::empty())
            == Some(Ok(retained)));
        assert(crate::specs::part2_jpip_main_header_scan(input, 2, 12, soc,
            seq![(1u8, 2usize, 5usize, true)]) == Some(Ok(retained)));
        assert(crate::specs::part2_jpip_normalize_main_header(input,
            prefix.push((1u8, 2usize, 5usize, true))) == Some(Ok(retained)));
        assert(crate::specs::part2_jpip_normalize_main_header(input, prefix.push(refusal))
            == Some(Err(DecodeError::AllocationFailed)));
        assert(crate::specs::part2_jpip_normalize_main_header(input,
            prefix.push((1u8, 0usize, 5usize, true))) == None);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_jpip_main_header_result(input@, jpip_packet_bytes_outcome(result)),
))]
pub(super) fn normalize_main_header(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    if !input.starts_with(&SOC) {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_normalize_main_header);
            main_header_result_witness(input@, Seq::empty(),
                Err(crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure)));
        }
        return Err(DecodeError::malformed(
            0,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    let mut output = match crate::allocation::empty_with_capacity(SOC.len()) {
        Ok(output) => output,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_normalize_main_header);
                main_header_result_witness(input@, seq![(0u8, 0usize, 2usize, false)], Err(error));
            }
            return Err(error);
        }
    };
    match crate::allocation::extend_bytes(&mut output, &SOC) {
        Ok(()) => {}
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_normalize_main_header);
                main_header_result_witness(input@,
                    seq![(0u8, 0usize, 2usize, true), (1u8, 0usize, 2usize, false)], Err(error));
            }
            return Err(error);
        }
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost mut events = seq![(0u8, 0usize, 2usize, true), (1u8, 0usize, 2usize, true)];
    }
    let mut position = 2_usize;
    let mut remaining_markers = input.len();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_jpip_normalize_main_header);
        assert(output@ =~= seq![0xffu8, 0x4fu8]);
        assert forall|tail: Seq<crate::specs::Part2JpipStorageEvent>|
            crate::specs::part2_jpip_normalize_main_header(input@, events + tail)
                == crate::specs::part2_jpip_main_header_scan(input@,
                    position, remaining_markers, output@, tail) by {
            assert((events + tail).drop_first().drop_first() =~= tail);
        }
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= input.len(), remaining_markers <= input.len(),
                forall|tail: Seq<crate::specs::Part2JpipStorageEvent>|
                    crate::specs::part2_jpip_normalize_main_header(input@, events + tail)
                        == crate::specs::part2_jpip_main_header_scan(input@,
                            position, remaining_markers, output@, tail),
            decreases remaining_markers,
        )
    )]
    while position < input.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_main_header_scan); }
        if remaining_markers == 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(events + Seq::empty() =~= events);
                assert(crate::specs::part2_jpip_normalize_main_header(input@, events + Seq::empty())
                    == crate::specs::part2_jpip_main_header_scan(input@,
                        position, remaining_markers, output@, Seq::empty()));
                main_header_result_witness(input@, events,
                    Err(crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::InvalidMarkerLength)));
            }
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerLength,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous_remaining = remaining_markers; }
        remaining_markers -= 1;
        let (marker, _, end) = match marker_segment(input, position) {
            Ok(segment) => segment,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(events + Seq::empty() =~= events);
                    assert(crate::specs::part2_jpip_normalize_main_header(input@, events + Seq::empty())
                        == crate::specs::part2_jpip_main_header_scan(input@,
                            position, previous_remaining, output@, Seq::empty()));
                    main_header_result_witness(input@, events, Err(error));
                }
                return Err(error);
            }
        };
        if matches!(marker, 0xff90 | 0xff93 | 0xffd9) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(events + Seq::empty() =~= events);
                assert(crate::specs::part2_jpip_normalize_main_header(input@, events + Seq::empty())
                    == crate::specs::part2_jpip_main_header_scan(input@,
                        position, previous_remaining, output@, Seq::empty()));
                main_header_result_witness(input@, events,
                    Err(crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::InvalidMarkerOrder)));
            }
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        if !crate::refinement::jpip_reframed_marker_removed(marker, false) {
            let bytes = input.get(position..end).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
                ))]
                || DecodeError::malformed(position as u64, MalformedKind::Truncated),
            )?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_output = output@;
                let ghost previous_events = events;
            }
            let extension = crate::allocation::extend_bytes(&mut output, bytes);
            #[cfg(verus_keep_ghost)]
            proof! {
                events = events.push((1u8, previous_output.len() as usize, bytes.len(), extension.is_ok()));
                if extension.is_err() {
                    let suffix = seq![(1u8, previous_output.len() as usize, bytes.len(), false)];
                    assert(previous_events + suffix =~= events);
                    assert(crate::specs::part2_jpip_normalize_main_header(input@, previous_events + suffix)
                        == crate::specs::part2_jpip_main_header_scan(input@,
                            position, previous_remaining, previous_output, suffix));
                    main_header_result_witness(input@, events, Err(extension.get_Err_0()));
                } else {
                    assert forall|tail: Seq<crate::specs::Part2JpipStorageEvent>|
                        crate::specs::part2_jpip_normalize_main_header(input@, events + tail)
                            == crate::specs::part2_jpip_main_header_scan(input@,
                                end, remaining_markers, output@, tail) by {
                        let suffix = seq![(1u8, previous_output.len() as usize, bytes.len(), true)] + tail;
                        assert(events + tail =~= previous_events + suffix);
                        assert(suffix.drop_first() =~= tail);
                        assert(crate::specs::part2_jpip_normalize_main_header(input@, previous_events + suffix)
                            == crate::specs::part2_jpip_main_header_scan(input@,
                                position, previous_remaining, previous_output, suffix));
                    }
                }
            }
            extension?;
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|tail: Seq<crate::specs::Part2JpipStorageEvent>|
                    crate::specs::part2_jpip_normalize_main_header(input@, events + tail)
                        == crate::specs::part2_jpip_main_header_scan(input@,
                            end, remaining_markers, output@, tail) by {
                    assert(crate::specs::part2_jpip_normalize_main_header(input@, events + tail)
                        == crate::specs::part2_jpip_main_header_scan(input@,
                            position, previous_remaining, output@, tail));
                }
            }
        }
        position = end;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_jpip_main_header_scan);
        assert(events + Seq::empty() =~= events);
        assert(crate::specs::part2_jpip_normalize_main_header(input@, events + Seq::empty())
            == crate::specs::part2_jpip_main_header_scan(input@,
                position, remaining_markers, output@, Seq::empty()));
        main_header_result_witness(input@, events, Ok(output@));
    }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures jpip_normalized_headers_outcome(result)
        == crate::specs::part2_jpip_normalize_automatic_tile_headers(input@, tile),
))]
pub(super) fn normalize_automatic_tile_headers(
    input: &[u8],
    tile: u16,
) -> Result<Vec<Vec<u8>>, DecodeError> {
    let transitions = parse_tile_part_transitions(input, tile)?;
    #[cfg(verus_keep_ghost)]
    proof! { jpip_transition_sequence_shapes(); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost entries = jpip_transitions_view(&transitions);
        let ghost expected = crate::specs::part2_jpip_normalized_header_entries(entries, tile, 0, Seq::empty());
    }
    let count = u8::try_from(transitions.len()).map_err(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_range_overflow(0),
            ))]
        |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?;
    let mut output = Vec::with_capacity(transitions.len());
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@.map_values(|header: Vec<u8>| header@) =~= Seq::<Seq<u8>>::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= transitions.len(), transitions.len() <= u8::MAX,
                entries == jpip_transitions_view(&transitions), entries.len() == transitions.len(),
                count as nat == entries.len(),
                forall|position: int| 0 <= position < transitions.len() ==>
                    #[trigger] entries[position] == jpip_transition_view(&transitions@[position]),
                expected == crate::specs::part2_jpip_normalize_automatic_tile_headers(input@, tile),
                expected == crate::specs::part2_jpip_normalized_header_entries(entries, tile,
                    index as nat, output@.map_values(|header: Vec<u8>| header@)),
            decreases transitions.len() - index,
        )
    )]
    while index < transitions.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_normalized_header_entries); }
        let transition = transitions
            .get(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidTilePart),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidTilePart),
            )?;
        let header = normalize_tile_header(transition.header_bytes(), tile, index, count)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous = output@.map_values(|header: Vec<u8>| header@);
            let ghost bytes = header@;
        }
        output.push(header);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(output@.map_values(|header: Vec<u8>| header@) =~= previous.push(bytes));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_jpip_normalized_header_entries); }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures jpip_packet_bytes_outcome(result)
        == crate::specs::part2_jpip_normalize_tile_header(source@, tile, index, count),
))]
pub(super) fn normalize_tile_header(
    source: &[u8],
    tile: u16,
    index: usize,
    count: u8,
) -> Result<Vec<u8>, DecodeError> {
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
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(((tile >> 8) & 0xff) <= 255) by (bit_vector);
        assert((tile & 0xff) <= 255) by (bit_vector);
    }
    header.push(((tile >> 8) & 0xff) as u8);
    header.push((tile & 0xff) as u8);
    header.extend_from_slice(&[0, 0, 0, 0]);
    header.push(u8::try_from(index).map_err(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_range_overflow(0),
            ))]
        |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?);
    header.push(count);
    let mut position = marker_start;
    let mut remaining_markers = source.len();
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost expected = crate::specs::part2_jpip_normalized_header_scan(
            source@, marker_start, source.len(), header@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(header@ =~= seq![0xffu8, 0x90u8, 0u8, 10u8, ((tile >> 8) & 0xff) as u8,
            (tile & 0xff) as u8, 0u8, 0u8, 0u8, 0u8, index as u8, count]);
        reveal(crate::specs::part2_jpip_normalized_header_scan);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= source.len(), remaining_markers <= source.len(),
                expected == crate::specs::part2_jpip_normalize_tile_header(source@, tile, index, count),
                position == source.len() ==> expected == Ok(header@ + seq![0xffu8, 0x93u8]),
            invariant_except_break expected == crate::specs::part2_jpip_normalized_header_scan(
                source@, position, remaining_markers, header@),
            ensures expected == if position != source.len() {
                Err(crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::MissingRequiredStructure))
            } else { Ok(header@ + seq![0xffu8, 0x93u8]) },
            decreases remaining_markers,
        )
    )]
    while position < source.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_normalized_header_scan); }
        if remaining_markers == 0 {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerLength,
            ));
        }
        remaining_markers -= 1;
        if source.get(position..position.saturating_add(2)) == Some(&[0xff, 0x93]) {
            position = position.checked_add(2).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(position as u64),
                ))]
                || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
            )?;
            break;
        }
        let (marker, _, end) = marker_segment(source, position)?;
        if !crate::refinement::jpip_reframed_marker_removed(marker, true) {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous = header@; }
            header.extend_from_slice(source.get(position..end).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
                ))]
                || DecodeError::malformed(position as u64, MalformedKind::Truncated),
            )?);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(header@ =~= previous + source@.subrange(position as int, end as int));
            }
        }
        position = end;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_normalized_header_scan); }
    }
    if position != source.len() {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost previous = header@; }
    header.extend_from_slice(&[0xff, 0x93]);
    #[cfg(verus_keep_ghost)]
    proof! { assert(header@ =~= previous + seq![0xffu8, 0x93u8]); }
    Ok(header)
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
