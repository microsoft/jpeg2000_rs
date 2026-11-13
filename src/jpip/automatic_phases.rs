//! Non-owning automatic snapshot phases with complete error-state contracts.

use super::{DecodeError, MalformedKind, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(slot)) == crate::specs::part2_jpip_ordinal_cell_phase(*old(slot), sequence),
))]
fn write_automatic_ordinal(slot: &mut Option<u16>, sequence: u16) -> Result<(), DecodeError> {
    if slot.is_some() {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::InvalidProgressionOrderChange,
        ));
    }
    *slot = Some(sequence);
    Ok(())
}

// Keep Vec dereference and suffix slicing after the decoder lookup.
#[allow(clippy::ptr_arg, clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires start <= prefix.len(),
    ensures (result, crate::decode::progression_plan_view(final(plan)))
        == crate::specs::part2_jpip_precinct_phase(crate::decode::progression_plan_view(old(plan)),
            execution, template, prefix@, start, sequence, layer, limits),
))]
pub(super) fn decode_automatic_precinct(
    plan: &mut crate::decode::ProgressionTilePlan,
    execution: usize,
    template: &crate::codestream::TilePartPayload<'_>,
    prefix: &Vec<u8>,
    start: usize,
    sequence: u16,
    layer: u16,
    limits: &ResourceLimits,
) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before_plan = crate::decode::progression_plan_view(plan); }
    let precincts = plan.precincts_mut();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before_precincts = precincts@; }
    let precinct_decoder = precincts.get_mut(execution).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_range_overflow(0),
        ))]
        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((execution as nat) < before_plan.precincts.len());
        assert(crate::packet::packet_precinct_view(precinct_decoder) == before_plan.precincts[execution as int]);
        assert(precincts@ =~= before_precincts.update(execution as int, *final(precinct_decoder)));
        assert(crate::decode::planning_precincts_view(precincts@)
            =~= before_plan.precincts.update(execution as int,
                crate::packet::packet_precinct_view(final(precinct_decoder))));
    }
    crate::packet::decode_jpip_precinct_packet(
        template,
        &prefix[start..],
        sequence,
        layer,
        precinct_decoder,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(bytes)@) == crate::specs::part2_jpip_emit_part_phase(
        old(bytes)@, super::jpip_automatic_tile_part_view(part), available_layers),
))]
pub(super) fn emit_automatic_tile_part(
    bytes: &mut Vec<u8>,
    part: &super::AutomaticTilePart,
    available_layers: u16,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = bytes@;
        let ghost value = super::jpip_automatic_tile_part_view(part);
        let ghost packets = crate::specs::part2_jpip_emit_packets_phase(value,
            available_layers, 0, before + value.0);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::jpip_automatic_tile_part_view);
        reveal(super::jpip_automatic_packet_view);
    }
    let tile_start = bytes.len();
    bytes.extend_from_slice(&part.header);
    #[cfg(verus_keep_ghost)]
    proof! { assert(bytes@ =~= before + value.0); }
    let mut packet_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant packet_index <= part.packets.len(), before == old(bytes)@,
            tile_start as nat == before.len(),
            value == super::jpip_automatic_tile_part_view(part),
            value.1 == part.packets@.map_values(
                |packet: super::AutomaticPacket| super::jpip_automatic_packet_view(&packet)),
            packets == crate::specs::part2_jpip_emit_packets_phase(value,
                available_layers, 0, before + value.0),
            packets == crate::specs::part2_jpip_emit_packets_phase(value,
                available_layers, packet_index as nat, bytes@),
        decreases part.packets.len() - packet_index,
    ))]
    while packet_index < part.packets.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_emit_packets_phase); }
        let packet = &part.packets[packet_index];
        let layer = packet.layer;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before_packet = bytes@; }
        if packet.required && layer < available_layers {
            let packet_bytes = packet.bytes.as_ref().ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(
                        packet.next_offset, MalformedKind::MissingRequiredStructure),
                ))]
                || {
                    DecodeError::malformed(
                        packet.next_offset,
                        MalformedKind::MissingRequiredStructure,
                    )
                },
            )?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(super::jpip_parsed_packet_value(packet.bytes) == Some(packet_bytes@)); }
            bytes.extend_from_slice(packet_bytes);
            #[cfg(verus_keep_ghost)]
            proof! { assert(bytes@ =~= before_packet + packet_bytes@); }
        } else {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before_empty = bytes@; }
            super::append_empty_packet(bytes, part.sop, part.eph, packet.ordinal)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((Ok(()), bytes@) == crate::specs::part2_jpip_append_empty_packet(
                    before_empty, part.sop, part.eph, packet.ordinal));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_jpip_emit_packet_phase(before_packet,
                super::jpip_automatic_packet_view(packet), available_layers, part.sop, part.eph)
                == (Ok(()), bytes@));
        }
        packet_index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_jpip_emit_packets_phase);
        assert(packets == (Ok(()), bytes@));
    }
    let tile_length = bytes.len().checked_sub(tile_start).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_range_overflow(0),
        ))]
        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?;
    let tile_length = u32::try_from(tile_length).map_err(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_range_overflow(0),
        ))]
        |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?;
    let length_position = tile_start.checked_add(6).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_range_overflow(0),
        ))]
        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before_psot = bytes@; }
    super::write_u32_be(bytes, length_position, tile_length)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((Ok(()), bytes@) == crate::specs::part2_jpip_write_u32(
            before_psot, length_position, tile_length));
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, crate::packet::progression_packet_iterator_view(final(iterator)),
        final(ordinals)@.map_values(|row: Vec<Option<u16>>| row@), final(order)@)
        == crate::specs::part2_jpip_order_phase(crate::decode::progression_plan_view(plan).grid,
            crate::packet::progression_packet_iterator_view(old(iterator)),
            old(ordinals)@.map_values(|row: Vec<Option<u16>>| row@), old(order)@,
            0, crate::limits::resource_work_limit(limits)),
))]
// Keep Vec dereferences at their original per-coordinate lookups.
#[allow(clippy::ptr_arg)]
pub(super) fn build_automatic_order(
    plan: &crate::decode::ProgressionTilePlan,
    iterator: &mut crate::packet::ProgressionPacketIterator<'_>,
    ordinals: &mut Vec<Vec<Option<u16>>>,
    order: &mut Vec<(crate::packet::PacketCoordinate, usize)>,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let mut ordinal = 0_u64;
    let mut remaining_packets = limits.maximum_work_units();
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_iterator = crate::packet::progression_packet_iterator_view(iterator);
        let ghost initial_ordinals = ordinals@.map_values(|row: Vec<Option<u16>>| row@);
        let ghost initial_order = order@;
        let ghost after_ordinals = final(ordinals)@.map_values(|row: Vec<Option<u16>>| row@);
        let ghost grid = crate::decode::progression_plan_view(plan).grid;
        let ghost goal = crate::specs::part2_jpip_order_phase(grid, initial_iterator,
            initial_ordinals, initial_order, 0, crate::limits::resource_work_limit(limits));
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant initial_iterator == crate::packet::progression_packet_iterator_view(old(iterator)),
            initial_ordinals == old(ordinals)@.map_values(|row: Vec<Option<u16>>| row@),
            initial_order == old(order)@,
            after_ordinals == final(ordinals)@.map_values(|row: Vec<Option<u16>>| row@),
            grid == crate::decode::progression_plan_view(plan).grid,
            goal == crate::specs::part2_jpip_order_phase(grid, initial_iterator,
                initial_ordinals, initial_order, 0, crate::limits::resource_work_limit(limits)),
            goal == crate::specs::part2_jpip_order_phase(grid,
                crate::packet::progression_packet_iterator_view(iterator),
                ordinals@.map_values(|row: Vec<Option<u16>>| row@), order@, ordinal, remaining_packets),
        decreases remaining_packets,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_order_phase); }
        let coordinate = match iterator.next_packet()? {
            Some(coordinate) => coordinate,
            None => return Ok(()),
        };
        if remaining_packets == 0 {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::InvalidProgressionOrderChange,
            ));
        }
        remaining_packets -= 1;
        let execution = plan.grid().precinct_index(
            coordinate.component,
            coordinate.resolution,
            coordinate.precinct,
        )?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((ordinal & 65535u64) <= u16::MAX as u64) by(bit_vector);
        }
        let sequence = u16::try_from(ordinal & u64::from(u16::MAX))
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before_native = ordinals@;
            let ghost before_ordinals = ordinals@.map_values(|row: Vec<Option<u16>>| row@);
        }
        let layer_slot = match ordinals.get_mut(execution) {
            Some(layers) => layers.get_mut(usize::from(coordinate.layer)),
            None => None,
        }
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(
                    0, MalformedKind::InvalidProgressionOrderChange),
            ))]
            || DecodeError::malformed(0, MalformedKind::InvalidProgressionOrderChange),
        )?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((execution as nat) < before_ordinals.len());
            assert((coordinate.layer as nat) < before_ordinals[execution as int].len());
            assert(*layer_slot == before_ordinals[execution as int][coordinate.layer as int]);
            assert(ordinals@ =~= before_native.update(execution as int, ordinals@[execution as int]));
            assert(ordinals@[execution as int]@ =~= before_native[execution as int]@.update(
                coordinate.layer as int, *final(layer_slot)));
            assert(ordinals@.map_values(|row: Vec<Option<u16>>| row@)
                =~= before_ordinals.update(execution as int, before_ordinals[execution as int].update(
                    coordinate.layer as int, *final(layer_slot))));
        }
        match write_automatic_ordinal(layer_slot, sequence) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(before_ordinals[execution as int].update(coordinate.layer as int,
                        before_ordinals[execution as int][coordinate.layer as int])
                        =~= before_ordinals[execution as int]);
                    assert(before_ordinals.update(execution as int, before_ordinals[execution as int].update(
                        coordinate.layer as int, before_ordinals[execution as int][coordinate.layer as int]))
                        =~= before_ordinals);
                    assert(ordinals@.map_values(|row: Vec<Option<u16>>| row@) == before_ordinals);
                }
                return Err(error);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(before_ordinals[execution as int][coordinate.layer as int].is_none()); }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ordinals@.map_values(|row: Vec<Option<u16>>| row@)
                == before_ordinals.update(execution as int,
                    before_ordinals[execution as int].update(coordinate.layer as int, Some(sequence))));
            assert(crate::specs::part2_jpip_ordinal_matrix_write(before_ordinals,
                ordinals@.map_values(|row: Vec<Option<u16>>| row@),
                execution, coordinate.layer, sequence));
        }
        order.push((coordinate, execution));
        ordinal = ordinal.checked_add(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_range_overflow(0),
            ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
    }
}
