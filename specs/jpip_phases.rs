//! Complete Results and scratch-state frames for non-owning automatic phases.

use super::*;

verus! {

pub type Part2JpipOrdinalMatrix = Seq<Seq<Option<u16>>>;
pub type Part2JpipPacketOrder = Seq<(crate::packet::PacketCoordinate, usize)>;
pub type Part2JpipOrderPhase = (
    Result<(), crate::DecodeError>, Part1ProgressionPacketIterator,
    Part2JpipOrdinalMatrix, Part2JpipPacketOrder,
);

pub open spec fn part2_jpip_ordinal_cell_phase(
    before: Option<u16>, sequence: u16,
) -> (Result<(), crate::DecodeError>, Option<u16>) {
    if before.is_some() {
        (Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidProgressionOrderChange)), before)
    } else { (Ok(()), Some(sequence)) }
}

pub open spec fn part2_jpip_precinct_phase(
    plan: Part2ProgressionTilePlan, execution: usize, template: &crate::codestream::TilePartPayload<'_>,
    prefix: Seq<u8>, start: usize, sequence: u16, layer: u16, limits: &crate::ResourceLimits,
) -> (Result<usize, crate::DecodeError>, Part2ProgressionTilePlan) {
    if execution as nat >= plan.precincts.len() {
        (Err(part2_jpip_range_overflow(0)), plan)
    } else {
        let step = part1_jpip_precinct_packet(plan.precincts[execution as int], template,
            prefix.subrange(start as int, prefix.len() as int), sequence, layer, limits);
        (step.0, Part2ProgressionTilePlan {
            precincts: plan.precincts.update(execution as int, step.1), ..plan })
    }
}

pub open spec fn part2_jpip_emit_packet_phase(
    before: Seq<u8>, packet: Part2JpipAutomaticPacket, available: u16, sop: bool, eph: bool,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    if packet.3 && packet.5 < available {
        match packet.1 {
            None => (Err(part2_jpip_cache_error(packet.2, crate::MalformedKind::MissingRequiredStructure)), before),
            Some(bytes) => (Ok(()), before + bytes),
        }
    } else { (Ok(()), before + part2_jpip_empty_packet_bytes(sop, eph, packet.4)) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_emit_packets_phase(
    part: Part2JpipAutomaticTilePart, available: u16, packet: nat, before: Seq<u8>,
) -> (Result<(), crate::DecodeError>, Seq<u8>)
    decreases if packet < part.1.len() { part.1.len() - packet } else { 0 },
{
    if packet >= part.1.len() { (Ok(()), before) }
    else {
        let step = part2_jpip_emit_packet_phase(before, part.1[packet as int], available, part.2, part.3);
        match step.0 {
            Err(error) => (Err(error), step.1),
            Ok(()) => part2_jpip_emit_packets_phase(part, available, packet + 1, step.1),
        }
    }
}

pub open spec fn part2_jpip_emit_part_patch(
    before: Seq<u8>, start: usize,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    if before.len() < start as nat || before.len() - start as nat > u32::MAX as nat
        || start as nat + 6 > usize::MAX as nat {
        (Err(part2_jpip_range_overflow(0)), before)
    } else {
        part2_jpip_write_u32(before, (start as nat + 6) as usize, (before.len() - start as nat) as u32)
    }
}

pub open spec fn part2_jpip_emit_part_phase(
    before: Seq<u8>, part: Part2JpipAutomaticTilePart, available: u16,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    let packets = part2_jpip_emit_packets_phase(part, available, 0, before + part.0);
    match packets.0 {
        Err(error) => (Err(error), packets.1),
        Ok(()) => part2_jpip_emit_part_patch(packets.1, before.len() as usize),
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_order_phase(
    grid: Part1PacketGrid, iterator: Part1ProgressionPacketIterator,
    ordinals: Part2JpipOrdinalMatrix, order: Part2JpipPacketOrder, ordinal: u64, remaining: u64,
) -> Part2JpipOrderPhase
    decreases remaining,
{
    let step = part1_progression_iterator_next(iterator);
    match step.0 {
        Err(error) => (Err(error), step.1, ordinals, order),
        Ok(None) => (Ok(()), step.1, ordinals, order),
        Ok(Some(coordinate)) => if remaining == 0 {
            (Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidProgressionOrderChange)),
                step.1, ordinals, order)
        } else {
            match part1_packet_grid_precinct_index(grid,
                coordinate.component, coordinate.resolution, coordinate.precinct) {
                Err(error) => (Err(error), step.1, ordinals, order),
                Ok(execution) => if execution as nat >= ordinals.len()
                    || coordinate.layer as nat >= ordinals[execution as int].len()
                    || ordinals[execution as int][coordinate.layer as int].is_some() {
                    (Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidProgressionOrderChange)),
                        step.1, ordinals, order)
                } else {
                    let ordinals = ordinals.update(execution as int, ordinals[execution as int].update(
                        coordinate.layer as int, Some((ordinal & 65535) as u16)));
                    let order = order.push((coordinate, execution));
                    if ordinal == u64::MAX {
                        (Err(part2_jpip_range_overflow(0)), step.1, ordinals, order)
                    } else {
                        part2_jpip_order_phase(grid, step.1, ordinals, order,
                            (ordinal + 1) as u64, (remaining - 1) as u64)
                    }
                },
            }
        },
    }
}

pub proof fn part2_jpip_order_phase_prefix_bounds(
    grid: Part1PacketGrid, iterator: Part1ProgressionPacketIterator,
    ordinals: Part2JpipOrdinalMatrix, order: Part2JpipPacketOrder, ordinal: u64, remaining: u64,
)
    ensures
        order.is_prefix_of(part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3),
        forall|index: int| order.len() <= index
            < part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3.len()
            ==> (#[trigger] part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3[index].1 as nat)
                < ordinals.len(),
        part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).2.len() == ordinals.len(),
        forall|row: int| 0 <= row < ordinals.len() ==>
            #[trigger] part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).2[row].len()
                == ordinals[row].len(),
        forall|index: int| order.len() <= index
            < part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3.len() ==>
                (part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3[index].1 as nat)
                    < ordinals.len()
                && (#[trigger] part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3[index].0.layer as nat)
                    < ordinals[part2_jpip_order_phase(grid, iterator, ordinals, order, ordinal, remaining).3[index].1 as int].len(),
    decreases remaining,
{
    reveal(part2_jpip_order_phase);
    let step = part1_progression_iterator_next(iterator);
    if let Ok(Some(coordinate)) = step.0 {
        if remaining != 0 {
            if let Ok(execution) = part1_packet_grid_precinct_index(grid,
                coordinate.component, coordinate.resolution, coordinate.precinct) {
                if (execution as nat) < ordinals.len()
                    && (coordinate.layer as nat) < ordinals[execution as int].len()
                    && ordinals[execution as int][coordinate.layer as int].is_none() {
                    let next_ordinals = ordinals.update(execution as int, ordinals[execution as int].update(
                        coordinate.layer as int, Some((ordinal & 65535) as u16)));
                    let next_order = order.push((coordinate, execution));
                    assert forall|row: int| 0 <= row < ordinals.len() implies
                        #[trigger] next_ordinals[row].len() == ordinals[row].len() by {
                    }
                    if ordinal != u64::MAX {
                        part2_jpip_order_phase_prefix_bounds(grid, step.1, next_ordinals, next_order,
                            (ordinal + 1) as u64, (remaining - 1) as u64);
                        let output = part2_jpip_order_phase(grid, step.1, next_ordinals, next_order,
                            (ordinal + 1) as u64, (remaining - 1) as u64).3;
                        assert(order.is_prefix_of(output));
                        assert forall|index: int| order.len() <= index < output.len()
                            implies (#[trigger] output[index].1 as nat) < ordinals.len() by {
                            if index == order.len() {
                                assert(output[index] == next_order[index]);
                            }
                        }
                        assert forall|index: int| order.len() <= index < output.len()
                            implies (#[trigger] output[index].0.layer as nat)
                                < ordinals[output[index].1 as int].len() by {
                            if index == order.len() {
                                assert(output[index] == next_order[index]);
                            }
                        }
                    }
                }
            }
        }
    }
}

}
