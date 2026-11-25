//! Stable positions and actual allocation prefixes for decode-local copy collection.
use super::*;
verus! {

#[verifier::opaque]
pub(crate) open spec fn part2_index_next(
    parts: Seq<Part2OwnedTilePart>, tile: u16, start: nat,
) -> nat
    decreases if start < parts.len() { parts.len() - start } else { 0int },
{
    if start >= parts.len() { parts.len() }
    else if parts[start as int].tile_index == tile { start }
    else { part2_index_next(parts, tile, start + 1) }
}

pub(crate) proof fn part2_index_next_bounds(
    parts: Seq<Part2OwnedTilePart>, tile: u16, start: nat,
)
    requires start <= parts.len(),
    ensures start <= part2_index_next(parts, tile, start) <= parts.len(),
        part2_collected_part_count(parts, tile, start) <= parts.len() - start,
        part2_index_next(parts, tile, start) < parts.len() ==>
            parts[part2_index_next(parts, tile, start) as int].tile_index == tile,
    decreases parts.len() - start,
{
    reveal_with_fuel(part2_index_next, 1);
    reveal_with_fuel(part2_collected_part_count, 1);
    if start < parts.len() {
        part2_index_next_bounds(parts, tile, start + 1);
    }
}

pub(crate) open spec fn part2_index_matches(
    parts: Seq<Part2OwnedTilePart>, entries: Seq<(usize, usize)>, next: Seq<usize>,
) -> bool {
    entries.len() <= u16::MAX as nat + 1 && next.len() == parts.len()
        && (forall|tile: int| 0 <= tile < entries.len() ==>
            #[trigger] entries[tile] == (
                part2_index_next(parts, tile as u16, 0) as usize,
                part2_collected_part_count(parts, tile as u16, 0) as usize))
        && (forall|position: int| 0 <= position < parts.len() ==>
            #[trigger] next[position] == if (parts[position].tile_index as nat) < entries.len() {
                part2_index_next(parts, parts[position].tile_index, (position + 1) as nat) as usize
            } else { parts.len() as usize })
}

pub(crate) proof fn part2_index_skip(
    parts: Seq<Part2OwnedTilePart>, tile: u16, start: nat,
    before: Seq<Part2OwnedTilePart>, events: Seq<Part2JpipSnapshotEvent>,
)
    requires start <= parts.len(),
    ensures part2_collected_loop_run(parts, tile, start, before, events)
            == part2_collected_loop_run(parts, tile, part2_index_next(parts, tile, start), before, events),
        part2_collect_tile_parts_run(parts, tile, start, before)
            == part2_collect_tile_parts_run(parts, tile, part2_index_next(parts, tile, start), before),
        part2_collected_part_count(parts, tile, start)
            == part2_collected_part_count(parts, tile, part2_index_next(parts, tile, start)),
    decreases parts.len() - start,
{
    reveal_with_fuel(part2_index_next, 1);
    if start < parts.len() && parts[start as int].tile_index != tile {
        reveal_with_fuel(part2_collected_loop_run, 1);
        reveal_with_fuel(part2_collect_tile_parts_run, 1);
        reveal_with_fuel(part2_collected_part_count, 1);
        part2_index_skip(parts, tile, start + 1, before, events);
    }
}

pub(crate) open spec fn part2_index_capacity_run(
    parts: Seq<Part2OwnedTilePart>, slots: nat, links: bool,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<()> {
    let elements = if links { parts.len() } else { slots };
    if elements == 0 { Some((Ok(()), events)) }
    else if events.len() == 0 { None }
    else {
        match events[0] {
            Part2JpipSnapshotEvent::TilePartIndexCapacity {
                source, tile_slots, next_positions, elements: actual, succeeded,
            } => if source != parts || tile_slots != slots || next_positions != links || actual != elements {
                None
            } else {
                Some((if succeeded { Ok(()) } else { Err(crate::DecodeError::AllocationFailed) },
                    events.drop_first()))
            },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_index_capacity_result(
    parts: Seq<Part2OwnedTilePart>, slots: nat, links: bool,
    result: Result<(), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_index_capacity_run(parts, slots, links, events), result)
}

pub(crate) proof fn part2_index_capacity_observed(
    parts: Seq<Part2OwnedTilePart>, slots: nat, links: bool,
    result: Result<(), crate::DecodeError>,
)
    requires result == Ok(()) || (
        (if links { parts.len() } else { slots }) > 0
            && result == Err(crate::DecodeError::AllocationFailed)),
    ensures part2_index_capacity_result(parts, slots, links, result),
{
    let elements = if links { parts.len() } else { slots };
    if elements == 0 {
        part2_cold_pure::<()>(result);
    } else {
        let prefix = seq![Part2JpipSnapshotEvent::TilePartIndexCapacity {
            source: parts, tile_slots: slots, next_positions: links, elements,
            succeeded: result.is_ok(),
        }];
        assert forall|tail: Seq<Part2JpipSnapshotEvent>|
            part2_index_capacity_run(parts, slots, links, prefix + tail) == Some((result, tail)) by {
            assert((prefix + tail).drop_first() =~= tail);
        }
        assert(part2_cold_prefix(|events| part2_index_capacity_run(parts, slots, links, events), prefix, result));
    }
}

pub(crate) proof fn part2_index_capacity_normal(
    parts: Seq<Part2OwnedTilePart>, slots: nat, links: bool,
)
    ensures part2_index_capacity_result(parts, slots, links, Ok(())),
{
    part2_index_capacity_observed(parts, slots, links, Ok(()));
}

pub(crate) open spec fn part2_prepare_tile_index_run(
    parts: Seq<Part2OwnedTilePart>, slots: nat, selected_count: nat,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<()> {
    if selected_count <= 1 { Some((Ok(()), events)) }
    else {
        part2_jpip_snapshot_bind(part2_index_capacity_run(parts, slots, false, events),
            |_: (), rest| part2_index_capacity_run(parts, slots, true, rest))
    }
}

pub(crate) open spec fn part2_prepare_tile_index_result(
    parts: Seq<Part2OwnedTilePart>, slots: nat, selected_count: nat,
    result: Result<(), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_prepare_tile_index_run(parts, slots, selected_count, events), result)
}

pub(crate) proof fn part2_prepare_tile_index_normal(
    parts: Seq<Part2OwnedTilePart>, slots: nat, selected_count: nat,
)
    ensures part2_prepare_tile_index_result(parts, slots, selected_count, Ok(())),
{
    if selected_count <= 1 {
        part2_cold_pure::<()>(Ok(()));
    } else {
        part2_index_capacity_observed(parts, slots, false, Ok(()));
        part2_index_capacity_observed(parts, slots, true, Ok(()));
        let child = |events| part2_index_capacity_run(parts, slots, false, events);
        let next = |_: (), events| part2_index_capacity_run(parts, slots, true, events);
        part2_cold_bind(child, next, Ok(()), Ok(()));
        part2_decode_eta(|events| part2_jpip_snapshot_bind(child(events), next), Ok(()));
    }
}

pub(crate) proof fn part2_index_prefix_normal<T>(
    parts: Seq<Part2OwnedTilePart>, slots: nat, selected_count: nat,
    next: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    result: Result<T, crate::DecodeError>,
)
    requires part2_cold_framed(next, result),
    ensures part2_cold_framed(|events| part2_jpip_snapshot_bind(
        part2_prepare_tile_index_run(parts, slots, selected_count, events),
        |_: (), rest| next(rest)), result),
{
    part2_prepare_tile_index_normal(parts, slots, selected_count);
    let child = |events| part2_prepare_tile_index_run(parts, slots, selected_count, events);
    let finish = |_: (), rest| next(rest);
    part2_cold_bind(child, finish, Ok(()), result);
}

pub(crate) open spec fn part2_index_tile_slots(size: &crate::codestream::ImageSize) -> nat {
    size.tiles_across as nat * size.tiles_down as nat
}

pub(crate) proof fn part2_index_selection_slots(
    size: Part2SelectionGeometry, requested: Part2DecodeSelection,
)
    requires part2_validate_selection(size, requested).is_ok(),
    ensures size.8 as nat * size.9 as nat <= u16::MAX as nat + 1,
{}

}
