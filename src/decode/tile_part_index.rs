use super::{DecodeError, ImageSize, TilePartPayload};
#[cfg(verus_keep_ghost)]
use super::{codestream, collected_tile_parts_outcome};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
struct TilePartIndexEntry {
    head: usize,
    count: usize,
}

pub(super) struct TilePartIndex {
    entries: Vec<TilePartIndexEntry>,
    next: Vec<usize>,
}

#[cfg(verus_keep_ghost)]
verus! {
    open spec fn entries_view(entries: Seq<TilePartIndexEntry>) -> Seq<(usize, usize)> {
        entries.map_values(|entry: TilePartIndexEntry| (entry.head, entry.count))
    }

    pub(super) open spec fn optional_index_matches(
        parts: Seq<crate::specs::Part2OwnedTilePart>, index: &Option<TilePartIndex>,
    ) -> bool {
        match index {
            None => true,
            Some(value) => crate::specs::part2_index_matches(parts, entries_view(value.entries@), value.next@),
        }
    }

    pub(super) open spec fn index_preparation_outcome(
        result: Result<Option<TilePartIndex>, DecodeError>,
    ) -> Result<(), DecodeError> {
        match result { Ok(_) => Ok(()), Err(error) => Err(error) }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::part2_index_tile_slots(size) <= u16::MAX as nat + 1,
    ensures result == crate::specs::part2_index_tile_slots(size),
))]
pub(super) fn tile_index_slots(size: &ImageSize) -> usize {
    (u64::from(size.tiles_across) * u64::from(size.tiles_down)) as usize
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires elements == if _links { _parts.len() } else { _slots },
    ensures crate::specs::part2_index_capacity_result(
        codestream::tile_parts_owned_view(_parts@), _slots as nat, _links,
        crate::allocation::inspection_capacity_outcome(result)),
        match result { Ok(values) => values@.len() == 0,
            Err(error) => error == DecodeError::AllocationFailed },
))]
fn reserve_index_values<T>(
    _parts: &[TilePartPayload<'_>],
    _slots: usize,
    _links: bool,
    elements: usize,
) -> Result<Vec<T>, DecodeError> {
    let result = if elements == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(elements)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_index_capacity_observed(
            codestream::tile_parts_owned_view(_parts@), _slots as nat, _links,
            crate::allocation::inspection_capacity_outcome(result));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires slots <= u16::MAX as usize + 1,
    ensures crate::specs::part2_prepare_tile_index_result(
        codestream::tile_parts_owned_view(parts@), slots as nat, selected_count as nat,
        index_preparation_outcome(result)),
        match result {
            Ok(index) => optional_index_matches(codestream::tile_parts_owned_view(parts@), &index)
                && (index.is_some() == (selected_count > 1)),
            Err(error) => error == DecodeError::AllocationFailed,
        },
))]
pub(super) fn prepare_tile_part_index(
    parts: &[TilePartPayload<'_>],
    slots: usize,
    selected_count: usize,
) -> Result<Option<TilePartIndex>, DecodeError> {
    if selected_count <= 1 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_prepare_tile_index_normal(
                codestream::tile_parts_owned_view(parts@), slots as nat, selected_count as nat);
        }
        return Ok(None);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source = codestream::tile_parts_owned_view(parts@);
        let ghost mut prefix = Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    let reserved = reserve_index_values::<TilePartIndexEntry>(parts, slots, false, slots);
    #[cfg(verus_keep_ghost)]
    proof! {
        let root = |events| crate::specs::part2_prepare_tile_index_run(source, slots as nat, selected_count as nat, events);
        let child = |events| crate::specs::part2_index_capacity_run(source, slots as nat, false, events);
        let next = |_: (), rest| crate::specs::part2_index_capacity_run(source, slots as nat, true, rest);
        match reserved {
            Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
            Ok(_) => { prefix = crate::specs::part2_decode_prefix_advance(root, child, next, prefix, ()); },
        }
    }
    let mut entries = reserved?;
    let reserved = reserve_index_values::<usize>(parts, slots, true, parts.len());
    #[cfg(verus_keep_ghost)]
    proof! {
        let root = |events| crate::specs::part2_prepare_tile_index_run(source, slots as nat, selected_count as nat, events);
        let child = |events| crate::specs::part2_index_capacity_run(source, slots as nat, true, events);
        crate::specs::part2_cold_prefix_result(
            root, child, prefix, crate::allocation::inspection_capacity_outcome(reserved));
    }
    let mut next = reserved?;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant entries.len() <= slots, slots <= u16::MAX as usize + 1,
            source == codestream::tile_parts_owned_view(parts@),
            next.len() == 0,
            crate::specs::part2_prepare_tile_index_result(source, slots as nat, selected_count as nat, Ok(())),
            forall|tile: int| 0 <= tile < entries.len() ==>
                #[trigger] entries@[tile].head == parts.len() && entries@[tile].count == 0,
        decreases slots - entries.len(),
    ))]
    while entries.len() < slots {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(entries.len())?;
        entries.push(TilePartIndexEntry {
            head: parts.len(),
            count: 0,
        });
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant entries.len() == slots, slots <= u16::MAX as usize + 1,
            source == codestream::tile_parts_owned_view(parts@),
            next.len() <= parts.len(),
            crate::specs::part2_prepare_tile_index_result(source, slots as nat, selected_count as nat, Ok(())),
            forall|tile: int| 0 <= tile < entries.len() ==>
                #[trigger] entries@[tile].head == parts.len() && entries@[tile].count == 0,
            forall|position: int| 0 <= position < next.len() ==> #[trigger] next@[position] == parts.len(),
        decreases parts.len() - next.len(),
    ))]
    while next.len() < parts.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(next.len())?;
        next.push(parts.len());
    }
    let mut position = parts.len();
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|tile: int| 0 <= tile < slots implies
            #[trigger] entries_view(entries@)[tile] == (
                crate::specs::part2_index_next(source, tile as u16, position as nat) as usize,
                crate::specs::part2_collected_part_count(source, tile as u16, position as nat) as usize) by {
            reveal_with_fuel(crate::specs::part2_index_next, 1);
            reveal_with_fuel(crate::specs::part2_collected_part_count, 1);
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= parts.len(), entries.len() == slots,
            slots <= u16::MAX as usize + 1, next.len() == parts.len(),
            source == codestream::tile_parts_owned_view(parts@),
            crate::specs::part2_prepare_tile_index_result(source, slots as nat, selected_count as nat, Ok(())),
            forall|tile: int| 0 <= tile < slots ==>
                #[trigger] entries_view(entries@)[tile] == (
                    crate::specs::part2_index_next(source, tile as u16, position as nat) as usize,
                    crate::specs::part2_collected_part_count(source, tile as u16, position as nat) as usize),
            forall|i: int| position <= i < parts.len() ==> #[trigger] next@[i] ==
                if (source[i].tile_index as nat) < slots {
                    crate::specs::part2_index_next(source, source[i].tile_index, (i + 1) as nat) as usize
                } else { parts.len() },
            forall|i: int| 0 <= i < position ==> #[trigger] next@[i] == parts.len(),
        decreases position,
    ))]
    while position > 0 {
        position -= 1;
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(position)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before_entries = entries@;
            let ghost before_next = next@;
        }
        #[cfg(verus_keep_ghost)]
        proof! { codestream::tile_part_owned_tile_known(&parts[position as int]); }
        let tile = usize::from(parts[position].tile_index);
        if tile < entries.len() {
            let entry = entries[tile];
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_index_next_bounds(source, parts[position as int].tile_index, (position + 1) as nat);
                assert(entry.count < usize::MAX);
            }
            next[position] = entry.head;
            entries[tile] = TilePartIndexEntry {
                head: position,
                count: entry.count + 1,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|selected: int| 0 <= selected < slots implies
                #[trigger] entries_view(entries@)[selected] == (
                    crate::specs::part2_index_next(source, selected as u16, position as nat) as usize,
                    crate::specs::part2_collected_part_count(source, selected as u16, position as nat) as usize) by {
                crate::specs::part2_index_next_bounds(source, selected as u16, (position + 1) as nat);
                reveal_with_fuel(crate::specs::part2_index_next, 1);
                reveal_with_fuel(crate::specs::part2_collected_part_count, 1);
            }
        }
    }
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    Ok(Some(TilePartIndex { entries, next }))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires optional_index_matches(codestream::tile_parts_owned_view(parts@), index),
    ensures crate::specs::part2_collected_parts_result(
        codestream::tile_parts_owned_view(parts@), tile, collected_tile_parts_outcome(result)),
        collected_tile_parts_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            collected_tile_parts_outcome(result) == crate::specs::part2_collect_tile_parts(
                codestream::tile_parts_owned_view(parts@), tile),
))]
pub(super) fn collect_tile_parts_with_index<'data>(
    parts: &[TilePartPayload<'data>],
    tile: u16,
    index: &Option<TilePartIndex>,
) -> Result<Vec<TilePartPayload<'data>>, DecodeError> {
    let index = match index {
        None => return super::execution::collect_tile_parts(parts, tile),
        Some(index) => index,
    };
    let entry = match index.entries.get(usize::from(tile)) {
        None => return super::execution::collect_tile_parts(parts, tile),
        Some(entry) => entry,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source = codestream::tile_parts_owned_view(parts@);
        let ghost mut prefix = Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_index_next_bounds(source, tile, 0); }
    let count = entry.count;
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_collected_capacity_observed(source, tile, count,
            crate::allocation::inspection_capacity_outcome(reserved));
        let root = |events| crate::specs::part2_collected_parts_run(source, tile, events);
        let child = |events| crate::specs::part2_collected_capacity_run(source, tile, events);
        let next = |_: (), rest| crate::specs::part2_collected_loop_run(source, tile, 0, Seq::empty(), rest);
        match reserved {
            Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
            Ok(_) => { prefix = crate::specs::part2_decode_prefix_advance(root, child, next, prefix, ()); },
        }
    }
    let mut output = reserved?;
    let mut position = entry.head;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_index_next_bounds(source, tile, 0);
        assert(codestream::tile_parts_owned_view(output@) =~= Seq::empty());
        assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
            crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                == crate::specs::part2_collected_loop_run(source, tile, position as nat, Seq::empty(), tail) by {
            crate::specs::part2_index_skip(source, tile, 0, Seq::empty(), tail);
        }
        crate::specs::part2_index_skip(source, tile, 0, Seq::empty(), Seq::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= parts.len(),
            source == codestream::tile_parts_owned_view(parts@),
            crate::specs::part2_index_matches(source, entries_view(index.entries@), index.next@),
            (tile as nat) < index.entries.len(),
            position < parts.len() ==> source[position as int].tile_index == tile,
            output.len() as nat + crate::specs::part2_collected_part_count(source, tile, position as nat)
                == count as nat,
            crate::specs::part2_collect_tile_parts(source, tile)
                == Ok(crate::specs::part2_collect_tile_parts_run(
                    source, tile, position as nat, codestream::tile_parts_owned_view(output@))),
            forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                #[trigger] crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                    == crate::specs::part2_collected_loop_run(
                        source, tile, position as nat, codestream::tile_parts_owned_view(output@), tail),
        decreases parts.len() - position,
    ))]
    while position < parts.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(output.len())?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = codestream::tile_parts_owned_view(output@);
            let ghost previous_position = position;
        }
        let part = &parts[position];
        #[cfg(verus_keep_ghost)]
        proof! {
            codestream::tile_part_owned_tile_known(part);
            assert(codestream::tile_part_owned_view(part) == source[position as int]);
        }
        let copied = part.try_duplicate();
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_payload_copy_observed(codestream::tile_part_owned_view(part),
                codestream::tile_part_copy_outcome(copied));
            let root = |events| crate::specs::part2_collected_parts_run(source, tile, events);
            let child = |events| crate::specs::part2_payload_copy_run(source[position as int], events);
            let next = |after: crate::specs::Part2OwnedTilePart, rest|
                crate::specs::part2_collected_loop_run(
                    source, tile, position as nat + 1, before.push(after), rest);
            reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
            reveal_with_fuel(crate::specs::part2_collect_tile_parts_run, 1);
            reveal_with_fuel(crate::specs::part2_collected_part_count, 1);
            assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                root(prefix + tail) == crate::specs::part2_jpip_snapshot_bind(child(tail), next) by {}
            match codestream::tile_part_copy_outcome(copied) {
                Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
                Ok(after) => {
                    prefix = crate::specs::part2_decode_prefix_advance(
                        root, child, next, prefix, after);
                },
            }
        }
        output.push(copied?);
        let following = index.next[position];
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_index_next_bounds(source, tile, position as nat + 1);
            assert(position < following <= parts.len());
        }
        position = following;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                    == crate::specs::part2_collected_loop_run(source, tile, position as nat,
                        codestream::tile_parts_owned_view(output@), tail) by {
                crate::specs::part2_index_skip(source, tile, previous_position as nat + 1,
                    codestream::tile_parts_owned_view(output@), tail);
            }
            crate::specs::part2_index_skip(source, tile, previous_position as nat + 1,
                codestream::tile_parts_owned_view(output@), Seq::empty());
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
        reveal_with_fuel(crate::specs::part2_collect_tile_parts_run, 1);
        assert(crate::specs::part2_cold_prefix(
            |events| crate::specs::part2_collected_parts_run(source, tile, events), prefix,
            Ok(codestream::tile_parts_owned_view(output@))));
    }
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    Ok(output)
}
