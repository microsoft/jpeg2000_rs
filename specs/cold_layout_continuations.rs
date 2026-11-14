//! Checked non-owning cold-copy exits, separate from the live normal tile fold.

use super::*;

verus! {

pub(crate) struct Part1ColdLayoutSot<'a> {
    pub root: Part1ColdLayoutRoot<'a>,
    pub reader: Part1CodestreamReader<'a>,
    pub tile: (usize, u32, u16, u8, u8),
    pub lengths: Part1PacketLengths,
    pub headers: Part1PackedHeaders,
    pub selected: Part1InheritedTileConfiguration,
}

pub(crate) open spec fn part1_cold_layout_sot_known(ctx: Part1ColdLayoutSot<'_>) -> bool {
    let root = ctx.root;
    &&& root.parts < u32::MAX
    &&& (root.parts as int + 1) <= crate::limits::resource_tile_part_limit(root.reader.limits)
    &&& part1_codestream_peek_marker(root.reader) == Ok(0xff90)
    &&& part1_codestream_read_sot(root.reader, root.main.tile_count) == (Ok(ctx.tile), ctx.reader)
    &&& part1_tile_part_main_metadata(ctx.reader.position, ctx.tile, root.parts,
            root.main.raw.extensions.lengths, root.main.raw.plm_seen, root.main.raw.plm,
            root.main.ppm_frames, root.main.raw.ppm_fragments, root.main.header) == Ok((ctx.lengths, ctx.headers))
    &&& part1_select_inherited_tile_configuration(ctx.reader.position, ctx.tile.2 as usize,
            root.main.raw.roi, root.main.coding_style, root.main.quantization, root.main.styles,
            (root.state.0.0, root.state.0.1, root.state.0.2, root.state.0.3, root.state.3)) == Ok(ctx.selected)
}

pub(crate) open spec fn part1_cold_layout_sot_input(ctx: Part1ColdLayoutSot<'_>) -> Part1ColdTileInput<'_> {
    part1_cold_layout_read_input(ctx.reader, ctx.root.main, ctx.root.state,
        ctx.tile, ctx.lengths, ctx.headers, ctx.selected)
}

pub(crate) open spec fn part1_cold_layout_sot_copy(ctx: Part1ColdLayoutSot<'_>, succeeded: bool)
    -> Seq<Part1ColdStorageEvent> {
    let owner = part1_inherited_tile_owner(
        ctx.tile.2 as usize, ctx.root.main.quantizations, ctx.root.state.0.4);
    if owner.1.len() == 0 { Seq::empty() } else {
        seq![Part1ColdStorageEvent { site: 10, elements: owner.1.len() as usize, succeeded }]
    }
}

pub(crate) open spec fn part1_cold_layout_sot_progression_copy(ctx: Part1ColdLayoutSot<'_>, succeeded: bool)
    -> Seq<Part1ColdStorageEvent> {
    let owner = part1_inherited_tile_owner(
        ctx.tile.2 as usize, ctx.root.main.raw.progression, ctx.root.state.0.5);
    if owner.len() == 0 { Seq::empty() } else {
        seq![Part1ColdStorageEvent { site: 14, elements: owner.len() as usize, succeeded }]
    }
}

pub(crate) proof fn part1_cold_layout_sot_progression_error(
    ctx: Part1ColdLayoutSot<'_>, error: crate::DecodeError,
)
    requires part1_cold_layout_prefix(ctx.root), part1_cold_layout_sot_known(ctx),
        part1_inherited_tile_owner(ctx.tile.2 as usize, ctx.root.main.raw.progression, ctx.root.state.0.5).len() > 0,
        error == crate::DecodeError::AllocationFailed,
    ensures part1_cold_layout_result(ctx.root.initial, Err(error)),
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    reveal(part1_cold_layout_tile_part);
    let quantization = part1_cold_layout_sot_copy(ctx, true);
    let progression = part1_cold_layout_sot_progression_copy(ctx, false);
    let calls = quantization + progression;
    if quantization.len() > 0 { assert(calls.drop_first() =~= progression); }
    else { assert(calls =~= progression); }
    assert(progression.drop_first() =~= Seq::<Part1ColdStorageEvent>::empty());
    part1_cold_layout_error(ctx.root, calls, error);
}

pub(crate) proof fn part1_cold_layout_sot_copy_error(
    ctx: Part1ColdLayoutSot<'_>, error: crate::DecodeError,
)
    requires part1_cold_layout_prefix(ctx.root), part1_cold_layout_sot_known(ctx),
        part1_inherited_tile_owner(ctx.tile.2 as usize, ctx.root.main.quantizations, ctx.root.state.0.4).1.len() > 0,
        error == crate::DecodeError::AllocationFailed,
    ensures part1_cold_layout_result(ctx.root.initial, Err(error)),
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    reveal(part1_cold_layout_tile_part);
    let calls = part1_cold_layout_sot_copy(ctx, false);
    assert(calls.drop_first() =~= Seq::<Part1ColdStorageEvent>::empty());
    part1_cold_layout_error(ctx.root, calls, error);
}

pub(crate) proof fn part1_cold_layout_sot_read_error<'a>(
    ctx: Part1ColdLayoutSot<'a>, calls: Seq<Part1ColdStorageEvent>,
    reader: Part1CodestreamReader<'a>, error: crate::DecodeError,
)
    requires part1_cold_layout_prefix(ctx.root), part1_cold_layout_sot_known(ctx),
        part1_cold_tile_part_run(part1_cold_layout_sot_input(ctx), calls)
            == Some(((Err(error), reader), Seq::empty())),
    ensures part1_cold_layout_result(ctx.root.initial, Err(error)),
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    reveal(part1_cold_layout_tile_part);
    let quantization = part1_cold_layout_sot_copy(ctx, true);
    let progression = part1_cold_layout_sot_progression_copy(ctx, true);
    let copied = quantization + progression;
    assert(copied + calls =~= quantization + (progression + calls));
    if quantization.len() > 0 { assert((copied + calls).drop_first() =~= progression + calls); }
    else { assert(copied + calls =~= progression + calls); }
    if progression.len() > 0 { assert((progression + calls).drop_first() =~= calls); }
    else { assert(progression + calls =~= calls); }
    part1_cold_layout_error(ctx.root, copied + calls, error);
}

pub(crate) open spec fn part1_cold_layout_sot_commit_rejected(
    ctx: Part1ColdLayoutSot<'_>, read_calls: Seq<Part1ColdStorageEvent>,
    commit_calls: Seq<Part1ColdStorageEvent>, error: crate::DecodeError,
) -> bool {
    match part1_cold_tile_part_run(part1_cold_layout_sot_input(ctx), read_calls) {
        Some(((Ok((payload, _, _)), reader), rest)) => rest.len() == 0 &&
            match part1_commit_quantization_cold_run(reader.position, ctx.tile.0, ctx.tile.2 as usize,
                ctx.root.state.3.len() as usize, ctx.selected.0, payload, ctx.root.state.0, commit_calls) {
                Some(((Err(actual), _), tail)) => actual == error && tail.len() == 0,
                _ => false,
            },
        _ => false,
    }
}

pub(crate) proof fn part1_cold_layout_sot_commit_error(
    ctx: Part1ColdLayoutSot<'_>, read_calls: Seq<Part1ColdStorageEvent>,
    commit_calls: Seq<Part1ColdStorageEvent>, error: crate::DecodeError,
)
    requires part1_cold_layout_prefix(ctx.root), part1_cold_layout_sot_known(ctx),
        part1_cold_layout_sot_commit_rejected(ctx, read_calls, commit_calls, error),
    ensures part1_cold_layout_result(ctx.root.initial, Err(error)),
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    reveal(part1_cold_layout_tile_part);
    reveal(part1_cold_layout_inherited);
    reveal(part1_cold_layout_after_inherited_copy);
    reveal(part1_cold_commit_state);
    reveal(part1_cold_commit_finish);
    let quantization = part1_cold_layout_sot_copy(ctx, true);
    let progression = part1_cold_layout_sot_progression_copy(ctx, true);
    let copied = quantization + progression;
    let calls = copied + read_calls + commit_calls;
    assert(calls =~= copied + (read_calls + commit_calls));
    assert(calls =~= quantization + (progression + (read_calls + commit_calls)));
    if quantization.len() > 0 { assert(calls.drop_first() =~= progression + (read_calls + commit_calls)); }
    else { assert(calls =~= progression + (read_calls + commit_calls)); }
    if progression.len() > 0 { assert((progression + (read_calls + commit_calls)).drop_first() =~= read_calls + commit_calls); }
    else { assert(progression + (read_calls + commit_calls) =~= read_calls + commit_calls); }
    if let Some(((Ok((payload, parameters, extensions)), reader), rest)) =
        part1_cold_tile_part_run(part1_cold_layout_sot_input(ctx), read_calls) {
        let result = (Ok((payload, parameters, extensions)), reader);
        assert(rest =~= Seq::<Part1ColdStorageEvent>::empty());
        part1_cold_tile_part_frame(part1_cold_layout_sot_input(ctx), read_calls, commit_calls, result, rest);
        assert(rest + commit_calls =~= commit_calls);
        let commit = Part1PersistentTileCommit {
            position: result.1.position, start: ctx.tile.0, index: ctx.tile.2 as usize,
            previous_roi: ctx.selected.0, payload,
            parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
        };
        let configured = part1_commit_quantization_cold_run(commit.position, commit.start, commit.index,
            ctx.root.state.3.len() as usize, commit.previous_roi, commit.payload, ctx.root.state.0, commit_calls);
        assert(configured.is_some());
        let (updated, after) = configured.unwrap();
        assert(updated.0 == Err(error));
        assert(after =~= Seq::<Part1ColdStorageEvent>::empty());
        assert(part1_cold_commit_state(ctx.root.state, commit, commit_calls)
            == Some(((Err(error), (updated.1, ctx.root.state.1, ctx.root.state.2, ctx.root.state.3)), Seq::empty())));
        assert(part1_cold_layout_after_progression_copy(ctx.reader, ctx.root.main, (ctx.root.parts + 1) as u32,
            ctx.root.state, ctx.tile, ctx.lengths, ctx.headers, ctx.selected, read_calls + commit_calls)
                == Some(((Err(error), result.1, (ctx.root.parts + 1) as u32,
                    (updated.1, ctx.root.state.1, ctx.root.state.2, ctx.root.state.3)), Seq::empty())));
    }
    part1_cold_layout_error(ctx.root, calls, error);
}

}
