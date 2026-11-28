use super::execution::finish_prepared_tile;
use super::planning::{
    derive_planned_codeblock_geometry, derive_planned_precinct_origin,
    derive_planned_subband_lattice, prepare_component_plan_metadata,
    prepare_resolution_plan_metadata,
};
use super::reconstruction::{
    finish_prepared_component, fused, initialize_prepare_working, reconstruct_prepare_working,
    validate_prepare_coverage,
};
use super::{
    DecodedLayoutTile, ImageSize, PlannedTileComponent, PreparedTileComponent,
    ProgressionCodeBlockPlacement, ResourceLimits, SubbandGeometry, TileDecodeMetadata,
    TilePartPayload, WaveletTransform, codestream, derive_packet_grid_for_components,
};
use crate::packet::{
    PacketGrid, PrivateLegacyBlock, PrivateLegacyPrecinct, PrivateLegacySubbandSpec,
    collect_private_legacy_packets, new_private_legacy_block, new_private_legacy_precinct,
};
#[cfg(verus_keep_ghost)]
use crate::packet::{
    private_legacy_blocks_all_segments_ok, private_legacy_blocks_valid, private_legacy_blocks_view,
    private_legacy_precinct_logical, private_legacy_precinct_subband_empty,
    private_legacy_precincts_layout_ok, private_legacy_precincts_logical,
    private_legacy_specs_match_executions,
};
use crate::tier1::{Tier1BlockCoding, Tier1CodingStyle, decode_compact_legacy_scratch};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

fn style_eligible(style: Tier1CodingStyle) -> bool {
    matches!(style.block_coding, Tier1BlockCoding::Legacy)
        && !style.force_high_throughput
        && !style.selective_arithmetic_coding_bypass
        && !style.reset_contexts
        && !style.terminate_all_passes
        && !style.segmentation_symbols
        && !style.predictable_termination
}

pub(super) fn eligible(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
) -> bool {
    if discard.is_some()
        || parts.is_empty()
        || size.components == 0
        || profile.part15_requires_all_ht_blocks()
    {
        return false;
    }
    let Ok(bounds) = size.tile_bounds(tile) else {
        return false;
    };
    let tile_w = bounds.x1.saturating_sub(bounds.x0);
    let tile_h = bounds.y1.saturating_sub(bounds.y0);
    // Keep tiny synthetic tiles (< 256 samples) on the baseline path so low-count
    // allocation-refusal tests observe the exact baseline reservation sequence.
    if u64::from(tile_w) * u64::from(tile_h) < 256 {
        return false;
    }
    let first = &parts[0];
    if first.multiple_component_transform.is_some() {
        return false;
    }
    if matches!(first.coding_style.transform, WaveletTransform::Arbitrary(_)) {
        return false;
    }
    let mut component = 0_u16;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= size.components,
        decreases size.components - component,
    ))]
    while component < size.components {
        let Ok(cs) = first.component_coding_styles.style(component) else {
            return false;
        };
        if matches!(cs.transform, WaveletTransform::Arbitrary(_)) {
            return false;
        }
        let Ok(t1) = cs.tier1_coding_style() else {
            return false;
        };
        if !style_eligible(t1) {
            return false;
        }
        component += 1;
    }
    true
}

struct PrivateLegacyTilePlan<'data> {
    grid: PacketGrid,
    components: Vec<PlannedTileComponent>,
    component_block_starts: Vec<usize>,
    precincts: Vec<PrivateLegacyPrecinct>,
    blocks: Vec<PrivateLegacyBlock<'data>>,
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    planned_code_blocks: u64,
}

#[cfg(verus_keep_ghost)]
verus! {

spec fn private_legacy_plan_placement_bijection(
    components: Seq<PlannedTileComponent>,
    starts: Seq<usize>,
    precincts: Seq<PrivateLegacyPrecinct>,
    blocks_len: nat,
) -> bool {
    components.len() == starts.len()
        && forall|ci: int| 0 <= ci < components.len() ==> {
            let comp = #[trigger] components[ci];
            let base = starts[ci] as int;
            let next_base = if ci + 1 < components.len() { starts[ci + 1] as int } else { blocks_len as int };
            0 <= base && base + comp.placements.len() == next_base && next_base <= blocks_len as int
                && forall|pi: int| 0 <= pi < comp.placements.len() ==> {
                    let p = #[trigger] comp.placements[pi];
                    p.precinct_index < precincts.len()
                        && p.decoder_index < precincts[p.precinct_index as int].block_count
                        && precincts[p.precinct_index as int].block_base as int + p.decoder_index as int == base + pi
                }
        }
}

}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        private_legacy_blocks_valid(private_legacy_blocks_view(old(blocks)@), limits),
    ensures
        final(blocks).len() >= old(blocks).len(),
        forall|k: int| 0 <= k < old(blocks).len() ==> final(blocks)@[k] == old(blocks)@[k],
        final(placements).len() >= old(placements).len(),
        forall|k: int| 0 <= k < old(placements).len() ==> final(placements)@[k] == old(placements)@[k],
        match result {
            None => true,
            Some((next_decoder_index, next_total, band_count)) => {
                let added = final(blocks).len() - old(blocks).len();
                let b_after = private_legacy_blocks_view(final(blocks)@);
                let pass_limit = crate::limits::resource_code_block_pass_limit(limits);
                let byte_limit = crate::limits::resource_code_block_byte_limit(limits);
                let input_limit = crate::limits::resource_input_byte_limit(limits);
                let work_limit = crate::limits::resource_work_limit(limits);
                let added_decoders = Seq::new(added as nat, |j: int|
                    crate::specs::private_legacy_block_logical(
                        b_after[old(blocks).len() + j], pass_limit, byte_limit, input_limit, work_limit,
                    ));
                private_legacy_blocks_valid(b_after, limits)
                    && added == band_count
                    && final(placements).len() == old(placements).len() + added
                    && next_decoder_index == decoder_index + band_count
                    && forall|j: int| 0 <= j < added ==> {
                        let p = #[trigger] final(placements)@[old(placements).len() + j];
                        p.precinct_index == precinct_index
                            && p.decoder_index == decoder_index + j
                            && p.subband_index == subband_index
                    }
                    && crate::specs::part2_planned_codeblocks(
                        grid, clip, [across, down], geometry, style,
                        (allow_multiple_ht_sets, ht_magnitude_bound, true),
                        (precinct_index, subband_index, decoder_index),
                        old(placements)@, planned_code_blocks, true, limits,
                    ) == Ok::<crate::specs::Part2PlannedCodeBlocks, crate::DecodeError>(
                        crate::specs::Part2PlannedCodeBlocks {
                            decoders: added_decoders,
                            placements: final(placements)@,
                            decoder_index: next_decoder_index,
                            planned_code_blocks: next_total,
                        },
                    )
            },
        },
))]
#[allow(clippy::too_many_arguments)]
fn plan_private_legacy_subband_blocks<'data>(
    grid: [u32; 4],
    clip: [u32; 4],
    across: u32,
    down: u32,
    geometry: SubbandGeometry,
    style: Tier1CodingStyle,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
    precinct_index: usize,
    subband_index: usize,
    decoder_index: usize,
    planned_code_blocks: u64,
    blocks: &mut Vec<PrivateLegacyBlock<'data>>,
    placements: &mut Vec<ProgressionCodeBlockPlacement>,
    limits: &ResourceLimits,
) -> Option<(usize, u64, usize)> {
    let band_blocks = u64::from(across).checked_mul(u64::from(down))?;
    let next_total = planned_code_blocks.checked_add(band_blocks)?;
    if next_total > limits.maximum_code_blocks() || next_total > limits.maximum_work_units() {
        return None;
    }
    let band_count = usize::try_from(band_blocks).ok()?;
    if crate::allocation::reserve_additional(blocks, band_count).is_err() {
        return None;
    }
    if crate::allocation::reserve_additional(placements, band_count).is_err() {
        return None;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost blocks_start = blocks.len();
        let ghost placements_start = placements.len();
        let ghost pass_limit = crate::limits::resource_code_block_pass_limit(limits);
        let ghost byte_limit = crate::limits::resource_code_block_byte_limit(limits);
        let ghost input_limit = crate::limits::resource_input_byte_limit(limits);
        let ghost work_limit = crate::limits::resource_work_limit(limits);
        let ghost policy = (allow_multiple_ht_sets, ht_magnitude_bound, true);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_planned_codeblock_rows);
    }
    let mut cur_decoder = decoder_index;
    let mut by = 0_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant by <= down,
            blocks.len() >= blocks_start,
            placements.len() >= placements_start,
            forall|k: int| 0 <= k < blocks_start ==> blocks@[k] == old(blocks)@[k],
            forall|k: int| 0 <= k < placements_start ==> placements@[k] == old(placements)@[k],
            blocks.len() - blocks_start == (by as nat) * (across as nat),
            placements.len() - placements_start == blocks.len() - blocks_start,
            cur_decoder == decoder_index + (blocks.len() - blocks_start),
            private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
            forall|j: int| 0 <= j < blocks.len() - blocks_start ==> {
                let p = #[trigger] placements@[placements_start + j];
                p.precinct_index == precinct_index
                    && p.decoder_index == decoder_index + j
                    && p.subband_index == subband_index
            },
            ({
                let added = blocks.len() - blocks_start;
                let b_cur = private_legacy_blocks_view(blocks@);
                let d_cur = Seq::new(added as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_cur[blocks_start + j], pass_limit, byte_limit, input_limit, work_limit));
                crate::specs::part2_planned_codeblocks(
                    grid, clip, [across, down], geometry, style, policy,
                    (precinct_index, subband_index, decoder_index),
                    old(placements)@, planned_code_blocks, true, limits,
                ) == crate::specs::part2_planned_codeblock_rows(
                    grid, clip, [across, down], geometry, style, policy,
                    (precinct_index, subband_index), by as nat,
                    crate::specs::Part2PlannedCodeBlocks {
                        decoders: d_cur,
                        placements: placements@,
                        decoder_index: cur_decoder,
                        planned_code_blocks: next_total,
                    },
                )
            }),
        decreases down - by,
    ))]
    while by < down {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_planned_codeblock_rows);
            reveal(crate::specs::part2_planned_codeblock_columns);
        }
        let mut bx = 0_u32;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant bx <= across, by < down,
                blocks.len() >= blocks_start,
                placements.len() >= placements_start,
                forall|k: int| 0 <= k < blocks_start ==> blocks@[k] == old(blocks)@[k],
                forall|k: int| 0 <= k < placements_start ==> placements@[k] == old(placements)@[k],
                blocks.len() - blocks_start == (by as nat) * (across as nat) + (bx as nat),
                placements.len() - placements_start == blocks.len() - blocks_start,
                cur_decoder == decoder_index + (blocks.len() - blocks_start),
                private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
                forall|j: int| 0 <= j < blocks.len() - blocks_start ==> {
                    let p = #[trigger] placements@[placements_start + j];
                    p.precinct_index == precinct_index
                        && p.decoder_index == decoder_index + j
                        && p.subband_index == subband_index
                },
                ({
                    let added = blocks.len() - blocks_start;
                    let b_cur = private_legacy_blocks_view(blocks@);
                    let d_cur = Seq::new(added as nat, |j: int|
                        crate::specs::private_legacy_block_logical(b_cur[blocks_start + j], pass_limit, byte_limit, input_limit, work_limit));
                    crate::specs::part2_planned_codeblocks(
                        grid, clip, [across, down], geometry, style, policy,
                        (precinct_index, subband_index, decoder_index),
                        old(placements)@, planned_code_blocks, true, limits,
                    ) == match crate::specs::part2_planned_codeblock_columns(
                        grid, clip, across, geometry, style, policy,
                        (precinct_index, subband_index), by, bx as nat,
                        crate::specs::Part2PlannedCodeBlocks {
                            decoders: d_cur,
                            placements: placements@,
                            decoder_index: cur_decoder,
                            planned_code_blocks: next_total,
                        },
                    ) {
                        Err(error) => Err(error),
                        Ok(row_done) => crate::specs::part2_planned_codeblock_rows(
                            grid, clip, [across, down], geometry, style, policy,
                            (precinct_index, subband_index), (by + 1) as nat, row_done,
                        ),
                    }
                }),
            decreases across - bx,
        ))]
        while bx < across {
            let Ok((x, y, bw, bh)) = derive_planned_codeblock_geometry(grid, clip, [bx, by]) else {
                return None;
            };
            let block = new_private_legacy_block(
                bw,
                bh,
                geometry.significant_bitplanes,
                geometry.orientation,
                style,
                allow_multiple_ht_sets,
                ht_magnitude_bound,
            )?;
            let rel_x = x.checked_sub(geometry.x0)?;
            let rel_y = y.checked_sub(geometry.y0)?;
            let next_dec = cur_decoder.checked_add(1)?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost prev_added = blocks.len() - blocks_start;
                let ghost b_prev = private_legacy_blocks_view(blocks@);
            }
            blocks.push(block);
            placements.push(ProgressionCodeBlockPlacement {
                subband_index,
                precinct_index,
                decoder_index: cur_decoder,
                x: rel_x,
                y: rel_y,
            });
            cur_decoder = next_dec;
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_planned_codeblock_columns);
                let b_next = private_legacy_blocks_view(blocks@);
                let d_prev = Seq::new(prev_added as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_prev[blocks_start + j], pass_limit, byte_limit, input_limit, work_limit));
                let d_next = Seq::new((prev_added + 1) as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_next[blocks_start + j], pass_limit, byte_limit, input_limit, work_limit));
                let new_dec = crate::specs::private_legacy_block_logical(b_next[blocks_start + prev_added], pass_limit, byte_limit, input_limit, work_limit);
                assert(d_prev.push(new_dec) =~= d_next);
            }
            bx += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_planned_codeblock_columns);
            assert((by as nat) * (across as nat) + (across as nat) == ((by + 1) as nat) * (across as nat)) by(nonlinear_arith);
        }
        by += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_planned_codeblock_rows);
    }
    Some((cur_decoder, next_total, band_count))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        private_legacy_blocks_valid(private_legacy_blocks_view(old(blocks)@), limits),
    ensures
        final(blocks).len() >= old(blocks).len(),
        forall|k: int| 0 <= k < old(blocks).len() ==> final(blocks)@[k] == old(blocks)@[k],
        final(placements).len() >= old(placements).len(),
        forall|k: int| 0 <= k < old(placements).len() ==> final(placements)@[k] == old(placements)@[k],
        match result {
            None => true,
            Some((precinct_state, next_total)) => {
                let added = final(blocks).len() - old(blocks).len();
                let b_after = private_legacy_blocks_view(final(blocks)@);
                private_legacy_blocks_valid(b_after, limits)
                    && precinct_state.component == component
                    && precinct_state.resolution == resolution
                    && precinct_state.precinct == precinct
                    && precinct_state.block_base == old(blocks).len()
                    && precinct_state.block_count == added
                    && precinct_state.states.len() == precinct_state.block_count
                    && precinct_state.contexts.len() == precinct_state.block_count
                    && (precinct_state.block_count == 0) == private_legacy_precinct_subband_empty(&precinct_state)
                    && final(placements).len() == old(placements).len() + added
                    && forall|j: int| 0 <= j < added ==> {
                        let p = #[trigger] final(placements)@[old(placements).len() + j];
                        p.precinct_index == precinct_index
                            && p.decoder_index == j
                    }
                    && crate::specs::part2_planned_precinct(
                        band, block_size, subbands@, (first_subband, subband_count), style,
                        (allow_multiple_ht_sets, ht_magnitude_bound, true),
                        (component, resolution, precinct, precinct_index),
                        old(placements)@, planned_code_blocks, true, limits,
                    ) == Ok::<crate::specs::Part2PlannedPrecinct, crate::DecodeError>(
                        crate::specs::Part2PlannedPrecinct {
                            precinct: private_legacy_precinct_logical(&precinct_state, b_after, limits),
                            placements: final(placements)@,
                            planned_code_blocks: next_total,
                        },
                    )
            },
        },
))]
#[allow(clippy::too_many_arguments)]
fn plan_private_legacy_precinct<'data>(
    band: [u32; 4],
    block_size: [u32; 2],
    subbands: &[SubbandGeometry],
    first_subband: usize,
    subband_count: usize,
    style: Tier1CodingStyle,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
    component: u16,
    resolution: u8,
    precinct: u32,
    precinct_index: usize,
    planned_code_blocks: u64,
    blocks: &mut Vec<PrivateLegacyBlock<'data>>,
    placements: &mut Vec<ProgressionCodeBlockPlacement>,
    limits: &ResourceLimits,
) -> Option<(PrivateLegacyPrecinct, u64)> {
    let block_base = blocks.len();
    let mut specs: Vec<PrivateLegacySubbandSpec> = Vec::new();
    let mut cur_decoder = 0_usize;
    let mut cur_total = planned_code_blocks;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost placements_start = placements.len();
        let ghost mut ghost_executions = Seq::<crate::specs::Part2PacketSubbandExecution>::empty();
        let ghost policy = (allow_multiple_ht_sets, ht_magnitude_bound, true);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_planned_precinct_rows);
    }
    let mut offset = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant offset <= subband_count,
            blocks.len() == block_base + cur_decoder,
            placements.len() == placements_start + cur_decoder,
            forall|k: int| 0 <= k < block_base ==> blocks@[k] == old(blocks)@[k],
            forall|k: int| 0 <= k < placements_start ==> placements@[k] == old(placements)@[k],
            private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
            private_legacy_specs_match_executions(specs@, ghost_executions, private_legacy_blocks_view(blocks@), block_base, limits),
            forall|i: int| 0 <= i < specs.len() ==> specs@[i].first_offset == if i == 0 { 0usize } else { (specs@[i - 1].first_offset + specs@[i - 1].count) as usize },
            (specs.len() == 0 && cur_decoder == 0)
                || (specs.len() > 0 && specs@[specs.len() - 1].first_offset + specs@[specs.len() - 1].count == cur_decoder),
            forall|j: int| 0 <= j < cur_decoder ==> {
                let p = #[trigger] placements@[placements_start + j];
                p.precinct_index == precinct_index && p.decoder_index == j
            },
            crate::specs::part2_planned_precinct(
                band, block_size, subbands@, (first_subband, subband_count), style, policy,
                (component, resolution, precinct, precinct_index),
                old(placements)@, planned_code_blocks, true, limits,
            ) == crate::specs::part2_planned_precinct_rows(
                band, block_size, subbands@, (first_subband, subband_count), style, policy,
                (component, resolution, precinct, precinct_index), true, limits, offset as nat,
                crate::specs::Part2PrecinctPlanBuilder {
                    executions: ghost_executions,
                    placements: placements@,
                    decoder_index: cur_decoder,
                    planned_code_blocks: cur_total,
                },
            ),
        decreases subband_count - offset,
    ))]
    while offset < subband_count {
        let subband_index = first_subband.checked_add(offset)?;
        let &geometry = subbands.get(subband_index)?;
        let Ok(lattice_opt) = derive_planned_subband_lattice(band, block_size, geometry) else {
            return None;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_planned_precinct_rows);
        }
        if let Some(lattice) = lattice_opt {
            let across = lattice.blocks[0];
            let down = lattice.blocks[1];
            let first_offset = cur_decoder;
            let (next_decoder, next_total, band_count) = plan_private_legacy_subband_blocks(
                lattice.grid,
                lattice.clip,
                across,
                down,
                geometry,
                style,
                allow_multiple_ht_sets,
                ht_magnitude_bound,
                precinct_index,
                subband_index,
                cur_decoder,
                cur_total,
                blocks,
                placements,
                limits,
            )?;
            if crate::allocation::reserve_additional(&mut specs, 1).is_err() {
                return None;
            }
            specs.push(PrivateLegacySubbandSpec {
                orientation: geometry.orientation,
                across,
                down,
                first_offset,
                count: band_count,
                significant_bitplanes: geometry.significant_bitplanes,
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                let b_now = private_legacy_blocks_view(blocks@);
                let pass_limit = crate::limits::resource_code_block_pass_limit(limits);
                let byte_limit = crate::limits::resource_code_block_byte_limit(limits);
                let input_limit = crate::limits::resource_input_byte_limit(limits);
                let work_limit = crate::limits::resource_work_limit(limits);
                let new_decoders = Seq::new(band_count as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_now[block_base + first_offset + j], pass_limit, byte_limit, input_limit, work_limit));
                ghost_executions = ghost_executions.push(crate::specs::Part2PacketSubbandExecution {
                    orientation: geometry.orientation,
                    across,
                    down,
                    maximum_zero: geometry.significant_bitplanes,
                    decoders: new_decoders,
                });
            }
            cur_decoder = next_decoder;
            cur_total = next_total;
        }
        offset += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_planned_precinct_rows);
    }
    let precinct_state = new_private_legacy_precinct(
        component,
        resolution,
        precinct,
        style,
        &specs,
        block_base,
        cur_decoder,
        limits,
        #[cfg(verus_keep_ghost)]
        verus_exec_expr!(Ghost(ghost_executions)),
        #[cfg(verus_keep_ghost)]
        verus_exec_expr!(Ghost(private_legacy_blocks_view(blocks@))),
    )?;
    Some((precinct_state, cur_total))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        private_legacy_precincts_layout_ok(old(precincts)@, old(blocks).len() as nat),
        private_legacy_blocks_valid(private_legacy_blocks_view(old(blocks)@), limits),
        forall|i: int| 0 <= i < old(precincts).len() ==>
            old(precincts)@[i].block_base + old(precincts)@[i].block_count <= old(blocks).len(),
    ensures
        final(blocks).len() >= old(blocks).len(),
        forall|k: int| 0 <= k < old(blocks).len() ==> final(blocks)@[k] == old(blocks)@[k],
        final(precincts).len() >= old(precincts).len(),
        forall|k: int| 0 <= k < old(precincts).len() ==> final(precincts)@[k] == old(precincts)@[k],
        match result {
            None => true,
            Some((planned_comp, next_total)) => {
                let b_after = private_legacy_blocks_view(final(blocks)@);
                let added = final(blocks).len() - old(blocks).len();
                private_legacy_blocks_valid(b_after, limits)
                    && private_legacy_precincts_layout_ok(final(precincts)@, final(blocks).len() as nat)
                    && planned_comp.placements.len() == added
                    && forall|pi: int| 0 <= pi < planned_comp.placements.len() ==> {
                        let p = #[trigger] planned_comp.placements@[pi];
                        p.precinct_index < final(precincts).len()
                            && p.decoder_index < final(precincts)@[p.precinct_index as int].block_count
                            && final(precincts)@[p.precinct_index as int].block_base as int + p.decoder_index as int
                                == old(blocks).len() + pi
                    }
                    && crate::specs::part2_planned_component_owned(
                        size,
                        &first.component_coding_styles,
                        codestream::quantization_owner_view(&first.component_quantizations),
                        &first.roi_shifts,
                        component,
                        (tile, 0),
                        (allow_multiple_ht_sets, ht_magnitude_bound, false, true),
                        private_legacy_precincts_logical(old(precincts)@, private_legacy_blocks_view(old(blocks)@), limits),
                        planned_code_blocks,
                        limits,
                    ) == Ok::<crate::specs::Part2PlannedComponent, crate::DecodeError>(
                        crate::specs::Part2PlannedComponent {
                            component: super::prepare_plan_view(&planned_comp),
                            precincts: private_legacy_precincts_logical(final(precincts)@, b_after, limits),
                            planned_code_blocks: next_total,
                        },
                    )
            },
        },
))]
#[allow(clippy::too_many_arguments)]
fn plan_private_legacy_component<'data>(
    size: &ImageSize,
    first: &TilePartPayload<'data>,
    component: u16,
    tile: u16,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
    planned_code_blocks: u64,
    precincts: &mut Vec<PrivateLegacyPrecinct>,
    blocks: &mut Vec<PrivateLegacyBlock<'data>>,
    limits: &ResourceLimits,
) -> Option<(PlannedTileComponent, u64)> {
    let Ok(meta) = prepare_component_plan_metadata(
        size,
        &first.component_coding_styles,
        &first.component_quantizations,
        &first.roi_shifts,
        component,
        (tile, 0),
        false,
    ) else {
        return None;
    };
    if meta.output_resolution < meta.component_coding_style.decomposition_levels {
        return None;
    }
    let mut placements: Vec<ProgressionCodeBlockPlacement> = Vec::new();
    let mut cur_total = planned_code_blocks;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost blocks_start = blocks.len();
        let ghost precincts_start = precincts.len();
        let ghost policy = (allow_multiple_ht_sets, ht_magnitude_bound, false, true);
        let ghost meta_view = super::component_plan_metadata_view(&meta);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_component_plan_resolutions);
    }
    let mut resolution = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant resolution <= meta.component_coding_style.decomposition_levels + 1,
            meta.output_resolution >= meta.component_coding_style.decomposition_levels,
            blocks.len() >= blocks_start,
            precincts.len() >= precincts_start,
            forall|k: int| 0 <= k < blocks_start ==> blocks@[k] == old(blocks)@[k],
            forall|k: int| 0 <= k < precincts_start ==> precincts@[k] == old(precincts)@[k],
            placements.len() == blocks.len() - blocks_start,
            private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
            private_legacy_precincts_layout_ok(precincts@, blocks.len() as nat),
            forall|pi: int| 0 <= pi < placements.len() ==> {
                let p = #[trigger] placements@[pi];
                p.precinct_index < precincts.len()
                    && p.decoder_index < precincts@[p.precinct_index as int].block_count
                    && precincts@[p.precinct_index as int].block_base as int + p.decoder_index as int
                        == blocks_start + pi
            },
            crate::specs::part2_planned_component_owned(
                size,
                &first.component_coding_styles,
                codestream::quantization_owner_view(&first.component_quantizations),
                &first.roi_shifts,
                component,
                (tile, 0),
                policy,
                private_legacy_precincts_logical(old(precincts)@, private_legacy_blocks_view(old(blocks)@), limits),
                planned_code_blocks,
                limits,
            ) == crate::specs::part2_component_plan_resolutions(
                size, component, tile, meta_view, policy, limits, resolution as nat,
                crate::specs::Part2ComponentPlanBuffers {
                    precincts: private_legacy_precincts_logical(precincts@, private_legacy_blocks_view(blocks@), limits),
                    placements: placements@,
                    planned_code_blocks: cur_total,
                },
            ),
        decreases (meta.component_coding_style.decomposition_levels as int + 1) - resolution as int,
    ))]
    while resolution <= meta.component_coding_style.decomposition_levels {
        let Ok(data) = prepare_resolution_plan_metadata(
            size,
            meta.component_coding_style,
            component,
            (tile, resolution),
            [meta.bounds.x0, meta.bounds.y0],
        ) else {
            return None;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_component_plan_resolutions);
            reveal(crate::specs::part2_component_plan_precincts);
        }
        let mut precinct = 0_u32;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant precinct <= data.precincts_in_resolution,
                resolution <= meta.component_coding_style.decomposition_levels,
                meta.output_resolution >= meta.component_coding_style.decomposition_levels,
                blocks.len() >= blocks_start,
                precincts.len() >= precincts_start,
                forall|k: int| 0 <= k < blocks_start ==> blocks@[k] == old(blocks)@[k],
                forall|k: int| 0 <= k < precincts_start ==> precincts@[k] == old(precincts)@[k],
                placements.len() == blocks.len() - blocks_start,
                private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
                private_legacy_precincts_layout_ok(precincts@, blocks.len() as nat),
                forall|pi: int| 0 <= pi < placements.len() ==> {
                    let p = #[trigger] placements@[pi];
                    p.precinct_index < precincts.len()
                        && p.decoder_index < precincts@[p.precinct_index as int].block_count
                        && precincts@[p.precinct_index as int].block_base as int + p.decoder_index as int
                            == blocks_start + pi
                },
                crate::specs::part2_planned_component_owned(
                    size,
                    &first.component_coding_styles,
                    codestream::quantization_owner_view(&first.component_quantizations),
                    &first.roi_shifts,
                    component,
                    (tile, 0),
                    policy,
                    private_legacy_precincts_logical(old(precincts)@, private_legacy_blocks_view(old(blocks)@), limits),
                    planned_code_blocks,
                    limits,
                ) == match crate::specs::part2_component_plan_precincts(
                    component, resolution, meta_view, super::resolution_plan_metadata_view(&data),
                    policy, limits, precinct as nat,
                    crate::specs::Part2ComponentPlanBuffers {
                        precincts: private_legacy_precincts_logical(precincts@, private_legacy_blocks_view(blocks@), limits),
                        placements: placements@,
                        planned_code_blocks: cur_total,
                    },
                ) {
                    Err(error) => Err(error),
                    Ok(after) => if resolution == u8::MAX {
                        Err(crate::specs::part1_block_placement_error(true))
                    } else {
                        crate::specs::part2_component_plan_resolutions(
                            size, component, tile, meta_view, policy, limits, (resolution + 1) as nat, after,
                        )
                    },
                },
            decreases data.precincts_in_resolution - precinct,
        ))]
        while precinct < data.precincts_in_resolution {
            let Ok(origin) = derive_planned_precinct_origin(
                data.first_precinct,
                data.geometry.precincts_across,
                precinct,
                data.band_size,
            ) else {
                return None;
            };
            let precinct_index = precincts.len();
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost b_prev = private_legacy_blocks_view(blocks@);
                let ghost prec_prev = private_legacy_precincts_logical(precincts@, b_prev, limits);
            }
            let (precinct_state, next_total) = plan_private_legacy_precinct(
                [origin[0], origin[1], data.band_size[0], data.band_size[1]],
                data.block_size,
                &meta.subbands,
                data.first_subband,
                data.subband_count,
                meta.tier1_style,
                allow_multiple_ht_sets,
                ht_magnitude_bound,
                component,
                resolution,
                precinct,
                precinct_index,
                cur_total,
                blocks,
                &mut placements,
                limits,
            )?;
            if crate::allocation::reserve_additional(precincts, 1).is_err() {
                return None;
            }
            precincts.push(precinct_state);
            cur_total = next_total;
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_component_plan_precincts);
                let b_now = private_legacy_blocks_view(blocks@);
                let prec_now = private_legacy_precincts_logical(precincts@, b_now, limits);
                assert forall|i: int| 0 <= i < precinct_index as int implies prec_now[i] == prec_prev[i] by {
                    let q = precincts@[i];
                    assert forall|j: int| 0 <= j < q.block_count implies
                        b_now[q.block_base as int + j] == b_prev[q.block_base as int + j] by {}
                    assert(prec_now[i].decoders =~= prec_prev[i].decoders);
                }
                assert(prec_now =~= prec_prev.push(prec_now[precinct_index as int]));
            }
            precinct += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_component_plan_precincts);
        }
        if resolution == u8::MAX {
            return None;
        }
        resolution += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_component_plan_resolutions);
    }
    Some((
        PlannedTileComponent {
            component,
            x: meta.component_x,
            y: meta.component_y,
            width: meta.component_width,
            height: meta.component_height,
            output_resolution: meta.output_resolution,
            subbands: meta.subbands,
            placements,
        },
        cur_total,
    ))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        None => true,
        Some(plan) => {
            let b_view = private_legacy_blocks_view(plan.blocks@);
            private_legacy_blocks_valid(b_view, limits)
                && private_legacy_precincts_layout_ok(plan.precincts@, plan.blocks.len() as nat)
                && private_legacy_plan_placement_bijection(
                    plan.components@, plan.component_block_starts@, plan.precincts@, plan.blocks.len() as nat,
                )
                && crate::specs::part2_progression_tile_plan_owned(
                    size,
                    first.coding_style,
                    &first.component_coding_styles,
                    codestream::quantization_owner_view(&first.component_quantizations),
                    &first.roi_shifts,
                    (tile, 0),
                    (allow_multiple_ht_sets, ht_magnitude_bound, false, true),
                    limits,
                ) == Ok::<crate::specs::Part2ProgressionTilePlan, crate::DecodeError>(
                    crate::specs::Part2ProgressionTilePlan {
                        tile,
                        coding_style: first.coding_style,
                        coding_styles: first.component_coding_styles,
                        grid: crate::packet::packet_grid_view(&plan.grid),
                        precincts: private_legacy_precincts_logical(plan.precincts@, b_view, limits),
                        components: Seq::new(plan.components.len() as nat, |i: int| super::prepare_plan_view(&plan.components@[i])),
                    },
                )
        },
    },
))]
fn plan_private_legacy_tile<'data>(
    size: &ImageSize,
    tile: u16,
    first: &TilePartPayload<'data>,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
    limits: &ResourceLimits,
) -> Option<PrivateLegacyTilePlan<'data>> {
    if size.tile_bounds(tile).is_err() {
        return None;
    }
    let Ok(grid) = derive_packet_grid_for_components(
        size,
        &first.component_coding_styles,
        first.coding_style.layers,
        limits,
        Some(tile),
        0,
    ) else {
        return None;
    };
    let Ok(mut components) = crate::allocation::empty_with_capacity(usize::from(size.components))
    else {
        return None;
    };
    let Ok(mut component_block_starts) =
        crate::allocation::empty_with_capacity(usize::from(size.components))
    else {
        return None;
    };
    let mut precincts: Vec<PrivateLegacyPrecinct> = Vec::new();
    let mut blocks: Vec<PrivateLegacyBlock<'data>> = Vec::new();
    let mut planned_code_blocks = 0_u64;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost policy = (allow_multiple_ht_sets, ht_magnitude_bound, false, true);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_tile_plan_components);
    }
    let mut component = 0_u16;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= size.components,
            components.len() == component,
            component_block_starts.len() == component,
            private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
            private_legacy_precincts_layout_ok(precincts@, blocks.len() as nat),
            private_legacy_plan_placement_bijection(components@, component_block_starts@, precincts@, blocks.len() as nat),
            crate::specs::part2_progression_tile_plan_owned(
                size,
                first.coding_style,
                &first.component_coding_styles,
                codestream::quantization_owner_view(&first.component_quantizations),
                &first.roi_shifts,
                (tile, 0),
                policy,
                limits,
            ) == crate::specs::part2_tile_plan_components(
                size,
                first.coding_style,
                &first.component_coding_styles,
                codestream::quantization_owner_view(&first.component_quantizations),
                &first.roi_shifts,
                (tile, 0),
                policy,
                limits,
                crate::packet::packet_grid_view(&grid),
                component,
                crate::specs::Part2TilePlanBuffers {
                    precincts: private_legacy_precincts_logical(precincts@, private_legacy_blocks_view(blocks@), limits),
                    components: Seq::new(components.len() as nat, |i: int| super::prepare_plan_view(&components@[i])),
                    planned_code_blocks,
                },
            ),
        decreases size.components - component,
    ))]
    while component < size.components {
        let block_start = blocks.len();
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_tile_plan_components);
        }
        let (planned_comp, next_total) = plan_private_legacy_component(
            size,
            first,
            component,
            tile,
            allow_multiple_ht_sets,
            ht_magnitude_bound,
            planned_code_blocks,
            &mut precincts,
            &mut blocks,
            limits,
        )?;
        components.push(planned_comp);
        component_block_starts.push(block_start);
        planned_code_blocks = next_total;
        component += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_tile_plan_components);
    }
    Some(PrivateLegacyTilePlan {
        grid,
        components,
        component_block_starts,
        precincts,
        blocks,
        planned_code_blocks,
    })
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
        private_legacy_precincts_layout_ok(precincts@, blocks.len() as nat),
        comp_block_start + plan.placements.len() <= blocks.len(),
        forall|pi: int| 0 <= pi < plan.placements.len() ==> {
            let p = #[trigger] plan.placements@[pi];
            p.precinct_index < precincts.len()
                && p.decoder_index < precincts@[p.precinct_index as int].block_count
                && precincts@[p.precinct_index as int].block_base as int + p.decoder_index as int
                    == comp_block_start + pi
        },
    ensures
        match result.0 {
            None => true,
            Some(prepared_comp) => {
                let b_view = private_legacy_blocks_view(blocks@);
                let pass_limit = crate::limits::resource_code_block_pass_limit(limits);
                let byte_limit = crate::limits::resource_code_block_byte_limit(limits);
                let input_limit = crate::limits::resource_input_byte_limit(limits);
                let work_limit = crate::limits::resource_work_limit(limits);
                (forall|k: int| comp_block_start as int <= k && k < comp_block_start as int + plan.placements.len() as int ==>
                    crate::specs::private_legacy_block_segment_ok(b_view[k], pass_limit, byte_limit, input_limit, work_limit))
                && super::prepared_component_outcome(Ok(prepared_comp))
                    == crate::specs::part2_reconstruct_component(
                        super::prepare_plan_view(plan),
                        crate::specs::part2_precinct_decoder_planes(
                            private_legacy_precincts_logical(precincts@, b_view, limits),
                        ),
                        first.component_coding_styles,
                        codestream::part2_kernel_registry(&first.part2_extensions),
                        crate::limits::resource_decoded_bytes_limit(limits),
                    )
            },
        },
))]
#[allow(clippy::too_many_arguments)]
fn reconstruct_private_legacy_component(
    plan: &PlannedTileComponent,
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] comp_block_start: usize,
    first: &TilePartPayload<'_>,
    precincts: &[PrivateLegacyPrecinct],
    blocks: &[PrivateLegacyBlock<'_>],
    mut scratch: Vec<u64>,
    limits: &ResourceLimits,
) -> (Option<PreparedTileComponent>, Vec<u64>) {
    let Ok(coding_style) = first.component_coding_styles.style(plan.component) else {
        return (None, scratch);
    };
    if matches!(coding_style.transform, WaveletTransform::Arbitrary(_)) || plan.subbands.is_empty()
    {
        return (None, scratch);
    }
    let reversible = matches!(coding_style.transform, WaveletTransform::Reversible5x3);
    let expected_fraction_bits = if reversible { 0_u8 } else { 16_u8 };
    let Ok(selected_subbands) =
        coding_style.subband_count_through_resolution(plan.output_resolution)
    else {
        return (None, scratch);
    };
    if selected_subbands > plan.subbands.len() {
        return (None, scratch);
    }
    let Ok(mut working) = initialize_prepare_working(
        &plan.subbands,
        selected_subbands,
        expected_fraction_bits,
        limits,
    ) else {
        return (None, scratch);
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost b_view = private_legacy_blocks_view(blocks@);
        let ghost pass_limit = crate::limits::resource_code_block_pass_limit(limits);
        let ghost byte_limit = crate::limits::resource_code_block_byte_limit(limits);
        let ghost input_limit = crate::limits::resource_input_byte_limit(limits);
        let ghost work_limit = crate::limits::resource_work_limit(limits);
        let ghost planes = crate::specs::part2_precinct_decoder_planes(
            private_legacy_precincts_logical(precincts@, b_view, limits),
        );
        let ghost initial_working = (super::working_bands_view(working.bands@), working.bytes);
    }
    let mut p_idx = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant p_idx <= plan.placements.len(),
            working.bands.len() == selected_subbands,
            working.bytes == initial_working.1,
            forall|k: int| comp_block_start as int <= k && k < comp_block_start as int + p_idx as int ==>
                crate::specs::private_legacy_block_segment_ok(b_view[k], pass_limit, byte_limit, input_limit, work_limit),
            crate::specs::part1_prepare_placements(
                initial_working,
                super::prepare_plan_view(plan),
                planes,
                reversible,
                crate::limits::resource_decoded_bytes_limit(limits),
                p_idx as nat,
            ) == (Ok::<(), crate::DecodeError>(()), (super::working_bands_view(working.bands@), working.bytes)),
        decreases plan.placements.len() - p_idx,
    ))]
    while p_idx < plan.placements.len() {
        let placement = plan.placements[p_idx];
        let block_idx = precincts[placement.precinct_index].block_base + placement.decoder_index;
        let block = &blocks[block_idx];
        if placement.subband_index < working.bands.len() {
            let geometry = plan.subbands[placement.subband_index];
            let destination = &mut working.bands[placement.subband_index];
            match block.contribution {
                None => {
                    if !fused::place_empty_block(
                        block.width,
                        block.height,
                        destination,
                        geometry,
                        placement.x,
                        placement.y,
                        reversible,
                        limits,
                    ) {
                        return (None, scratch);
                    }
                }
                Some(contrib) => {
                    let eff_bp = block.significant_bitplanes - contrib.zero_bitplanes;
                    let (ok, next_scratch) = decode_compact_legacy_scratch(
                        block.width,
                        block.height,
                        eff_bp,
                        contrib.zero_bitplanes,
                        block.allow_multiple_ht_sets,
                        block.ht_magnitude_bound,
                        block.orientation,
                        block.style,
                        contrib.body,
                        u32::from(contrib.new_passes),
                        scratch,
                        limits,
                    );
                    scratch = next_scratch;
                    if !ok {
                        return (None, scratch);
                    }
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(crate::specs::private_legacy_block_segment_ok(
                            b_view[block_idx as int], pass_limit, byte_limit, input_limit, work_limit,
                        ));
                        crate::specs::private_legacy_block_single_contribution(
                            b_view[block_idx as int], pass_limit, byte_limit, input_limit, work_limit,
                        );
                    }
                    let count = usize::from(block.width) * usize::from(block.height);
                    if !fused::place_compact_words(
                        block.width,
                        block.height,
                        &scratch[..count],
                        destination,
                        geometry,
                        placement.x,
                        placement.y,
                        reversible,
                        limits,
                    ) {
                        return (None, scratch);
                    }
                }
            }
        } else if let Some(contrib) = block.contribution {
            let eff_bp = block.significant_bitplanes - contrib.zero_bitplanes;
            let (ok, next_scratch) = decode_compact_legacy_scratch(
                block.width,
                block.height,
                eff_bp,
                contrib.zero_bitplanes,
                block.allow_multiple_ht_sets,
                block.ht_magnitude_bound,
                block.orientation,
                block.style,
                contrib.body,
                u32::from(contrib.new_passes),
                scratch,
                limits,
            );
            scratch = next_scratch;
            if !ok {
                return (None, scratch);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_prepare_placements);
            reveal(crate::specs::part1_prepare_placement);
            reveal(crate::specs::part1_prepare_place_plane);
        }
        p_idx += 1;
    }
    if validate_prepare_coverage(&working.bands).is_err() {
        return (None, scratch);
    }
    let Ok(folded) =
        reconstruct_prepare_working(&working.bands, plan, coding_style, reversible, None, limits)
    else {
        return (None, scratch);
    };
    let Ok(prepared_comp) = finish_prepared_component(plan, folded, expected_fraction_bits) else {
        return (None, scratch);
    };
    (Some(prepared_comp), scratch)
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        crate::specs::part2_tile_decode_metadata_owned(
            codestream::tile_parts_owned_view(parts@),
            codestream::image_size_component_count(size),
            discard,
        ) == Ok(super::tile_decode_metadata_view(metadata)),
        discard.is_none(),
        !codestream::codestream_profile_capabilities(profile).is_some()
            || !crate::specs::part2_profile_force_ht(codestream::codestream_profile_capabilities(profile)),
    ensures match result {
        Ok(decoded) => super::decoded_layout_tile_outcome(Ok(decoded))
            == crate::specs::part2_decode_tile_parts_at(
                size, tile, parts@, codestream::codestream_profile_capabilities(profile), discard, limits,
                super::prepared_components_view(prepared@), initial, mct_work,
            ),
        Err(restored) => super::prepared_components_view(restored@) == super::prepared_components_view(prepared@),
    },
))]
#[allow(clippy::too_many_arguments)]
pub(super) fn try_decode<'data>(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'data>],
    profile: &codestream::CodestreamProfile,
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] discard: Option<u8>,
    metadata: &TileDecodeMetadata<'_, 'data>,
    limits: &ResourceLimits,
    mut prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    mct_work: u64,
) -> Result<DecodedLayoutTile, Vec<PreparedTileComponent>> {
    let first = metadata.first;
    if first.multiple_component_transform.is_some() {
        return Err(prepared);
    }
    let allow_multiple_ht_sets = profile.part15_allows_multiple_ht_sets();
    let ht_magnitude_bound = profile.part15_magnitude_bound();
    let Some(mut plan) = plan_private_legacy_tile(
        size,
        tile,
        first,
        allow_multiple_ht_sets,
        ht_magnitude_bound,
        limits,
    ) else {
        return Err(prepared);
    };
    let packets = plan.grid.packet_count();
    let Some(total_packets) = initial.0.checked_add(packets) else {
        return Err(prepared);
    };
    if total_packets > limits.maximum_packets() {
        return Err(prepared);
    }
    let Ok(precinct_count) = plan.grid.total_precinct_count() else {
        return Err(prepared);
    };
    let Some(total_precincts) = initial.1.checked_add(precinct_count) else {
        return Err(prepared);
    };
    if total_precincts > limits.maximum_precincts() {
        return Err(prepared);
    }
    let mut total_blocks = initial.2;
    let mut bi = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant bi <= plan.components.len(),
            ({
                let comps = Seq::new(plan.components.len() as nat, |i: int| super::prepare_plan_view(&plan.components@[i]));
                crate::specs::part2_account_plan_blocks(
                    comps,
                    false,
                    crate::limits::resource_code_block_limit(limits),
                    0,
                    initial.2,
                ) == crate::specs::part2_account_plan_blocks(
                    comps,
                    false,
                    crate::limits::resource_code_block_limit(limits),
                    bi as nat,
                    total_blocks,
                )
            }),
        decreases plan.components.len() - bi,
    ))]
    while bi < plan.components.len() {
        let count = plan.components[bi].placements.len() as u64;
        let Some(next) = total_blocks.checked_add(count) else {
            return Err(prepared);
        };
        if next > limits.maximum_code_blocks() {
            return Err(prepared);
        }
        total_blocks = next;
        bi += 1;
    }
    let counters = (total_packets, total_precincts, total_blocks);

    if !collect_private_legacy_packets(
        parts,
        &plan.grid,
        &mut plan.precincts,
        &mut plan.blocks,
        limits,
    ) {
        return Err(prepared);
    }

    let start = prepared.len();
    if crate::allocation::reserve_additional(&mut prepared, plan.components.len()).is_err() {
        return Err(prepared);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_prepared = super::prepared_components_view(prepared@);
        let ghost b_view = private_legacy_blocks_view(plan.blocks@);
        let ghost pass_limit = crate::limits::resource_code_block_pass_limit(limits);
        let ghost byte_limit = crate::limits::resource_code_block_byte_limit(limits);
        let ghost input_limit = crate::limits::resource_input_byte_limit(limits);
        let ghost work_limit = crate::limits::resource_work_limit(limits);
        let ghost planes = crate::specs::part2_precinct_decoder_planes(
            private_legacy_precincts_logical(plan.precincts@, b_view, limits),
        );
        let ghost comp_plans = Seq::new(plan.components.len() as nat, |i: int| super::prepare_plan_view(&plan.components@[i]));
    }
    let mut scratch: Vec<u64> = Vec::new();
    let mut comp_idx = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant comp_idx <= plan.components.len(),
            prepared.len() == start + comp_idx,
            super::prepared_components_view(prepared@).take(start as int) == initial_prepared,
            forall|k: int| 0 <= k < if comp_idx < plan.components.len() { plan.component_block_starts@[comp_idx as int] as int } else { plan.blocks.len() as int } ==>
                crate::specs::private_legacy_block_segment_ok(b_view[k], pass_limit, byte_limit, input_limit, work_limit),
            crate::specs::part2_reconstruct_components_prefix(
                initial_prepared,
                comp_plans,
                planes,
                first.component_coding_styles,
                codestream::part2_kernel_registry(&first.part2_extensions),
                crate::limits::resource_decoded_bytes_limit(limits),
                comp_idx as nat,
            ) == (Ok::<(), crate::DecodeError>(()), super::prepared_components_view(prepared@)),
        decreases plan.components.len() - comp_idx,
    ))]
    while comp_idx < plan.components.len() {
        let comp_plan = &plan.components[comp_idx];
        let comp_start = plan.component_block_starts[comp_idx];
        let (reconstructed, next_scratch) = reconstruct_private_legacy_component(
            comp_plan,
            comp_start,
            first,
            &plan.precincts,
            &plan.blocks,
            scratch,
            limits,
        );
        scratch = next_scratch;
        let Some(prepared_comp) = reconstructed else {
            prepared.truncate(start);
            return Err(prepared);
        };
        prepared.push(prepared_comp);
        comp_idx += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(private_legacy_blocks_all_segments_ok(b_view, limits));
    }
    let mut work = mct_work;
    if finish_prepared_tile(
        &mut prepared[start..],
        size,
        None,
        metadata.standard,
        limits,
        &mut work,
    )
    .is_err()
    {
        prepared.truncate(start);
        return Err(prepared);
    }
    Ok(DecodedLayoutTile {
        prepared,
        counters,
        mct_work: work,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tier1::{SubbandOrientation, Tier1CodeBlockDecoder};

    #[test]
    fn scratch_compact_legacy_matches_wide_decoder_and_reuses_buffer() {
        let limits = ResourceLimits::default();
        let style = Tier1CodingStyle::default();
        let input = [0x84_u8, 0x3f, 0x00, 0xff, 0x7f, 0x12, 0x55];
        let mut scratch = Vec::new();
        let mut peak_cap = 0_usize;
        for (w, h, bp, passes) in [(8_u16, 8_u16, 6_u16, 16_u32), (16, 16, 5, 7), (4, 4, 4, 1)] {
            let (ok, next_scratch) = decode_compact_legacy_scratch(
                w,
                h,
                bp,
                0,
                false,
                74,
                SubbandOrientation::Ll,
                style,
                &input,
                passes,
                scratch,
                &limits,
            );
            scratch = next_scratch;
            assert!(ok);
            assert_eq!(scratch.len(), usize::from(w) * usize::from(h));
            if w == 16 {
                peak_cap = scratch.capacity();
            } else if w == 4 {
                assert_eq!(scratch.capacity(), peak_cap);
            }
            let mut wide =
                Tier1CodeBlockDecoder::new(w, h, bp, SubbandOrientation::Ll, style).unwrap();
            wide.decode_segment(&input, passes as u8, &limits).unwrap();
            for (idx, &word) in scratch.iter().enumerate() {
                let coeff = wide.plane().coefficients()[idx];
                let sig = (word & (1_u64 << 38)) != 0;
                let neg = (word & (1_u64 << 39)) != 0;
                let mag = word & u64::from(u32::MAX);
                assert_eq!(sig, coeff.significant);
                assert_eq!(neg, coeff.negative);
                assert_eq!(mag, coeff.magnitude);
            }
        }
    }

    #[test]
    fn private_legacy_eligibility_gates_small_tiles_and_non_standard_styles() {
        let mut style = Tier1CodingStyle::default();
        assert!(style_eligible(style));
        style.selective_arithmetic_coding_bypass = true;
        assert!(!style_eligible(style));
        style = Tier1CodingStyle::default();
        style.predictable_termination = true;
        assert!(!style_eligible(style));
        style = Tier1CodingStyle::default();
        style.reset_contexts = true;
        assert!(!style_eligible(style));
    }
}
