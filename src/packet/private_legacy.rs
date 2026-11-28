#[cfg(verus_keep_ghost)]
use super::DecodeError;
use super::body::preflight_packet_body_ranges;
use super::precinct::{
    decode_precinct_contribution_headers, decode_precinct_packet_payload_prefix,
    prepare_precinct_contexts,
};
use super::tag_tree::tag_tree_new;
use super::tile::{
    account_progression_packet, advance_progression_tile_part, all_progression_packets_seen,
    finish_progression_tile_packets, omit_progression_packet, prepare_progression_payloads,
    progression_packet_slot, progression_tile_progress_new, set_progression_context_layer,
    validate_progression_layout,
};
use super::{
    CodeBlockContribution, CodeBlockPacketContext, CodeBlockPacketState, PacketBodyDecode,
    PacketBodyPreflight, PacketGrid, PacketSubbandState, PrecinctHeaderParameters,
    PrecinctHeaderProgress, PrecinctPayloadParameters, ProgressionTileParameters, ResourceLimits,
    SubbandOrientation, Tier1CodingStyle, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(crate) struct PrivateLegacyBlock<'data> {
    pub(crate) width: u16,
    pub(crate) height: u16,
    pub(crate) significant_bitplanes: u16,
    pub(crate) orientation: SubbandOrientation,
    pub(crate) style: Tier1CodingStyle,
    pub(crate) allow_multiple_ht_sets: bool,
    pub(crate) ht_magnitude_bound: u8,
    pub(crate) contribution: Option<(CodeBlockContribution, &'data [u8])>,
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn private_legacy_block_view(block: &PrivateLegacyBlock<'_>) -> crate::specs::PrivateLegacyBlockSpec {
    crate::specs::PrivateLegacyBlockSpec {
        width: block.width,
        height: block.height,
        significant_bitplanes: block.significant_bitplanes,
        orientation: block.orientation,
        style: block.style,
        allow_multiple_ht_sets: block.allow_multiple_ht_sets,
        ht_magnitude_bound: block.ht_magnitude_bound,
        contribution: match block.contribution {
            None => None,
            Some((c, body)) => Some((super::code_block_contribution_view(&c), body@)),
        },
    }
}

pub(crate) open spec fn private_legacy_blocks_view(blocks: Seq<PrivateLegacyBlock<'_>>) -> Seq<crate::specs::PrivateLegacyBlockSpec> {
    Seq::new(blocks.len(), |i: int| private_legacy_block_view(&blocks[i]))
}

pub(crate) open spec fn private_legacy_block_same_config(
    a: crate::specs::PrivateLegacyBlockSpec,
    b: crate::specs::PrivateLegacyBlockSpec,
) -> bool {
    a.width == b.width
        && a.height == b.height
        && a.significant_bitplanes == b.significant_bitplanes
        && a.orientation == b.orientation
        && a.style == b.style
        && a.allow_multiple_ht_sets == b.allow_multiple_ht_sets
        && a.ht_magnitude_bound == b.ht_magnitude_bound
}

pub(crate) open spec fn private_legacy_blocks_extends(
    before: Seq<crate::specs::PrivateLegacyBlockSpec>,
    after: Seq<crate::specs::PrivateLegacyBlockSpec>,
) -> bool {
    before.len() == after.len()
        && forall|i: int| 0 <= i < before.len() ==> {
            private_legacy_block_same_config(#[trigger] before[i], after[i])
                && (before[i].contribution.is_some() ==> after[i].contribution == before[i].contribution)
        }
}

pub(crate) open spec fn private_legacy_blocks_valid(
    blocks: Seq<crate::specs::PrivateLegacyBlockSpec>,
    limits: &ResourceLimits,
) -> bool {
    forall|i: int| 0 <= i < blocks.len() ==> crate::specs::private_legacy_block_valid(
        #[trigger] blocks[i],
        crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits),
        crate::limits::resource_work_limit(limits),
    )
}

pub(crate) open spec fn private_legacy_blocks_all_segments_ok(
    blocks: Seq<crate::specs::PrivateLegacyBlockSpec>,
    limits: &ResourceLimits,
) -> bool {
    forall|i: int| 0 <= i < blocks.len() ==> crate::specs::private_legacy_block_segment_ok(
        #[trigger] blocks[i],
        crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits),
        crate::limits::resource_work_limit(limits),
    )
}

pub(crate) open spec fn private_legacy_precinct_logical(
    precinct: &PrivateLegacyPrecinct,
    blocks: Seq<crate::specs::PrivateLegacyBlockSpec>,
    limits: &ResourceLimits,
) -> crate::specs::Part1PacketPrecinctState {
    crate::specs::Part1PacketPrecinctState {
        component: precinct.component,
        resolution: precinct.resolution,
        precinct: precinct.precinct,
        states: precinct.states@.map_values(|s: CodeBlockPacketState| super::code_block_packet_state_view(&s)),
        contexts: precinct.contexts@,
        decoders: Seq::new(precinct.block_count as nat, |j: int| {
            crate::specs::private_legacy_block_logical(
                blocks[precinct.block_base as int + j],
                crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),
                crate::limits::resource_work_limit(limits),
            )
        }),
        subbands: precinct.subbands@.map_values(|s: PacketSubbandState| super::packet_subband_view(&s)),
    }
}

pub(crate) open spec fn private_legacy_precincts_logical(
    precincts: Seq<PrivateLegacyPrecinct>,
    blocks: Seq<crate::specs::PrivateLegacyBlockSpec>,
    limits: &ResourceLimits,
) -> Seq<crate::specs::Part1PacketPrecinctState> {
    Seq::new(precincts.len(), |i: int| private_legacy_precinct_logical(&precincts[i], blocks, limits))
}

pub(crate) open spec fn private_legacy_precinct_subband_empty(p: &PrivateLegacyPrecinct) -> bool {
    p.subbands.len() == 0
}

pub(crate) open spec fn private_legacy_precincts_layout_ok(
    precincts: Seq<PrivateLegacyPrecinct>,
    block_len: nat,
) -> bool {
    forall|i: int| 0 <= i < precincts.len() ==> {
        let p = #[trigger] precincts[i];
        p.states.len() == p.block_count
            && p.contexts.len() == p.block_count
            && (p.block_count == 0) == (p.subbands.len() == 0)
            && p.block_base as nat + p.block_count as nat <= block_len
            && forall|j: int| 0 <= j < precincts.len() && j != i ==> {
                let q = #[trigger] precincts[j];
                p.block_base as nat + p.block_count as nat <= q.block_base as nat
                    || q.block_base as nat + q.block_count as nat <= p.block_base as nat
            }
    }
}

}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        None => true,
        Some(block) => {
            let v = private_legacy_block_view(&block);
            v.width == width
                && v.height == height
                && v.significant_bitplanes == significant_bitplanes
                && v.orientation == orientation
                && v.style == style
                && v.allow_multiple_ht_sets == allow_multiple_ht_sets
                && v.ht_magnitude_bound == ht_magnitude_bound
                && v.contribution.is_none()
                && width > 0 && height > 0 && (width as nat) * (height as nat) <= 4096
                && significant_bitplanes > 0 && significant_bitplanes <= 31
                && crate::specs::private_legacy_style_ok(style)
                && crate::specs::part2_configured_checkpoint(
                    width, height, significant_bitplanes, orientation, style,
                    allow_multiple_ht_sets, ht_magnitude_bound, true,
                ) == Ok::<crate::specs::Tier1DecoderState, DecodeError>(crate::specs::private_legacy_block_initial(v))
        },
    },
))]
pub(crate) fn new_private_legacy_block<'data>(
    width: u16,
    height: u16,
    significant_bitplanes: u16,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
) -> Option<PrivateLegacyBlock<'data>> {
    let count = usize::from(width).checked_mul(usize::from(height))?;
    if count == 0
        || count > 4096
        || significant_bitplanes == 0
        || significant_bitplanes > 31
        || ht_magnitude_bound == 0
        || ht_magnitude_bound > 74
        || !matches!(style.block_coding, crate::tier1::Tier1BlockCoding::Legacy)
        || style.force_high_throughput
        || style.selective_arithmetic_coding_bypass
        || style.reset_contexts
        || style.terminate_all_passes
        || style.segmentation_symbols
        || style.predictable_termination
    {
        return None;
    }
    let block = PrivateLegacyBlock {
        width,
        height,
        significant_bitplanes,
        orientation,
        style,
        allow_multiple_ht_sets,
        ht_magnitude_bound,
        contribution: None,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(width > 0 && height > 0) by(nonlinear_arith)
            requires (width as nat) * (height as nat) > 0;
        crate::specs::private_legacy_block_initial_matches_configured(private_legacy_block_view(&block));
    }
    Some(block)
}

impl<'data> PrivateLegacyBlock<'data> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires crate::specs::private_legacy_block_valid(
            private_legacy_block_view(old(self)),
            crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits),
            crate::limits::resource_work_limit(limits),
        ),
        ensures result ==> {
            let before = private_legacy_block_view(old(self));
            let after = private_legacy_block_view(final(self));
            before.contribution.is_none()
                && private_legacy_block_same_config(before, after)
                && after.contribution == Some((super::code_block_contribution_view(&contribution), body@))
                && crate::specs::private_legacy_block_valid(
                    after,
                    crate::limits::resource_code_block_pass_limit(limits),
                    crate::limits::resource_code_block_byte_limit(limits),
                    crate::limits::resource_input_byte_limit(limits),
                    crate::limits::resource_work_limit(limits),
                )
        },
    ))]
    fn record_single_contribution(
        &mut self,
        contribution: CodeBlockContribution,
        body: &'data [u8],
        limits: &ResourceLimits,
    ) -> bool {
        let Ok(first_seg) = contribution.segment(0) else {
            return false;
        };
        if self.contribution.is_some()
            || contribution.high_throughput
            || !contribution.first_inclusion
            || contribution.new_passes == 0
            || contribution.segment_count() != 1
            || first_seg.passes != contribution.new_passes
            || first_seg.data_length != contribution.data_length
            || body.is_empty()
            || (body.len() as u64) != u64::from(contribution.data_length)
            || (body.len() as u64) > u64::from(u32::MAX)
        {
            return false;
        }
        if contribution.zero_bitplanes >= self.significant_bitplanes {
            return false;
        }
        let eff = self.significant_bitplanes - contribution.zero_bitplanes;
        let max_passes = 3 * u32::from(eff) - 2;
        let passes = u32::from(contribution.new_passes);
        if passes > max_passes || passes > limits.maximum_code_block_passes() {
            return false;
        }
        let body_len = body.len() as u64;
        if body_len > limits.maximum_code_block_bytes() || body_len > limits.maximum_input_bytes() {
            return false;
        }
        let count = u64::from(self.width) * u64::from(self.height);
        let Some(base_work) = count.checked_mul(u64::from(passes)) else {
            return false;
        };
        let Some(total_work) = base_work.checked_add(body_len) else {
            return false;
        };
        if total_work > limits.maximum_work_units() {
            return false;
        }
        self.contribution = Some((contribution, body));
        true
    }
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn private_legacy_subband_execution(
    spec: PrivateLegacySubbandSpec,
    decoders: Seq<crate::specs::Tier1DecoderState>,
) -> crate::specs::Part2PacketSubbandExecution {
    crate::specs::Part2PacketSubbandExecution {
        orientation: spec.orientation,
        across: spec.across,
        down: spec.down,
        maximum_zero: spec.significant_bitplanes,
        decoders,
    }
}

pub(crate) open spec fn private_legacy_specs_match_executions(
    specs: Seq<PrivateLegacySubbandSpec>,
    executions: Seq<crate::specs::Part2PacketSubbandExecution>,
    blocks: Seq<crate::specs::PrivateLegacyBlockSpec>,
    block_base: usize,
    limits: &ResourceLimits,
) -> bool {
    specs.len() == executions.len() && {
        let pass_limit = crate::limits::resource_code_block_pass_limit(limits);
        let byte_limit = crate::limits::resource_code_block_byte_limit(limits);
        let input_limit = crate::limits::resource_input_byte_limit(limits);
        let work_limit = crate::limits::resource_work_limit(limits);
        forall|i: int| 0 <= i < specs.len() ==> {
            let s = #[trigger] specs[i];
            let e = executions[i];
            e.orientation == s.orientation
                && e.across == s.across
                && e.down == s.down
                && e.maximum_zero == s.significant_bitplanes
                && e.decoders.len() == s.count
                && s.first_offset as nat + s.count as nat + block_base as nat <= blocks.len()
                && e.decoders == Seq::new(s.count as nat, |j: int| {
                    crate::specs::private_legacy_block_logical(
                        blocks[block_base as int + s.first_offset as int + j],
                        pass_limit, byte_limit, input_limit, work_limit,
                    )
                })
        }
    }
}

}

pub(crate) struct PrivateLegacySubbandSpec {
    pub(crate) orientation: SubbandOrientation,
    pub(crate) across: u32,
    pub(crate) down: u32,
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    pub(crate) first_offset: usize,
    pub(crate) count: usize,
    pub(crate) significant_bitplanes: u16,
}

pub(crate) struct PrivateLegacyPrecinct {
    pub(crate) component: u16,
    pub(crate) resolution: u8,
    pub(crate) precinct: u32,
    pub(crate) states: Vec<CodeBlockPacketState>,
    pub(crate) contexts: Vec<CodeBlockPacketContext>,
    pub(crate) subbands: Vec<PacketSubbandState>,
    pub(crate) block_base: usize,
    #[cfg_attr(not(verus_keep_ghost), allow(dead_code))]
    pub(crate) block_count: usize,
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        block_base + total_blocks <= ghost_blocks@.len(),
        private_legacy_specs_match_executions(specs@, ghost_executions@, ghost_blocks@, block_base, limits),
        forall|i: int| 0 <= i < specs.len() ==> specs@[i].first_offset == if i == 0 { 0usize } else { (specs@[i - 1].first_offset + specs@[i - 1].count) as usize },
        (specs.len() == 0 && total_blocks == 0)
            || (specs.len() > 0 && specs@[specs.len() - 1].first_offset + specs@[specs.len() - 1].count == total_blocks),
    ensures match result {
        None => true,
        Some(precinct_state) => {
            precinct_state.component == component
                && precinct_state.resolution == resolution
                && precinct_state.precinct == precinct
                && precinct_state.block_base == block_base
                && precinct_state.block_count == total_blocks
                && precinct_state.states.len() == precinct_state.block_count
                && precinct_state.contexts.len() == precinct_state.block_count
                && (precinct_state.block_count == 0) == private_legacy_precinct_subband_empty(&precinct_state)
                && crate::specs::part2_precinct_from_executions(
                    component, resolution, precinct, style, ghost_executions@, limits,
                ) == Ok::<crate::specs::Part1PacketPrecinctState, DecodeError>(
                    private_legacy_precinct_logical(&precinct_state, ghost_blocks@, limits),
                )
        },
    },
))]
#[allow(clippy::too_many_arguments)]
pub(crate) fn new_private_legacy_precinct(
    component: u16,
    resolution: u8,
    precinct: u32,
    style: Tier1CodingStyle,
    specs: &[PrivateLegacySubbandSpec],
    block_base: usize,
    total_blocks: usize,
    limits: &ResourceLimits,
    #[cfg(verus_keep_ghost)] ghost_executions: Ghost<
        Seq<crate::specs::Part2PacketSubbandExecution>,
    >,
    #[cfg(verus_keep_ghost)] ghost_blocks: Ghost<Seq<crate::specs::PrivateLegacyBlockSpec>>,
) -> Option<PrivateLegacyPrecinct> {
    if specs.len() > 3 {
        return None;
    }
    let Ok(mut subbands) = crate::allocation::empty_with_capacity(specs.len()) else {
        return None;
    };
    let mut states: Vec<CodeBlockPacketState> = Vec::new();
    let mut contexts: Vec<CodeBlockPacketContext> = Vec::new();
    let mut total = 0_u64;
    let mut decoded_total = 0_usize;
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_precinct_initialization_run);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= specs.len(),
            specs.len() <= 3,
            subbands.len() == index,
            states.len() == decoded_total,
            contexts.len() == decoded_total,
            total == decoded_total as u64,
            decoded_total <= total_blocks,
            block_base + total_blocks <= ghost_blocks@.len(),
            (decoded_total == 0) == (index == 0),
            index < specs.len() ==> specs@[index as int].first_offset == decoded_total,
            index == specs.len() ==> decoded_total == total_blocks,
            ({
                let cur_state = crate::specs::Part1PacketPrecinctState {
                    component,
                    resolution,
                    precinct,
                    states: states@.map_values(|s: CodeBlockPacketState| super::code_block_packet_state_view(&s)),
                    contexts: contexts@,
                    decoders: Seq::new(decoded_total as nat, |j: int| {
                        crate::specs::private_legacy_block_logical(
                            ghost_blocks@[block_base as int + j],
                            crate::limits::resource_code_block_pass_limit(limits),
                            crate::limits::resource_code_block_byte_limit(limits),
                            crate::limits::resource_input_byte_limit(limits),
                            crate::limits::resource_work_limit(limits),
                        )
                    }),
                    subbands: subbands@.map_values(|s: PacketSubbandState| super::packet_subband_view(&s)),
                };
                crate::specs::part2_precinct_from_executions(component, resolution, precinct, style, ghost_executions@, limits)
                    == crate::specs::part2_precinct_initialization_run(ghost_executions@, style, limits, index as nat, cur_state, total)
            }),
        decreases specs.len() - index,
    ))]
    while index < specs.len() {
        let s = &specs[index];
        if s.across == 0
            || s.down == 0
            || s.count == 0
            || s.significant_bitplanes == 0
            || s.significant_bitplanes > crate::tier1::MAX_TIER1_BITPLANES
        {
            return None;
        }
        let count_u64 = u64::from(s.across).checked_mul(u64::from(s.down))?;
        let next_total = total.checked_add(count_u64)?;
        if next_total > limits.maximum_code_blocks() || next_total > limits.maximum_work_units() {
            return None;
        }
        let count_usize = usize::try_from(count_u64).ok()?;
        if count_usize != s.count {
            return None;
        }
        let next_decoded = decoded_total.checked_add(count_usize)?;
        let Ok((next_states, next_contexts)) = prepare_precinct_contexts(
            states,
            contexts,
            count_usize,
            s.across,
            s.significant_bitplanes,
            style,
        ) else {
            return None;
        };
        let Ok(inclusion_tree) = tag_tree_new(s.across, s.down, limits) else {
            return None;
        };
        let Ok(zero_bitplane_tree) = tag_tree_new(s.across, s.down, limits) else {
            return None;
        };
        let first_decoder = decoded_total;
        subbands.push(PacketSubbandState {
            orientation: s.orientation,
            code_blocks_across: s.across,
            code_blocks_down: s.down,
            first_decoder,
            decoder_count: count_usize,
            inclusion_tree,
            zero_bitplane_tree,
        });
        states = next_states;
        contexts = next_contexts;
        total = next_total;
        decoded_total = next_decoded;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_precinct_initialization_run);
            let pass_limit = crate::limits::resource_code_block_pass_limit(limits);
            let byte_limit = crate::limits::resource_code_block_byte_limit(limits);
            let input_limit = crate::limits::resource_input_byte_limit(limits);
            let work_limit = crate::limits::resource_work_limit(limits);
            let d_prev = Seq::new(first_decoder as nat, |j: int|
                crate::specs::private_legacy_block_logical(ghost_blocks@[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
            let d_next = Seq::new(decoded_total as nat, |j: int|
                crate::specs::private_legacy_block_logical(ghost_blocks@[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
            assert(d_prev + ghost_executions@[index as int].decoders =~= d_next);
        }
        index += 1;
    }
    if decoded_total != total_blocks {
        return None;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_precinct_initialization_run);
    }
    Some(PrivateLegacyPrecinct {
        component,
        resolution,
        precinct,
        states,
        contexts,
        subbands,
        block_base,
        block_count: total_blocks,
    })
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        block_base + contributions.len() <= old(blocks).len(),
        private_legacy_blocks_valid(private_legacy_blocks_view(old(blocks)@), limits),
    ensures
        final(blocks).len() == old(blocks).len(),
        forall|k: int| 0 <= k < old(blocks).len()
            && !(block_base as int <= k && k < block_base as int + contributions.len() as int)
            ==> final(blocks)@[k] == old(blocks)@[k],
        match result {
            None => true,
            Some((end_offset, segments, passes)) => {
                let b0 = private_legacy_blocks_view(old(blocks)@);
                let b1 = private_legacy_blocks_view(final(blocks)@);
                private_legacy_blocks_extends(b0, b1)
                    && private_legacy_blocks_valid(b1, limits)
                    && forall|end_blocks: Seq<crate::specs::PrivateLegacyBlockSpec>|
                        private_legacy_blocks_extends(b1, end_blocks)
                            && private_legacy_blocks_all_segments_ok(end_blocks, limits) ==> {
                        let pass_limit = crate::limits::resource_code_block_pass_limit(limits);
                        let byte_limit = crate::limits::resource_code_block_byte_limit(limits);
                        let input_limit = crate::limits::resource_input_byte_limit(limits);
                        let work_limit = crate::limits::resource_work_limit(limits);
                        let d0 = Seq::new(contributions.len() as nat, |j: int|
                            crate::specs::private_legacy_block_logical(b0[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
                        let d1 = Seq::new(contributions.len() as nat, |j: int|
                            crate::specs::private_legacy_block_logical(b1[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
                        let c_view = contributions@.map_values(|c: Option<CodeBlockContribution>| match c {
                            None => None,
                            Some(v) => Some(super::code_block_contribution_view(&v)),
                        });
                        crate::specs::part1_packet_body_execute(
                            crate::specs::Part1PacketBodyExecution {
                                decoders: d0,
                                index: 0,
                                offset: body_start,
                                segments: 0,
                                passes: 0,
                            },
                            c_view,
                            data@,
                            error_offset,
                            true,
                            pass_limit,
                            byte_limit,
                            input_limit,
                            work_limit,
                        ) == (
                            Ok::<(), DecodeError>(()),
                            crate::specs::Part1PacketBodyExecution {
                                decoders: d1,
                                index: contributions.len(),
                                offset: end_offset,
                                segments,
                                passes,
                            },
                        )
                    }
            },
        },
))]
fn execute_private_legacy_body_contributions<'data>(
    blocks: &mut [PrivateLegacyBlock<'data>],
    block_base: usize,
    contributions: &[Option<CodeBlockContribution>],
    data: &'data [u8],
    body_start: usize,
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] error_offset: usize,
    limits: &ResourceLimits,
) -> Option<(usize, u32, u32)> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost pass_limit = crate::limits::resource_code_block_pass_limit(limits);
        let ghost byte_limit = crate::limits::resource_code_block_byte_limit(limits);
        let ghost input_limit = crate::limits::resource_input_byte_limit(limits);
        let ghost work_limit = crate::limits::resource_work_limit(limits);
        let ghost b_init = private_legacy_blocks_view(blocks@);
        let ghost c_view = contributions@.map_values(|c: Option<CodeBlockContribution>| match c {
            None => None,
            Some(v) => Some(super::code_block_contribution_view(&v)),
        });
        let ghost d_init = Seq::new(contributions.len() as nat, |j: int|
            crate::specs::private_legacy_block_logical(b_init[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
    }
    let n_slots = contributions.len();
    let mut ci = 0_usize;
    let mut offset = body_start;
    let mut segments = 0_u32;
    let mut passes = 0_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant ci <= n_slots,
            n_slots == contributions.len(),
            blocks.len() == old(blocks).len(),
            block_base + n_slots <= blocks.len(),
            forall|k: int| 0 <= k < blocks.len()
                && !(block_base as int <= k && k < block_base as int + n_slots as int)
                ==> blocks@[k] == old(blocks)@[k],
            private_legacy_blocks_extends(b_init, private_legacy_blocks_view(blocks@)),
            private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
            forall|end_blocks: Seq<crate::specs::PrivateLegacyBlockSpec>|
                private_legacy_blocks_extends(private_legacy_blocks_view(blocks@), end_blocks)
                    && private_legacy_blocks_all_segments_ok(end_blocks, limits) ==> {
                let d_cur = Seq::new(n_slots as nat, |j: int|
                    crate::specs::private_legacy_block_logical(private_legacy_blocks_view(blocks@)[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
                crate::specs::part1_packet_body_execute_at(
                    crate::specs::Part1PacketBodyExecution { decoders: d_init, index: 0, offset: body_start, segments: 0, passes: 0 },
                    c_view, data@, error_offset, 0, true, pass_limit, byte_limit, input_limit, work_limit,
                ) == crate::specs::part1_packet_body_execute_at(
                    crate::specs::Part1PacketBodyExecution { decoders: d_cur, index: ci, offset, segments, passes },
                    c_view, data@, error_offset, 0, true, pass_limit, byte_limit, input_limit, work_limit,
                )
            },
        decreases n_slots - ci,
    ))]
    while ci < n_slots {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost b_before = private_legacy_blocks_view(blocks@);
            let ghost offset_before = offset;
            let ghost seg_before = segments;
            let ghost pass_before = passes;
        }
        if let Some(contrib) = contributions[ci] {
            let len = usize::try_from(contrib.data_length).ok()?;
            let body_end = offset.checked_add(len)?;
            let body = data.get(offset..body_end)?;
            let block_idx = block_base + ci;
            if !blocks[block_idx].record_single_contribution(contrib, body, limits) {
                return None;
            }
            segments = segments.checked_add(1)?;
            passes = passes.checked_add(u32::from(contrib.new_passes))?;
            offset = body_end;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_packet_body_execute_at);
            let b_after = private_legacy_blocks_view(blocks@);
            assert(private_legacy_blocks_extends(b_before, b_after));
            assert(private_legacy_blocks_extends(b_init, b_after));
            assert forall|end_blocks: Seq<crate::specs::PrivateLegacyBlockSpec>|
                private_legacy_blocks_extends(b_after, end_blocks)
                    && private_legacy_blocks_all_segments_ok(end_blocks, limits) implies {
                let d_after = Seq::new(n_slots as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_after[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
                crate::specs::part1_packet_body_execute_at(
                    crate::specs::Part1PacketBodyExecution { decoders: d_init, index: 0, offset: body_start, segments: 0, passes: 0 },
                    c_view, data@, error_offset, 0, true, pass_limit, byte_limit, input_limit, work_limit,
                ) == crate::specs::part1_packet_body_execute_at(
                    crate::specs::Part1PacketBodyExecution { decoders: d_after, index: (ci + 1) as usize, offset, segments, passes },
                    c_view, data@, error_offset, 0, true, pass_limit, byte_limit, input_limit, work_limit,
                )
            } by {
                assert(private_legacy_blocks_extends(b_before, end_blocks));
                let d_before = Seq::new(n_slots as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_before[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
                let d_after = Seq::new(n_slots as nat, |j: int|
                    crate::specs::private_legacy_block_logical(b_after[block_base as int + j], pass_limit, byte_limit, input_limit, work_limit));
                if let Some(contrib) = contributions@[ci as int] {
                    let b_idx = block_base as int + ci as int;
                    assert(end_blocks[b_idx].contribution == b_after[b_idx].contribution);
                    assert(crate::specs::private_legacy_block_segment_ok(b_after[b_idx], pass_limit, byte_limit, input_limit, work_limit));
                    crate::specs::private_legacy_block_single_contribution(b_after[b_idx], pass_limit, byte_limit, input_limit, work_limit);
                    let tx = crate::specs::part1_legacy_code_block_transaction(
                        crate::specs::private_legacy_block_initial(b_after[b_idx]),
                        super::code_block_contribution_view(&contrib),
                        data@.subrange(offset_before as int, offset as int),
                        pass_limit, byte_limit, input_limit, work_limit,
                    );
                    assert(d_after =~= d_before.update(ci as int, tx.1));
                } else {
                    assert(d_after =~= d_before);
                }
            }
        }
        ci += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_packet_body_execute_at);
    }
    Some((offset, segments, passes))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        old(precinct).states.len() == old(precinct).block_count,
        old(precinct).contexts.len() == old(precinct).block_count,
        (old(precinct).block_count == 0) == (old(precinct).subbands.len() == 0),
        old(precinct).block_base + old(precinct).block_count <= old(blocks).len(),
        private_legacy_blocks_valid(private_legacy_blocks_view(old(blocks)@), limits),
    ensures
        final(precinct).component == old(precinct).component,
        final(precinct).resolution == old(precinct).resolution,
        final(precinct).precinct == old(precinct).precinct,
        final(precinct).block_base == old(precinct).block_base,
        final(precinct).block_count == old(precinct).block_count,
        final(precinct).states.len() == final(precinct).block_count,
        final(precinct).contexts.len() == final(precinct).block_count,
        (final(precinct).block_count == 0) == (final(precinct).subbands.len() == 0),
        final(blocks).len() == old(blocks).len(),
        forall|k: int| 0 <= k < old(blocks).len()
            && !(old(precinct).block_base as int <= k && k < old(precinct).block_base as int + old(precinct).block_count as int)
            ==> final(blocks)@[k] == old(blocks)@[k],
        match result {
            None => true,
            Some((decoded, tile_bytes, packed_bytes)) => {
                let b0 = private_legacy_blocks_view(old(blocks)@);
                let b1 = private_legacy_blocks_view(final(blocks)@);
                private_legacy_blocks_extends(b0, b1)
                    && private_legacy_blocks_valid(b1, limits)
                    && forall|end_blocks: Seq<crate::specs::PrivateLegacyBlockSpec>|
                        private_legacy_blocks_extends(b1, end_blocks)
                            && private_legacy_blocks_all_segments_ok(end_blocks, limits) ==> {
                        crate::specs::part1_precinct_packet_owned(
                            private_legacy_precinct_logical(old(precinct), b0, limits),
                            crate::codestream::tile_part_owned_view(part),
                            offset,
                            packed@,
                            packed_offset,
                            expected,
                            sequence,
                            true,
                            crate::limits::resource_code_block_limit(limits),
                            crate::limits::resource_packet_header_byte_limit(limits),
                            crate::limits::resource_code_block_pass_limit(limits),
                            crate::limits::resource_code_block_byte_limit(limits),
                            crate::limits::resource_input_byte_limit(limits),
                            crate::limits::resource_work_limit(limits),
                        ) == (
                            Ok::<(PacketBodyDecode, usize, usize), DecodeError>((decoded, tile_bytes, packed_bytes)),
                            private_legacy_precinct_logical(final(precinct), b1, limits),
                        )
                    }
            },
        },
))]
#[allow(clippy::too_many_arguments)]
fn decode_private_legacy_precinct_packet<'data>(
    precinct: &mut PrivateLegacyPrecinct,
    blocks: &mut [PrivateLegacyBlock<'data>],
    contributions_buf: &mut Vec<Option<CodeBlockContribution>>,
    part: &TilePartPayload<'data>,
    offset: usize,
    packed: &[u8],
    packed_offset: usize,
    expected: Option<u32>,
    sequence: u16,
    limits: &ResourceLimits,
) -> Option<(PacketBodyDecode, usize, usize)> {
    let n_slots = precinct.states.len();
    let code_blocks = n_slots as u64;
    if code_blocks > limits.maximum_code_blocks() || code_blocks > limits.maximum_work_units() {
        return None;
    }
    let data = part.data.get(offset..)?;
    let component_style = part
        .component_coding_styles
        .style(precinct.component)
        .ok()?;
    let style = component_style.tier1_coding_style().ok()?;
    let parameters = PrecinctPayloadParameters {
        error_offset: offset,
        packed_offset,
        expected_packet_length: expected,
        expected_sop_sequence: sequence,
        style,
        sop: part.coding_style.sop_markers,
        eph: part.coding_style.eph_markers,
        packed: part.packed_packet_headers.is_present(),
        decode_tier1: true,
    };
    let prefix = decode_precinct_packet_payload_prefix(data, packed, parameters, limits).ok()?;
    let mut reader = prefix.reader;
    let packet_data = prefix.packet_data;
    let packet_present = prefix.present;
    let sop_bytes = prefix.sop_bytes;
    contributions_buf.clear();
    if crate::allocation::reserve_additional(contributions_buf, n_slots).is_err() {
        return None;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant contributions_buf.len() <= n_slots,
            contributions_buf@ == Seq::new(contributions_buf.len() as nat, |_: int| None::<CodeBlockContribution>),
        decreases n_slots - contributions_buf.len(),
    ))]
    while contributions_buf.len() < n_slots {
        contributions_buf.push(None);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(contributions_buf@ =~= Seq::new(contributions_buf.len() as nat, |_: int| None::<CodeBlockContribution>));
        }
    }
    let mut contribution_count = 0_u32;
    if packet_present && !precinct.contexts.is_empty() {
        let layer = precinct.contexts[0].layer;
        let mut progress = PrecinctHeaderProgress {
            subband_index: 0,
            local_index: 0,
            contribution_count: 0,
        };
        if decode_precinct_contribution_headers(
            &mut precinct.states,
            &precinct.contexts,
            &mut precinct.subbands,
            contributions_buf,
            &mut reader,
            PrecinctHeaderParameters { layer, style },
            &mut progress,
        )
        .is_err()
        {
            return None;
        }
        contribution_count = progress.contribution_count;
    }
    if reader.finish_packet_header().is_err() {
        return None;
    }
    let header_bytes = reader.bytes_consumed();
    let mut tile_offset = sop_bytes;
    let mut packed_bytes_consumed = 0_usize;
    if parameters.packed {
        packed_bytes_consumed = header_bytes;
    } else {
        tile_offset = tile_offset.checked_add(header_bytes)?;
    }
    if parameters.eph {
        let marker_end = header_bytes.checked_add(2)?;
        let marker = packet_data.get(header_bytes..marker_end)?;
        if !crate::refinement::eph_valid(marker[0], marker[1]) {
            return None;
        }
        if parameters.packed {
            packed_bytes_consumed = marker_end;
        } else {
            tile_offset = tile_offset.checked_add(2)?;
        }
    }
    let body_start = tile_offset;
    let mut preflight = PacketBodyPreflight {
        index: 0,
        end: tile_offset,
    };
    if preflight_packet_body_ranges(contributions_buf, data, &mut preflight, (offset, 0)).is_err() {
        return None;
    }
    tile_offset = preflight.end;
    let (_, segments, passes) = execute_private_legacy_body_contributions(
        blocks,
        precinct.block_base,
        contributions_buf,
        data,
        body_start,
        offset,
        limits,
    )?;
    let body_bytes = tile_offset.checked_sub(body_start)?;
    if tile_offset > usize::MAX - packed_bytes_consumed {
        return None;
    }
    let logical_bytes = crate::refinement::packet_logical_bytes(tile_offset, packed_bytes_consumed);
    if let Some(expected_len) = expected {
        let expected_usize = usize::try_from(expected_len).ok()?;
        if !crate::refinement::packet_length_matches(logical_bytes, expected_usize) {
            return None;
        }
    }
    let decoded = PacketBodyDecode {
        present: packet_present,
        code_blocks: u32::try_from(code_blocks).ok()?,
        contributions: contribution_count,
        segments,
        passes,
        header_bytes: u32::try_from(header_bytes).ok()?,
        body_bytes: u32::try_from(body_bytes).ok()?,
        bytes_consumed: u32::try_from(logical_bytes).ok()?,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_precinct_payload_headers);
        reveal(crate::specs::part1_precinct_payload_after_headers);
        reveal(crate::specs::part1_precinct_payload_body);
    }
    Some((decoded, tile_offset, packed_bytes_consumed))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        private_legacy_precincts_layout_ok(old(precincts)@, old(blocks).len() as nat),
        private_legacy_blocks_valid(private_legacy_blocks_view(old(blocks)@), limits),
    ensures
        final(precincts).len() == old(precincts).len(),
        final(blocks).len() == old(blocks).len(),
        forall|i: int| 0 <= i < old(precincts).len() ==> {
            final(precincts)@[i].block_base == old(precincts)@[i].block_base
                && final(precincts)@[i].block_count == old(precincts)@[i].block_count
        },
        result ==> {
            let b0 = private_legacy_blocks_view(old(blocks)@);
            let b1 = private_legacy_blocks_view(final(blocks)@);
            private_legacy_blocks_extends(b0, b1)
                && private_legacy_blocks_valid(b1, limits)
                && (private_legacy_blocks_all_segments_ok(b1, limits) ==> {
                    let res = crate::specs::part1_progression_tile_decode_owned(
                        crate::codestream::tile_parts_owned_view(tile_parts@),
                        super::packet_grid_view(grid),
                        private_legacy_precincts_logical(old(precincts)@, b0, limits),
                        None,
                        limits,
                    );
                    res.0.is_ok()
                        && res.1 == private_legacy_precincts_logical(final(precincts)@, b1, limits)
                })
        },
))]
pub(crate) fn collect_private_legacy_packets<'data>(
    tile_parts: &[TilePartPayload<'data>],
    grid: &PacketGrid,
    precincts: &mut [PrivateLegacyPrecinct],
    blocks: &mut [PrivateLegacyBlock<'data>],
    limits: &ResourceLimits,
) -> bool {
    if validate_progression_layout(tile_parts, grid, None, limits).is_err() {
        return false;
    }
    let Ok(total_precincts_u64) = grid.total_precinct_count() else {
        return false;
    };
    let Ok(total_precincts) = usize::try_from(total_precincts_u64) else {
        return false;
    };
    if precincts.len() != total_precincts {
        return false;
    }
    let mut idx = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant idx <= precincts.len(),
            forall|k: int| 0 <= k < idx ==> crate::specs::part1_packet_grid_precinct_index(
                super::packet_grid_view(grid),
                precincts@[k].component,
                precincts@[k].resolution,
                precincts@[k].precinct,
            ) == Ok::<usize, DecodeError>(k as usize),
        decreases precincts.len() - idx,
    ))]
    while idx < precincts.len() {
        let p = &precincts[idx];
        match grid.precinct_index(p.component, p.resolution, p.precinct) {
            Ok(expected) if expected == idx => {}
            _ => return false,
        }
        idx += 1;
    }
    let Some(first) = tile_parts.first() else {
        return false;
    };
    let Ok(input) = prepare_progression_payloads(tile_parts, first.tile_index, limits) else {
        return false;
    };
    let params = ProgressionTileParameters {
        tile_parts,
        grid,
        input: &input,
        selection: None,
        limits,
    };
    let Ok(mut p) = progression_tile_progress_new(&params) else {
        return false;
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost p_view_init = super::progression_tile_progress_view(&p);
        let ghost params_view = super::progression_tile_parameters_view(&params);
        let ghost b_init = private_legacy_blocks_view(blocks@);
        let ghost prec_init = private_legacy_precincts_logical(precincts@, b_init, limits);
    }
    let mut contributions_buf: Vec<Option<CodeBlockContribution>> = Vec::new();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_tile_run);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            precincts.len() == old(precincts).len(),
            blocks.len() == old(blocks).len(),
            forall|i: int| 0 <= i < precincts.len() ==> {
                precincts@[i].block_base == old(precincts)@[i].block_base
                    && precincts@[i].block_count == old(precincts)@[i].block_count
            },
            private_legacy_precincts_layout_ok(precincts@, blocks.len() as nat),
            private_legacy_blocks_extends(b_init, private_legacy_blocks_view(blocks@)),
            private_legacy_blocks_valid(private_legacy_blocks_view(blocks@), limits),
            forall|end_blocks: Seq<crate::specs::PrivateLegacyBlockSpec>|
                private_legacy_blocks_extends(private_legacy_blocks_view(blocks@), end_blocks)
                    && private_legacy_blocks_all_segments_ok(end_blocks, limits) ==> {
                let exec_init = crate::specs::Part1TilePacketExecution { progress: p_view_init, precincts: prec_init };
                let exec_cur = crate::specs::Part1TilePacketExecution {
                    progress: super::progression_tile_progress_view(&p),
                    precincts: private_legacy_precincts_logical(precincts@, private_legacy_blocks_view(blocks@), limits),
                };
                crate::specs::part1_tile_run(params_view, exec_init)
                    == crate::specs::part1_tile_run(params_view, exec_cur)
            },
        decreases p.remaining_packets,
    ))]
    loop {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        if crate::deadline::checkpoint().is_err() {
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost b_before = private_legacy_blocks_view(blocks@);
            let ghost prec_before = private_legacy_precincts_logical(precincts@, b_before, limits);
            let ghost prog_before = super::progression_tile_progress_view(&p);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_run);
        }
        if advance_progression_tile_part(&params, &mut p).is_err() {
            return false;
        }
        if p.current_tile_part == params.tile_parts.len()
            && p.packets == params.grid.packet_count
            && all_progression_packets_seen(&p.seen)
        {
            break;
        }
        let Ok(next_coord) = p.iterator.next_packet() else {
            return false;
        };
        let Some(coordinate) = next_coord else {
            break;
        };
        if p.remaining_packets == 0 {
            return false;
        }
        p.remaining_packets -= 1;
        if p.current_tile_part == params.tile_parts.len() {
            if omit_progression_packet(&params, &mut p, coordinate, precincts.len()).is_err() {
                return false;
            }
            continue;
        }
        let Some(part) = params.tile_parts.get(p.current_tile_part) else {
            return false;
        };
        let slot = progression_packet_slot(params.grid, coordinate);
        if let Ok((_, seen_index)) = slot {
            #[allow(
                clippy::collapsible_if,
                reason = "Avoid let-chains for MSRV 1.88 and Verus compatibility."
            )]
            if let Some(seen) = p.seen.get(seen_index) {
                if !crate::refinement::progression_emit_allowed(*seen) {
                    continue;
                }
            }
        }
        if p.length_tile_part != p.current_tile_part {
            p.length_iterator = part.packet_lengths.iter();
            p.length_tile_part = p.current_tile_part;
        }
        let expected = if part.packet_lengths.is_present() {
            match p.length_iterator.next_length() {
                Ok(Some(len)) => Some(len),
                _ => return false,
            }
        } else {
            None
        };
        let Ok((precinct_index, seen_index)) = slot else {
            return false;
        };
        let Some(seen) = p.seen.get(seen_index) else {
            return false;
        };
        if !crate::refinement::progression_emit_allowed(*seen) {
            continue;
        }
        if precinct_index >= precincts.len() {
            return false;
        }
        let Some(packed) = params.input.packed.get(p.current_tile_part) else {
            return false;
        };
        let sequence = (p.packets & u64::from(u16::MAX)) as u16;
        let offset = p.offset;
        let packed_offset = p.packed_offset;
        let packet_res = {
            let precinct = &mut precincts[precinct_index];
            if set_progression_context_layer(&mut precinct.contexts, coordinate.layer).is_err() {
                return false;
            }
            decode_private_legacy_precinct_packet(
                precinct,
                blocks,
                &mut contributions_buf,
                part,
                offset,
                packed,
                packed_offset,
                expected,
                sequence,
                limits,
            )
        };
        let Some((decoded, tile_bytes, packed_bytes)) = packet_res else {
            return false;
        };
        if account_progression_packet(
            &mut p,
            decoded,
            tile_bytes,
            packed_bytes,
            expected,
            seen_index,
        )
        .is_err()
        {
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let b_after = private_legacy_blocks_view(blocks@);
            let prec_after = private_legacy_precincts_logical(precincts@, b_after, limits);
            assert(private_legacy_blocks_extends(b_init, b_after));
            assert forall|i: int| 0 <= i < precincts.len() && i != precinct_index as int implies
                prec_after[i] == prec_before[i] by {
                let q = precincts@[i];
                assert forall|j: int| 0 <= j < q.block_count implies
                    b_after[q.block_base as int + j] == b_before[q.block_base as int + j] by {}
                assert(prec_after[i].decoders =~= prec_before[i].decoders);
            }
            assert(prec_after =~= prec_before.update(precinct_index as int, prec_after[precinct_index as int]));
        }
    }
    if finish_progression_tile_packets(&params, &mut p).is_err() {
        return false;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let b_final = private_legacy_blocks_view(blocks@);
        assert(private_legacy_blocks_extends(b_final, b_final));
    }
    true
}
