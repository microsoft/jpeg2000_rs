use super::bit_reader::packet_reader_prefix;
use super::body::{execute_packet_body_contributions, preflight_packet_body_ranges};
use super::contributions::{
    code_block_packet_state_new, decode_code_block_contribution, tier1_styles_equal,
};
use super::errors::{
    invalid_packet_header, packet_arithmetic_overflow, packet_reader_error, packet_reader_limit,
};
use super::tag_tree::tag_tree_new;
use super::tile::set_progression_context_layer;
use super::{
    CodeBlockContribution, CodeBlockPacketContext, CodeBlockPacketState, DecodeError,
    MalformedKind, PacketBitReader, PacketBodyDecode, PacketBodyExecutionProgress,
    PacketBodyPreflight, PacketPrecinctDecoder, PacketPrecinctGeometry, PacketSubbandExecution,
    PacketSubbandState, PrecinctHeaderParameters, PrecinctHeaderProgress, PrecinctPayloadHeader,
    PrecinctPayloadParameters, PrecinctPayloadReader, Resource, ResourceLimits, SubbandOrientation,
    Tier1CodeBlockDecoder, Tier1CodingStyle, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_contribution_option_view, code_block_header_outcome, code_block_packet_state_view,
    packet_bit_reader_view, packet_body_contributions_view, packet_decoder_outcome,
    packet_execution_view, packet_executions_view, packet_precinct_decoders,
    packet_precinct_outcome, packet_precinct_view, packet_states_view, packet_subband_view,
    precinct_contexts_outcome, precinct_header_view, precinct_initialization_view,
    precinct_payload_header_view, precinct_payload_parameters_view,
    precinct_payload_reader_outcome, precinct_payload_reader_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,packet_precinct_view(final(precinct)))==crate::specs::part1_jpip_precinct_packet(
        packet_precinct_view(old(precinct)),template,data@,expected_sop_sequence,layer,limits),
        result.is_err() ==> packet_precinct_view(final(precinct))==packet_precinct_view(old(precinct)),
))]
pub(crate) fn decode_jpip_precinct_packet(
    template: &TilePartPayload<'_>,
    data: &[u8],
    expected_sop_sequence: u16,
    layer: u16,
    precinct: &mut PacketPrecinctDecoder,
    limits: &ResourceLimits,
) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial=packet_precinct_view(precinct);}
    let states = precinct.states.clone();
    let contexts = precinct.contexts.clone();
    let subbands = precinct.subbands.clone();
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(states@.map_values(|state:CodeBlockPacketState|code_block_packet_state_view(&state))==initial.states);
        assert(contexts@==initial.contexts);
        assert(subbands@.map_values(|subband:PacketSubbandState|packet_subband_view(&subband))==initial.subbands);
    }
    let result = decode_jpip_precinct_packet_inner(
        template,
        data,
        expected_sop_sequence,
        layer,
        precinct,
        limits,
    );
    if result.is_err() {
        precinct.states = states;
        precinct.contexts = contexts;
        precinct.subbands = subbands;
    }
    result
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures (result,packet_precinct_view(final(precinct)))==crate::specs::part1_jpip_precinct_packet_inner(
        packet_precinct_view(old(precinct)),template,data@,expected_sop_sequence,layer,limits),
        final(precinct).decoders@==old(precinct).decoders@,
        (final(precinct).component,final(precinct).resolution,final(precinct).precinct)
            ==(old(precinct).component,old(precinct).resolution,old(precinct).precinct),
))]
pub(super) fn decode_jpip_precinct_packet_inner(
    template: &TilePartPayload<'_>,
    data: &[u8],
    expected_sop_sequence: u16,
    layer: u16,
    precinct: &mut PacketPrecinctDecoder,
    limits: &ResourceLimits,
) -> Result<usize, DecodeError> {
    set_progression_context_layer(&mut precinct.contexts, layer)?;
    let inline = TilePartPayload {
        tile_index: template.tile_index,
        tile_part_index: 0,
        tile_part_count: 1,
        coding_style: template.coding_style,
        quantization: template.quantization,
        component_coding_styles: template.component_coding_styles,
        component_quantizations: template.component_quantizations.clone(),
        roi_shifts: template.roi_shifts,
        progression_changes: template.progression_changes.clone(),
        multiple_component_transform: template.multiple_component_transform.clone(),
        part2_extensions: template.part2_extensions.clone(),
        packet_lengths: crate::codestream::packet_lengths_none(),
        packed_packet_headers: crate::codestream::packed_packet_headers_none(),
        has_functional_header_marker: template.has_functional_header_marker,
        has_roi_marker: template.has_roi_marker,
        data,
    };
    let (decoded, consumed, packed) = decode_precinct_packet(
        &inline,
        0,
        &[],
        0,
        None,
        expected_sop_sequence,
        precinct,
        false,
        limits,
    )?;
    if packed != 0 {
        return Err(packet_reader_error(0, MalformedKind::InvalidPacketLength));
    }
    let logical = match usize::try_from(decoded.bytes_consumed) {
        Ok(logical) => logical,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    if consumed != logical {
        return Err(packet_reader_error(0, MalformedKind::InvalidPacketLength));
    }
    Ok(consumed)
}

impl Clone for PacketSubbandState {
    #[cfg_attr(verus_keep_ghost,verus_spec(result =>
        ensures packet_subband_view(&result)==packet_subband_view(self),
    ))]
    fn clone(&self) -> Self {
        Self {
            orientation: self.orientation,
            first_decoder: self.first_decoder,
            decoder_count: self.decoder_count,
            code_blocks_across: self.code_blocks_across,
            code_blocks_down: self.code_blocks_down,
            inclusion_tree: self.inclusion_tree.clone(),
            zero_bitplane_tree: self.zero_bitplane_tree.clone(),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures precinct_contexts_outcome(result) == crate::specs::part2_precinct_contexts(
        packet_states_view(before_states@),
        before_contexts@, count, across, maximum_zero, tier1_style,
    ),
))]
pub(crate) fn prepare_precinct_contexts(
    before_states: Vec<CodeBlockPacketState>,
    before_contexts: Vec<CodeBlockPacketContext>,
    count: usize,
    across: u32,
    maximum_zero: u16,
    tier1_style: Tier1CodingStyle,
) -> Result<(Vec<CodeBlockPacketState>, Vec<CodeBlockPacketContext>), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_states = before_states@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state));
        let ghost initial_contexts = before_contexts@;
    }
    let mut states = before_states;
    let mut contexts = before_contexts;
    let mut local_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            local_index <= count,
            local_index as nat <= u32::MAX as nat + 1,
            local_index == 0 || across != 0,
            states@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state))
                == initial_states + Seq::new(local_index as nat, |index: int| crate::specs::part1_code_block_packet_initial()),
            contexts@ == initial_contexts + Seq::new(local_index as nat, |index: int| CodeBlockPacketContext {
                leaf_x: if across == 0 { 0u32 } else { (index % across as int) as u32 },
                leaf_y: if across == 0 { 0u32 } else { (index / across as int) as u32 },
                layer: 0, maximum_zero_bitplanes: maximum_zero, tier1_style,
            }),
        decreases count - local_index,
    ))]
    while local_index < count {
        let linear_index = match u32::try_from(local_index) {
            Ok(index) => index,
            Err(_) => return Err(packet_arithmetic_overflow()),
        };
        let state = code_block_packet_state_new();
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous_states = states@; }
        states.push(state);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(states@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state))
                =~= previous_states.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state))
                    .push(crate::specs::part1_code_block_packet_initial()));
            assert(initial_states + Seq::new(local_index as nat + 1, |index: int| crate::specs::part1_code_block_packet_initial())
                =~= (initial_states + Seq::new(local_index as nat, |index: int| crate::specs::part1_code_block_packet_initial()))
                    .push(crate::specs::part1_code_block_packet_initial()));
        }
        contexts.push(CodeBlockPacketContext {
            leaf_x: linear_index
                .checked_rem(across)
                .ok_or_else(packet_arithmetic_overflow)?,
            leaf_y: linear_index
                .checked_div(across)
                .ok_or_else(packet_arithmetic_overflow)?,
            layer: 0,
            maximum_zero_bitplanes: maximum_zero,
            tier1_style,
        });
        local_index = local_index
            .checked_add(1)
            .ok_or_else(packet_arithmetic_overflow)?;
    }
    Ok((states, contexts))
}

impl PacketPrecinctDecoder {
    pub fn new(
        geometry: PacketPrecinctGeometry,
        tier1_style: Tier1CodingStyle,
        decoders: Vec<Tier1CodeBlockDecoder>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        Self::new_subbands(
            geometry.component,
            geometry.resolution,
            geometry.precinct,
            tier1_style,
            vec![PacketSubbandExecution {
                orientation: SubbandOrientation::Ll,
                code_blocks_across: geometry.code_blocks_across,
                code_blocks_down: geometry.code_blocks_down,
                maximum_zero_bitplanes: geometry.maximum_zero_bitplanes,
                decoders,
            }],
            limits,
        )
    }

    /// An empty execution list represents a precinct with no nonempty subbands.
    pub fn new_subbands(
        component: u16,
        resolution: u8,
        precinct: u32,
        tier1_style: Tier1CodingStyle,
        executions: Vec<PacketSubbandExecution>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        packet_precinct_from_subbands(
            component,
            resolution,
            precinct,
            tier1_style,
            executions,
            limits,
        )
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_precinct_outcome(result) == crate::specs::part2_precinct_from_executions(
        component, resolution, precinct, tier1_style, packet_executions_view(before@), limits,
    ),
))]
pub(crate) fn packet_precinct_from_subbands(
    component: u16,
    resolution: u8,
    precinct: u32,
    tier1_style: Tier1CodingStyle,
    before: Vec<PacketSubbandExecution>,
    limits: &ResourceLimits,
) -> Result<PacketPrecinctDecoder, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = packet_executions_view(before@); }
    let mut executions = before;
    if executions.len() > 3 {
        return Err(invalid_packet_header());
    }
    let mut states = Vec::new();
    let mut contexts = Vec::new();
    let mut decoders = Vec::new();
    let mut subbands = Vec::with_capacity(executions.len());
    let mut execution_index = 0_usize;
    let mut total_code_blocks = 0_u64;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(original.len() == executions@.len());
        assert(original.len() <= 3);
        reveal(precinct_initialization_view);
        assert(states@.map_values(|state: CodeBlockPacketState| code_block_packet_state_view(&state)) =~= Seq::empty());
        assert(decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)) =~= Seq::empty());
        assert(subbands@.map_values(|subband: PacketSubbandState| packet_subband_view(&subband)) =~= Seq::empty());
        assert(precinct_initialization_view((component, resolution, precinct), states@, contexts@, decoders@, subbands@)
            == crate::specs::Part1PacketPrecinctState {
                component, resolution, precinct, states: Seq::empty(), contexts: Seq::empty(),
                decoders: Seq::empty(), subbands: Seq::empty(),
            });
        reveal(crate::specs::part2_precinct_initialization_run);
    }
    #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    execution_index <= executions.len(),
                    executions@.len() == original.len(),
                    original == packet_executions_view(before@),
                    original.len() <= 3,
                    forall |index: int| execution_index <= index < original.len()
                        ==> #[trigger] packet_execution_view(&executions@[index]) == original[index],
                    crate::specs::part2_precinct_from_executions(component, resolution, precinct, tier1_style, original, limits)
                        == crate::specs::part2_precinct_initialization_run(
                            original, tier1_style, limits, execution_index as nat,
                            precinct_initialization_view((component, resolution, precinct), states@, contexts@, decoders@, subbands@),
                            total_code_blocks,
                        ),
                decreases executions.len() - execution_index,
            )
        )]
    while execution_index < executions.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_state = precinct_initialization_view(
                (component, resolution, precinct), states@, contexts@, decoders@, subbands@);
            let ghost previous_total = total_code_blocks;
            let ghost row = original[execution_index as int];
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_precinct_initialization_run);
            reveal(packet_execution_view);
            reveal(precinct_initialization_view);
            assert(packet_execution_view(&executions@[execution_index as int]) == original[execution_index as int]);
        }
        let execution = executions
            .get_mut(execution_index)
            .ok_or_else(invalid_packet_header)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(packet_execution_view(execution) == original[execution_index as int]);
            assert(original[execution_index as int].across == execution.code_blocks_across);
            assert(original[execution_index as int].down == execution.code_blocks_down);
            assert(original[execution_index as int].maximum_zero == execution.maximum_zero_bitplanes);
        }
        if execution.code_blocks_across == 0
            || execution.code_blocks_down == 0
            || execution.maximum_zero_bitplanes == 0
            || execution.maximum_zero_bitplanes > crate::tier1::MAX_TIER1_BITPLANES
        {
            return Err(invalid_packet_header());
        }
        let count = u64::from(execution.code_blocks_across)
            .checked_mul(u64::from(execution.code_blocks_down))
            .ok_or_else(packet_arithmetic_overflow)?;
        total_code_blocks = total_code_blocks
            .checked_add(count)
            .ok_or_else(packet_arithmetic_overflow)?;
        if total_code_blocks > limits.maximum_code_blocks() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlocks,
                limit: limits.maximum_code_blocks(),
                actual: total_code_blocks,
            });
        }
        if total_code_blocks > limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: total_code_blocks,
            });
        }
        let count = match usize::try_from(count) {
            Ok(count) => count,
            Err(_) => return Err(packet_arithmetic_overflow()),
        };
        if execution.decoders.len() != count {
            return Err(invalid_packet_header());
        }
        let first_decoder = decoders.len();
        let prepared = prepare_precinct_contexts(
            states,
            contexts,
            count,
            execution.code_blocks_across,
            execution.maximum_zero_bitplanes,
            tier1_style,
        )?;
        states = prepared.0;
        contexts = prepared.1;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_decoders = decoders@;
            let ghost row_decoders = execution.decoders@;
        }
        decoders.append(&mut execution.decoders);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder))
                =~= previous_decoders.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder))
                    + row_decoders.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)));
        }
        let inclusion_tree = tag_tree_new(
            execution.code_blocks_across,
            execution.code_blocks_down,
            limits,
        )?;
        let zero_bitplane_tree = tag_tree_new(
            execution.code_blocks_across,
            execution.code_blocks_down,
            limits,
        )?;
        let subband = PacketSubbandState {
            orientation: execution.orientation,
            first_decoder,
            decoder_count: count,
            code_blocks_across: execution.code_blocks_across,
            code_blocks_down: execution.code_blocks_down,
            inclusion_tree,
            zero_bitplane_tree,
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_subbands = subbands@;
            let ghost added_subband = packet_subband_view(&subband);
        }
        subbands.push(subband);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(subbands@.map_values(|value: PacketSubbandState| packet_subband_view(&value))
                =~= previous_subbands.map_values(|value: PacketSubbandState| packet_subband_view(&value)).push(added_subband));
            assert(crate::specs::part2_precinct_execution(previous_state, previous_total, row, tier1_style, limits)
                == Ok((precinct_initialization_view((component, resolution, precinct),
                    states@, contexts@, decoders@, subbands@), total_code_blocks)));
            crate::proofs::production_impl::production_precinct_initialization_step(
                original, tier1_style, limits, execution_index as nat, previous_state, previous_total,
                precinct_initialization_view((component, resolution, precinct),
                    states@, contexts@, decoders@, subbands@), total_code_blocks,
            );
        }
        execution_index = execution_index
            .checked_add(1)
            .ok_or_else(packet_arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_precinct_initialization_run); }
    Ok(PacketPrecinctDecoder {
        component,
        resolution,
        precinct,
        states,
        contexts,
        decoders,
        subbands,
    })
}

impl PacketPrecinctDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == (packet_precinct_view(self).component,
            packet_precinct_view(self).resolution, packet_precinct_view(self).precinct),
    ))]
    pub const fn coordinate(&self) -> (u16, u8, u32) {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(packet_precinct_view); }
        (self.component, self.resolution, self.precinct)
    }

    pub fn states(&self) -> &[CodeBlockPacketState] {
        &self.states
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == packet_precinct_decoders(self),
    ))]
    pub fn decoders(&self) -> &[Tier1CodeBlockDecoder] {
        &self.decoders
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result as nat == crate::specs::part1_packet_decoder_count(packet_precinct_decoders(self)),
    ))]
    pub const fn decoder_count(&self) -> usize {
        self.decoders.len()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures packet_decoder_outcome(result) == crate::specs::part1_packet_precinct_decoder(packet_precinct_decoders(self), index),
    ))]
    pub fn decoder(&self, index: usize) -> Result<&Tier1CodeBlockDecoder, DecodeError> {
        self.decoders.get(index).ok_or_else(invalid_packet_header)
    }

    pub const fn subband_count(&self) -> usize {
        self.subbands.len()
    }

    pub fn subband_orientation(&self, index: usize) -> Result<SubbandOrientation, DecodeError> {
        self.subbands
            .get(index)
            .map(|subband| subband.orientation)
            .ok_or_else(invalid_packet_header)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, precinct_header_view(final(states), final(subbands), final(contributions), final(reader), final(progress)))
        == crate::specs::part1_precinct_header_slot(
            precinct_header_view(old(states), old(subbands), old(contributions), old(reader), old(progress)),
            contexts@, parameters.layer, parameters.style),
        result.is_ok() ==> final(progress).local_index as nat == old(progress).local_index as nat + 1,
        final(progress).subband_index == old(progress).subband_index,
        final(states)@.len() == old(states)@.len(),
        final(subbands)@.len() == old(subbands)@.len(),
        final(contributions)@.len() == old(contributions)@.len(),
        result == Ok(()) || result.is_err(),
))]
fn decode_precinct_header_slot(
    states: &mut [CodeBlockPacketState],
    contexts: &[CodeBlockPacketContext],
    subbands: &mut [PacketSubbandState],
    contributions: &mut [Option<CodeBlockContribution>],
    reader: &mut PacketBitReader<'_>,
    parameters: PrecinctHeaderParameters,
    progress: &mut PrecinctHeaderProgress,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_precinct_header_slot); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost prior_states = states@;
        let ghost prior_subbands = subbands@;
        let ghost prior = precinct_header_view(states, subbands, contributions, reader, progress);
        let ghost subband_index = progress.subband_index;
    }
    let (header_result, block_index) = {
        let subband = subbands
            .get(progress.subband_index)
            .ok_or_else(invalid_packet_header)?;
        let block_index = subband
            .first_decoder
            .checked_add(progress.local_index)
            .ok_or_else(packet_arithmetic_overflow)?;
        let context = contexts
            .get(block_index)
            .ok_or_else(invalid_packet_header)?;
        let linear_index = match u32::try_from(progress.local_index) {
            Ok(value) => value,
            Err(_) => {
                #[cfg(verus_keep_ghost)]
                proof! { assert(progress.local_index > u32::MAX); }
                return Err(packet_arithmetic_overflow());
            }
        };
        let expected_x = linear_index
            .checked_rem(subband.code_blocks_across)
            .ok_or_else(packet_arithmetic_overflow)?;
        let expected_y = linear_index
            .checked_div(subband.code_blocks_across)
            .ok_or_else(packet_arithmetic_overflow)?;
        if context.layer != parameters.layer
            || context.leaf_x != expected_x
            || context.leaf_y != expected_y
            || !tier1_styles_equal(context.tier1_style, parameters.style)
        {
            return Err(invalid_packet_header());
        }
        let state = states
            .get_mut(block_index)
            .ok_or_else(invalid_packet_header)?;
        let subband = &mut subbands[progress.subband_index];
        let result = decode_code_block_contribution(
            state,
            &mut subband.inclusion_tree,
            &mut subband.zero_bitplane_tree,
            *context,
            reader,
        );
        (result, block_index)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(states@.len() == prior_states.len());
        assert(subbands@.len() == prior_subbands.len());
        assert forall |i: int| 0 <= i < states@.len() && i != block_index as int implies
            states@[i] == prior_states[i] by {}
        assert forall |i: int| 0 <= i < subbands@.len() && i != subband_index as int implies
            subbands@[i] == prior_subbands[i] by {}
        let after = precinct_header_view(states, subbands, contributions, reader, progress);
        let expected_header = crate::specs::part1_packet_header_decode(
            prior.states[block_index as int],
            prior.subbands[subband_index as int].inclusion_tree,
            prior.subbands[subband_index as int].zero_bitplane_tree,
            contexts@[block_index as int], prior.reader);
        assert(code_block_header_outcome(header_result) == expected_header.0);
        assert(code_block_packet_state_view(&states@[block_index as int]) == expected_header.1);
        assert(packet_subband_view(&subbands@[subband_index as int])
            == crate::specs::Part1PacketSubbandState {
                inclusion_tree: expected_header.2, zero_bitplane_tree: expected_header.3,
                ..prior.subbands[subband_index as int]
            });
        assert(after.reader == expected_header.4);
        assert(after.states =~= prior.states.update(block_index as int,
            code_block_packet_state_view(&states@[block_index as int])));
        assert(after.subbands =~= prior.subbands.update(subband_index as int,
            packet_subband_view(&subbands@[subband_index as int])));
    }
    let contribution = header_result?;
    if contribution.is_some() {
        progress.contribution_count = progress
            .contribution_count
            .checked_add(1)
            .ok_or_else(packet_arithmetic_overflow)?;
    }
    {
        let slot = contributions
            .get_mut(block_index)
            .ok_or_else(invalid_packet_header)?;
        *slot = contribution;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(packet_body_contributions_view(contributions) =~=
            prior.contributions.update(block_index as int, code_block_contribution_option_view(contribution)));
    }
    progress.local_index = progress
        .local_index
        .checked_add(1)
        .ok_or_else(packet_arithmetic_overflow)?;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, precinct_header_view(final(states), final(subbands), final(contributions), final(reader), final(progress)))
        == crate::specs::part1_precinct_header_members(
            precinct_header_view(old(states), old(subbands), old(contributions), old(reader), old(progress)),
            contexts@, parameters.0.layer, parameters.0.style, parameters.1),
        final(progress).subband_index == old(progress).subband_index,
        final(states)@.len() == old(states)@.len(),
        final(subbands)@.len() == old(subbands)@.len(),
        final(contributions)@.len() == old(contributions)@.len(),
        result == Ok(()) || result.is_err(),
))]
fn decode_precinct_header_members(
    states: &mut [CodeBlockPacketState],
    contexts: &[CodeBlockPacketContext],
    subbands: &mut [PacketSubbandState],
    contributions: &mut [Option<CodeBlockContribution>],
    reader: &mut PacketBitReader<'_>,
    parameters: (PrecinctHeaderParameters, usize),
    progress: &mut PrecinctHeaderProgress,
) -> Result<(), DecodeError> {
    let decoder_count = parameters.1;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_precinct_header_members_run); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            decoder_count == parameters.1,
            progress.subband_index == old(progress).subband_index,
            states@.len() == old(states)@.len(),
            subbands@.len() == old(subbands)@.len(),
            contributions@.len() == old(contributions)@.len(),
            crate::specs::part1_precinct_header_members(
                precinct_header_view(old(states), old(subbands), old(contributions), old(reader), old(progress)),
                contexts@, parameters.0.layer, parameters.0.style, decoder_count)
            == crate::specs::part1_precinct_header_members_run(
                precinct_header_view(states, subbands, contributions, reader, progress),
                contexts@, parameters.0.layer, parameters.0.style,
                if progress.local_index >= decoder_count { 0 }
                else { (decoder_count - progress.local_index) as nat }),
        decreases decoder_count as int - progress.local_index as int,
    ))]
    while progress.local_index < decoder_count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_precinct_header_members_run); }
        decode_precinct_header_slot(
            states,
            contexts,
            subbands,
            contributions,
            reader,
            parameters.0,
            progress,
        )?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_precinct_header_members_run); }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, precinct_header_view(final(states), final(subbands), final(contributions), final(reader), final(progress)))
        == crate::specs::part1_precinct_headers(
            precinct_header_view(old(states), old(subbands), old(contributions), old(reader), old(progress)),
            contexts@, parameters.layer, parameters.style),
))]
pub(super) fn decode_precinct_contribution_headers(
    states: &mut [CodeBlockPacketState],
    contexts: &[CodeBlockPacketContext],
    subbands: &mut [PacketSubbandState],
    contributions: &mut [Option<CodeBlockContribution>],
    reader: &mut PacketBitReader<'_>,
    parameters: PrecinctHeaderParameters,
    progress: &mut PrecinctHeaderProgress,
) -> Result<(), DecodeError> {
    let subband_count = subbands.len();
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_precinct_headers_run); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            subband_count == subbands.len(),
            crate::specs::part1_precinct_headers(
                precinct_header_view(old(states), old(subbands), old(contributions), old(reader), old(progress)),
                contexts@, parameters.layer, parameters.style)
            == crate::specs::part1_precinct_headers_run(
                precinct_header_view(states, subbands, contributions, reader, progress),
                contexts@, parameters.layer, parameters.style,
                if progress.subband_index >= subband_count { 0 }
                else { (subband_count - progress.subband_index) as nat }),
        decreases subband_count as int - progress.subband_index as int,
    ))]
    while progress.subband_index < subband_count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_precinct_headers_run); }
        let decoder_count = {
            let subband = subbands
                .get(progress.subband_index)
                .ok_or_else(invalid_packet_header)?;
            let count = u64::from(subband.code_blocks_across)
                .checked_mul(u64::from(subband.code_blocks_down))
                .ok_or_else(packet_arithmetic_overflow)?;
            let expected_count = match usize::try_from(count) {
                Ok(value) => value,
                Err(_) => {
                    #[cfg(verus_keep_ghost)]
                    proof! { assert(count > usize::MAX); }
                    return Err(packet_arithmetic_overflow());
                }
            };
            if expected_count != subband.decoder_count
                || subband.inclusion_tree.leaf_count()? != expected_count as u64
                || subband.zero_bitplane_tree.leaf_count()? != expected_count as u64
            {
                return Err(invalid_packet_header());
            }
            subband.decoder_count
        };
        progress.local_index = 0;
        decode_precinct_header_members(
            states,
            contexts,
            subbands,
            contributions,
            reader,
            (parameters, decoder_count),
            progress,
        )?;
        progress.subband_index = progress
            .subband_index
            .checked_add(1)
            .ok_or_else(packet_arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_precinct_headers_run); }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, packet_precinct_view(final(precinct))) == crate::specs::part1_precinct_packet(
        packet_precinct_view(old(precinct)), tile_part, offset, packed_headers@, packed_offset,
        expected_packet_length, expected_sop_sequence, decode_tier1,
        crate::limits::resource_code_block_limit(limits), crate::limits::resource_packet_header_byte_limit(limits),
        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        !decode_tier1 ==> final(precinct).decoders@==old(precinct).decoders@,
        (final(precinct).component,final(precinct).resolution,final(precinct).precinct)
            ==(old(precinct).component,old(precinct).resolution,old(precinct).precinct),
))]
pub(super) fn decode_precinct_packet(
    tile_part: &TilePartPayload<'_>,
    offset: usize,
    packed_headers: &[u8],
    packed_offset: usize,
    expected_packet_length: Option<u32>,
    expected_sop_sequence: u16,
    precinct: &mut PacketPrecinctDecoder,
    decode_tier1: bool,
    limits: &ResourceLimits,
) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
    let component = precinct.component;
    if precinct.states.len() != precinct.contexts.len()
        || precinct.states.len() != precinct.decoders.len()
        || precinct.states.is_empty() != precinct.subbands.is_empty()
    {
        return Err(invalid_packet_header());
    }
    let code_blocks = precinct.states.len() as u64;
    if code_blocks > limits.maximum_code_blocks() {
        return Err(packet_reader_limit(
            Resource::CodeBlocks,
            limits.maximum_code_blocks(),
            code_blocks,
        ));
    }
    if code_blocks > limits.maximum_work_units() {
        return Err(packet_reader_limit(
            Resource::WorkUnits,
            limits.maximum_work_units(),
            code_blocks,
        ));
    }
    let data = match tile_part.data.get(offset..) {
        Some(data) => data,
        None => {
            return Err(packet_reader_error(
                offset,
                MalformedKind::InvalidPacketLength,
            ));
        }
    };
    let tier1_style = tile_part
        .component_coding_styles
        .style(component)?
        .tier1_coding_style()?;
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::coding_style_known_packet_markers(&tile_part.coding_style); }
    decode_precinct_packet_payload(
        data,
        packed_headers,
        PrecinctPayloadParameters {
            error_offset: offset,
            packed_offset,
            expected_packet_length,
            expected_sop_sequence,
            style: tier1_style,
            sop: tile_part.coding_style.sop_markers,
            eph: tile_part.coding_style.eph_markers,
            packed: tile_part.packed_packet_headers.is_present(),
            decode_tier1,
        },
        precinct,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures precinct_payload_reader_outcome(result) == crate::specs::part1_precinct_payload_prefix(
        data@, packed_headers@, precinct_payload_parameters_view(parameters),
        crate::limits::resource_packet_header_byte_limit(limits),
        crate::limits::resource_work_limit(limits)),
))]
pub(super) fn decode_precinct_packet_payload_prefix<'a>(
    data: &'a [u8],
    packed_headers: &'a [u8],
    parameters: PrecinctPayloadParameters,
    limits: &ResourceLimits,
) -> Result<PrecinctPayloadReader<'a>, DecodeError> {
    let offset = parameters.error_offset;
    let packed_offset = parameters.packed_offset;
    let expected_sop_sequence = parameters.expected_sop_sequence;
    let mut tile_offset = 0_usize;
    // Packed body bytes are not inline headers; only a real SOP prefix selects one.
    if parameters.sop
        && data.len() >= 2
        && data[0] == 0xff
        && (data[1] == 0x91 || (!parameters.packed && data[1] >= 0x90))
    {
        let marker = match data.get(0..2) {
            Some(marker) => marker,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        };
        let marker_length = match data.get(2..4) {
            Some(marker) => marker,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        };
        if !crate::refinement::sop_valid(marker[0], marker[1], marker_length[0], marker_length[1]) {
            return Err(invalid_packet_header());
        }
        let sequence = match data.get(4..6) {
            Some(sequence) => sequence,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        };
        let sequence_number = crate::refinement::sop_sequence(sequence[0], sequence[1]);
        if sequence_number != expected_sop_sequence {
            return Err(invalid_packet_header());
        }
        tile_offset = 6;
    }
    let packed = parameters.packed;
    let packet_data = if packed {
        match packed_headers.get(packed_offset..) {
            Some(data) => data,
            None => return Err(packet_reader_error(packed_offset, MalformedKind::Truncated)),
        }
    } else {
        match data.get(tile_offset..) {
            Some(data) => data,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        }
    };
    let mut reader = packet_reader_prefix(packet_data, limits);
    let packet_present = reader.read_bit()?;
    Ok(PrecinctPayloadReader {
        reader,
        packet_data,
        present: packet_present,
        sop_bytes: tile_offset,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, packet_precinct_view(final(precinct))) == crate::specs::part1_precinct_payload(
        packet_precinct_view(old(precinct)), data@, packed_headers@, precinct_payload_parameters_view(parameters),
        crate::limits::resource_packet_header_byte_limit(limits),
        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        !parameters.decode_tier1 ==> final(precinct).decoders@==old(precinct).decoders@,
        (final(precinct).component,final(precinct).resolution,final(precinct).precinct)
            ==(old(precinct).component,old(precinct).resolution,old(precinct).precinct),
))]
pub(super) fn decode_precinct_packet_payload(
    data: &[u8],
    packed_headers: &[u8],
    parameters: PrecinctPayloadParameters,
    precinct: &mut PacketPrecinctDecoder,
    limits: &ResourceLimits,
) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial_precinct = packet_precinct_view(precinct); }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_precinct_payload_headers);
    }
    let tier1_style = parameters.style;
    let prefix = decode_precinct_packet_payload_prefix(data, packed_headers, parameters, limits)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial_reader = precinct_payload_reader_view(prefix); }
    let mut reader = prefix.reader;
    let packet_data = prefix.packet_data;
    let packet_present = prefix.present;
    let mut contributions = vec![None; precinct.states.len()];
    let mut contribution_count = 0_u32;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(contributions@.map_values(|value: Option<CodeBlockContribution>| code_block_contribution_option_view(value)) =~=
            Seq::new(initial_precinct.states.len(), |i: int| None));
    }
    if packet_present && !precinct.contexts.is_empty() {
        let layer = precinct
            .contexts
            .first()
            .ok_or_else(invalid_packet_header)?
            .layer;
        let mut progress = PrecinctHeaderProgress {
            subband_index: 0,
            local_index: 0,
            contribution_count,
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost expected_headers = crate::specs::part1_precinct_headers(
                crate::specs::Part1PrecinctHeaderState {
                    states: initial_precinct.states, subbands: initial_precinct.subbands,
                    contributions: contributions@.map_values(|value: Option<CodeBlockContribution>| code_block_contribution_option_view(value)),
                    reader: packet_bit_reader_view(&reader), subband_index: 0, local_index: 0, contribution_count: 0,
                },
                precinct.contexts@, layer, tier1_style);
        }
        let header_result = decode_precinct_contribution_headers(
            &mut precinct.states,
            &precinct.contexts,
            &mut precinct.subbands,
            &mut contributions,
            &mut reader,
            PrecinctHeaderParameters {
                layer,
                style: tier1_style,
            },
            &mut progress,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(header_result == expected_headers.0);
            assert(packet_precinct_view(precinct).states == expected_headers.1.states);
            assert(packet_precinct_view(precinct).subbands == expected_headers.1.subbands);
            assert(packet_bit_reader_view(&reader) == expected_headers.1.reader);
            assert(contributions@.map_values(|value: Option<CodeBlockContribution>| code_block_contribution_option_view(value))
                == expected_headers.1.contributions);
            assert(progress.contribution_count == expected_headers.1.contribution_count);
            assert(packet_precinct_view(precinct) == crate::specs::Part1PacketPrecinctState {
                states: expected_headers.1.states, subbands: expected_headers.1.subbands, ..initial_precinct
            });
        }
        header_result?;
        contribution_count = progress.contribution_count;
    }
    decode_precinct_packet_payload_after_headers(
        data,
        parameters,
        PrecinctPayloadHeader {
            prefix: PrecinctPayloadReader {
                reader,
                packet_data,
                present: packet_present,
                sop_bytes: prefix.sop_bytes,
            },
            contributions,
            contribution_count,
        },
        precinct,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, packet_precinct_view(final(precinct))) == crate::specs::part1_precinct_payload_after_headers(
        packet_precinct_view(old(precinct)), precinct_payload_parameters_view(parameters), data@,
        precinct_payload_header_view(header).0.packet_data, precinct_payload_header_view(header).0.reader,
        precinct_payload_header_view(header).1, precinct_payload_header_view(header).2,
        precinct_payload_header_view(header).0.present, precinct_payload_header_view(header).0.sop_bytes,
        crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
        !parameters.decode_tier1 ==> final(precinct).decoders@==old(precinct).decoders@,
        (final(precinct).component,final(precinct).resolution,final(precinct).precinct)
            ==(old(precinct).component,old(precinct).resolution,old(precinct).precinct),
))]
fn decode_precinct_packet_payload_after_headers(
    data: &[u8],
    parameters: PrecinctPayloadParameters,
    header: PrecinctPayloadHeader<'_>,
    precinct: &mut PacketPrecinctDecoder,
    limits: &ResourceLimits,
) -> Result<(PacketBodyDecode, usize, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_precinct_payload_after_headers);
        reveal(crate::specs::part1_precinct_payload_body);
    }
    let code_blocks = precinct.states.len() as u64;
    let offset = parameters.error_offset;
    let expected_packet_length = parameters.expected_packet_length;
    let decode_tier1 = parameters.decode_tier1;
    let mut reader = header.prefix.reader;
    let packet_data = header.prefix.packet_data;
    let packet_present = header.prefix.present;
    let mut tile_offset = header.prefix.sop_bytes;
    let mut packed_bytes_consumed = 0_usize;
    let packed = parameters.packed;
    let contributions = header.contributions;
    let contribution_count = header.contribution_count;
    reader.finish_packet_header()?;
    let header_bytes = reader.bytes_consumed();
    if packed {
        packed_bytes_consumed = header_bytes;
    } else {
        tile_offset = match tile_offset.checked_add(header_bytes) {
            Some(offset) => offset,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    if parameters.eph {
        let marker_start = header_bytes;
        let marker_end = match marker_start.checked_add(2) {
            Some(end) => end,
            None => return Err(packet_arithmetic_overflow()),
        };
        let marker = match packet_data.get(marker_start..marker_end) {
            Some(marker) => marker,
            None => return Err(packet_reader_error(offset, MalformedKind::Truncated)),
        };
        if !crate::refinement::eph_valid(marker[0], marker[1]) {
            return Err(invalid_packet_header());
        }
        if packed {
            packed_bytes_consumed = marker_end;
        } else {
            tile_offset = match tile_offset.checked_add(2) {
                Some(offset) => offset,
                None => return Err(packet_arithmetic_overflow()),
            };
        }
    }
    let body_start = tile_offset;
    let mut preflight = PacketBodyPreflight {
        index: 0,
        end: tile_offset,
    };
    preflight_packet_body_ranges(&contributions, data, &mut preflight, (offset, 0))?;
    tile_offset = preflight.end;
    let mut execution = PacketBodyExecutionProgress {
        index: 0,
        offset: body_start,
        segments: 0,
        passes: 0,
    };
    execute_packet_body_contributions(
        &mut precinct.decoders,
        &contributions,
        data,
        &mut execution,
        (offset, 0),
        decode_tier1,
        limits,
    )?;
    let body_bytes = match tile_offset.checked_sub(body_start) {
        Some(bytes) => bytes,
        None => return Err(packet_arithmetic_overflow()),
    };
    if tile_offset > usize::MAX - packed_bytes_consumed {
        return Err(packet_arithmetic_overflow());
    }
    let logical_bytes = crate::refinement::packet_logical_bytes(tile_offset, packed_bytes_consumed);
    let packet_length_matches = match expected_packet_length {
        Some(expected) => {
            let expected = match usize::try_from(expected) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            };
            crate::refinement::packet_length_matches(logical_bytes, expected)
        }
        None => true,
    };
    if !packet_length_matches {
        return Err(packet_reader_error(
            offset,
            MalformedKind::InvalidPacketLength,
        ));
    }
    Ok((
        PacketBodyDecode {
            present: packet_present,
            code_blocks: match u32::try_from(code_blocks) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
            contributions: contribution_count,
            segments: execution.segments,
            passes: execution.passes,
            header_bytes: match u32::try_from(header_bytes) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
            body_bytes: match u32::try_from(body_bytes) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
            bytes_consumed: match u32::try_from(logical_bytes) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
        },
        tile_offset,
        packed_bytes_consumed,
    ))
}
