use super::coding::{legacy_maximum_passes, pass_kind};
use super::state::{arithmetic_overflow, code_block_plane_from_dimensions, invalid_code_block};
use super::{
    CodeBlockPlane, CodeBlockSegmentAccounting, LegacySegmentState, MAX_HT_MAGNITUDE_BITS,
    MAX_TIER1_BITPLANES, SubbandOrientation, Tier1BlockCoding, Tier1CodeBlockDecoder,
    Tier1CodingStyle, Tier1PassKind, Tier1SegmentDecode,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_view, legacy_segment_view, tier1_decoder_plane_view, tier1_decoder_state,
    tier1_initial_decoder_outcome,
};
use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Clone for LegacySegmentState {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures legacy_segment_view(&result) == legacy_segment_view(self),
    ))]
    fn clone(&self) -> Self {
        Self {
            plane: self.plane.clone(),
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            bitplane_state: self.bitplane_state.clone(),
            mq_context_state: self.mq_context_state,
            reset_contexts_before_mq: self.reset_contexts_before_mq,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            input: self.input.clone(),
            passes: self.passes,
        }
    }
}

impl LegacySegmentState {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_nested_legacy_result(legacy_segment_view(self),role,super::legacy_segment_outcome(result)),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>super::legacy_segment_outcome(Ok(value))==Ok(legacy_segment_view(self))},
    ))]
    fn try_duplicate(&self, role: super::HtRefinementCopyRole) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=legacy_segment_view(self);}
        Ok(Self {
            plane: {
                let copied = self.plane.try_duplicate_raw(role, false, true);
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_nested_legacy_plane_error(before,role,error);}}
                copied?
            },
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            bitplane_state: {
                let copied =
                    super::legacy_passes::try_duplicate_bitplane(&self.bitplane_state, role, true);
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_nested_legacy_flags_error(before,role,error);}}
                copied?
            },
            mq_context_state: self.mq_context_state,
            reset_contexts_before_mq: self.reset_contexts_before_mq,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            input: {
                let copied = crate::allocation::copy_values(&self.input);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let result=match copied{Err(error)=>Err(error),Ok(_)=>Ok(())};
                    crate::specs::part2_nested_owner_observed(crate::specs::Part2NestedCopyOwner::Input {source:before,role},result);
                    crate::specs::part2_nested_legacy_observed(before,role,result);
                }
                copied?
            },
            passes: self.passes,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_append_result(
            legacy_segment_view(old(self)), input@, passes,
            match result { Err(error) => Err(error), Ok(()) => Ok(legacy_segment_view(final(self))) }),
            match result {
            Ok(()) => legacy_segment_view(final(self)) == crate::specs::part1_legacy_append(
                legacy_segment_view(old(self)), input@, passes),
            Err(error) => error == DecodeError::AllocationFailed
                && legacy_segment_view(final(self)) == legacy_segment_view(old(self)),
        },
    ))]
    fn append(&mut self, input: &[u8], passes: u32) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = legacy_segment_view(self); }
        let extended = crate::allocation::extend_bytes(&mut self.input, input);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_legacy_append_observed(before, input@, passes, self.input@, extended);
        }
        extended?;
        self.passes = passes;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.input@ =~= legacy_segment_view(old(self)).input + input@);
        }
        Ok(())
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_nested_legacy_option_result(super::legacy_segment_option_view(source),role,super::legacy_segment_option_outcome(result)),
        match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>super::legacy_segment_option_view(&value)==super::legacy_segment_option_view(source)},
))]
fn try_duplicate_legacy_segment(
    source: &Option<LegacySegmentState>,
    role: super::HtRefinementCopyRole,
) -> Result<Option<LegacySegmentState>, DecodeError> {
    match source.as_ref() {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_nested_option_none(|value,rest|crate::specs::part2_nested_legacy_run(value,role,rest));}
            Ok(None)
        }
        Some(value) => {
            let copied = value.try_duplicate(role);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_nested_legacy_frames(legacy_segment_view(value),role,super::legacy_segment_outcome(copied));
                crate::specs::part2_nested_option_observed(legacy_segment_view(value),|source,rest|crate::specs::part2_nested_legacy_run(source,role,rest),super::legacy_segment_outcome(copied));
            }
            Ok(Some(copied?))
        }
    }
}

impl Clone for Tier1CodeBlockDecoder {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tier1_decoder_state(&result) == tier1_decoder_state(self),
    ))]
    fn clone(&self) -> Self {
        Self {
            plane: self.plane.clone(),
            orientation: self.orientation,
            style: self.style,
            maximum_passes: self.maximum_passes,
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            zero_bitplanes: self.zero_bitplanes,
            bitplane_state: self.bitplane_state.clone(),
            mq_context_state: self.mq_context_state,
            reset_contexts_before_mq: self.reset_contexts_before_mq,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            legacy_segment: self.legacy_segment.clone(),
            legacy_decode_work: self.legacy_decode_work,
            ht_cleanup_plane: self.ht_cleanup_plane.clone(),
            ht_refinement_data: self.ht_refinement_data.clone(),
            ht_refinement_passes: self.ht_refinement_passes,
            ht_decoded_bitplanes: self.ht_decoded_bitplanes,
            ht_current_set_has_cleanup: self.ht_current_set_has_cleanup,
            ht_sets_seen: self.ht_sets_seen,
            allow_multiple_ht_sets: self.allow_multiple_ht_sets,
            ht_magnitude_bound: self.ht_magnitude_bound,
        }
    }
}

impl Tier1CodeBlockDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_ht_duplicate_result(tier1_decoder_state(self),role,tier1_initial_decoder_outcome(result)),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>tier1_decoder_state(&value)==tier1_decoder_state(self)},
    ))]
    pub(crate) fn try_duplicate(
        &self,
        role: super::HtRefinementCopyRole,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        Ok(Self {
            plane: {
                let copied = self.plane.try_duplicate_raw(role, false, false);
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_ht_duplicate_primary_error(before,role,error);}}
                copied?
            },
            orientation: self.orientation,
            style: self.style,
            maximum_passes: self.maximum_passes,
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            zero_bitplanes: self.zero_bitplanes,
            bitplane_state: {
                let copied =
                    super::legacy_passes::try_duplicate_bitplane(&self.bitplane_state, role, false);
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_ht_duplicate_bitplane_error(before,role,error);}}
                copied?
            },
            mq_context_state: self.mq_context_state,
            reset_contexts_before_mq: self.reset_contexts_before_mq,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            legacy_segment: {
                let copied = try_duplicate_legacy_segment(&self.legacy_segment, role);
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_ht_duplicate_legacy_error(before,role,error);}}
                copied?
            },
            legacy_decode_work: self.legacy_decode_work,
            ht_cleanup_plane: match self.ht_cleanup_plane.as_ref() {
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {crate::specs::part2_decoder_cleanup_none(role);}
                    None
                }
                Some(source) => {
                    let copied = source.try_duplicate_raw(role, true, false);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::specs::part2_decoder_cleanup_observed(code_block_plane_view(source),role,super::code_block_plane_outcome(copied));
                        if let Err(error)=copied{crate::specs::part2_ht_duplicate_cleanup_error(before,role,error);}
                    }
                    Some(copied?)
                }
            },
            ht_refinement_data: {
                let copied =
                    super::ht_refinement::copy_ht_refinement_bytes(&self.ht_refinement_data, role);
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::part2_ht_duplicate_observed(before,role,super::ht_byte_vector_outcome(copied));}
                copied?
            },
            ht_refinement_passes: self.ht_refinement_passes,
            ht_decoded_bitplanes: self.ht_decoded_bitplanes,
            ht_current_set_has_cleanup: self.ht_current_set_has_cleanup,
            ht_sets_seen: self.ht_sets_seen,
            allow_multiple_ht_sets: self.allow_multiple_ht_sets,
            ht_magnitude_bound: self.ht_magnitude_bound,
        })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_tier1_initial_storage_result(width,height,significant_bitplanes,orientation,style,tier1_initial_decoder_outcome(result)),
        tier1_initial_decoder_outcome(result)!=Err(DecodeError::AllocationFailed) ==> tier1_initial_decoder_outcome(result) == crate::specs::part2_tier1_initial_decoder(
        width, height, significant_bitplanes, orientation, style,
    ),
))]
pub(crate) fn tier1_decoder_from_dimensions(
    width: u16,
    height: u16,
    significant_bitplanes: u16,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1CodeBlockDecoder, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_tier1_initial_normal(width,height,significant_bitplanes,orientation,style);}
    if significant_bitplanes == 0 || significant_bitplanes > MAX_TIER1_BITPLANES {
        return Err(invalid_code_block());
    }
    let bitplane = significant_bitplanes
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    let maximum_passes = u32::from(significant_bitplanes)
        .checked_mul(3)
        .ok_or_else(arithmetic_overflow)?;
    let maximum_passes = maximum_passes
        .checked_sub(2)
        .ok_or_else(arithmetic_overflow)?;
    Ok(Tier1CodeBlockDecoder {
        plane: {
            let result = code_block_plane_from_dimensions(
                width,
                height,
                super::CoefficientStorageRole::InitialDecoder,
            );
            #[cfg(verus_keep_ghost)]
            proof! {if let Err(error)=result{crate::specs::part2_tier1_initial_plane_error(width,height,significant_bitplanes,orientation,style,error);}}
            result?
        },
        orientation,
        style,
        maximum_passes,
        next_pass: 0,
        bitplane,
        zero_bitplanes: None,
        bitplane_state: None,
        mq_context_state: None,
        reset_contexts_before_mq: false,
        decoded_segments: 0,
        decoded_bytes: 0,
        legacy_segment: None,
        legacy_decode_work: 0,
        ht_cleanup_plane: None,
        ht_refinement_data: Vec::new(),
        ht_refinement_passes: 0,
        ht_decoded_bitplanes: 0,
        ht_current_set_has_cleanup: false,
        ht_sets_seen: 0,
        allow_multiple_ht_sets: false,
        ht_magnitude_bound: MAX_HT_MAGNITUDE_BITS,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_tier1_configured_storage_result(width,height,significant_bitplanes,orientation,style,allow_multiple_ht_sets,ht_magnitude_bound,tier1_initial_decoder_outcome(result)),
        tier1_initial_decoder_outcome(result)!=Err(DecodeError::AllocationFailed) ==> tier1_initial_decoder_outcome(result) == crate::specs::part2_tier1_configured_decoder(
        width, height, significant_bitplanes, orientation, style, allow_multiple_ht_sets, ht_magnitude_bound,
    ),
))]
pub(crate) fn tier1_configured_decoder(
    width: u16,
    height: u16,
    significant_bitplanes: u16,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
) -> Result<Tier1CodeBlockDecoder, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_tier1_configured_normal(width,height,significant_bitplanes,orientation,style,allow_multiple_ht_sets,ht_magnitude_bound);}
    let initial_result =
        tier1_decoder_from_dimensions(width, height, significant_bitplanes, orientation, style);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=initial_result {crate::specs::part2_tier1_configured_initial_error(width,height,significant_bitplanes,orientation,style,allow_multiple_ht_sets,ht_magnitude_bound,error);}}
    let mut decoder = initial_result?;
    decoder.set_multiple_ht_sets_allowed(allow_multiple_ht_sets);
    decoder.set_ht_magnitude_bound(ht_magnitude_bound)?;
    Ok(decoder)
}

impl Tier1CodeBlockDecoder {
    pub fn new(
        width: u16,
        height: u16,
        significant_bitplanes: u16,
        orientation: SubbandOrientation,
        style: Tier1CodingStyle,
    ) -> Result<Self, DecodeError> {
        tier1_decoder_from_dimensions(width, height, significant_bitplanes, orientation, style)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures code_block_plane_view(result) == tier1_decoder_plane_view(self),
    ))]
    pub const fn plane(&self) -> &CodeBlockPlane {
        &self.plane
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == tier1_decoder_state(self).style.block_coding,
    ))]
    pub const fn block_coding(&self) -> Tier1BlockCoding {
        self.style.block_coding
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == (!tier1_decoder_state(self).style.force_high_throughput || high_throughput),
    ))]
    pub const fn accepts_high_throughput_route(&self, high_throughput: bool) -> bool {
        !self.style.force_high_throughput || high_throughput
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == tier1_decoder_state(self).next_pass,))]
    pub const fn next_pass(&self) -> u32 {
        self.next_pass
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == tier1_decoder_state(self).maximum_passes,))]
    pub const fn maximum_passes(&self) -> u32 {
        self.maximum_passes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == tier1_decoder_state(self).decoded_segments,))]
    pub const fn decoded_segments(&self) -> u32 {
        self.decoded_segments
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == tier1_decoder_state(self).decoded_bytes,))]
    pub const fn decoded_bytes(&self) -> u64 {
        self.decoded_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_zero_bitplanes(
            tier1_decoder_state(old(self)), zero_bitplanes),
    ))]
    pub(crate) fn set_zero_bitplanes(&mut self, zero_bitplanes: u16) -> Result<(), DecodeError> {
        if let Some(previous) = self.zero_bitplanes {
            return if previous == zero_bitplanes {
                Ok(())
            } else {
                Err(invalid_code_block())
            };
        }
        if self.next_pass != 0 || self.decoded_segments != 0 || zero_bitplanes > self.bitplane {
            return Err(invalid_code_block());
        }
        let bitplane = self
            .bitplane
            .checked_sub(zero_bitplanes)
            .ok_or_else(invalid_code_block)?;
        let maximum_passes = legacy_maximum_passes(bitplane)?;
        self.bitplane = bitplane;
        self.maximum_passes = maximum_passes;
        self.zero_bitplanes = Some(zero_bitplanes);
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(_result =>
        ensures ((), tier1_decoder_state(final(self))) == crate::specs::part2_tier1_allow_sets(tier1_decoder_state(old(self)), allowed),
    ))]
    pub fn set_multiple_ht_sets_allowed(&mut self, allowed: bool) {
        self.allow_multiple_ht_sets = allowed;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self)))
            == crate::specs::part2_tier1_magnitude_bound(tier1_decoder_state(old(self)), bound),
    ))]
    pub fn set_ht_magnitude_bound(&mut self, bound: u8) -> Result<(), DecodeError> {
        if bound == 0 || bound > MAX_HT_MAGNITUDE_BITS {
            return Err(invalid_code_block());
        }
        self.ht_magnitude_bound = bound;
        Ok(())
    }

    pub const fn is_complete(&self) -> bool {
        if self.active_high_throughput() {
            self.next_pass > 0
        } else {
            self.next_pass == self.maximum_passes
        }
    }

    pub const fn active_high_throughput(&self) -> bool {
        matches!(self.style.block_coding, Tier1BlockCoding::HighThroughput)
            || (matches!(self.style.block_coding, Tier1BlockCoding::Mixed)
                && self.ht_cleanup_plane.is_some())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_contribution_admission(
            tier1_decoder_state(old(self)), input@, passes,
            crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    fn admit_legacy_contribution(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<(u32, u32, u32), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_contribution_admission); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = tier1_decoder_state(self); }
        if passes == 0 {
            return Err(invalid_code_block());
        }
        let next_bytes = self
            .decoded_bytes
            .checked_add(input.len() as u64)
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            return Err(crate::mq::mq_limit(
                Resource::CodeBlockBytes,
                limits.maximum_code_block_bytes(),
                next_bytes,
            ));
        }
        let replay_passes = match &self.legacy_segment {
            Some(segment) => segment.passes,
            None => 0,
        }
        .checked_add(u32::from(passes))
        .ok_or_else(arithmetic_overflow)?;
        let work = legacy_contribution_work(
            self.plane.coefficients().len(),
            replay_passes,
            next_bytes,
            self.legacy_decode_work,
            limits.maximum_work_units(),
        )?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(tier1_decoder_state(self) == before); }
        self.legacy_decode_work = work;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(tier1_decoder_state(self) == (crate::specs::Tier1DecoderState { legacy_decode_work: work, ..before }));
        }
        let next_pass = self
            .next_pass
            .checked_add(u32::from(passes))
            .ok_or_else(arithmetic_overflow)?;
        let last_pass = next_pass.checked_sub(1).ok_or_else(invalid_code_block)?;
        Ok((replay_passes, next_pass, last_pass))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_contribution_result(tier1_decoder_state(old(self)),input@,passes,super::legacy_storage_limits(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_contribution(
            tier1_decoder_state(old(self)), input@, passes,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    pub(crate) fn decode_legacy_contribution(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_contribution); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        let admitted = self.admit_legacy_contribution(input, passes, limits);
        #[cfg(verus_keep_ghost)]
        proof! {if admitted.is_err(){crate::specs::part2_legacy_contribution_pure(before,input@,passes,super::legacy_storage_limits(limits));}}
        let (replay_passes, next_pass, last_pass) = admitted?;
        if self.legacy_segment.is_none()
            && (next_pass == self.maximum_passes
                || self.style.pass_plan(last_pass).terminates_segment)
        {
            let decoded = self.decode_legacy_segment(input, u32::from(passes), limits);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_legacy_contribution_segment_observed(before,input@,passes,super::legacy_storage_limits(limits),replay_passes,next_pass,last_pass,(decoded,tier1_decoder_state(self)));}
            decoded?;
            return Ok(());
        }
        let decoded = self.decode_legacy_replay(input, replay_passes, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_legacy_contribution_observed(before,input@,passes,super::legacy_storage_limits(limits),replay_passes,next_pass,last_pass,(decoded,tier1_decoder_state(self)));}
        decoded
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_replay_result(tier1_decoder_state(old(self)),input@,replay_passes,super::legacy_storage_limits(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_replay(
            tier1_decoder_state(old(self)), input@, replay_passes,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    fn decode_legacy_replay(
        &mut self,
        input: &[u8],
        replay_passes: u32,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_replay); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before_replay = tier1_decoder_state(self);
            let ghost replay_model = match before_replay.legacy_segment {
                Some(segment) => segment,
                None => crate::specs::part1_legacy_snapshot(crate::specs::Tier1DecoderState { legacy_segment: None, ..before_replay }),
            };
        }
        let had_segment = self.legacy_segment.is_some();
        let mut segment = match self.legacy_segment.take() {
            Some(segment) => segment,
            None => {
                let copied = self.legacy_segment_snapshot();
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_legacy_replay_snapshot_error(before_replay,input@,replay_passes,super::legacy_storage_limits(limits),error);}}
                copied?
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(tier1_decoder_state(self) == (crate::specs::Tier1DecoderState { legacy_segment: None, ..before_replay }));
            assert(legacy_segment_view(&segment) == replay_model);
        }
        if let Err(error) = segment.append(input, replay_passes) {
            if had_segment {
                self.legacy_segment = Some(segment);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(tier1_decoder_state(self) == before_replay);
                crate::specs::part2_legacy_replay_append_error(
                    before_replay, input@, replay_passes, super::legacy_storage_limits(limits), error);
            }
            return Err(error);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(legacy_segment_view(&segment) == (crate::specs::Tier1LegacyFrame {
                input: replay_model.input + input@, passes: replay_passes, ..replay_model
            }));
        }
        let restored = self.restore_legacy_segment(&segment);
        #[cfg(verus_keep_ghost)]
        proof! {if restored.is_err(){crate::specs::part2_legacy_replay_restored(before_replay,input@,replay_passes,super::legacy_storage_limits(limits),(restored,tier1_decoder_state(self)));}}
        restored?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost restore_state=tier1_decoder_state(self);}
        // Layer boundaries can truncate an unterminated arithmetic segment.
        // Replay its bounded prefix so virtual end-fill is never resumed as real input.
        let decoded = self.decode_legacy_segment(&segment.input, segment.passes, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_legacy_replay_segment_observed(before_replay,input@,replay_passes,super::legacy_storage_limits(limits),(Ok(()),restore_state),(decoded,tier1_decoder_state(self)));}
        decoded?;
        self.commit_legacy_replay(segment)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_replay_commit(
            tier1_decoder_state(old(self)), legacy_segment_view(&segment)),
    ))]
    fn commit_legacy_replay(&mut self, segment: LegacySegmentState) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_replay_commit); }
        let last_pass = self
            .next_pass
            .checked_sub(1)
            .ok_or_else(invalid_code_block)?;
        if self.next_pass < self.maximum_passes
            && !self.style.pass_plan(last_pass).terminates_segment
        {
            self.legacy_segment = Some(segment);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_snapshot_result(tier1_decoder_state(self),super::legacy_segment_outcome(result)),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>legacy_segment_view(&value)==crate::specs::part1_legacy_snapshot(tier1_decoder_state(self))},
    ))]
    pub(super) fn legacy_segment_snapshot(&self) -> Result<LegacySegmentState, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        Ok(LegacySegmentState {
            plane: {
                let copied = self.plane.try_duplicate_raw(
                    super::HtRefinementCopyRole::LegacySnapshot,
                    false,
                    true,
                );
                #[cfg(verus_keep_ghost)]
                proof! {if let Err(error)=copied{crate::specs::part2_legacy_snapshot_plane_error(before,error);}}
                copied?
            },
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            bitplane_state: {
                let copied = super::legacy_passes::try_duplicate_bitplane(
                    &self.bitplane_state,
                    super::HtRefinementCopyRole::LegacySnapshot,
                    true,
                );
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::part2_legacy_snapshot_observed(before,super::legacy_bitplane_option_outcome(copied));}
                copied?
            },
            mq_context_state: self.mq_context_state,
            reset_contexts_before_mq: self.reset_contexts_before_mq,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            input: Vec::new(),
            passes: 0,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_restore_result(tier1_decoder_state(old(self)),legacy_segment_view(segment),(result,tier1_decoder_state(final(self)))),
            result==Ok(()) || result==Err(DecodeError::AllocationFailed),
            result!=Err(DecodeError::AllocationFailed) ==> tier1_decoder_state(final(self)) == crate::specs::part1_legacy_restore(
            tier1_decoder_state(old(self)), legacy_segment_view(segment)),
    ))]
    pub(super) fn restore_legacy_segment(
        &mut self,
        segment: &LegacySegmentState,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);let ghost source=legacy_segment_view(segment);}
        let copied = segment.plane.try_duplicate_raw(
            super::HtRefinementCopyRole::LegacyRestore,
            false,
            true,
        );
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=copied{crate::specs::part2_legacy_restore_plane_error(before,source,error);}}
        self.plane = copied?;
        self.next_pass = segment.next_pass;
        self.bitplane = segment.bitplane;
        let copied = super::legacy_passes::try_duplicate_bitplane(
            &segment.bitplane_state,
            super::HtRefinementCopyRole::LegacyRestore,
            true,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(tier1_decoder_state(self)==crate::specs::part2_legacy_restore_partial(before,source));
            crate::specs::part2_legacy_restore_observed(before,source,super::legacy_bitplane_option_outcome(copied));
        }
        self.bitplane_state = copied?;
        self.mq_context_state = segment.mq_context_state;
        self.reset_contexts_before_mq = segment.reset_contexts_before_mq;
        self.decoded_segments = segment.decoded_segments;
        self.decoded_bytes = segment.decoded_bytes;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_plane_segment_result(tier1_decoder_state(old(self)),input@,passes,crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::part1_tier1_segment(
                tier1_decoder_state(old(self)), input@, passes, crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_input_byte_limit(limits),
                crate::limits::resource_work_limit(limits)),
            (result!=Err(DecodeError::AllocationFailed) && (passes == 0 || crate::specs::ht_group_route(tier1_decoder_state(old(self))))) ==>
            (result, tier1_decoder_state(final(self))) == crate::specs::ht_decode_staged_group(
                tier1_decoder_state(old(self)), input@, passes, crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    pub fn decode_segment(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_plane_segment_normal(before,input@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits));}
        if passes == 0 {
            return Err(invalid_code_block());
        }
        if matches!(self.style.block_coding, Tier1BlockCoding::HighThroughput)
            || (matches!(self.style.block_coding, Tier1BlockCoding::Mixed)
                && self.ht_cleanup_plane.is_some())
        {
            let decoded = self.decode_ht_staged_group(input, passes, limits);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_plane_segment_observed(before,input@,passes,crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,tier1_decoder_state(self)));}
            return decoded;
        }
        let decoded = self.decode_legacy_segment(input, u32::from(passes), limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_plane_segment_legacy_observed(before,input@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(decoded,tier1_decoder_state(self)));}
        decoded
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_contribution_work(samples as nat, replay, bytes, previous, maximum),
))]
pub(super) fn legacy_contribution_work(
    samples: usize,
    replay: u32,
    bytes: u64,
    previous: u64,
    maximum: u64,
) -> Result<u64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_contribution_work); }
    let base_work = match (samples as u64).checked_mul(u64::from(replay)) {
        Some(work) => work,
        None => return Err(arithmetic_overflow()),
    };
    let input_work = match base_work.checked_add(bytes) {
        Some(work) => work,
        None => return Err(arithmetic_overflow()),
    };
    let work = match input_work.checked_add(previous) {
        Some(work) => work,
        None => return Err(arithmetic_overflow()),
    };
    if work > maximum {
        return Err(crate::mq::mq_limit(Resource::WorkUnits, maximum, work));
    }
    Ok(work)
}

impl CodeBlockSegmentAccounting {
    pub fn new(maximum_passes: u32, limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if maximum_passes == 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        Ok(Self {
            maximum_passes,
            maximum_bytes: limits.maximum_input_bytes(),
            total_passes: 0,
            total_bytes: 0,
            segments: 0,
        })
    }

    pub fn add_segment(&mut self, passes: u32, bytes: u32) -> Result<Tier1PassKind, DecodeError> {
        if passes == 0 || bytes == 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        let next_passes = self
            .total_passes
            .checked_add(passes)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let next_bytes = self
            .total_bytes
            .checked_add(u64::from(bytes))
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let next_segments = self
            .segments
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if next_passes > self.maximum_passes {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        if next_bytes > self.maximum_bytes {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.maximum_bytes,
                next_bytes,
            ));
        }
        let first_pass = pass_kind(self.total_passes);
        self.total_passes = next_passes;
        self.total_bytes = next_bytes;
        self.segments = next_segments;
        Ok(first_pass)
    }

    pub const fn total_passes(&self) -> u32 {
        self.total_passes
    }

    pub const fn total_bytes(&self) -> u64 {
        self.total_bytes
    }

    pub const fn segments(&self) -> u32 {
        self.segments
    }
}
