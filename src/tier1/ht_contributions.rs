use super::ht_cleanup::{ht_significant_bitplanes, prepare_ht_cleanup_symbols};
use super::ht_refinement::{copy_ht_refinement_bytes, decode_ht_refinement_plane};
use super::ht_segments::{ht_pass_group_from_packet, parse_ht_block_segments};
use super::state::{arithmetic_overflow, ht_statistics_zero, invalid_code_block};
use super::{
    CodeBlockPlane, HtBlockSegments, HtRefinementSegment, HtStreamDirection, HtSubstreamView,
    MAX_HT_REFINEMENT_BYTES, Tier1CodeBlockDecoder, Tier1PassStatistics, Tier1SegmentDecode,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_view, ht_block_segments_view, ht_optional_bytes_view,
    ht_refinement_segment_view, tier1_decoder_state,
};
use crate::{DecodeError, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Tier1CodeBlockDecoder {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::ht_placeholder_group_run(
            tier1_decoder_state(old(self)), placeholder_passes as nat, crate::limits::resource_code_block_pass_limit(limits)),
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn run_ht_placeholder_groups(
        &mut self,
        placeholder_passes: u8,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        let mut remaining = placeholder_passes;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_placeholder_group_run); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant remaining <= placeholder_passes,
                crate::specs::ht_placeholder_group_run(tier1_decoder_state(old(self)), placeholder_passes as nat,
                    crate::limits::resource_code_block_pass_limit(limits))
                    == crate::specs::ht_placeholder_group_run(tier1_decoder_state(self), remaining as nat,
                        crate::limits::resource_code_block_pass_limit(limits)),
            decreases remaining,
        ))]
        while remaining > 0 {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_placeholder_group_run); }
            self.skip_high_throughput_segment(1, limits)?;
            self.skip_high_throughput_segment(2, limits)?;
            remaining = remaining.checked_sub(3).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_placeholder_group_run); }
        Ok(())
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_ht_staged_result(tier1_decoder_state(old(self)),input@,passes,crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::ht_decode_staged_group(
            tier1_decoder_state(old(self)), input@, passes, crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    pub(super) fn decode_ht_staged_group(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_ht_staged_normal(before,input@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
        if passes == 0 || input.is_empty() {
            return Err(invalid_code_block());
        }
        let grouping = ht_pass_group_from_packet(passes)?;
        if grouping.refinement_passes != 0 {
            return Err(invalid_code_block());
        }
        let duplicated = self.try_duplicate(super::HtRefinementCopyRole::HtStaging);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=duplicated{crate::specs::part2_ht_staged_duplicate_error(before,input@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),error);}}
        let mut staged = duplicated?;
        staged.run_ht_placeholder_groups(grouping.placeholder_passes, limits)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost staged_before=tier1_decoder_state(&staged);}
        let decoded_result = staged.decode_high_throughput_segments(input, 1, None, 0, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_ht_staged_observed(before,input@,passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),staged_before,(decoded_result,tier1_decoder_state(&staged)));}
        let decoded = decoded_result?;
        *self = staged;
        Ok(Tier1SegmentDecode {
            passes: u32::from(passes),
            ..decoded
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_ht_segments_result(tier1_decoder_state(old(self)),cleanup@,cleanup_passes,ht_optional_bytes_view(refinement),refinement_passes,
            crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::ht_decode_segments(
            tier1_decoder_state(old(self)), cleanup@, cleanup_passes, ht_optional_bytes_view(refinement),
            refinement_passes, crate::limits::resource_code_block_pass_limit(limits),
            crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    pub fn decode_high_throughput_segments(
        &mut self,
        cleanup: &[u8],
        cleanup_passes: u8,
        refinement: Option<&[u8]>,
        refinement_passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_ht_segments_normal(before,cleanup@,cleanup_passes,ht_optional_bytes_view(refinement),refinement_passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
        if !self.style.block_coding.uses_high_throughput()
            || !self.next_pass.is_multiple_of(3)
            || cleanup_passes != 1
            || refinement_passes > 2
            || (refinement_passes == 0) != refinement.is_none()
        {
            return Err(invalid_code_block());
        }
        if self.ht_sets_seen > 0 && !self.allow_multiple_ht_sets {
            return Err(invalid_code_block());
        }
        let pass_count = u32::from(cleanup_passes)
            .checked_add(u32::from(refinement_passes))
            .ok_or_else(arithmetic_overflow)?;
        let next_pass = self
            .next_pass
            .checked_add(pass_count)
            .ok_or_else(arithmetic_overflow)?;
        if next_pass > self.maximum_passes {
            return Err(invalid_code_block());
        }
        if next_pass > limits.maximum_code_block_passes() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockPasses,
                limit: u64::from(limits.maximum_code_block_passes()),
                actual: u64::from(next_pass),
            });
        }
        let significant_bitplanes = ht_significant_bitplanes(self.maximum_passes)?;
        if refinement_passes > 0 && significant_bitplanes < 2 {
            return Err(invalid_code_block());
        }
        let segments = parse_ht_block_segments(cleanup, refinement, limits)?;
        let next_bytes = self
            .decoded_bytes
            .checked_add(u64::from(segments.bytes()))
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockBytes,
                limit: limits.maximum_code_block_bytes(),
                actual: next_bytes,
            });
        }
        let substantive_passes = u64::from(refinement_passes)
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        let coefficient_work = (self.plane.coefficients().len() as u64)
            .checked_mul(substantive_passes)
            .ok_or_else(arithmetic_overflow)?;
        let work_base = coefficient_work
            .checked_add(u64::from(segments.bytes()))
            .ok_or_else(arithmetic_overflow)?;
        let work = work_base
            .checked_add(u64::from(pass_count))
            .ok_or_else(arithmetic_overflow)?;
        if work > limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: work,
            });
        }
        let skipped = self.next_pass / 3;
        if skipped > u32::from(u16::MAX) {
            return Err(arithmetic_overflow());
        }
        let skipped_bitplanes = skipped as u16;
        let missing_msbs = self.zero_bitplanes.unwrap_or(0);
        let maximum_u = crate::refinement::part15_cleanup_u_bound(
            missing_msbs,
            skipped_bitplanes,
            self.ht_magnitude_bound,
        );
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost admitted=(ht_block_segments_view(&segments),pass_count,maximum_u,skipped_bitplanes);}
        let decoded = self.decode_ht_coefficient_symbols(
            segments,
            pass_count,
            maximum_u,
            skipped_bitplanes,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_ht_segments_observed(before,cleanup@,cleanup_passes,ht_optional_bytes_view(refinement),refinement_passes,crate::limits::resource_code_block_pass_limit(limits),
        crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),admitted,(decoded,tier1_decoder_state(self)));}
        decoded
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_ht_coeff_result(tier1_decoder_state(old(self)),ht_block_segments_view(&segments),pass_count,maximum_u,skipped_bitplanes,
            crate::limits::resource_work_limit(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::ht_coefficient_symbols(
                tier1_decoder_state(old(self)), ht_block_segments_view(&segments),
                pass_count, maximum_u, skipped_bitplanes, crate::limits::resource_work_limit(limits)),
    ))]
    pub(super) fn decode_ht_coefficient_symbols(
        &mut self,
        segments: HtBlockSegments<'_>,
        pass_count: u32,
        maximum_u: u8,
        skipped_bitplanes: u16,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_ht_coeff_normal(before,ht_block_segments_view(&segments),pass_count,maximum_u,skipped_bitplanes,crate::limits::resource_work_limit(limits));}
        let prepared_result = prepare_ht_cleanup_symbols(
            &self.plane,
            segments.cleanup(),
            self.maximum_passes,
            maximum_u,
            skipped_bitplanes,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=prepared_result {crate::specs::part2_ht_coeff_prepare_error(before,ht_block_segments_view(&segments),pass_count,maximum_u,skipped_bitplanes,crate::limits::resource_work_limit(limits),error);}}
        let (plane, cleanup_plane, statistics, decoded_bitplanes) = prepared_result?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost prepared=(code_block_plane_view(&plane),code_block_plane_view(&cleanup_plane),statistics,decoded_bitplanes);}
        let mut output = plane;
        let mut statistics = statistics;
        self.clear_ht_refinement_state();
        if let Some(refinement) = segments.refinement() {
            let following_passes = pass_count.saturating_sub(1);
            if following_passes > u32::from(u8::MAX) {
                return Err(arithmetic_overflow());
            }
            let refinement_passes = following_passes as u8;
            let refined_result = decode_ht_refinement_plane(
                &cleanup_plane,
                refinement,
                refinement_passes,
                decoded_bitplanes,
                self.style.vertical_causal_context,
                limits,
            );
            #[cfg(verus_keep_ghost)]
            proof! {if let Err(error)=refined_result {crate::specs::part2_ht_coeff_refinement_error(before,ht_block_segments_view(&segments),pass_count,maximum_u,skipped_bitplanes,
            crate::limits::resource_work_limit(limits),prepared,ht_refinement_segment_view(&refinement),error);}}
            let (refined, refinement_statistics) = refined_result?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost refinement_output=(code_block_plane_view(&refined),refinement_statistics);}
            output = refined;
            statistics.merge(refinement_statistics)?;
            let copied = copy_ht_refinement_bytes(
                refinement.encoded(),
                super::HtRefinementCopyRole::CleanupRetention,
            );
            #[cfg(verus_keep_ghost)]
            proof! {if let Err(error)=copied{crate::specs::part2_ht_coeff_bytes_error(before,ht_block_segments_view(&segments),pass_count,maximum_u,skipped_bitplanes,
            crate::limits::resource_work_limit(limits),prepared,ht_refinement_segment_view(&refinement),
            refinement_output,error);}}
            self.ht_refinement_data = copied?;
            self.ht_refinement_passes = refinement_passes;
        }
        self.store_ht_coefficient_symbols(
            output,
            cleanup_plane,
            statistics,
            decoded_bitplanes,
            pass_count,
            segments.bytes(),
            segments.refinement().is_some(),
        )
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures tier1_decoder_state(final(self)) == crate::specs::ht_clear_refinement_state(tier1_decoder_state(old(self))),
    ))]
    fn clear_ht_refinement_state(&mut self) {
        self.ht_refinement_data.clear();
        self.ht_refinement_passes = 0;
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "This shared production commit stage preserves the actual ordered fields and accounting inputs."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::ht_store_coefficient_symbols(
            tier1_decoder_state(old(self)), code_block_plane_view(&output), code_block_plane_view(&cleanup_plane),
            statistics, decoded_bitplanes, pass_count, bytes, has_refinement),
    ))]
    fn store_ht_coefficient_symbols(
        &mut self,
        output: CodeBlockPlane,
        cleanup_plane: CodeBlockPlane,
        statistics: Tier1PassStatistics,
        decoded_bitplanes: u16,
        pass_count: u32,
        bytes: u32,
        has_refinement: bool,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        self.plane = output;
        self.ht_cleanup_plane = Some(cleanup_plane);
        self.ht_current_set_has_cleanup = true;
        self.ht_decoded_bitplanes = decoded_bitplanes;
        self.ht_sets_seen = self
            .ht_sets_seen
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        self.next_pass = self
            .next_pass
            .checked_add(pass_count)
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_segments = self
            .decoded_segments
            .checked_add(if has_refinement { 2 } else { 1 })
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_bytes = self
            .decoded_bytes
            .checked_add(u64::from(bytes))
            .ok_or_else(arithmetic_overflow)?;
        Ok(Tier1SegmentDecode {
            passes: pass_count,
            bytes,
            statistics,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::ht_skip_segment(
            tier1_decoder_state(old(self)), passes, crate::limits::resource_code_block_pass_limit(limits)),
    ))]
    pub fn skip_high_throughput_segment(
        &mut self,
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        if !self.style.block_coding.uses_high_throughput() || passes == 0 || passes > 2 {
            return Err(invalid_code_block());
        }
        let phase = self.next_pass % 3;
        if (phase == 0 && passes != 1)
            || (phase != 0 && u32::from(passes) > 3_u32.saturating_sub(phase))
        {
            return Err(invalid_code_block());
        }
        let next_pass = self
            .next_pass
            .checked_add(u32::from(passes))
            .ok_or_else(arithmetic_overflow)?;
        if next_pass > self.maximum_passes {
            return Err(invalid_code_block());
        }
        if next_pass > limits.maximum_code_block_passes() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockPasses,
                limit: u64::from(limits.maximum_code_block_passes()),
                actual: u64::from(next_pass),
            });
        }
        if phase == 0 {
            if !crate::refinement::ht_replacement_allowed(
                phase,
                self.ht_current_set_has_cleanup,
                true,
            ) {
                return Err(invalid_code_block());
            }
            if self.ht_sets_seen > 0 {
                if !crate::refinement::ht_multiple_set_allowed(
                    self.ht_sets_seen,
                    self.allow_multiple_ht_sets,
                ) {
                    return Err(invalid_code_block());
                }
                self.ht_sets_seen = self
                    .ht_sets_seen
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
            self.ht_current_set_has_cleanup = false;
            self.clear_ht_refinement_state();
        } else if self.ht_current_set_has_cleanup {
            return Err(invalid_code_block());
        }
        self.next_pass = next_pass;
        self.decoded_segments = self
            .decoded_segments
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(Tier1SegmentDecode {
            passes: u32::from(passes),
            bytes: 0,
            statistics: ht_statistics_zero(),
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::ht_has_current_cleanup(tier1_decoder_state(self)),
    ))]
    pub const fn ht_current_set_has_cleanup(&self) -> bool {
        self.ht_current_set_has_cleanup
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_ht_replay_result(tier1_decoder_state(old(self)),input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
            (result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::ht_decode_refinement_contribution(
            tier1_decoder_state(old(self)), input@, passes,
            crate::limits::resource_code_block_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    pub fn decode_high_throughput_refinement(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost start = tier1_decoder_state(self); }
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_replay_entry(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
        if !self.style.block_coding.uses_high_throughput()
            || self.next_pass == 0
            || !self.ht_current_set_has_cleanup
            || self.next_pass.is_multiple_of(3)
            || passes == 0
            || match self.ht_refinement_passes.checked_add(passes) {
                Some(value) => value > 2,
                None => true,
            }
        {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_ht_replay_primary_consequence(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
            (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),start));}
            return Err(invalid_code_block());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if start.ht_cleanup_plane.is_none(){crate::specs::part2_ht_replay_primary_consequence(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
                (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),start));}
            if start.ht_cleanup_plane.is_some() && start.decoded_bytes as nat+(input@.len() as u64) as nat>u64::MAX{
                crate::specs::part2_ht_replay_primary_consequence(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
                    (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),start));
            }
        }
        let cleanup_plane = self
            .ht_cleanup_plane
            .as_ref()
            .ok_or_else(invalid_code_block)?;
        let next_bytes = self
            .decoded_bytes
            .checked_add(input.len() as u64)
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_ht_replay_primary_consequence(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
            (Err(DecodeError::LimitExceeded {resource:Resource::CodeBlockBytes,limit:crate::limits::resource_code_block_byte_limit(limits),actual:next_bytes}),start));}
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockBytes,
                limit: limits.maximum_code_block_bytes(),
                actual: next_bytes,
            });
        }
        let copied = copy_ht_refinement_bytes(
            &self.ht_refinement_data,
            super::HtRefinementCopyRole::RetainedReplay,
        );
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=copied{crate::specs::part2_ht_replay_copy_error(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),
        crate::limits::resource_work_limit(limits),error);
        crate::specs::part2_ht_replay_primary_consequence(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(Err(error),start));}}
        let mut refinement_data = copied?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(refinement_data@ == start.ht_refinement_data); }
        refinement_data.extend_from_slice(input);
        #[cfg(verus_keep_ghost)]
        proof! { assert(refinement_data@ == start.ht_refinement_data + input@); }
        if refinement_data.len() > MAX_HT_REFINEMENT_BYTES {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_replay_late_error(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));}
            return Err(invalid_code_block());
        }
        let refinement_passes =
            crate::refinement::ht_refinement_pass_total(self.ht_refinement_passes, passes);
        if refinement_data.is_empty() {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost t:crate::specs::Part2ReplayFinish;
                let ghost mut prior=tier1_decoder_state(self);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_ht_replay_admission_fields(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits));
                t=crate::specs::part2_replay_finish_empty(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits));
            }
            self.ht_refinement_passes = refinement_passes;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_replay_advance(t,2,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);
                if self.next_pass as nat+passes as nat>u32::MAX{crate::specs::part2_replay_counter_error(t,3,prior);}
            }
            self.next_pass = self
                .next_pass
                .checked_add(u32::from(passes))
                .ok_or_else(arithmetic_overflow)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_replay_advance(t,3,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);
                if self.decoded_segments==u32::MAX{crate::specs::part2_replay_counter_error(t,4,prior);}
            }
            self.decoded_segments = self
                .decoded_segments
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_replay_advance(t,4,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);
                crate::specs::part2_replay_advance(t,5,prior,prior);
                crate::specs::part2_replay_return(t,prior);
            }
            return Ok(Tier1SegmentDecode {
                passes: u32::from(passes),
                bytes: 0,
                statistics: ht_statistics_zero(),
            });
        }
        let segment = HtRefinementSegment {
            encoded: &refinement_data,
            significance_propagation: HtSubstreamView {
                bytes: &refinement_data,
                offset: 0,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: &refinement_data,
                offset: 0,
                direction: HtStreamDirection::Reverse,
            },
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(code_block_plane_view(cleanup_plane) == start.ht_cleanup_plane.get_Some_0());
            assert(refinement_passes as nat == start.ht_refinement_passes as nat + passes as nat);
            assert(ht_refinement_segment_view(&segment) == crate::specs::HtRefinementSegmentState {
                encoded: refinement_data@,
                significance_propagation: crate::specs::HtSubstreamState { bytes: refinement_data@, offset: 0, forward: true },
                magnitude_refinement: crate::specs::HtSubstreamState { bytes: refinement_data@, offset: 0, forward: false },
            });
        }
        let replayed = decode_ht_refinement_plane(
            cleanup_plane,
            segment,
            refinement_passes,
            self.ht_decoded_bitplanes,
            self.style.vertical_causal_context,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_ht_replay_admission_fields(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits));
            if let Err(error)=replayed {
                crate::specs::part2_ht_replay_error(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
                    (code_block_plane_view(cleanup_plane),ht_refinement_segment_view(&segment),refinement_passes),error);
                crate::specs::part2_ht_replay_primary_consequence(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),(Err(error),start));
            }
        }
        let (plane, statistics) = replayed?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost t:crate::specs::Part2ReplayFinish;
            let ghost mut prior=tier1_decoder_state(self);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            t=crate::specs::part2_replay_finish_from_child(start,input@,passes,crate::limits::resource_code_block_byte_limit(limits),crate::limits::resource_work_limit(limits),
                (code_block_plane_view(cleanup_plane),ht_refinement_segment_view(&segment),refinement_passes),code_block_plane_view(&plane),statistics);
        }
        self.plane = plane;
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_replay_advance(t,0,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);}
        self.ht_refinement_data = refinement_data;
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_replay_advance(t,1,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);}
        self.ht_refinement_passes = refinement_passes;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_replay_advance(t,2,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);
            if self.next_pass as nat+passes as nat>u32::MAX{crate::specs::part2_replay_counter_error(t,3,prior);}
        }
        self.next_pass = self
            .next_pass
            .checked_add(u32::from(passes))
            .ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_replay_advance(t,3,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);
            if self.decoded_segments==u32::MAX{crate::specs::part2_replay_counter_error(t,4,prior);}
        }
        self.decoded_segments = self
            .decoded_segments
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_replay_advance(t,4,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);}
        self.decoded_bytes = next_bytes;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_replay_advance(t,5,prior,tier1_decoder_state(self));prior=tier1_decoder_state(self);
            if input@.len()>u32::MAX{crate::specs::part2_replay_counter_error(t,6,prior);}
            else{crate::specs::part2_replay_return(t,prior);}
        }
        Ok(Tier1SegmentDecode {
            passes: u32::from(passes),
            bytes: u32::try_from(input.len()).map_err(|_| arithmetic_overflow())?,
            statistics,
        })
    }
}
