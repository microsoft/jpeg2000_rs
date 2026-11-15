use super::legacy_passes::{
    decode_cleanup_pass_with_style, decode_magnitude_refinement_pass_with_style,
    decode_raw_magnitude_refinement_pass, decode_raw_significance_propagation_pass,
    decode_significance_propagation_pass_with_style, legacy_bitplane_from_plane,
};
use super::raw::raw_reader_from_input;
use super::state::{
    arithmetic_overflow, ht_statistics_zero, initialize_tier1_contexts, invalid_code_block,
    reset_tier1_contexts_after_pass,
};
use super::{
    RawBitReader, Tier1CodeBlockDecoder, Tier1CodingMode, Tier1PassKind, Tier1PassStatistics,
    Tier1SegmentDecode,
};
#[cfg(verus_keep_ghost)]
use super::{raw_bit_reader_view, tier1_decoder_state};
use crate::mq::MqDecoder;
use crate::{DecodeError, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Tier1CodeBlockDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_legacy_segment_admission(
            tier1_decoder_state(self), input@, pass_count,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits)),
    ))]
    fn validate_legacy_segment(
        &self,
        input: &[u8],
        pass_count: u32,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_segment_admission); }
        // Later terminated passes can carry no bytes; an initial empty block cannot.
        if pass_count == 0 || (input.is_empty() && self.next_pass == 0) {
            return Err(invalid_code_block());
        }
        let next_pass = self
            .next_pass
            .checked_add(pass_count)
            .ok_or_else(arithmetic_overflow)?;
        if next_pass > limits.maximum_code_block_passes() {
            return Err(crate::mq::mq_limit(
                Resource::CodeBlockPasses,
                u64::from(limits.maximum_code_block_passes()),
                u64::from(next_pass),
            ));
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
        if next_pass > self.maximum_passes
            || self.style.segment_passes(self.next_pass, pass_count) != pass_count
        {
            return Err(invalid_code_block());
        }
        if input.is_empty()
            && next_pass != self.maximum_passes
            && !self.style.pass_plan(next_pass - 1).terminates_segment
        {
            return Err(invalid_code_block());
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_segment_result(tier1_decoder_state(old(self)),input@,pass_count,super::legacy_storage_limits(limits),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_segment(
            tier1_decoder_state(old(self)), input@, pass_count,
            crate::limits::resource_code_block_pass_limit(limits), crate::limits::resource_code_block_byte_limit(limits),
            crate::limits::resource_input_byte_limit(limits), crate::limits::resource_work_limit(limits)),
    ))]
    pub(super) fn decode_legacy_segment(
        &mut self,
        input: &[u8],
        pass_count: u32,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);let ghost caps=super::legacy_storage_limits(limits);}
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_legacy_segment_prepared_equation(before,input@,pass_count,caps);}
        let admitted = self.validate_legacy_segment(input, pass_count, limits);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=admitted{
            crate::specs::part2_legacy_segment_prepared_error(before,input@,pass_count,caps,error);
            crate::specs::part2_legacy_segment_primary_consequence(before,input@,pass_count,caps,(Err(error),tier1_decoder_state(self)));
        }}
        admitted?;
        let coding_mode = self.style.pass_plan(self.next_pass).coding_mode;
        let statistics;
        if matches!(coding_mode, Tier1CodingMode::Mq) {
            let constructed = crate::mq::mq_from_input(
                input,
                limits.maximum_input_bytes(),
                limits.maximum_work_units(),
            );
            #[cfg(verus_keep_ghost)]
            proof! {if let Err(error)=constructed{
                crate::specs::part2_legacy_segment_prepared_error(before,input@,pass_count,caps,error);
                crate::specs::part2_legacy_segment_primary_consequence(before,input@,pass_count,caps,(Err(error),tier1_decoder_state(self)));
            }}
            let mut decoder = constructed?;
            if self.reset_contexts_before_mq || self.mq_context_state.is_none() {
                initialize_tier1_contexts(&mut decoder)?;
                self.reset_contexts_before_mq = false;
            } else if let Some(context_state) = self.mq_context_state {
                decoder.restore_context_state(context_state);
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost ready=crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
            symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(&decoder)),statistics:crate::specs::tier1_statistics_zero()};}
            let decoded = self.decode_mq_segment_passes(&mut decoder, pass_count);
            #[cfg(verus_keep_ghost)]
            proof! {
                let inner=(decoded,tier1_decoder_state(self),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(&decoder)));
                crate::specs::part2_legacy_segment_observed(before,input@,pass_count,caps,ready,inner);
                crate::specs::part2_legacy_segment_finish_equation(before,input@,pass_count,inner);
                crate::specs::part2_legacy_segment_primary_consequence(before,input@,pass_count,caps,crate::specs::part2_legacy_segment_finish(before,input@,pass_count,inner));
            }
            statistics = decoded?;
            if self.style.predictable_termination {
                decoder.validate_predictable_termination()?;
            }
            self.mq_context_state = Some(decoder.context_state());
        } else {
            let constructed = raw_reader_from_input(
                input,
                limits.maximum_input_bytes(),
                limits.maximum_work_units(),
            );
            #[cfg(verus_keep_ghost)]
            proof! {if let Err(error)=constructed{
                crate::specs::part2_legacy_segment_prepared_error(before,input@,pass_count,caps,error);
                crate::specs::part2_legacy_segment_primary_consequence(before,input@,pass_count,caps,(Err(error),tier1_decoder_state(self)));
            }}
            let mut reader = constructed?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost ready=crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
            symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(&reader)),statistics:crate::specs::tier1_statistics_zero()};}
            let decoded = self.decode_raw_segment_passes(&mut reader, pass_count);
            #[cfg(verus_keep_ghost)]
            proof! {
                let inner=(decoded,tier1_decoder_state(self),crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(&reader)));
                crate::specs::part2_legacy_segment_observed(before,input@,pass_count,caps,ready,inner);
                crate::specs::part2_legacy_segment_finish_equation(before,input@,pass_count,inner);
                crate::specs::part2_legacy_segment_primary_consequence(before,input@,pass_count,caps,crate::specs::part2_legacy_segment_finish(before,input@,pass_count,inner));
            }
            statistics = decoded?;
            if self.style.predictable_termination {
                reader.validate_predictable_termination()?;
            }
        }

        self.commit_legacy_segment(input.len(), pass_count, statistics)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_segment_account(
            tier1_decoder_state(old(self)), bytes as nat, pass_count, statistics),
    ))]
    pub(super) fn commit_legacy_segment(
        &mut self,
        bytes: usize,
        pass_count: u32,
        statistics: Tier1PassStatistics,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_segment_account); }
        self.decoded_segments = self
            .decoded_segments
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_bytes = self
            .decoded_bytes
            .checked_add(bytes as u64)
            .ok_or_else(arithmetic_overflow)?;
        Ok(Tier1SegmentDecode {
            passes: pass_count,
            bytes: match u32::try_from(bytes) {
                Ok(bytes) => bytes,
                Err(_) => return Err(arithmetic_overflow()),
            },
            statistics,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_inner_body_result(crate::specs::Part1LegacySegmentRun {
                decoder:tier1_decoder_state(old(self)),symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),statistics:crate::specs::tier1_statistics_zero()},
            pass_count,(result,tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
            == crate::specs::part1_legacy_segment_finish(crate::specs::part1_legacy_segment_run(
                crate::specs::Part1LegacySegmentRun {
                    decoder: tier1_decoder_state(old(self)), symbols: crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics: crate::specs::tier1_statistics_zero(),
                }, pass_count as nat)),
    ))]
    fn decode_mq_segment_passes(
        &mut self,
        decoder: &mut MqDecoder<'_>,
        pass_count: u32,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut statistics = ht_statistics_zero();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = crate::specs::Part1LegacySegmentRun {
                decoder: tier1_decoder_state(self), symbols: crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)), statistics,
            };
            let ghost goal = crate::specs::part1_legacy_segment_run(initial, pass_count as nat);
            let ghost root=|calls|crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls);
            let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_legacy_inner_body_start(initial,pass_count);}
        let mut decoded = 0_u32;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant decoded <= pass_count,
                forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(calls)==crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls),
                crate::specs::part2_tier1_phase(root,prefix,|calls|crate::specs::part2_tier1_storage_bind(
                    crate::specs::part2_legacy_inner_fold(crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                        symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics},(pass_count-decoded) as nat,calls),
                    |effect:crate::specs::Part1LegacySegmentEffect,rest|Some((Ok(crate::specs::part1_legacy_segment_finish(effect)),rest)))),
                initial == (crate::specs::Part1LegacySegmentRun {
                    decoder: tier1_decoder_state(old(self)), symbols: crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics: crate::specs::tier1_statistics_zero(),
                }),
                goal == crate::specs::part1_legacy_segment_run(initial, pass_count as nat),
                goal == crate::specs::part1_legacy_segment_run(crate::specs::Part1LegacySegmentRun {
                    decoder: tier1_decoder_state(self), symbols: crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)), statistics,
                }, (pass_count - decoded) as nat),
            decreases pass_count - decoded,
        ))]
        while decoded < pass_count {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_step=crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
            symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics};let ghost remaining=(pass_count-decoded) as nat;}
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_tier1_phase_eta(root,|calls|crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls),prefix,
                    |calls|crate::specs::part2_tier1_storage_bind(crate::specs::part2_legacy_inner_fold(before_step,remaining,calls),
                        |effect:crate::specs::Part1LegacySegmentEffect,rest|Some((Ok(crate::specs::part1_legacy_segment_finish(effect)),rest))));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_legacy_segment_run);
                reveal(crate::specs::part1_legacy_segment_step);
            }
            let plan = self.style.pass_plan(self.next_pass);
            if !matches!(plan.coding_mode, Tier1CodingMode::Mq) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_legacy_inner_step_normal(before_step);
                    let effect=(Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before_step);
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,effect);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,effect);
                }
                return Err(invalid_code_block());
            }
            let pass = self.decode_mq_pass(decoder, plan.kind);
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost pass_effect=(pass,tier1_decoder_state(self),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)));
            let ghost expected=crate::specs::part2_legacy_step_after_pass(before_step,plan.kind,pass_effect);}
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_legacy_inner_step_observed(before_step,plan.kind,pass_effect);
                if pass.is_err(){
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,expected);
                }
            }
            let merged = statistics.merge(pass?);
            #[cfg(verus_keep_ghost)]
            proof! {
                if merged.is_err(){
                    assert(expected==(merged,crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                        symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics}));
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,expected);
                }
            }
            merged?;
            let advanced = self.advance_pass(plan.kind);
            #[cfg(verus_keep_ghost)]
            proof! {
                if advanced.is_err(){
                    assert(expected==(advanced,crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                        symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics}));
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,expected);
                }
            }
            advanced?;
            reset_tier1_contexts_after_pass(decoder, self.style)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(expected==(Ok(()),crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics}));
                prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                crate::specs::part2_tier1_phase_eta(|calls|crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls),root,prefix,
                    |calls|crate::specs::part2_tier1_storage_bind(crate::specs::part2_legacy_inner_fold(expected.1,(remaining-1) as nat,calls),
                        |effect:crate::specs::Part1LegacySegmentEffect,rest|Some((Ok(crate::specs::part1_legacy_segment_finish(effect)),rest))));
            }
            decoded = decoded.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_segment_run);
            crate::specs::part2_legacy_inner_body_end(initial,pass_count,crate::specs::Part1LegacySegmentRun {
                decoder:tier1_decoder_state(self),symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics},prefix);
        }
        Ok(statistics)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_inner_body_result(crate::specs::Part1LegacySegmentRun {
                decoder:tier1_decoder_state(old(self)),symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))),statistics:crate::specs::tier1_statistics_zero()},
            pass_count,(result,tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(final(reader))))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self)),
            crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(final(reader))))
            == crate::specs::part1_legacy_segment_finish(crate::specs::part1_legacy_segment_run(
                crate::specs::Part1LegacySegmentRun {
                    decoder: tier1_decoder_state(old(self)), symbols: crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))),
                    statistics: crate::specs::tier1_statistics_zero(),
                }, pass_count as nat)),
    ))]
    fn decode_raw_segment_passes(
        &mut self,
        reader: &mut RawBitReader<'_>,
        pass_count: u32,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut statistics = ht_statistics_zero();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = crate::specs::Part1LegacySegmentRun {
                decoder: tier1_decoder_state(self), symbols: crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)), statistics,
            };
            let ghost goal = crate::specs::part1_legacy_segment_run(initial, pass_count as nat);
            let ghost root=|calls|crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls);
            let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_legacy_inner_body_start(initial,pass_count);}
        let mut decoded = 0_u32;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant decoded <= pass_count,
                forall|calls:Seq<crate::specs::Part2Tier1StorageEvent>| #[trigger] root(calls)==crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls),
                crate::specs::part2_tier1_phase(root,prefix,|calls|crate::specs::part2_tier1_storage_bind(
                    crate::specs::part2_legacy_inner_fold(crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                        symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)),statistics},(pass_count-decoded) as nat,calls),
                    |effect:crate::specs::Part1LegacySegmentEffect,rest|Some((Ok(crate::specs::part1_legacy_segment_finish(effect)),rest)))),
                initial == (crate::specs::Part1LegacySegmentRun {
                    decoder: tier1_decoder_state(old(self)), symbols: crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))),
                    statistics: crate::specs::tier1_statistics_zero(),
                }),
                goal == crate::specs::part1_legacy_segment_run(initial, pass_count as nat),
                goal == crate::specs::part1_legacy_segment_run(crate::specs::Part1LegacySegmentRun {
                    decoder: tier1_decoder_state(self), symbols: crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)), statistics,
                }, (pass_count - decoded) as nat),
            decreases pass_count - decoded,
        ))]
        while decoded < pass_count {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_step=crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
            symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)),statistics};let ghost remaining=(pass_count-decoded) as nat;}
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_tier1_phase_eta(root,|calls|crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls),prefix,
                    |calls|crate::specs::part2_tier1_storage_bind(crate::specs::part2_legacy_inner_fold(before_step,remaining,calls),
                        |effect:crate::specs::Part1LegacySegmentEffect,rest|Some((Ok(crate::specs::part1_legacy_segment_finish(effect)),rest))));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_legacy_segment_run);
                reveal(crate::specs::part1_legacy_segment_step);
            }
            let plan = self.style.pass_plan(self.next_pass);
            if !matches!(plan.coding_mode, Tier1CodingMode::Raw) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_legacy_inner_step_normal(before_step);
                    let effect=(Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before_step);
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,effect);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,effect);
                }
                return Err(invalid_code_block());
            }
            let pass = self.decode_raw_pass(reader, plan.kind);
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost pass_effect=(pass,tier1_decoder_state(self),crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)));
            let ghost expected=crate::specs::part2_legacy_step_after_pass(before_step,plan.kind,pass_effect);}
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_legacy_inner_step_observed(before_step,plan.kind,pass_effect);
                if pass.is_err(){
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,expected);
                }
            }
            let merged = statistics.merge(pass?);
            #[cfg(verus_keep_ghost)]
            proof! {
                if merged.is_err(){
                    assert(expected==(merged,crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                        symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)),statistics}));
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,expected);
                }
            }
            merged?;
            let advanced = self.advance_pass(plan.kind);
            #[cfg(verus_keep_ghost)]
            proof! {
                if advanced.is_err(){
                    assert(expected==(advanced,crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                        symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)),statistics}));
                    prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                    crate::specs::part2_legacy_inner_body_finish(initial,pass_count,prefix,expected);
                }
            }
            advanced?;
            if self.style.reset_contexts {
                self.reset_contexts_before_mq = true;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(expected==(Ok(()),crate::specs::Part1LegacySegmentRun {decoder:tier1_decoder_state(self),
                    symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)),statistics}));
                prefix=crate::specs::part2_legacy_inner_body_step(initial,pass_count,before_step,remaining,prefix,expected);
                crate::specs::part2_tier1_phase_eta(|calls|crate::specs::part2_legacy_inner_body_run(initial,pass_count,calls),root,prefix,
                    |calls|crate::specs::part2_tier1_storage_bind(crate::specs::part2_legacy_inner_fold(expected.1,(remaining-1) as nat,calls),
                        |effect:crate::specs::Part1LegacySegmentEffect,rest|Some((Ok(crate::specs::part1_legacy_segment_finish(effect)),rest))));
            }
            decoded = decoded.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_segment_run);
            crate::specs::part2_legacy_inner_body_end(initial,pass_count,crate::specs::Part1LegacySegmentRun {
                decoder:tier1_decoder_state(self),symbols:crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader)),statistics},prefix);
        }
        Ok(statistics)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_pass_result(tier1_decoder_state(old(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),kind,
            (result,tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
            == crate::specs::part1_legacy_decode_pass(tier1_decoder_state(old(self)),
                crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), kind),
    ))]
    fn decode_mq_pass(
        &mut self,
        decoder: &mut MqDecoder<'_>,
        kind: Tier1PassKind,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);let ghost symbols=crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder));}
        let ensured = self.ensure_bitplane_state();
        #[cfg(verus_keep_ghost)]
        proof! {
            let ready=(ensured,tier1_decoder_state(self));
            crate::specs::part2_legacy_mq_ready_contract(before,crate::mq::mq_decoder_view(decoder),kind,ready);
        }
        ensured?;
        let state = self
            .bitplane_state
            .as_mut()
            .ok_or_else(invalid_code_block)?;
        match kind {
            Tier1PassKind::SignificancePropagation => {
                decode_significance_propagation_pass_with_style(
                    &mut self.plane,
                    state,
                    decoder,
                    self.orientation,
                    self.style,
                )
            }
            Tier1PassKind::MagnitudeRefinement => decode_magnitude_refinement_pass_with_style(
                &mut self.plane,
                state,
                decoder,
                self.style,
            ),
            Tier1PassKind::Cleanup => decode_cleanup_pass_with_style(
                &mut self.plane,
                state,
                decoder,
                self.orientation,
                self.style,
            ),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_pass_result(tier1_decoder_state(old(self)),crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))),kind,
            (result,tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(final(reader))))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self)),
            crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(final(reader))))
            == crate::specs::part1_legacy_decode_pass(tier1_decoder_state(old(self)),
                crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))), kind),
    ))]
    fn decode_raw_pass(
        &mut self,
        reader: &mut RawBitReader<'_>,
        kind: Tier1PassKind,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);let ghost symbols=crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(reader));}
        let ensured = self.ensure_bitplane_state();
        #[cfg(verus_keep_ghost)]
        proof! {
            let ready=(ensured,tier1_decoder_state(self));
            crate::specs::part2_legacy_raw_ready_contract(before,raw_bit_reader_view(reader),kind,ready);
        }
        ensured?;
        let state = self
            .bitplane_state
            .as_mut()
            .ok_or_else(invalid_code_block)?;
        match kind {
            Tier1PassKind::SignificancePropagation => decode_raw_significance_propagation_pass(
                &mut self.plane,
                state,
                reader,
                self.orientation,
                self.style,
            ),
            Tier1PassKind::MagnitudeRefinement => {
                decode_raw_magnitude_refinement_pass(&mut self.plane, state, reader, self.style)
            }
            Tier1PassKind::Cleanup => Err(invalid_code_block()),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_legacy_ensure_result(tier1_decoder_state(old(self)),(result,tier1_decoder_state(final(self)))),
            result!=Err(DecodeError::AllocationFailed) ==> (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_ensure_bitplane(tier1_decoder_state(old(self))),
    ))]
    fn ensure_bitplane_state(&mut self) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=tier1_decoder_state(self);}
        if self.bitplane_state.is_none() {
            let constructed = legacy_bitplane_from_plane(&self.plane, self.bitplane);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_legacy_ensure_observed(before,super::legacy_bitplane_outcome(constructed));}
            self.bitplane_state = Some(constructed?);
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_legacy_ensure_present(before);}
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tier1_decoder_state(final(self))) == crate::specs::part1_legacy_advance(tier1_decoder_state(old(self)), kind),
    ))]
    fn advance_pass(&mut self, kind: Tier1PassKind) -> Result<(), DecodeError> {
        self.next_pass = self
            .next_pass
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if matches!(kind, Tier1PassKind::Cleanup) {
            self.bitplane_state = None;
            if self.next_pass < self.maximum_passes {
                self.bitplane = self
                    .bitplane
                    .checked_sub(1)
                    .ok_or_else(invalid_code_block)?;
            }
        }
        Ok(())
    }
}
