//! MCT/MCC fragment assembly, numeric decoding and marker parsing.

use super::mct::u16_lists_equal;
#[cfg(verus_keep_ghost)]
use super::mct_copy::copy_outcome;
use super::mct_copy::{copy_flat, reserve_values};
use super::mct_resolution::{u8_list_contains, validate_parallel_collections};
use super::reader::{read_u16, read_u32, read_u64, signed_u16, signed_u32};
use super::{
    DecodeError, FreshMarkerPath, MCC, MCT, MCT_FIXED_BITS, MalformedKind, MccFragment, MctArray,
    MctArrayKind, MctCollectionReference, MctCollectionReferenceTransform, MctCopyPath,
    MctFragment, MctNumericFormat, MctRecord, MctWavelet, MctWaveletType, Parser, Resource,
    Segment,
};
#[cfg(verus_keep_ghost)]
use super::{
    marker_words_outcome, mcc_collection_outcome, mcc_collection_reference_view,
    mcc_collection_references_view, mcc_fragment_outcome, mcc_fragment_view, mcc_pending_view,
    mcc_record_outcome, mcc_reference_transform_view, mct_array_outcome, mct_array_view,
    mct_fixed_precision_is_q32, mct_fragment_outcome, mct_fragment_view, mct_pending_view,
    mct_wavelet_view, segment_tail_outcome, segment_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mct_fragment_find(mct_pending_view(pending@), index, 0),
        match result { Some(position) => position < pending.len(), None => true },
))]
pub(super) fn find_mct_fragment(pending: &[MctFragment], index: u8) -> Option<usize> {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= pending.len(),
            crate::specs::part1_mct_fragment_find(mct_pending_view(pending@), index, 0)
                == crate::specs::part1_mct_fragment_find(mct_pending_view(pending@), index, position as nat),
        decreases pending.len() - position,
    ))]
    while position < pending.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_fragment_find, 1); reveal(mct_fragment_view); }
        if (pending[position].descriptor & 255) as u8 == index {
            return Some(position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_mct_fragment_find, 1); }
    None
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mcc_fragment_find(mcc_pending_view(pending@), index, 0),
        match result { Some(position) => position < pending.len(), None => true },
))]
pub(super) fn find_mcc_fragment(pending: &[MccFragment], index: u8) -> Option<usize> {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= pending.len(),
            crate::specs::part1_mcc_fragment_find(mcc_pending_view(pending@), index, 0)
                == crate::specs::part1_mcc_fragment_find(mcc_pending_view(pending@), index, position as nat),
        decreases pending.len() - position,
    ))]
    while position < pending.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mcc_fragment_find, 1); reveal(mcc_fragment_view); }
        if pending[position].record_index == index {
            return Some(position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_mcc_fragment_find, 1); }
    None
}
impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_consume_mct_result(segment_view(segment), self.limits,
                mct_pending_view(old(pending)@), old(completed)@,
                (mct_fragment_outcome(result), mct_pending_view(final(pending)@), final(completed)@)),
            mct_fragment_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                (mct_fragment_outcome(result), mct_pending_view(final(pending)@), final(completed)@)
                    == crate::specs::part1_consume_mct_fragment(segment_view(segment), self.limits,
                        mct_pending_view(old(pending)@), old(completed)@),
    ))]
    pub(super) fn consume_mct_fragment(
        &self,
        segment: Segment<'a>,
        pending: &mut Vec<MctFragment>,
        completed: &mut Vec<u8>,
    ) -> Result<Option<MctArray>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = mct_pending_view(pending@);
            let ghost completed_input = completed@;
            let ghost goal = crate::specs::part1_consume_mct_fragment(
                segment_view(segment), self.limits, input, completed_input);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_consume_mct_fragment);
            crate::specs::part1_fresh_consume_mct_normal(segment_view(segment), self.limits, input, completed_input, Seq::empty());
        }
        let copied = self.prepare_mct_fragment(segment, pending, completed);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = copied {
                crate::specs::part1_fresh_consume_mct_prepare_error(segment_view(segment), self.limits, input, completed_input, error, mct_pending_view(pending@));
            }
        }
        let (active_index, maximum_bytes) = copied?;
        let complete = {
            let state = &pending[active_index];
            crate::refinement::mct_fragment_complete(state.next_index, state.final_index)
        };
        if !complete {
            return Ok(None);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost prepared = mct_pending_view(pending@); }
        let state = pending.swap_remove(active_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mct_fragment_view(&state) == prepared[active_index as int]);
            assert(mct_pending_view(pending@) =~= crate::specs::part1_mct_fragment_swap_remove(prepared, active_index));
        }
        if state.data.len() as u64 > maximum_bytes {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum_bytes,
                actual: state.data.len() as u64,
            });
        }
        let copied = reserve_values(
            state.data.len().saturating_add(6),
            MctCopyPath::FreshMarker(FreshMarkerPath::MctReassembly(state.offset)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if copied.is_err() { crate::specs::part1_fresh_consume_mct_reassembly_error(segment_view(segment), self.limits, input, completed_input); }
        }
        let mut payload = copied?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(payload@ =~= Seq::<u8>::empty()); }
        payload.extend_from_slice(&[0, 0]);
        let descriptor = state.descriptor;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(descriptor >> 8 <= 255u16) by (bit_vector);
            assert(descriptor & 255 <= 255u16) by (bit_vector);
        }
        payload.push((descriptor >> 8) as u8);
        payload.push((descriptor & 255) as u8);
        payload.extend_from_slice(&[0, 0]);
        payload.extend_from_slice(&state.data);
        #[cfg(verus_keep_ghost)]
        proof! { assert(payload@ =~= crate::specs::part1_mct_fragment_payload(mct_fragment_view(&state))); }
        let copied = self.parse_mct(Segment {
            marker: MCT,
            offset: state.offset,
            payload: &payload,
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_fresh_consume_mct_parsed(segment_view(segment), self.limits, input, completed_input, mct_array_outcome(copied));
            crate::specs::part1_fresh_mct_observed(crate::specs::part1_fresh_mct_reassembled(mct_fragment_view(&state)), self.limits, mct_array_outcome(copied));
        }
        let array = copied?;
        completed.push(segment.payload[3]);
        Ok(Some(array))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_prepare_mct_result(
            segment_view(segment), self.limits, mct_pending_view(old(pending)@), completed@,
            (result, mct_pending_view(final(pending)@))),
            result != Err(DecodeError::AllocationFailed) ==>
                (result, mct_pending_view(final(pending)@)) == crate::specs::part1_prepare_mct_fragment(
                    segment_view(segment), self.limits, mct_pending_view(old(pending)@), completed@),
        match result { Ok((index, maximum)) => segment.payload.len() >= 4 && index < final(pending).len()
            && maximum == crate::specs::part1_mct_fragment_maximum_bytes(self.limits), Err(_) => true },
    ))]
    pub(super) fn prepare_mct_fragment(
        &self,
        segment: Segment<'a>,
        pending: &mut Vec<MctFragment>,
        completed: &[u8],
    ) -> Result<(usize, u64), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost input = mct_pending_view(pending@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_prepare_mct_fragment); reveal(mct_fragment_view);
            crate::specs::part1_fresh_prepare_mct_normal(segment_view(segment), self.limits, input, completed@);
            crate::specs::part1_fresh_prepare_mct_normal_rule(segment_view(segment), self.limits, input, completed@);
        }
        if segment.payload.len() < 4 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let fragment_index = read_u16([segment.payload[0], segment.payload[1]]);
        let descriptor = read_u16([segment.payload[2], segment.payload[3]]);
        #[cfg(verus_keep_ghost)]
        proof! { assert(descriptor & 255 <= 255u16) by (bit_vector); }
        let array_index = (descriptor & 0xff) as u8;
        if array_index == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let components = self.limits.maximum_components();
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(0 <= components as int <= 65535 ==>
                components as int * components as int <= 4294967296
                && components as int * components as int * 8 <= 34359738368) by (nonlinear_arith);
        }
        let square = match u64::from(components).checked_mul(u64::from(components)) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let maximum_bytes = match square.checked_mul(8) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let state_index = find_mct_fragment(pending, array_index);
        let already_completed = u8_list_contains(completed, array_index);
        let active_index;
        if fragment_index == 0 {
            if segment.payload.len() < 6 || state_index.is_some() || already_completed {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
            let final_index = read_u16([segment.payload[4], segment.payload[5]]);
            if u64::from(final_index) + 1 > maximum_bytes {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: maximum_bytes,
                    actual: u64::from(final_index) + 1,
                });
            }
            if segment.payload[6..].len() as u64 > maximum_bytes {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: maximum_bytes,
                    actual: segment.payload[6..].len() as u64,
                });
            }
            let copied = copy_flat(
                &segment.payload[6..],
                MctCopyPath::FreshMarker(FreshMarkerPath::MctInitial(segment.offset)),
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if copied.is_err() { crate::specs::part1_fresh_prepare_mct_refused(segment_view(segment), self.limits, input, completed@); }
            }
            let data = copied?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(data@ =~= segment.payload@.subrange(6, segment.payload.len() as int)); }
            active_index = pending.len();
            pending.push(MctFragment {
                descriptor,
                next_index: 1,
                final_index,
                offset: segment.offset,
                data,
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(mct_pending_view(pending@) =~= input.push(crate::specs::Part1MctFragment {
                    descriptor, next_index: 1, final_index, offset: segment.offset,
                    data: segment.payload@.subrange(6, segment.payload.len() as int),
                }));
            }
        } else {
            let index = match state_index {
                Some(index) => index,
                None => {
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost before = mct_fragment_view(&pending[index as int]);
                let ghost appended_data = before.data + segment.payload@.subrange(4, segment.payload.len() as int);
            }
            let state = &mut pending[index];
            if state.descriptor != descriptor
                || fragment_index != state.next_index
                || fragment_index > state.final_index
            {
                let error = self.malformed_at(segment.offset, MalformedKind::InvalidTransform);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(mct_pending_view(pending@) =~= input);
                    assert(crate::specs::part1_prepare_mct_fragment(segment_view(segment), self.limits, input, completed@)
                        == (Err(error), input));
                    crate::specs::part1_fresh_prepare_mct_normal(segment_view(segment), self.limits, input, completed@);
                    assert(crate::specs::part1_fresh_prepare_mct_result(segment_view(segment), self.limits, input, completed@,
                        (Err(error), mct_pending_view(pending@))));
                }
                return Err(error);
            }
            state.data.extend_from_slice(&segment.payload[4..]);
            #[cfg(verus_keep_ghost)]
            proof! { assert(state.data@ =~= appended_data); }
            let actual_bytes = state.data.len() as u64;
            if actual_bytes > maximum_bytes {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(mct_pending_view(pending@) =~= input.update(index as int,
                        crate::specs::part1_mct_fragment_updated(before, appended_data, before.next_index)));
                }
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: maximum_bytes,
                    actual: actual_bytes,
                });
            }
            let next_index = state.next_index;
            if next_index == u16::MAX {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(mct_pending_view(pending@) =~= input.update(index as int,
                        crate::specs::part1_mct_fragment_updated(before, appended_data, before.next_index)));
                }
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
            state.next_index = crate::refinement::mct_fragment_next(next_index);
            active_index = index;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(mct_pending_view(pending@) =~= input.update(index as int,
                    crate::specs::part1_mct_fragment_updated(before, appended_data, (next_index + 1) as u16)));
            }
        }
        Ok((active_index, maximum_bytes))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_consume_mcc_result(segment_view(segment), components, self.limits,
                mcc_pending_view(old(pending)@), old(completed)@,
                (mcc_fragment_outcome(result), mcc_pending_view(final(pending)@), final(completed)@)),
            mcc_fragment_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                (mcc_fragment_outcome(result), mcc_pending_view(final(pending)@), final(completed)@)
                    == crate::specs::part1_consume_mcc_fragment(segment_view(segment), components, self.limits,
                        mcc_pending_view(old(pending)@), old(completed)@),
    ))]
    pub(super) fn consume_mcc_fragment(
        &self,
        segment: Segment<'a>,
        components: u16,
        pending: &mut Vec<MccFragment>,
        completed: &mut Vec<u8>,
    ) -> Result<Option<MctRecord>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = mcc_pending_view(pending@);
            let ghost completed_input = completed@;
            let ghost goal = crate::specs::part1_consume_mcc_fragment(
                segment_view(segment), components, self.limits, input, completed_input);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_consume_mcc_fragment);
            crate::specs::part1_fresh_consume_mcc_normal(segment_view(segment), components, self.limits, input, completed_input, Seq::empty());
        }
        let copied = self.prepare_mcc_fragment(segment, components, pending, completed);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = copied {
                crate::specs::part1_fresh_consume_mcc_prepare_error(segment_view(segment), components, self.limits, input, completed_input, error, mcc_pending_view(pending@));
            }
        }
        let (active_index, maximum_bytes) = copied?;
        let complete = {
            let state = &pending[active_index];
            crate::refinement::mct_fragment_complete(state.next_index, state.final_index)
        };
        if !complete {
            return Ok(None);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost prepared = mcc_pending_view(pending@); }
        let state = pending.swap_remove(active_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(mcc_fragment_view(&state) == prepared[active_index as int]);
            assert(mcc_pending_view(pending@) =~= crate::specs::part1_mcc_fragment_swap_remove(prepared, active_index));
        }
        if state.data.len() as u64 > maximum_bytes {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum_bytes,
                actual: state.data.len() as u64,
            });
        }
        let copied = reserve_values(
            state.data.len().saturating_add(7),
            MctCopyPath::FreshMarker(FreshMarkerPath::MccReassembly(state.offset)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if copied.is_err() { crate::specs::part1_fresh_consume_mcc_reassembly_error(segment_view(segment), components, self.limits, input, completed_input); }
        }
        let mut payload = copied?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(payload@ =~= Seq::<u8>::empty()); }
        payload.extend_from_slice(&[0, 0]);
        payload.push(state.record_index);
        payload.extend_from_slice(&[0, 0]);
        let count = state.collection_count;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(count >> 8 <= 255u16) by (bit_vector);
            assert(count & 255 <= 255u16) by (bit_vector);
        }
        payload.push((count >> 8) as u8);
        payload.push((count & 255) as u8);
        payload.extend_from_slice(&state.data);
        #[cfg(verus_keep_ghost)]
        proof! { assert(payload@ =~= crate::specs::part1_mcc_fragment_payload(mcc_fragment_view(&state))); }
        let copied = self.parse_mcc(
            Segment {
                marker: MCC,
                offset: state.offset,
                payload: &payload,
            },
            components,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_fresh_consume_mcc_parsed(segment_view(segment), components, self.limits, input, completed_input, mcc_record_outcome(copied));
            crate::specs::part1_fresh_mcc_observed(crate::specs::part1_fresh_mcc_reassembled(mcc_fragment_view(&state)), components, self.limits, mcc_record_outcome(copied));
        }
        let record = copied?;
        completed.push(segment.payload[2]);
        Ok(Some(record))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_prepare_mcc_result(
            segment_view(segment), components, mcc_pending_view(old(pending)@), completed@,
            (result, mcc_pending_view(final(pending)@))),
            result != Err(DecodeError::AllocationFailed) ==>
                (result, mcc_pending_view(final(pending)@)) == crate::specs::part1_prepare_mcc_fragment(
                    segment_view(segment), components, mcc_pending_view(old(pending)@), completed@),
        match result { Ok((index, maximum)) => segment.payload.len() >= 3 && index < final(pending).len()
            && maximum == crate::specs::part1_mcc_fragment_maximum_bytes(components), Err(_) => true },
    ))]
    pub(super) fn prepare_mcc_fragment(
        &self,
        segment: Segment<'a>,
        components: u16,
        pending: &mut Vec<MccFragment>,
        completed: &[u8],
    ) -> Result<(usize, u64), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost input = mcc_pending_view(pending@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_prepare_mcc_fragment); reveal(mcc_fragment_view);
            crate::specs::part1_fresh_prepare_mcc_normal(segment_view(segment), components, input, completed@);
            crate::specs::part1_fresh_prepare_mcc_normal_rule(segment_view(segment), components, input, completed@);
        }
        if segment.payload.len() < 3 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let fragment_index = read_u16([segment.payload[0], segment.payload[1]]);
        let record_index = segment.payload[2];
        if record_index == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let scaled = match u64::from(components).checked_mul(4) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let per_component = match scaled.checked_add(12) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(0 <= components as int <= 65535 ==>
                components as int * (components as int * 4 + 12) <= 34359738368) by (nonlinear_arith);
        }
        let maximum_bytes = match u64::from(components).checked_mul(per_component) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let state_index = find_mcc_fragment(pending, record_index);
        let already_completed = u8_list_contains(completed, record_index);
        let active_index;
        if fragment_index == 0 {
            if segment.payload.len() < 7 || state_index.is_some() || already_completed {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
            let final_index = read_u16([segment.payload[3], segment.payload[4]]);
            let collection_count = read_u16([segment.payload[5], segment.payload[6]]);
            if u64::from(final_index) + 1 > maximum_bytes {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: maximum_bytes,
                    actual: u64::from(final_index) + 1,
                });
            }
            if segment.payload[7..].len() as u64 > maximum_bytes {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: maximum_bytes,
                    actual: segment.payload[7..].len() as u64,
                });
            }
            let copied = copy_flat(
                &segment.payload[7..],
                MctCopyPath::FreshMarker(FreshMarkerPath::MccInitial(segment.offset)),
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                if copied.is_err() { crate::specs::part1_fresh_prepare_mcc_refused(segment_view(segment), components, input, completed@); }
            }
            let data = copied?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(data@ =~= segment.payload@.subrange(7, segment.payload.len() as int)); }
            active_index = pending.len();
            pending.push(MccFragment {
                record_index,
                next_index: 1,
                final_index,
                collection_count,
                offset: segment.offset,
                data,
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(mcc_pending_view(pending@) =~= input.push(crate::specs::Part1MccFragment {
                    record_index, next_index: 1, final_index, collection_count, offset: segment.offset,
                    data: segment.payload@.subrange(7, segment.payload.len() as int),
                }));
            }
        } else {
            let index = match state_index {
                Some(index) => index,
                None => {
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost before = mcc_fragment_view(&pending[index as int]);
                let ghost appended_data = before.data + segment.payload@.subrange(3, segment.payload.len() as int);
            }
            let state = &mut pending[index];
            if fragment_index != state.next_index || fragment_index > state.final_index {
                let error = self.malformed_at(segment.offset, MalformedKind::InvalidTransform);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(mcc_pending_view(pending@) =~= input);
                    assert(crate::specs::part1_prepare_mcc_fragment(segment_view(segment), components, input, completed@)
                        == (Err(error), input));
                    crate::specs::part1_fresh_prepare_mcc_normal(segment_view(segment), components, input, completed@);
                    assert(crate::specs::part1_fresh_prepare_mcc_result(segment_view(segment), components, input, completed@,
                        (Err(error), mcc_pending_view(pending@))));
                }
                return Err(error);
            }
            state.data.extend_from_slice(&segment.payload[3..]);
            #[cfg(verus_keep_ghost)]
            proof! { assert(state.data@ =~= appended_data); }
            let actual_bytes = state.data.len() as u64;
            if actual_bytes > maximum_bytes {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(mcc_pending_view(pending@) =~= input.update(index as int,
                        crate::specs::part1_mcc_fragment_updated(before, appended_data, before.next_index)));
                }
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::TransformElements,
                    limit: maximum_bytes,
                    actual: actual_bytes,
                });
            }
            let next_index = state.next_index;
            if next_index == u16::MAX {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(mcc_pending_view(pending@) =~= input.update(index as int,
                        crate::specs::part1_mcc_fragment_updated(before, appended_data, before.next_index)));
                }
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
            state.next_index = crate::refinement::mct_fragment_next(next_index);
            active_index = index;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(mcc_pending_view(pending@) =~= input.update(index as int,
                    crate::specs::part1_mcc_fragment_updated(before, appended_data, (next_index + 1) as u16)));
            }
        }
        Ok((active_index, maximum_bytes))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_mct_result(segment_view(segment), self.limits, mct_array_outcome(result)),
            mct_array_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                mct_array_outcome(result) == crate::specs::part1_parse_mct(segment_view(segment), self.limits),
    ))]
    pub(super) fn parse_mct(&self, segment: Segment<'a>) -> Result<MctArray, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_mct); reveal(crate::specs::part1_mct_header);
            crate::specs::part1_fresh_mct_normal(segment_view(segment), self.limits);
            mct_fixed_precision_is_q32();
        }
        if segment.payload.len() < 8 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let z = read_u16([segment.payload[0], segment.payload[1]]);
        let descriptor = read_u16([segment.payload[2], segment.payload[3]]);
        let y = read_u16([segment.payload[4], segment.payload[5]]);
        if z != 0 || y != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        if descriptor & 0xf000 != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(descriptor & 255 <= 255u16) by (bit_vector); }
        let index = (descriptor & 0xff) as u8;
        if index == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let kind = match (descriptor >> 8) & 3 {
            0 => MctArrayKind::Dependency,
            1 => MctArrayKind::Decorrelation,
            2 => MctArrayKind::Offset,
            _ => {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
        };
        let (numeric_format, element_bytes) = match (descriptor >> 10) & 3 {
            0 => (MctNumericFormat::Int16, 2_usize),
            1 => (MctNumericFormat::Int32, 4_usize),
            2 => (MctNumericFormat::Float32, 4_usize),
            _ => (MctNumericFormat::Float64, 8_usize),
        };
        let data = &segment.payload[6..];
        let remainder = data.len() % element_bytes;
        if data.is_empty() || remainder != 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let element_count = data.len() / element_bytes;
        let cap = self.limits.maximum_components();
        #[cfg(verus_keep_ghost)]
        proof! { assert(0 <= cap as int <= 65535 ==> cap as int * cap as int <= 4294836225) by (nonlinear_arith); }
        let maximum = match u64::from(cap).checked_mul(u64::from(cap)) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if element_count as u64 > maximum {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: maximum,
                actual: element_count as u64,
            });
        }
        let fraction_bits = if matches!(
            numeric_format,
            MctNumericFormat::Float32 | MctNumericFormat::Float64
        ) {
            MCT_FIXED_BITS
        } else {
            0
        };
        let copied = reserve_values(
            element_count,
            MctCopyPath::FreshMarker(FreshMarkerPath::Values(segment.offset)),
        );
        let mut values = match copied {
            Ok(values) => values,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::specs::part1_fresh_mct_refused(segment_view(segment), self.limits); }
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(values@ =~= Seq::<i64>::empty()); }
        let mut position = 0_usize;
        let mut remaining_elements = element_count;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost goal = crate::specs::part1_parse_mct(segment_view(segment), self.limits);
            let ghost target = crate::specs::part1_mct_values(segment.offset, data@, numeric_format, 0, Seq::empty());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(data.len() as int, element_bytes as int);
            assert(element_bytes as int * remaining_elements as int == remaining_elements as int * element_bytes as int) by (nonlinear_arith);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant position <= data.len(), remaining_elements <= element_count,
                    crate::specs::part1_fresh_mct_result(segment_view(segment), self.limits,
                        crate::specs::part1_parse_mct(segment_view(segment), self.limits)),
                    element_bytes == crate::specs::part1_mct_element_width(numeric_format),
                    element_bytes == 2 || element_bytes == 4 || element_bytes == 8,
                    position + remaining_elements as int * element_bytes as int == data.len(),
                    target == crate::specs::part1_mct_values(segment.offset, data@, numeric_format, position as nat, values@),
                    goal == crate::specs::part1_parse_mct(segment_view(segment), self.limits),
                    goal == match target { Err(error) => Err(error), Ok(parsed) => Ok((index, kind, numeric_format, fraction_bits, parsed)) },
                decreases remaining_elements,
            )
        )]
        while position < data.len() {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost start = position; }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mct_values, 1);
                assert(element_bytes > 0 && position + remaining_elements as int * element_bytes as int == data.len()
                    && position < data.len() ==> remaining_elements > 0 && position + element_bytes <= data.len()) by (nonlinear_arith);
            }
            if remaining_elements == 0 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
            remaining_elements -= 1;
            let value = self.decode_mct_element(data, position, numeric_format, segment.offset)?;
            values.push(value);
            position = match position.checked_add(element_bytes) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(position == start + element_bytes);
                assert((remaining_elements as int + 1) * element_bytes as int ==
                    remaining_elements as int * element_bytes as int + element_bytes as int) by (nonlinear_arith);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mct_values, 1); reveal(mct_array_view); }
        Ok(MctArray {
            index,
            kind,
            numeric_format,
            fraction_bits,
            values,
        })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_mct_element(offset, data@, position, numeric_format),
    ))]
    pub(super) fn decode_mct_element(
        &self,
        data: &[u8],
        position: usize,
        numeric_format: MctNumericFormat,
        offset: usize,
    ) -> Result<i64, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_mct_element); }
        let width = match numeric_format {
            MctNumericFormat::Int16 => 2usize,
            MctNumericFormat::Int32 | MctNumericFormat::Float32 => 4,
            MctNumericFormat::Float64 => 8,
        };
        if position > data.len() || data.len() - position < width {
            return Err(self.malformed_at(offset, MalformedKind::InvalidTransform));
        }
        let position_1 = match position.checked_add(1) {
            Some(value) => value,
            None => return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow)),
        };
        let byte_0 = data[position];
        let byte_1 = data[position_1];
        match numeric_format {
            MctNumericFormat::Int16 => Ok(signed_u16(read_u16([byte_0, byte_1]))),
            MctNumericFormat::Int32 | MctNumericFormat::Float32 => {
                let position_2 = match position.checked_add(2) {
                    Some(value) => value,
                    None => {
                        return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow));
                    }
                };
                let position_3 = match position.checked_add(3) {
                    Some(value) => value,
                    None => {
                        return Err(self.malformed_at(offset, MalformedKind::ArithmeticOverflow));
                    }
                };
                let bits = read_u32([byte_0, byte_1, data[position_2], data[position_3]]);
                if matches!(numeric_format, MctNumericFormat::Int32) {
                    Ok(signed_u32(bits))
                } else {
                    match float32_to_fixed(bits) {
                        Ok(value) => Ok(value),
                        Err(()) => Err(self.malformed_at(offset, MalformedKind::InvalidTransform)),
                    }
                }
            }
            MctNumericFormat::Float64 => {
                let mut bytes = [0_u8; 8];
                let mut byte_index = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant byte_index <= 8, position as int + 8 <= data.len(),
                        forall|index: int| 0 <= index < byte_index ==> bytes@[index] == data@[position as int + index],
                    decreases 8 - byte_index,
                ))]
                while byte_index < bytes.len() {
                    let source = match position.checked_add(byte_index) {
                        Some(value) => value,
                        None => {
                            return Err(
                                self.malformed_at(offset, MalformedKind::ArithmeticOverflow)
                            );
                        }
                    };
                    bytes[byte_index] = data[source];
                    byte_index += 1;
                }
                #[cfg(verus_keep_ghost)]
                proof! { assert(bytes@ =~= data@.subrange(position as int, position as int + 8)); }
                match float64_to_fixed(read_u64(bytes)) {
                    Ok(value) => Ok(value),
                    Err(()) => Err(self.malformed_at(offset, MalformedKind::InvalidTransform)),
                }
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_mcc_result(segment_view(segment), components, self.limits, mcc_record_outcome(result)),
            mcc_record_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                mcc_record_outcome(result) == crate::specs::part1_parse_mcc(segment_view(segment), components, self.limits),
    ))]
    pub(super) fn parse_mcc(
        &self,
        segment: Segment<'a>,
        components: u16,
    ) -> Result<MctRecord, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_mcc);
            crate::specs::part1_fresh_mcc_normal(segment_view(segment), components, self.limits);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        }
        if segment.payload.len() < 7 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        if read_u16([segment.payload[0], segment.payload[1]]) != 0
            || read_u16([segment.payload[3], segment.payload[4]]) != 0
        {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let index = segment.payload[2];
        let collection_count = read_u16([segment.payload[5], segment.payload[6]]);
        if index == 0 || collection_count == 0 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        if collection_count > self.limits.maximum_components() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::TransformElements,
                limit: u64::from(self.limits.maximum_components()),
                actual: u64::from(collection_count),
            });
        }
        let mut position = 7_usize;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost all = crate::specs::part1_fresh_mcc_requests(segment_view(segment), components, self.limits);
            let ghost mut done = crate::specs::part1_fresh_leaf(
                FreshMarkerPath::Collections(segment.offset), collection_count as usize);
        }
        let copied = reserve_values(
            usize::from(collection_count),
            MctCopyPath::FreshMarker(FreshMarkerPath::Collections(segment.offset)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(Seq::empty(), done,
                crate::specs::part1_fresh_records_requests(segment_view(segment), components, 7, collection_count as nat), copy_outcome(copied));
            if copied.is_err() { crate::specs::part1_fresh_mcc_refused(segment_view(segment), components, self.limits); }
        }
        let mut collections = copied?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(collections@ =~= Seq::<MctCollectionReference>::empty());
            assert(mcc_collection_references_view(collections@) =~= Seq::empty());
        }
        let mut collection = 0_u16;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant collection <= collection_count,
                    crate::specs::part1_fresh_mcc_result(segment_view(segment), components, self.limits,
                        crate::specs::part1_parse_mcc(segment_view(segment), components, self.limits)),
                    all == crate::specs::part1_fresh_mcc_requests(segment_view(segment), components, self.limits),
                    all == done + crate::specs::part1_fresh_records_requests(
                        segment_view(segment), components, position, (collection_count - collection) as nat),
                    crate::specs::part1_mct_copy_result(done, Ok(())),
                    segment.payload.len() >= 7, index == segment.payload@[2],
                    crate::specs::part1_parse_mcc(segment_view(segment), components, self.limits)
                        == crate::specs::part1_mcc_records(segment_view(segment), components, position,
                            (collection_count - collection) as nat, mcc_collection_references_view(collections@)),
                decreases collection_count - collection,
            )
        )]
        while collection < collection_count {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_mcc_records, 1);
                reveal_with_fuel(crate::specs::part1_fresh_records_requests, 1);
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous_position = position; }
            let copied = self.decode_mcc_collection(segment, components, position);
            #[cfg(verus_keep_ghost)]
            proof! {
                let step = crate::specs::part1_fresh_collection_requests(segment_view(segment), components, position);
                crate::specs::part1_fresh_collection_observed(segment_view(segment), components, position, mcc_collection_outcome(copied));
                let tail = match crate::specs::part1_mcc_collection(segment_view(segment), components, position) {
                    Err(_) => Seq::empty(), Ok((_, next)) => crate::specs::part1_fresh_records_requests(
                        segment_view(segment), components, next, (collection_count - collection - 1) as nat),
                };
                let status = if mcc_collection_outcome(copied) == Err(DecodeError::AllocationFailed) {
                    Err(DecodeError::AllocationFailed)
                } else { Ok(()) };
                crate::specs::part1_mct_copy_continue(done, step, tail, status);
                assert(all =~= (done + step) + tail);
                if mcc_collection_outcome(copied) == Err(DecodeError::AllocationFailed) {
                    crate::specs::part1_fresh_mcc_refused(segment_view(segment), components, self.limits);
                }
            }
            let (decoded, next) = copied?;
            position = next;
            #[cfg(verus_keep_ghost)]
            proof! { done = done + crate::specs::part1_fresh_collection_requests(segment_view(segment), components, previous_position); }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous = mcc_collection_references_view(collections@);
                let ghost value = mcc_collection_reference_view(&decoded);
            }
            collections.push(decoded);
            #[cfg(verus_keep_ghost)]
            proof! { assert(mcc_collection_references_view(collections@) =~= previous.push(value)); }
            collection = match collection.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mcc_records, 1); }
        if position != segment.payload.len() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        validate_parallel_collections(&collections, segment.offset)?;
        Ok(MctRecord { index, collections })
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_collection_result(segment_view(segment), components, start, mcc_collection_outcome(result)),
            mcc_collection_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                mcc_collection_outcome(result) == crate::specs::part1_mcc_collection(segment_view(segment), components, start),
    ))]
    pub(super) fn decode_mcc_collection(
        &self,
        segment: Segment<'a>,
        components: u16,
        start: usize,
    ) -> Result<(MctCollectionReference, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_fresh_collection_normal(segment_view(segment), components, start);
            crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
            reveal(crate::specs::part1_mcc_collection); reveal(mcc_collection_reference_view);
            reveal(mcc_reference_transform_view); reveal(mct_wavelet_view);
        }
        let mut position = start;
        let transform_kind_byte = match segment.payload.get(position) {
            Some(value) => *value,
            None => return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform)),
        };
        position = match position.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        if transform_kind_byte & 0xfc != 0 || transform_kind_byte & 3 == 2 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(transform_kind_byte & 0xfc == 0 ==> transform_kind_byte == (transform_kind_byte & 3)) by (bit_vector);
            assert(transform_kind_byte & 3 <= 3u8) by (bit_vector);
        }
        let transform_kind = transform_kind_byte & 3;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input_start = position;
            let ghost all = crate::specs::part1_fresh_collection_requests(segment_view(segment), components, start);
            let ghost first = crate::specs::part1_fresh_list_requests(segment.payload@, input_start, components, segment.offset, false);
        }
        let copied = parse_mcc_component_list(
            segment.payload,
            &mut position,
            components,
            segment.offset,
            false,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_fresh_list_observed(segment.payload@, input_start, components, segment.offset, false,
                (marker_words_outcome(copied), position));
            let before = crate::specs::part1_parse_mcc_component_list(segment.payload@, input_start, components, segment.offset);
            let tail = if before.0.is_ok() {
                crate::specs::part1_fresh_list_requests(segment.payload@, before.1, components, segment.offset, true)
            } else { Seq::empty() };
            let status = if marker_words_outcome(copied) == Err(DecodeError::AllocationFailed) { Err(DecodeError::AllocationFailed) } else { Ok(()) };
            crate::specs::part1_mct_copy_continue(Seq::empty(), first, tail, status);
            assert(all =~= first + tail);
            if marker_words_outcome(copied) == Err(DecodeError::AllocationFailed) {
                crate::specs::part1_fresh_collection_refused(segment_view(segment), components, start);
            }
        }
        let input_components = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost output_start = position; }
        let copied = parse_mcc_component_list(
            segment.payload,
            &mut position,
            components,
            segment.offset,
            true,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_fresh_list_observed(segment.payload@, output_start, components, segment.offset, true,
                (marker_words_outcome(copied), position));
            let last = crate::specs::part1_fresh_list_requests(segment.payload@, output_start, components, segment.offset, true);
            let status = if marker_words_outcome(copied) == Err(DecodeError::AllocationFailed) { Err(DecodeError::AllocationFailed) } else { Ok(()) };
            crate::specs::part1_mct_copy_continue(first, last, Seq::empty(), status);
            assert(all =~= (first + last) + Seq::<crate::specs::Part1MctCopyRequest>::empty());
            if marker_words_outcome(copied) == Err(DecodeError::AllocationFailed) {
                crate::specs::part1_fresh_collection_refused(segment_view(segment), components, start);
            }
        }
        let output_components = copied?;
        if input_components.is_empty()
            || position > segment.payload.len()
            || segment.payload.len() - position < 3
        {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let transform = (u32::from(segment.payload[position]) << 16)
            | (u32::from(segment.payload[position + 1]) << 8)
            | u32::from(segment.payload[position + 2]);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(transform & 255 <= 255u32) by (bit_vector);
            assert((transform >> 8) & 255 <= 255u32) by (bit_vector);
            assert((transform >> 16) & 63 <= 63u32) by (bit_vector);
        }
        position = match position.checked_add(3) {
            Some(value) => value,
            None => {
                return Err(self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow));
            }
        };
        let reference_transform = match transform_kind {
            0 | 1 => {
                if transform & 0xfe0000 != 0
                    || input_components.len() != output_components.len()
                    || (transform_kind == 0
                        && !u16_lists_equal(&input_components, &output_components))
                {
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
                MctCollectionReferenceTransform::Array {
                    kind: if transform_kind == 0 {
                        MctArrayKind::Dependency
                    } else {
                        MctArrayKind::Decorrelation
                    },
                    reversible: transform & 0x010000 != 0,
                    transform_index: (transform & 0xff) as u8,
                    offset_index: ((transform >> 8) & 0xff) as u8,
                }
            }
            3 => {
                if transform & 0xc0ff00 != 0
                    || input_components.len() != output_components.len()
                    || position > segment.payload.len()
                    || segment.payload.len() - position < 4
                {
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
                let wavelet_type = match (transform & 0xff) as u8 {
                    0 => MctWaveletType::Irreversible9x7,
                    1 => MctWaveletType::Reversible5x3,
                    _ => {
                        return Err(
                            self.malformed_at(segment.offset, MalformedKind::InvalidTransform)
                        );
                    }
                };
                let levels = ((transform >> 16) & 0x3f) as u8;
                if levels > 32 {
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
                let offset_end = match position.checked_add(4) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                        );
                    }
                };
                let offset_bytes = match segment.payload.get(position..offset_end) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment.offset, MalformedKind::InvalidTransform)
                        );
                    }
                };
                let component_offset = signed_u32(read_u32([
                    offset_bytes[0],
                    offset_bytes[1],
                    offset_bytes[2],
                    offset_bytes[3],
                ]));
                position = offset_end;
                MctCollectionReferenceTransform::Wavelet(MctWavelet {
                    transform: wavelet_type,
                    levels,
                    component_offset: component_offset as i32,
                })
            }
            _ => return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform)),
        };
        Ok((
            MctCollectionReference {
                input_components,
                output_components,
                transform: reference_transform,
            },
            position,
        ))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_fresh_mco_result(segment_view(segment), segment_tail_outcome(result)),
            segment_tail_outcome(result) != Err(DecodeError::AllocationFailed) ==>
                segment_tail_outcome(result) == crate::specs::part1_parse_mco(segment_view(segment)),
    ))]
    pub(super) fn parse_mco(&self, segment: Segment<'a>) -> Result<Vec<u8>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_mco);
            crate::specs::part1_fresh_mco_normal(segment_view(segment));
        }
        let count = match segment.payload.first() {
            Some(value) => usize::from(*value),
            None => return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform)),
        };
        if segment.payload.len() != count + 1 {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
        }
        let copied = reserve_values(
            count,
            MctCopyPath::FreshMarker(FreshMarkerPath::Order(segment.offset)),
        );
        let mut order = match copied {
            Ok(order) => order,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::specs::part1_fresh_mco_refused(segment_view(segment)); }
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(order@ =~= Seq::<u8>::empty()); }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= count <= 255, order.len() == index,
                    crate::specs::part1_fresh_mco_result(segment_view(segment), crate::specs::part1_parse_mco(segment_view(segment))),
                    segment.payload.len() == count + 1,
                    crate::specs::part1_parse_mco(segment_view(segment))
                        == crate::specs::part1_mco_run(segment_view(segment), index as nat, order@),
                decreases count - index,
            )
        )]
        while index < count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_mco_run, 1); }
            let stage = match segment.payload.get(index + 1) {
                Some(value) => *value,
                None => {
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
            };
            let mut previous = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant previous <= order.len(), order.len() == index,
                        crate::specs::part1_fresh_mco_result(segment_view(segment), crate::specs::part1_parse_mco(segment_view(segment))),
                        index < count <= 255, segment.payload.len() == count + 1,
                        stage == segment.payload@[index as int + 1],
                        forall|position: int| 0 <= position < previous ==> order@[position] != stage,
                        crate::specs::part1_parse_mco(segment_view(segment))
                            == crate::specs::part1_mco_run(segment_view(segment), index as nat, order@),
                    decreases order.len() - previous,
                )
            )]
            while previous < order.len() {
                #[cfg(verus_keep_ghost)]
                proof! { reveal_with_fuel(crate::specs::part1_mco_run, 1); }
                if order[previous] == stage {
                    #[cfg(verus_keep_ghost)]
                    proof! { assert(order@.contains(stage)); }
                    return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
                }
                previous = match previous.checked_add(1) {
                    Some(value) => value,
                    None => {
                        return Err(
                            self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                        );
                    }
                };
            }
            #[cfg(verus_keep_ghost)]
            proof! { assert(!order@.contains(stage)); }
            if stage == 0 {
                return Err(self.malformed_at(segment.offset, MalformedKind::InvalidTransform));
            }
            order.push(stage);
            index = match index.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_mco_run, 1); }
        Ok(order)
    }
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_fresh_list_result(payload@, *old(position), components, marker_offset, _output,
            (marker_words_outcome(result), *final(position))),
        marker_words_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            (marker_words_outcome(result), *final(position)) == crate::specs::part1_parse_mcc_component_list(
                payload@, *old(position), components, marker_offset),
))]
pub(super) fn parse_mcc_component_list(
    payload: &[u8],
    position: &mut usize,
    components: u16,
    marker_offset: usize,
    _output: bool,
) -> Result<Vec<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost start = *position;
        let ghost goal = crate::specs::part1_parse_mcc_component_list(payload@, start, components, marker_offset);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_parse_mcc_component_list);
        crate::specs::part1_fresh_list_normal(payload@, start, components, marker_offset, _output);
    }
    if *position > payload.len() || payload.len() - *position < 2 {
        return Err(DecodeError::MalformedInput {
            offset: marker_offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let encoded_count = read_u16([payload[*position], payload[*position + 1]]);
    *position = match position.checked_add(2) {
        Some(value) => value,
        None => {
            return Err(DecodeError::MalformedInput {
                offset: marker_offset as u64,
                kind: MalformedKind::ArithmeticOverflow,
            });
        }
    };
    let reference_bytes = if encoded_count & 0x8000 == 0 {
        1_usize
    } else {
        2_usize
    };
    let count = encoded_count & 0x7fff;
    #[cfg(verus_keep_ghost)]
    proof! { assert(encoded_count & 0x7fff <= 32767u16) by (bit_vector); }
    if count == 0 || count > components {
        return Err(DecodeError::MalformedInput {
            offset: marker_offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let required = match usize::from(count).checked_mul(reference_bytes) {
        Some(value) => value,
        None => {
            return Err(DecodeError::MalformedInput {
                offset: marker_offset as u64,
                kind: MalformedKind::ArithmeticOverflow,
            });
        }
    };
    if *position > payload.len() || payload.len() - *position < required {
        return Err(DecodeError::MalformedInput {
            offset: marker_offset as u64,
            kind: MalformedKind::InvalidTransform,
        });
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost end = *position as int + required as int;
        let ghost target = crate::specs::part1_mcc_reference_run(
            payload@, components, marker_offset, *position, reference_bytes, count as nat, Seq::empty());
    }
    let path = if _output {
        FreshMarkerPath::Outputs(marker_offset, *position)
    } else {
        FreshMarkerPath::Inputs(marker_offset, *position)
    };
    let copied = reserve_values(usize::from(count), MctCopyPath::FreshMarker(path));
    let mut references = match copied {
        Ok(references) => references,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! { crate::specs::part1_fresh_list_refused(payload@, start, components, marker_offset, _output); }
            return Err(error);
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! { assert(references@ =~= Seq::<u16>::empty()); }
    let mut reference_index = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant reference_index <= count <= 32767, references.len() == reference_index,
                crate::specs::part1_fresh_list_result(payload@, start, components, marker_offset, _output,
                    crate::specs::part1_parse_mcc_component_list(payload@, start, components, marker_offset)),
                reference_bytes == 1 || reference_bytes == 2,
                start == *old(position),
                *position as int + (count - reference_index) * reference_bytes as int == end,
                end <= payload.len(),
                goal == crate::specs::part1_parse_mcc_component_list(payload@, start, components, marker_offset),
                goal == target,
                target == crate::specs::part1_mcc_reference_run(
                    payload@, components, marker_offset, *position, reference_bytes, (count - reference_index) as nat, references@),
            decreases count - reference_index,
        )
    )]
    while reference_index < count {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_mcc_reference_run, 1);
            assert(*position + reference_bytes <= payload.len());
        }
        let current = match payload.get(*position) {
            Some(value) => *value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: marker_offset as u64,
                    kind: MalformedKind::InvalidTransform,
                });
            }
        };
        let reference = if reference_bytes == 1 {
            u16::from(current)
        } else {
            let next = match position.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(DecodeError::MalformedInput {
                        offset: marker_offset as u64,
                        kind: MalformedKind::ArithmeticOverflow,
                    });
                }
            };
            read_u16([
                current,
                match payload.get(next) {
                    Some(value) => *value,
                    None => {
                        return Err(DecodeError::MalformedInput {
                            offset: marker_offset as u64,
                            kind: MalformedKind::InvalidTransform,
                        });
                    }
                },
            ])
        };
        if reference >= components {
            return Err(DecodeError::MalformedInput {
                offset: marker_offset as u64,
                kind: MalformedKind::InvalidTransform,
            });
        }
        if u16_list_contains(&references, reference) {
            return Err(DecodeError::MalformedInput {
                offset: marker_offset as u64,
                kind: MalformedKind::InvalidTransform,
            });
        }
        references.push(reference);
        *position = match position.checked_add(reference_bytes) {
            Some(value) => value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: marker_offset as u64,
                    kind: MalformedKind::ArithmeticOverflow,
                });
            }
        };
        reference_index = match reference_index.checked_add(1) {
            Some(value) => value,
            None => {
                return Err(DecodeError::MalformedInput {
                    offset: marker_offset as u64,
                    kind: MalformedKind::ArithmeticOverflow,
                });
            }
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_mcc_reference_run, 1); }
    Ok(references)
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_mcc_reference_present(values@, value),
))]
pub(super) fn u16_list_contains(values: &[u16], value: u16) -> bool {
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= values.len(),
            forall|position: int| 0 <= position < index ==> values@[position] != value,
        decreases values.len() - index,
    ))]
    while index < values.len() {
        if values[index] == value {
            return true;
        }
        index += 1;
    }
    false
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_float32_to_fixed(bits),
))]
pub(super) fn float32_to_fixed(bits: u32) -> Result<i64, ()> {
    let negative = bits >> 31 != 0;
    let exponent = (bits >> 23) & 0xff;
    let fraction = bits & 0x7f_ffff;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_atk_binary_format);
        assert(((1u128 << 8) - 1) as u128 == 255u128) by (bit_vector);
        assert(((1u128 << 23) - 1) as u128 == 0x7fffffu128) by (bit_vector);
        assert(((bits as u128) >> 31 != 0) == (bits >> 31 != 0)) by (bit_vector);
        assert((((bits as u128) >> 23) & (((1u128 << 8) - 1) as u128)) == (((bits >> 23) & 255) as u128)) by (bit_vector);
        assert(((bits as u128) & (((1u128 << 23) - 1) as u128)) == ((bits & 0x7fffff) as u128)) by (bit_vector);
        assert(((1u32 << 23) | fraction) as u128 == (1u128 << 23) | fraction as u128) by (bit_vector);
        assert((bits >> 23) & 255 <= 255u32) by (bit_vector);
    }
    if exponent == 0xff {
        return Err(());
    }
    if exponent == 0 && fraction == 0 {
        return Ok(0);
    }
    let (significand, binary_exponent) = if exponent == 0 {
        (u128::from(fraction), -149_i32)
    } else {
        (u128::from((1_u32 << 23) | fraction), exponent as i32 - 150)
    };
    fixed_from_binary(negative, significand, binary_exponent)
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_float64_to_fixed(bits),
))]
pub(super) fn float64_to_fixed(bits: u64) -> Result<i64, ()> {
    let negative = bits >> 63 != 0;
    let exponent = (bits >> 52) & 0x7ff;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_atk_binary_format);
        assert(((1u128 << 11) - 1) as u128 == 2047u128) by (bit_vector);
        assert(((1u128 << 52) - 1) as u128 == 0x000fffffffffffffu128) by (bit_vector);
        assert(((bits as u128) >> 63 != 0) == (bits >> 63 != 0)) by (bit_vector);
        assert((((bits as u128) >> 52) & (((1u128 << 11) - 1) as u128)) == (((bits >> 52) & 2047) as u128)) by (bit_vector);
        assert(((bits as u128) & (((1u128 << 52) - 1) as u128)) == ((bits & 0x000fffffffffffff) as u128)) by (bit_vector);
        assert(((1u64 << 52) | fraction) as u128 == (1u128 << 52) | fraction as u128) by (bit_vector);
        assert((bits >> 52) & 2047 <= 2047u64) by (bit_vector);
    }
    if exponent == 0x7ff {
        return Err(());
    }
    if exponent == 0 && fraction == 0 {
        return Ok(0);
    }
    let (significand, binary_exponent) = if exponent == 0 {
        (u128::from(fraction), -1074_i32)
    } else {
        (u128::from((1_u64 << 52) | fraction), exponent as i32 - 1075)
    };
    fixed_from_binary(negative, significand, binary_exponent)
}
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_fixed_from_binary(negative, significand, binary_exponent),
))]
pub(super) fn fixed_from_binary(
    negative: bool,
    significand: u128,
    binary_exponent: i32,
) -> Result<i64, ()> {
    #[cfg(verus_keep_ghost)]
    proof! { mct_fixed_precision_is_q32(); }
    if binary_exponent < i32::MIN + i32::from(MCT_FIXED_BITS)
        || binary_exponent > i32::MAX - i32::from(MCT_FIXED_BITS)
    {
        return Err(());
    }
    let shift = crate::refinement::binary_fixed_shift(binary_exponent);
    let magnitude = if shift >= 0 {
        let shift = u32::try_from(shift).map_err(|_| ())?;
        if shift >= 128 || significand > (u128::MAX >> shift) {
            return Err(());
        }
        significand << shift
    } else {
        let right = u32::try_from(0_i32.checked_sub(shift).ok_or(())?).map_err(|_| ())?;
        if right >= 128 {
            0
        } else {
            let truncated = significand >> right;
            #[cfg(verus_keep_ghost)]
            proof! { assert(right < 128 ==> (1u128 << right) > 0u128) by (bit_vector); }
            let remainder_mask = if right == 0 {
                0
            } else {
                (1_u128 << right).checked_sub(1).ok_or(())?
            };
            let remainder = significand & remainder_mask;
            let half = if right == 0 { 0 } else { 1_u128 << (right - 1) };
            let round_up = remainder > half || (remainder == half && truncated & 1 != 0);
            truncated
                .checked_add(if round_up { 1u128 } else { 0u128 })
                .ok_or(())?
        }
    };
    if negative {
        let signed = i128::try_from(magnitude).map_err(|_| ())?;
        i64::try_from(0_i128.checked_sub(signed).ok_or(())?).map_err(|_| ())
    } else {
        i64::try_from(magnitude).map_err(|_| ())
    }
}
