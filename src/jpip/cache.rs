//! Fragment insertion, conflict detection, cache accounting, and byte views.

use super::{
    Databin, DatabinCache, DatabinId, DatabinStatus, DecodeError, JpipByteView, JpipFragment,
    JpipMessageHeader, MalformedKind, Resource, ResourceLimits, StoredFragment,
};
#[cfg(verus_keep_ghost)]
use super::{
    databin_id_view, jpip_byte_outcome, jpip_byte_storage, jpip_byte_view, jpip_cache_fields,
    jpip_cache_view, jpip_databin_fields, jpip_databin_view, jpip_fragment_fields,
    jpip_fragment_message_input, jpip_fragment_new_input, jpip_fragment_outcome,
    jpip_fragment_view, jpip_header_fields, jpip_header_view, jpip_layout_view, jpip_status_fields,
    jpip_status_outcome, jpip_status_view, jpip_stored_fragment_view, jpip_stored_parts,
    jpip_stored_parts_fields, jpip_view_parts,
};
#[cfg(verus_keep_ghost)]
use crate::specs::{
    part2_jpip_insert_account, part2_jpip_insert_bin, part2_jpip_insert_commit,
    part2_jpip_insert_copy_stored, part2_jpip_insert_finish, part2_jpip_insert_first,
    part2_jpip_insert_first_result, part2_jpip_insert_incoming_copy, part2_jpip_insert_merge,
    part2_jpip_insert_merge_result, part2_jpip_insert_normalize, part2_jpip_insert_replaced,
    part2_jpip_insert_result, part2_jpip_insert_stored_copy, part2_jpip_insert_sum,
    part2_jpip_stored_end,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(test)]
#[path = "cache_entry_result_tests.rs"]
mod entry_result_tests;
#[cfg(test)]
#[path = "cache_insert_result_tests.rs"]
mod insert_result_tests;
#[cfg(test)]
#[path = "cache_view_result_tests.rs"]
mod view_result_tests;

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipFragment {
    pub fn new(
        databin: DatabinId,
        offset: u64,
        bytes: Vec<u8>,
        is_final: bool,
        auxiliary: Option<u64>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                jpip_fragment_outcome(result),
                jpip_fragment_new_input(databin, offset, &bytes, is_final, auxiliary, limits),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_fragment_view); }
        if bytes.is_empty() && !is_final {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidJpipFragment,
            ));
        }
        let length = bytes.len() as u64;
        let end = offset
            .checked_add(length)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_fragment_error(offset, MalformedKind::ArithmeticOverflow),
                ))]
                || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
            )?;
        if !crate::refinement::jpip_fragment_valid(offset, length, limits.maximum_input_bytes()) {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                limits.maximum_input_bytes(),
                end,
            ));
        }
        Ok(Self {
            databin,
            offset,
            bytes,
            final_length: if is_final { Some(end) } else { None },
            auxiliary,
        })
    }

    pub fn from_message(
        header: JpipMessageHeader,
        body: &[u8],
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                jpip_fragment_outcome(result),
                jpip_fragment_message_input(header, body, limits),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(header); }
        if body.len() as u64 != header.length {
            return Err(DecodeError::malformed(
                header.offset,
                MalformedKind::InvalidJpipFragment,
            ));
        }
        Self::new(
            header.databin,
            header.offset,
            copy_bytes(body),
            header.last_byte,
            header.auxiliary,
            limits,
        )
    }
}

impl JpipFragment {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures databin_id_view(result) == jpip_fragment_view(self).0,
    ))]
    pub const fn databin(&self) -> DatabinId {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_fragment_fields(self); }
        self.databin
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_fragment_view(self).1,))]
    pub const fn offset(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_fragment_fields(self); }
        self.offset
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == jpip_fragment_view(self).2,))]
    pub fn bytes(&self) -> &[u8] {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_fragment_fields(self); }
        &self.bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_fragment_view(self).3,))]
    pub const fn final_length(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_fragment_fields(self); }
        self.final_length
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_fragment_view(self).4,))]
    pub const fn auxiliary(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_fragment_fields(self); }
        self.auxiliary
    }
}

impl StoredFragment {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_jpip_stored_end(jpip_stored_fragment_view(self)),
    ))]
    pub(super) const fn end(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_stored_fragment_view); }
        self.offset.saturating_add(self.bytes.len() as u64)
    }
}

impl Databin {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires first <= last <= jpip_databin_view(old(self)).1.len(),
        ensures if jpip_databin_view(old(self)).1.len() + 1 > usize::MAX as nat {
            result == Err(crate::specs::part2_jpip_insert_overflow(merged_start))
                && *final(self) == *old(self)
        } else {
            result == Ok(()) && jpip_databin_view(final(self)) == (
                jpip_databin_view(old(self)).0,
                part2_jpip_insert_normalize(jpip_databin_view(old(self)).1,
                    first as nat, last as nat, merged_start, merged@),
                jpip_databin_view(old(self)).2)
        },
    ))]
    fn normalize_fragments(
        &mut self,
        first: usize,
        last: usize,
        merged_start: u64,
        merged: Vec<u8>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_databin_fields(self); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost bin = jpip_databin_view(self);
            let ghost owner = *self;
            let ghost merged_bytes = merged@;
        }
        let normalized_capacity = self.fragments.len().checked_add(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
            ))]
            || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
        )?;
        let mut normalized = Vec::with_capacity(normalized_capacity);
        let mut prefix_index = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant prefix_index <= first <= last <= self.fragments.len(),
                *self == owner,
                bin == jpip_databin_view(self),
                bin.1.len() == self.fragments.len(),
                bin.1.len() + 1 <= usize::MAX as nat,
                forall|position: int| 0 <= position < self.fragments.len() ==>
                    #[trigger] bin.1[position] == jpip_stored_fragment_view(&self.fragments@[position]),
                jpip_stored_parts(&normalized) == bin.1.subrange(0, prefix_index as int),
            decreases first - prefix_index,
        ))]
        while prefix_index < first {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(jpip_stored_parts); }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous_normalized = jpip_stored_parts(&normalized); }
            normalized.push(
                self.fragments
                    .get(prefix_index)
                    .ok_or_else(|| {
                        DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow)
                    })?
                    .clone(),
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(jpip_stored_parts(&normalized) =~= previous_normalized.push(bin.1[prefix_index as int]));
            }
            prefix_index += 1;
            #[cfg(verus_keep_ghost)]
            proof! { assert(jpip_stored_parts(&normalized) =~= bin.1.subrange(0, prefix_index as int)); }
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_stored_parts); reveal(jpip_stored_fragment_view); }
        normalized.push(StoredFragment {
            offset: merged_start,
            bytes: merged,
        });
        let mut suffix_index = last;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant first <= last <= suffix_index <= self.fragments.len(),
                *self == owner,
                bin == jpip_databin_view(self),
                bin.1.len() == self.fragments.len(),
                bin.1.len() + 1 <= usize::MAX as nat,
                forall|position: int| 0 <= position < self.fragments.len() ==>
                    #[trigger] bin.1[position] == jpip_stored_fragment_view(&self.fragments@[position]),
                jpip_stored_parts(&normalized) == bin.1.subrange(0, first as int)
                    + seq![(merged_start, merged_bytes)] + bin.1.subrange(last as int, suffix_index as int),
            decreases self.fragments.len() - suffix_index,
        ))]
        while suffix_index < self.fragments.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(jpip_stored_parts); }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous_normalized = jpip_stored_parts(&normalized); }
            normalized.push(
                self.fragments
                    .get(suffix_index)
                    .ok_or_else(|| {
                        DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow)
                    })?
                    .clone(),
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(jpip_stored_parts(&normalized) =~= previous_normalized.push(bin.1[suffix_index as int]));
            }
            suffix_index += 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(jpip_stored_parts(&normalized) =~= bin.1.subrange(0, first as int)
                    + seq![(merged_start, merged_bytes)] + bin.1.subrange(last as int, suffix_index as int));
            }
        }
        self.fragments = normalized;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_databin_view); reveal(jpip_stored_parts); }
        Ok(())
    }

    #[allow(clippy::collapsible_if)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires incoming_end as nat == jpip_fragment_view(fragment).1 as nat
            + (jpip_fragment_view(fragment).2.len() as u64) as nat,
        ensures (result, jpip_databin_view(final(self))) == crate::specs::part2_jpip_insert_final_state(
            jpip_databin_view(old(self)), jpip_fragment_view(fragment), incoming_end, 0),
            result.is_err() ==> *final(self) == *old(self),
    ))]
    fn validate_final_length(
        &mut self,
        fragment: &JpipFragment,
        incoming_end: u64,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_databin_fields(self); jpip_fragment_fields(fragment); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost original = jpip_databin_view(self);
            let ghost owner = *self;
            let ghost incoming = jpip_fragment_view(fragment);
        }
        if let Some(final_length) = self.final_length {
            if incoming_end > final_length {
                return Err(conflict(fragment.offset));
            }
        }
        if let Some(new_final) = fragment.final_length {
            if let Some(final_length) = self.final_length {
                if !crate::refinement::jpip_final_length_consistent(final_length, new_final) {
                    return Err(conflict(fragment.offset));
                }
            }
            let mut stored_index = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant stored_index <= self.fragments.len(),
                    *self == owner,
                    jpip_databin_view(self) == original,
                    original.1.len() == self.fragments.len(),
                    forall|position: int| 0 <= position < self.fragments.len() ==>
                        #[trigger] original.1[position] == (self.fragments@[position].offset, self.fragments@[position].bytes@),
                    incoming == (databin_id_view(fragment.databin), fragment.offset, fragment.bytes@,
                        fragment.final_length, fragment.auxiliary),
                    incoming.3 == Some(new_final),
                    original.2.is_some() ==> original.2.unwrap() == new_final,
                    original.2.is_some() ==> incoming_end <= original.2.unwrap(),
                    crate::specs::part2_jpip_insert_final_state(original, incoming, incoming_end, 0)
                        == crate::specs::part2_jpip_insert_final_state(original, incoming, incoming_end, stored_index as nat),
                decreases self.fragments.len() - stored_index,
            ))]
            while stored_index < self.fragments.len() {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_insert_final_scan); reveal(jpip_stored_fragment_view); }
                if self.fragments[stored_index].end() > new_final {
                    return Err(conflict(fragment.offset));
                }
                stored_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_insert_final_scan); }
            self.final_length = Some(new_final);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_databin_view); }
        Ok(())
    }
}

impl DatabinStatus {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_status_view(self).0,))]
    pub const fn final_length(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_status_fields(self); }
        self.final_length
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_status_view(self).1,))]
    pub const fn contiguous_prefix(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_status_fields(self); }
        self.contiguous_prefix
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_status_view(self).2,))]
    pub const fn stored_bytes(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_status_fields(self); }
        self.stored_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_status_view(self).3,))]
    pub const fn interval_count(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_status_fields(self); }
        self.intervals
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_jpip_status_complete(jpip_status_view(self)),
    ))]
    pub const fn is_complete(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_status_fields(self); }
        match self.final_length {
            Some(length) => {
                crate::refinement::jpip_databin_complete(self.contiguous_prefix, length)
            }
            None => false,
        }
    }
}

impl JpipByteView {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == jpip_byte_view(self),))]
    pub fn as_bytes(&self) -> &[u8] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_byte_view); }
        &self.bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result as nat == jpip_byte_view(self).len(),))]
    pub const fn len(&self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_byte_view); }
        self.bytes.len()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (jpip_byte_view(self).len() == 0),))]
    pub const fn is_empty(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_byte_view); }
        self.bytes.is_empty()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == jpip_byte_view(&self),
            result == *jpip_byte_storage(&self),
    ))]
    pub fn into_bytes(self) -> Vec<u8> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_byte_view); reveal(jpip_byte_storage); }
        self.bytes
    }
}

impl AsRef<[u8]> for JpipByteView {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == jpip_byte_view(self),))]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl DatabinCache {
    pub const fn new(limits: ResourceLimits) -> Self {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Self| {
            vstd::prelude::equal(
                jpip_cache_view(&result),
                crate::specs::part2_jpip_empty_cache(limits),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_cache_view); }
        Self {
            limits,
            databins: Vec::new(),
            stored_bytes: 0,
            accepted_fragments: 0,
        }
    }
}

impl DatabinCache {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_cache_view(self).2,))]
    pub const fn stored_bytes(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); }
        self.stored_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_cache_view(self).3,))]
    pub const fn accepted_fragments(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); }
        self.accepted_fragments
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result as nat == jpip_cache_view(self).1.len(),))]
    pub fn databin_count(&self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); }
        self.databins.len()
    }

    #[allow(clippy::collapsible_if)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, jpip_cache_view(final(self))) == crate::specs::part2_jpip_cache_insert(
                jpip_cache_view(old(self)), jpip_fragment_view(&fragment)),
            result.is_err() ==> *final(self) == *old(self),
    ))]
    pub fn insert(&mut self, fragment: JpipFragment) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); jpip_fragment_fields(&fragment); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost original_cache = jpip_cache_view(self);
            let ghost original_owner = *self;
            let ghost incoming = jpip_fragment_view(&fragment);
            let ghost expected = part2_jpip_insert_result(original_cache, incoming);
        }
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part2_jpip_insert_result_unfold(original_cache, incoming); }
        if !crate::refinement::jpip_standard_class_assigned(fragment.databin.class_identifier()) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipHeader));
        }
        let next_count = self.accepted_fragments.checked_add(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_insert_overflow(fragment.offset),
            ))]
            || DecodeError::malformed(fragment.offset, MalformedKind::ArithmeticOverflow),
        )?;
        if next_count > self.limits.maximum_jpip_fragments() {
            return Err(DecodeError::limit(
                Resource::JpipFragments,
                self.limits.maximum_jpip_fragments(),
                next_count,
            ));
        }
        let index = self.find_databin_index(fragment.databin);
        let mut databin = if let Some(index) = index {
            self.databins
                .get(index)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_insert_overflow(fragment.offset),
                    ))]
                    || DecodeError::malformed(fragment.offset, MalformedKind::ArithmeticOverflow),
                )?
                .clone()
        } else {
            Databin {
                id: fragment.databin,
                fragments: Vec::new(),
                final_length: None,
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! { jpip_databin_fields(&databin); reveal(jpip_databin_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost selected_bin = jpip_databin_view(&databin); }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(index == crate::specs::part2_jpip_find_databin(original_cache.1, incoming.0, 0));
            match index {
                Some(position) => {
                    assert(position < original_cache.1.len());
                    assert(selected_bin == original_cache.1[position as int]);
                },
                None => { assert(selected_bin == (incoming.0, Seq::empty(), None)); },
            }
            assert(next_count as nat == original_cache.3 as nat + 1);
            assert(expected == part2_jpip_insert_bin(original_cache, incoming, index, selected_bin, next_count));
            crate::specs::part2_jpip_insert_bin_remaining_unfold(original_cache, incoming, index, selected_bin, next_count, 0);
        }

        let incoming_end = fragment
            .offset
            .checked_add(fragment.bytes.len() as u64)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_insert_overflow(fragment.offset),
                ))]
                || DecodeError::malformed(fragment.offset, MalformedKind::ArithmeticOverflow),
            )?;
        databin.validate_final_length(&fragment, incoming_end)?;
        #[cfg(verus_keep_ghost)]
        proof! { jpip_databin_fields(&databin); reveal(jpip_databin_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost bin = jpip_databin_view(&databin); }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(expected == part2_jpip_insert_first_result(original_cache, incoming, index, bin, 0, next_count));
        }

        let mut first = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant first <= databin.fragments.len(),
                    jpip_cache_view(self) == original_cache,
                    *self == original_owner,
                    original_cache.3 < u64::MAX,
                    original_cache.3 as nat + 1 <= crate::limits::resource_jpip_fragment_limit(&original_cache.0) as nat,
                    next_count as nat == original_cache.3 as nat + 1,
                    incoming == jpip_fragment_view(&fragment),
                    incoming == (databin_id_view(fragment.databin), fragment.offset, fragment.bytes@,
                        fragment.final_length, fragment.auxiliary),
                    bin == jpip_databin_view(&databin),
                    bin.1 == jpip_stored_parts(&databin.fragments),
                    bin.1.len() == databin.fragments.len(),
                    forall|position: int| 0 <= position < databin.fragments.len() ==>
                        #[trigger] bin.1[position] ==
                            (databin.fragments@[position].offset, databin.fragments@[position].bytes@),
                    incoming_end as nat == incoming.1 as nat + (incoming.2.len() as u64) as nat,
                    expected == part2_jpip_insert_first_result(original_cache, incoming, index, bin, first as nat, next_count),
                    expected == part2_jpip_insert_result(original_cache, incoming),
                decreases databin.fragments.len() - first,
            )
        )]
        while first < databin.fragments.len() && databin.fragments[first].end() < fragment.offset {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(part2_jpip_insert_first); }
            first += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(part2_jpip_insert_first); }
        let mut merged_start = fragment.offset;
        let mut merged_end = incoming_end;
        let mut last = first;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant first <= last <= databin.fragments.len(),
                    jpip_cache_view(self) == original_cache,
                    *self == original_owner,
                    original_cache.3 < u64::MAX,
                    original_cache.3 as nat + 1 <= crate::limits::resource_jpip_fragment_limit(&original_cache.0) as nat,
                    next_count as nat == original_cache.3 as nat + 1,
                    incoming == jpip_fragment_view(&fragment),
                    incoming == (databin_id_view(fragment.databin), fragment.offset, fragment.bytes@,
                        fragment.final_length, fragment.auxiliary),
                    bin == jpip_databin_view(&databin),
                    bin.1 == jpip_stored_parts(&databin.fragments),
                    bin.1.len() == databin.fragments.len(),
                    forall|position: int| 0 <= position < databin.fragments.len() ==>
                        #[trigger] bin.1[position] ==
                            (databin.fragments@[position].offset, databin.fragments@[position].bytes@),
                    incoming_end as nat == incoming.1 as nat + (incoming.2.len() as u64) as nat,
                    merged_start <= fragment.offset,
                    incoming_end <= merged_end,
                    merged_start <= merged_end,
                    expected == part2_jpip_insert_merge_result(original_cache, incoming, index, bin,
                        first as nat, last as nat, merged_start, merged_end, next_count),
                    expected == part2_jpip_insert_result(original_cache, incoming),
                decreases databin.fragments.len() - last,
            )
        )]
        while last < databin.fragments.len() && databin.fragments[last].offset <= merged_end {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(part2_jpip_insert_merge); }
            let stored = &databin.fragments[last];
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(jpip_stored_fragment_view);
                assert(bin.1[last as int] == (stored.offset, stored.bytes@));
            }
            let overlap_start = stored.offset.max(fragment.offset);
            let overlap_end = stored.end().min(incoming_end);
            if overlap_start < overlap_end {
                let stored_start =
                    usize::try_from(overlap_start - stored.offset).map_err(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                        ))]
                        |_error| DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                    )?;
                let incoming_start =
                    usize::try_from(overlap_start - fragment.offset).map_err(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                        ))]
                        |_error| DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                    )?;
                let overlap_length =
                    usize::try_from(overlap_end - overlap_start).map_err(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                        ))]
                        |_error| DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                    )?;
                let stored_end = stored_start.checked_add(overlap_length).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                    ))]
                    || DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                )?;
                let incoming_end = incoming_start.checked_add(overlap_length).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                    ))]
                    || DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                )?;
                let stored_overlap =
                    stored.bytes.get(stored_start..stored_end).ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                        ))]
                        || DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                    )?;
                let incoming_overlap = fragment
                    .bytes
                    .get(incoming_start..incoming_end)
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_insert_overflow(overlap_start),
                        ))]
                        || DecodeError::malformed(overlap_start, MalformedKind::ArithmeticOverflow),
                    )?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(<[u8] as vstd::std_specs::cmp::PartialEqSpec>::obeys_eq_spec());
                    assert(stored_overlap@ == stored.bytes@.subrange(stored_start as int, stored_end as int));
                    assert(incoming_overlap@ == fragment.bytes@.subrange(incoming_start as int, incoming_end as int));
                }
                if !crate::refinement::jpip_overlap_consistent(stored_overlap == incoming_overlap) {
                    return Err(conflict(overlap_start));
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(vstd::std_specs::cmp::PartialEqSpec::eq_spec(stored_overlap, incoming_overlap));
                    assert(stored_overlap@ =~= incoming_overlap@);
                    assert(crate::specs::part2_jpip_insert_overlap(bin.1[last as int], incoming,
                        (incoming.1 as nat + (incoming.2.len() as u64) as nat) as u64).is_none());
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_jpip_insert_overlap(bin.1[last as int], incoming, incoming_end).is_none());
            }
            merged_start = crate::refinement::jpip_merge_start(merged_start, stored.offset);
            merged_end = crate::refinement::jpip_merge_end(merged_end, stored.end());
            last += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(part2_jpip_insert_merge);
            assert(expected == part2_jpip_insert_finish(original_cache, incoming, index, bin,
                first as nat, (last as nat, merged_start, merged_end), next_count));
        }

        let merged_span = merged_end.checked_sub(merged_start).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
            ))]
            || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
        )?;
        let merged_length = usize::try_from(merged_span).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
                ))]
            |_error| DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
        )?;
        let mut replaced_bytes = 0_u64;
        let mut replaced_index = first;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant first <= replaced_index <= last <= databin.fragments.len(),
                    jpip_cache_view(self) == original_cache,
                    *self == original_owner,
                    original_cache.3 < u64::MAX,
                    original_cache.3 as nat + 1 <= crate::limits::resource_jpip_fragment_limit(&original_cache.0) as nat,
                    next_count as nat == original_cache.3 as nat + 1,
                    incoming == jpip_fragment_view(&fragment),
                    incoming == (databin_id_view(fragment.databin), fragment.offset, fragment.bytes@,
                        fragment.final_length, fragment.auxiliary),
                    bin == jpip_databin_view(&databin),
                    bin.1 == jpip_stored_parts(&databin.fragments),
                    bin.1.len() == databin.fragments.len(),
                    forall|position: int| 0 <= position < databin.fragments.len() ==>
                        #[trigger] bin.1[position] ==
                            (databin.fragments@[position].offset, databin.fragments@[position].bytes@),
                    expected == part2_jpip_insert_sum(original_cache, incoming, index, bin,
                        first as nat, replaced_index as nat, last as nat, merged_start,
                        merged_length, replaced_bytes, next_count),
                    expected == part2_jpip_insert_result(original_cache, incoming),
                decreases last as int - replaced_index as int,
            )
        )]
        while replaced_index < last {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(part2_jpip_insert_replaced); }
            replaced_bytes = replaced_bytes
                .checked_add(
                    databin
                        .fragments
                        .get(replaced_index)
                        .ok_or_else(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
                            ))]
                            || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
                        )?
                        .bytes
                        .len() as u64,
                )
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
                    ))]
                    || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
                )?;
            replaced_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(part2_jpip_insert_replaced);
            assert(expected == part2_jpip_insert_account(original_cache, incoming, index, bin,
                first as nat, last as nat, merged_start, merged_length, replaced_bytes, next_count));
        }
        let added_bytes = (merged_length as u64)
            .checked_sub(replaced_bytes)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
                ))]
                || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
            )?;
        let new_stored_bytes = self.stored_bytes.checked_add(added_bytes).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
            ))]
            || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
        )?;
        if new_stored_bytes > self.limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.limits.maximum_input_bytes(),
                new_stored_bytes,
            ));
        }

        let mut merged = vec![0_u8; merged_length];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(merged@ == Seq::new(merged_length as nat, |_: int| 0u8));
            assert(new_stored_bytes as nat == original_cache.2 as nat + (merged_length as u64) as nat - replaced_bytes as nat);
            assert(expected == part2_jpip_insert_stored_copy(original_cache, incoming, index, bin,
                first as nat, first as nat, last as nat, merged_start, merged@, new_stored_bytes, next_count));
        }
        let mut stored_index = first;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant first <= stored_index <= last <= databin.fragments.len(),
                    jpip_cache_view(self) == original_cache,
                    *self == original_owner,
                    original_cache.3 < u64::MAX,
                    original_cache.3 as nat + 1 <= crate::limits::resource_jpip_fragment_limit(&original_cache.0) as nat,
                    next_count as nat == original_cache.3 as nat + 1,
                    incoming == jpip_fragment_view(&fragment),
                    incoming == (databin_id_view(fragment.databin), fragment.offset, fragment.bytes@,
                        fragment.final_length, fragment.auxiliary),
                    bin == jpip_databin_view(&databin),
                    bin.1 == jpip_stored_parts(&databin.fragments),
                    bin.1.len() == databin.fragments.len(),
                    forall|position: int| 0 <= position < databin.fragments.len() ==>
                        #[trigger] bin.1[position] ==
                            (databin.fragments@[position].offset, databin.fragments@[position].bytes@),
                    expected == part2_jpip_insert_stored_copy(original_cache, incoming, index, bin,
                        first as nat, stored_index as nat, last as nat, merged_start,
                        merged@, new_stored_bytes, next_count),
                    expected == part2_jpip_insert_result(original_cache, incoming),
                decreases last as int - stored_index as int,
            )
        )]
        while stored_index < last {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(part2_jpip_insert_copy_stored); }
            let stored = databin.fragments.get(stored_index).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_insert_overflow(merged_start),
                ))]
                || DecodeError::malformed(merged_start, MalformedKind::ArithmeticOverflow),
            )?;
            #[cfg(verus_keep_ghost)]
            proof! { assert(bin.1[stored_index as int] == (stored.offset, stored.bytes@)); }
            let relative = stored.offset.checked_sub(merged_start).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_insert_overflow(stored.offset),
                ))]
                || DecodeError::malformed(stored.offset, MalformedKind::ArithmeticOverflow),
            )?;
            let start = usize::try_from(relative).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_insert_overflow(stored.offset),
                ))]
                |_error| DecodeError::malformed(stored.offset, MalformedKind::ArithmeticOverflow),
            )?;
            copy_into(&mut merged, start, &stored.bytes, stored.offset)?;
            stored_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(part2_jpip_insert_copy_stored);
            assert(expected == part2_jpip_insert_incoming_copy(original_cache, incoming, index, bin,
                first as nat, last as nat, merged_start, merged@, new_stored_bytes, next_count));
        }
        let incoming_relative = fragment.offset.checked_sub(merged_start).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_insert_overflow(fragment.offset),
            ))]
            || DecodeError::malformed(fragment.offset, MalformedKind::ArithmeticOverflow),
        )?;
        let incoming_start = usize::try_from(incoming_relative).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_insert_overflow(fragment.offset),
            ))]
            |_error| DecodeError::malformed(fragment.offset, MalformedKind::ArithmeticOverflow),
        )?;
        copy_into(
            &mut merged,
            incoming_start,
            &fragment.bytes,
            fragment.offset,
        )?;

        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost merged_bytes = merged@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(expected == part2_jpip_insert_commit(original_cache, index, bin,
                first as nat, last as nat, merged_start, merged_bytes, new_stored_bytes, next_count));
        }
        databin.normalize_fragments(first, last, merged_start, merged)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(jpip_databin_view); reveal(jpip_stored_parts);
            assert(jpip_databin_view(&databin) == (bin.0, part2_jpip_insert_normalize(bin.1,
                first as nat, last as nat, merged_start, merged_bytes), bin.2));
            jpip_cache_fields(self);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost committed_bin = jpip_databin_view(&databin); }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(expected == match index {
                Some(position) => Ok((original_cache.0, original_cache.1.update(position as int, committed_bin),
                    new_stored_bytes, next_count)),
                None => Ok((original_cache.0, original_cache.1.push(committed_bin), new_stored_bytes, next_count)),
            });
        }

        if !crate::refinement::jpip_transaction_commit(true) {
            return Err(conflict(fragment.offset));
        }
        if let Some(index) = index {
            self.databins[index] = databin;
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(jpip_cache_view);
                assert(jpip_cache_view(self).1 =~= original_cache.1.update(index as int, committed_bin));
            }
        } else {
            self.databins.push(databin);
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(jpip_cache_view);
                assert(jpip_cache_view(self).1 =~= original_cache.1.push(committed_bin));
            }
        }
        self.stored_bytes = new_stored_bytes;
        self.accepted_fragments = next_count;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(jpip_cache_view);
            assert(expected == Ok(jpip_cache_view(self)));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_status_outcome(result) == crate::specs::part2_jpip_cache_status(jpip_cache_view(self), databin_id_view(id)),
    ))]
    pub fn status(&self, id: DatabinId) -> Option<DatabinStatus> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); }
        let index = self.find_databin_index(id)?;
        let databin = self.databins.get(index)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            jpip_databin_fields(databin);
            assert(crate::specs::part2_jpip_cache_status(jpip_cache_view(self), databin_id_view(id)) ==
                Some(crate::specs::part2_jpip_databin_status(jpip_databin_view(databin))));
        }
        let mut prefix = 0_u64;
        let mut bytes = 0_u64;
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= databin.fragments.len(),
                    crate::specs::part2_jpip_cache_status(jpip_cache_view(self), databin_id_view(id)) ==
                        Some(crate::specs::part2_jpip_databin_status(jpip_databin_view(databin))),
                    jpip_databin_view(databin).2 == databin.final_length,
                    jpip_databin_view(databin).1.len() == databin.fragments.len(),
                    forall|position: int| 0 <= position < databin.fragments.len() ==>
                        #[trigger] jpip_databin_view(databin).1[position] ==
                            (databin.fragments@[position].offset, databin.fragments@[position].bytes@),
                    forall|position: int| 0 <= position < databin.fragments.len() ==>
                        #[trigger] jpip_databin_view(databin).1[position] ==
                            jpip_stored_fragment_view(&databin.fragments@[position]),
                    crate::specs::part2_jpip_status_scan(jpip_databin_view(databin).1, 0, 0, 0) ==
                        crate::specs::part2_jpip_status_scan(jpip_databin_view(databin).1, index as nat, prefix, bytes),
                decreases databin.fragments.len() - index,
            )
        )]
        while index < databin.fragments.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_status_scan); }
            let fragment = &databin.fragments[index];
            bytes = bytes.saturating_add(fragment.bytes.len() as u64);
            if fragment.offset == prefix {
                prefix = fragment.end();
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_status_scan);
            reveal(jpip_status_view);
            assert(crate::specs::part2_jpip_status_scan(jpip_databin_view(databin).1, 0, 0, 0) == (prefix, bytes));
            assert(crate::specs::part2_jpip_databin_status(jpip_databin_view(databin)) ==
                (databin.final_length, prefix, bytes, databin.fragments.len() as u64));
            assert(crate::specs::part2_jpip_cache_status(jpip_cache_view(self), databin_id_view(id)) ==
                Some((databin.final_length, prefix, bytes, databin.fragments.len() as u64)));
        }
        Some(DatabinStatus {
            final_length: databin.final_length,
            contiguous_prefix: prefix,
            stored_bytes: bytes,
            intervals: databin.fragments.len() as u64,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_jpip_cache_complete(jpip_cache_view(self), databin_id_view(id)),
    ))]
    pub fn is_complete(&self, id: DatabinId) -> bool {
        match self.status(id) {
            Some(status) => status.is_complete(),
            None => false,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_byte_outcome(result) == crate::specs::part2_jpip_cache_view(jpip_cache_view(self), databin_id_view(id)),
    ))]
    pub fn databin_view(&self, id: DatabinId) -> Result<JpipByteView, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); reveal(jpip_byte_view); }
        let index = self
            .find_databin_index(id)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure),
                ))]
                || DecodeError::malformed(0, MalformedKind::MissingRequiredStructure),
            )?;
        let databin = self
            .databins
            .get(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                ))]
                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?;
        #[cfg(verus_keep_ghost)]
        proof! { jpip_databin_fields(databin); }
        let status = self
            .status(id)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure),
                ))]
                || DecodeError::malformed(0, MalformedKind::MissingRequiredStructure),
            )?;
        if !status.is_complete() {
            #[cfg(verus_keep_ghost)]
            proof! { jpip_status_fields(&status); }
            return Err(DecodeError::malformed(
                status.contiguous_prefix,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        let bytes = if databin.fragments.is_empty() {
            Vec::new()
        } else {
            databin.fragments[0].bytes.clone()
        };
        Ok(JpipByteView { bytes })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == crate::specs::part2_jpip_cache_prefix(jpip_cache_view(self), databin_id_view(id)),
    ))]
    pub(super) fn databin_prefix(&self, id: DatabinId) -> Vec<u8> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); }
        let Some(index) = self.find_databin_index(id) else {
            return Vec::new();
        };
        let Some(databin) = self.databins.get(index) else {
            return Vec::new();
        };
        #[cfg(verus_keep_ghost)]
        proof! { jpip_databin_fields(databin); }
        let Some(first) = databin.fragments.first() else {
            return Vec::new();
        };
        if first.offset != 0 {
            return Vec::new();
        }
        first.bytes.clone()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_jpip_find_databin(jpip_cache_view(self).1, databin_id_view(id), 0),
    ))]
    pub(super) fn find_databin_index(&self, id: DatabinId) -> Option<usize> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.databins.len(),
                    jpip_cache_view(self).1.len() == self.databins.len(),
                    forall|position: int| 0 <= position < self.databins.len() ==>
                        #[trigger] jpip_cache_view(self).1[position].0 == databin_id_view(self.databins@[position].id),
                    crate::specs::part2_jpip_find_databin(jpip_cache_view(self).1, databin_id_view(id), 0)
                        == crate::specs::part2_jpip_find_databin(jpip_cache_view(self).1, databin_id_view(id), index as nat),
                decreases self.databins.len() - index,
            )
        )]
        while index < self.databins.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_find_databin); }
            if self.databins[index].id.same_as(id) {
                return Some(index);
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_find_databin); }
        None
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_byte_outcome(result) == crate::specs::part2_jpip_cache_reconstruct(jpip_cache_view(self), jpip_layout_view(layout)),
    ))]
    pub(super) fn reconstruct(&self, layout: &[DatabinId]) -> Result<JpipByteView, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); reveal(jpip_byte_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost cache = jpip_cache_view(self);
            let ghost identifiers = jpip_layout_view(layout);
        }
        let mut total = 0_u64;
        let mut parts = Vec::with_capacity(layout.len());
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_reconstruct_prefix);
            assert(jpip_view_parts(&parts) =~= Seq::<Seq<u8>>::empty());
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= layout.len(),
                    cache == jpip_cache_view(self),
                    cache.0 == self.limits,
                    identifiers == jpip_layout_view(layout),
                    identifiers.len() == layout.len(),
                    forall|position: int| 0 <= position < layout.len() ==>
                        #[trigger] identifiers[position] == databin_id_view(layout@[position]),
                    parts.len() == index,
                    crate::specs::part2_jpip_reconstruct_prefix(cache, identifiers, index as nat) ==
                        Ok((jpip_view_parts(&parts), total)),
                decreases layout.len() - index,
            )
        )]
        while index < layout.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error) = crate::specs::part2_jpip_cache_view(cache, identifiers[index as int]) {
                    reveal(crate::specs::part2_jpip_reconstruct_prefix);
                    crate::specs::part2_jpip_reconstruct_error_persists(cache, identifiers, index as nat + 1, identifiers.len(), error);
                }
            }
            let view = self.databin_view(layout[index])?;
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(jpip_byte_view);
                reveal(crate::specs::part2_jpip_reconstruct_prefix);
                let next_total = total as nat + (jpip_byte_view(&view).len() as u64) as nat;
                if next_total > u64::MAX as nat {
                    crate::specs::part2_jpip_reconstruct_error_persists(cache, identifiers, index as nat + 1, identifiers.len(),
                        crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow));
                } else if next_total > crate::limits::resource_input_byte_limit(&cache.0) as nat {
                    crate::specs::part2_jpip_reconstruct_error_persists(cache, identifiers, index as nat + 1, identifiers.len(),
                        DecodeError::LimitExceeded { resource: Resource::InputBytes,
                            limit: crate::limits::resource_input_byte_limit(&cache.0), actual: next_total as u64 });
                }
            }
            total = total
                .checked_add(view.bytes.len() as u64)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                    ))]
                    || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
            if total > self.limits.maximum_input_bytes() {
                return Err(DecodeError::limit(
                    Resource::InputBytes,
                    self.limits.maximum_input_bytes(),
                    total,
                ));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_parts = jpip_view_parts(&parts);
                let ghost current_bytes = jpip_byte_view(&view);
            }
            parts.push(view);
            #[cfg(verus_keep_ghost)]
            proof! { assert(jpip_view_parts(&parts) =~= previous_parts.push(current_bytes)); }
            index += 1;
        }
        let contracted_total = crate::refinement::jpip_reconstruction_length(total, 0, 0, 0);
        let capacity = usize::try_from(contracted_total)
            .map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                ))]
                |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?;
        let mut bytes = Vec::with_capacity(capacity);
        let mut part_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_flatten_prefix); }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant part_index <= parts.len(),
                    cache == jpip_cache_view(self),
                    identifiers == jpip_layout_view(layout),
                    crate::specs::part2_jpip_reconstruct_prefix(cache, identifiers, identifiers.len()) ==
                        Ok((jpip_view_parts(&parts), total)),
                    contracted_total == total as u128,
                    contracted_total as nat <= usize::MAX as nat,
                    jpip_view_parts(&parts).len() == parts.len(),
                    forall|position: int| 0 <= position < parts.len() ==>
                        #[trigger] jpip_view_parts(&parts)[position] == parts@[position].bytes@,
                    bytes@ == crate::specs::part2_jpip_flatten_prefix(jpip_view_parts(&parts), part_index as nat),
                decreases parts.len() - part_index,
            )
        )]
        while part_index < parts.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_flatten_prefix); }
            bytes.extend_from_slice(&parts[part_index].bytes);
            part_index += 1;
        }
        Ok(JpipByteView { bytes })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_jpip_insert_conflict(offset),
))]
const fn conflict(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::ConflictingJpipFragment)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result@ == crate::specs::part2_jpip_copy_bytes(input@),
))]
pub(super) fn copy_bytes(input: &[u8]) -> Vec<u8> {
    let mut output = Vec::with_capacity(input.len());
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= input.len(),
                output@ == input@.subrange(0, index as int),
            decreases input.len() - index,
        )
    )]
    while index < input.len() {
        output.push(input[index]);
        index += 1;
    }
    output
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part2_jpip_copy_into(old(output)@, output_start, input@, error_offset),
))]
fn copy_into(
    output: &mut [u8],
    output_start: usize,
    input: &[u8],
    error_offset: u64,
) -> Result<(), DecodeError> {
    let output_end = output_start
        .checked_add(input.len())
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_fragment_error(error_offset, MalformedKind::ArithmeticOverflow),
            ))]
            || DecodeError::malformed(error_offset, MalformedKind::ArithmeticOverflow),
        )?;
    let target = output
        .get_mut(output_start..output_end)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_fragment_error(error_offset, MalformedKind::ArithmeticOverflow),
            ))]
            || DecodeError::malformed(error_offset, MalformedKind::ArithmeticOverflow),
        )?;
    target.copy_from_slice(input);
    Ok(())
}
