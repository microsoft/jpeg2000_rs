//! Cache insertion outcomes derived from the original cache and incoming fragment.

use super::*;

verus! {

pub type Part2JpipMerge = (nat, u64, u64);

pub open spec fn part2_jpip_insert_overflow(offset: u64) -> crate::DecodeError {
    part2_jpip_fragment_error(offset, crate::MalformedKind::ArithmeticOverflow)
}

pub open spec fn part2_jpip_insert_conflict(offset: u64) -> crate::DecodeError {
    part2_jpip_fragment_error(offset, crate::MalformedKind::ConflictingJpipFragment)
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_first(
    stored: Seq<Part2JpipStoredFragment>, offset: u64, position: nat,
) -> nat
    decreases if position < stored.len() { stored.len() - position } else { 0 },
{
    if position >= stored.len() || part2_jpip_stored_end(stored[position as int]) >= offset {
        position
    } else { part2_jpip_insert_first(stored, offset, position + 1) }
}

pub open spec fn part2_jpip_insert_overlap(
    stored: Part2JpipStoredFragment, incoming: Part2JpipFragment, incoming_end: u64,
) -> Option<crate::DecodeError> {
    let start = if stored.0 > incoming.1 { stored.0 } else { incoming.1 };
    let end = if part2_jpip_stored_end(stored) < incoming_end {
        part2_jpip_stored_end(stored)
    } else { incoming_end };
    if start >= end { None } else {
        let stored_start = (start - stored.0) as nat;
        let incoming_start = (start - incoming.1) as nat;
        let length = (end - start) as nat;
        if stored_start > usize::MAX as nat || incoming_start > usize::MAX as nat
            || length > usize::MAX as nat
            || stored_start + length > usize::MAX as nat
            || incoming_start + length > usize::MAX as nat
            || stored_start + length > stored.1.len()
            || incoming_start + length > incoming.2.len() {
            Some(part2_jpip_insert_overflow(start))
        } else if stored.1.subrange(stored_start as int, (stored_start + length) as int)
            != incoming.2.subrange(incoming_start as int, (incoming_start + length) as int) {
            Some(part2_jpip_insert_conflict(start))
        } else { None }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_merge(
    stored: Seq<Part2JpipStoredFragment>, incoming: Part2JpipFragment, incoming_end: u64,
    position: nat, start: u64, end: u64,
) -> Result<Part2JpipMerge, crate::DecodeError>
    decreases if position < stored.len() { stored.len() - position } else { 0 },
{
    if position >= stored.len() || stored[position as int].0 > end {
        Ok((position, start, end))
    } else {
        let fragment = stored[position as int];
        match part2_jpip_insert_overlap(fragment, incoming, incoming_end) {
            Some(error) => Err(error),
            None => part2_jpip_insert_merge(stored, incoming, incoming_end, position + 1,
                if start < fragment.0 { start } else { fragment.0 },
                if end > part2_jpip_stored_end(fragment) { end } else { part2_jpip_stored_end(fragment) }),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_replaced(
    stored: Seq<Part2JpipStoredFragment>, position: nat, last: nat, bytes: u64, start: u64,
) -> Result<u64, crate::DecodeError>
    decreases if position < last { last - position } else { 0 },
{
    if position >= last { Ok(bytes) }
    else if position >= stored.len() { Err(part2_jpip_insert_overflow(start)) }
    else {
        let total = bytes as nat + (stored[position as int].1.len() as u64) as nat;
        if total > u64::MAX as nat { Err(part2_jpip_insert_overflow(start)) }
        else { part2_jpip_insert_replaced(stored, position + 1, last, total as u64, start) }
    }
}

pub open spec fn part2_jpip_insert_copy(
    output: Seq<u8>, stored: Part2JpipStoredFragment, start: u64,
) -> Result<Seq<u8>, crate::DecodeError> {
    if stored.0 < start || (stored.0 - start) as nat > usize::MAX as nat {
        Err(part2_jpip_insert_overflow(stored.0))
    } else {
        match part2_jpip_copy_into(output, (stored.0 - start) as usize, stored.1, stored.0) {
            (Err(error), _) => Err(error),
            (Ok(()), bytes) => Ok(bytes),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_copy_stored(
    stored: Seq<Part2JpipStoredFragment>, position: nat, last: nat, start: u64, output: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if position < last { last - position } else { 0 },
{
    if position >= last { Ok(output) }
    else if position >= stored.len() { Err(part2_jpip_insert_overflow(start)) }
    else {
        match part2_jpip_insert_copy(output, stored[position as int], start) {
            Err(error) => Err(error),
            Ok(bytes) => part2_jpip_insert_copy_stored(stored, position + 1, last, start, bytes),
        }
    }
}

pub open spec fn part2_jpip_insert_normalize(
    stored: Seq<Part2JpipStoredFragment>, first: nat, last: nat, start: u64, bytes: Seq<u8>,
) -> Seq<Part2JpipStoredFragment> {
    stored.subrange(0, first as int) + seq![(start, bytes)]
        + stored.subrange(last as int, stored.len() as int)
}

pub open spec fn part2_jpip_insert_commit(
    cache: Part2JpipCache, index: Option<usize>, bin: Part2JpipDatabinState,
    first: nat, last: nat, start: u64, bytes: Seq<u8>, total: u64, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    if bin.1.len() + 1 > usize::MAX as nat {
        Err(part2_jpip_insert_overflow(start))
    } else {
        let updated = (bin.0, part2_jpip_insert_normalize(bin.1, first, last, start, bytes), bin.2);
        match index {
            None => Ok((cache.0, cache.1.push(updated), total, count)),
            Some(index) => Ok((cache.0, cache.1.update(index as int, updated), total, count)),
        }
    }
}

pub open spec fn part2_jpip_insert_incoming_copy(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, first: nat, last: nat, start: u64,
    bytes: Seq<u8>, total: u64, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    match part2_jpip_insert_copy(bytes, (incoming.1, incoming.2), start) {
        Err(error) => Err(error),
        Ok(bytes) => part2_jpip_insert_commit(cache, index, bin, first, last, start, bytes, total, count),
    }
}

pub open spec fn part2_jpip_insert_stored_copy(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, first: nat, position: nat, last: nat, start: u64,
    bytes: Seq<u8>, total: u64, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    match part2_jpip_insert_copy_stored(bin.1, position, last, start, bytes) {
        Err(error) => Err(error),
        Ok(bytes) => part2_jpip_insert_incoming_copy(cache, incoming, index, bin, first, last, start,
            bytes, total, count),
    }
}

pub open spec fn part2_jpip_insert_account(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, first: nat, last: nat, start: u64, length: usize,
    replaced: u64, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    if (length as u64) < replaced
        || cache.2 as nat + ((length as u64) - replaced) as nat > u64::MAX as nat {
        Err(part2_jpip_insert_overflow(start))
    } else {
        let total = (cache.2 as nat + ((length as u64) - replaced) as nat) as u64;
        if total > crate::limits::resource_input_byte_limit(&cache.0) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(&cache.0), actual: total })
        } else {
            part2_jpip_insert_stored_copy(cache, incoming, index, bin, first, first, last, start,
                Seq::new(length as nat, |_: int| 0u8), total, count)
        }
    }
}

pub open spec fn part2_jpip_insert_sum(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, first: nat, position: nat, last: nat,
    start: u64, length: usize, replaced: u64, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    match part2_jpip_insert_replaced(bin.1, position, last, replaced, start) {
        Err(error) => Err(error),
        Ok(replaced) => part2_jpip_insert_account(cache, incoming, index, bin, first, last, start,
            length, replaced, count),
    }
}

pub open spec fn part2_jpip_insert_finish(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, first: nat, merge: Part2JpipMerge, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    let (last, start, end) = merge;
    if end < start || (end - start) as nat > usize::MAX as nat {
        Err(part2_jpip_insert_overflow(start))
    } else {
        let length = (end - start) as usize;
        part2_jpip_insert_sum(cache, incoming, index, bin, first, first, last, start, length, 0, count)
    }
}

pub open spec fn part2_jpip_insert_merge_result(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, first: nat, position: nat, start: u64, end: u64, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    let incoming_end = (incoming.1 as nat + (incoming.2.len() as u64) as nat) as u64;
    match part2_jpip_insert_merge(bin.1, incoming, incoming_end, position, start, end) {
        Err(error) => Err(error),
        Ok(merge) => part2_jpip_insert_finish(cache, incoming, index, bin, first, merge, count),
    }
}

pub open spec fn part2_jpip_insert_first_result(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, position: nat, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    let first = part2_jpip_insert_first(bin.1, incoming.1, position);
    let end = (incoming.1 as nat + (incoming.2.len() as u64) as nat) as u64;
    part2_jpip_insert_merge_result(cache, incoming, index, bin, first, first, incoming.1, end, count)
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_final_scan(
    stored: Seq<Part2JpipStoredFragment>, length: u64, position: nat,
) -> bool
    decreases if position < stored.len() { stored.len() - position } else { 0 },
{
    if position >= stored.len() { true }
    else if part2_jpip_stored_end(stored[position as int]) > length { false }
    else { part2_jpip_insert_final_scan(stored, length, position + 1) }
}

pub open spec fn part2_jpip_insert_final_state(
    bin: Part2JpipDatabinState, incoming: Part2JpipFragment, end: u64, position: nat,
) -> (Result<(), crate::DecodeError>, Part2JpipDatabinState) {
    if (match bin.2 { None => false, Some(length) => end > length })
        || (match incoming.3 { None => false, Some(length) =>
            (match bin.2 { None => false, Some(old_length) => old_length != length })
            || !part2_jpip_insert_final_scan(bin.1, length, position) }) {
        (Err(part2_jpip_insert_conflict(incoming.1)), bin)
    } else {
        (Ok(()), (bin.0, bin.1, match incoming.3 { None => bin.2, Some(length) => Some(length) }))
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_bin_remaining(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, count: u64, position: nat,
) -> Result<Part2JpipCache, crate::DecodeError> {
    let end = incoming.1 as nat + (incoming.2.len() as u64) as nat;
    if end > u64::MAX as nat { Err(part2_jpip_insert_overflow(incoming.1)) }
    else {
        match part2_jpip_insert_final_state(bin, incoming, end as u64, position) {
            (Err(error), _) => Err(error),
            (Ok(()), bin) => part2_jpip_insert_first_result(cache, incoming, index, bin, 0, count),
        }
    }
}

pub proof fn part2_jpip_insert_bin_remaining_unfold(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, count: u64, position: nat,
)
    ensures part2_jpip_insert_bin_remaining(cache, incoming, index, bin, count, position) == {
        let end = incoming.1 as nat + (incoming.2.len() as u64) as nat;
        if end > u64::MAX as nat { Err(part2_jpip_insert_overflow(incoming.1)) }
        else {
            match part2_jpip_insert_final_state(bin, incoming, end as u64, position) {
                (Err(error), _) => Err(error),
                (Ok(()), bin) => part2_jpip_insert_first_result(cache, incoming, index, bin, 0, count),
            }
        }
    },
{
    reveal(part2_jpip_insert_bin_remaining);
}

pub open spec fn part2_jpip_insert_bin(
    cache: Part2JpipCache, incoming: Part2JpipFragment, index: Option<usize>,
    bin: Part2JpipDatabinState, count: u64,
) -> Result<Part2JpipCache, crate::DecodeError> {
    part2_jpip_insert_bin_remaining(cache, incoming, index, bin, count, 0)
}

pub proof fn part2_jpip_insert_final_scan_extent(
    stored: Seq<Part2JpipStoredFragment>, length: u64, position: nat,
)
    ensures part2_jpip_insert_final_scan(stored, length, position)
        == (forall|index: int| position <= index < stored.len() ==>
            part2_jpip_stored_end(#[trigger] stored[index]) <= length),
    decreases if position < stored.len() { stored.len() - position } else { 0 },
{
    reveal(part2_jpip_insert_final_scan);
    if position < stored.len() && part2_jpip_stored_end(stored[position as int]) <= length {
        part2_jpip_insert_final_scan_extent(stored, length, position + 1);
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_insert_result(
    cache: Part2JpipCache, incoming: Part2JpipFragment,
) -> Result<Part2JpipCache, crate::DecodeError> {
    let count = cache.3 as nat + 1;
    if !part9_standard_class_assigned(incoming.0.0 as nat) {
        Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader))
    } else if count > u64::MAX as nat { Err(part2_jpip_insert_overflow(incoming.1)) }
    else if count > crate::limits::resource_jpip_fragment_limit(&cache.0) as nat {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::JpipFragments,
            limit: crate::limits::resource_jpip_fragment_limit(&cache.0), actual: count as u64 })
    } else {
        let index = part2_jpip_find_databin(cache.1, incoming.0, 0);
        match index {
            Some(index) => if index as nat >= cache.1.len() {
                Err(part2_jpip_insert_overflow(incoming.1))
            } else { part2_jpip_insert_bin(cache, incoming, Some(index), cache.1[index as int], count as u64) },
            None => part2_jpip_insert_bin(cache, incoming, None, (incoming.0, Seq::empty(), None), count as u64),
        }
    }
}

pub proof fn part2_jpip_insert_result_unfold(cache: Part2JpipCache, incoming: Part2JpipFragment)
    ensures part2_jpip_insert_result(cache, incoming) == {
        let count = cache.3 as nat + 1;
        if !part9_standard_class_assigned(incoming.0.0 as nat) {
            Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader))
        } else if count > u64::MAX as nat { Err(part2_jpip_insert_overflow(incoming.1)) }
        else if count > crate::limits::resource_jpip_fragment_limit(&cache.0) as nat {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::JpipFragments,
                limit: crate::limits::resource_jpip_fragment_limit(&cache.0), actual: count as u64 })
        } else {
            let index = part2_jpip_find_databin(cache.1, incoming.0, 0);
            match index {
                Some(index) => if index as nat >= cache.1.len() {
                    Err(part2_jpip_insert_overflow(incoming.1))
                } else { part2_jpip_insert_bin(cache, incoming, Some(index), cache.1[index as int], count as u64) },
                None => part2_jpip_insert_bin(cache, incoming, None, (incoming.0, Seq::empty(), None), count as u64),
            }
        }
    },
{
    reveal(part2_jpip_insert_result);
}

pub open spec fn part2_jpip_cache_insert(
    cache: Part2JpipCache, incoming: Part2JpipFragment,
) -> (Result<(), crate::DecodeError>, Part2JpipCache) {
    match part2_jpip_insert_result(cache, incoming) {
        Err(error) => (Err(error), cache),
        Ok(updated) => (Ok(()), updated),
    }
}

pub proof fn part2_jpip_cache_insert_error_frame(cache: Part2JpipCache, incoming: Part2JpipFragment)
    ensures part2_jpip_cache_insert(cache, incoming).0.is_err()
        ==> part2_jpip_cache_insert(cache, incoming).1 == cache,
{}

pub proof fn part2_jpip_insert_first_bounds(
    stored: Seq<Part2JpipStoredFragment>, offset: u64, position: nat,
)
    requires position <= stored.len(),
    ensures position <= part2_jpip_insert_first(stored, offset, position) <= stored.len(),
    decreases stored.len() - position,
{
    reveal(part2_jpip_insert_first);
    if position < stored.len() && part2_jpip_stored_end(stored[position as int]) < offset {
        part2_jpip_insert_first_bounds(stored, offset, position + 1);
    }
}

pub proof fn part2_jpip_insert_merge_bounds(
    stored: Seq<Part2JpipStoredFragment>, incoming: Part2JpipFragment, incoming_end: u64,
    position: nat, start: u64, end: u64,
)
    requires position <= stored.len(), start <= end,
    ensures match part2_jpip_insert_merge(stored, incoming, incoming_end, position, start, end) {
        Err(_) => true,
        Ok(merge) => position <= merge.0 <= stored.len() && merge.1 <= start
            && end <= merge.2 && merge.1 <= merge.2,
    },
    decreases stored.len() - position,
{
    reveal(part2_jpip_insert_merge);
    if position < stored.len() && stored[position as int].0 <= end {
        let fragment = stored[position as int];
        if part2_jpip_insert_overlap(fragment, incoming, incoming_end).is_none() {
            part2_jpip_insert_merge_bounds(stored, incoming, incoming_end, position + 1,
                if start < fragment.0 { start } else { fragment.0 },
                if end > part2_jpip_stored_end(fragment) { end } else { part2_jpip_stored_end(fragment) });
        }
    }
}

}
