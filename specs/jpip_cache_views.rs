//! Actual cache status, first-fragment byte views and layout reconstruction.

use super::*;

verus! {

pub open spec fn part2_jpip_cache_error(offset: u64, kind: crate::MalformedKind) -> crate::DecodeError {
    part2_jpip_fragment_error(offset, kind)
}

#[verifier::opaque]
pub open spec fn part2_jpip_status_scan(
    fragments: Seq<Part2JpipStoredFragment>, position: nat, prefix: u64, bytes: u64,
) -> (u64, u64)
    decreases if position < fragments.len() { fragments.len() - position } else { 0 },
{
    if position >= fragments.len() { (prefix, bytes) }
    else {
        let fragment = fragments[position as int];
        let total = bytes as nat + (fragment.1.len() as u64) as nat;
        let next_bytes = if total > u64::MAX as nat { u64::MAX } else { total as u64 };
        let next_prefix = if fragment.0 == prefix { part2_jpip_stored_end(fragment) } else { prefix };
        part2_jpip_status_scan(fragments, position + 1, next_prefix, next_bytes)
    }
}

pub open spec fn part2_jpip_databin_status(databin: Part2JpipDatabinState) -> Part2JpipStatus {
    let scan = part2_jpip_status_scan(databin.1, 0, 0, 0);
    (databin.2, scan.0, scan.1, databin.1.len() as u64)
}

pub open spec fn part2_jpip_cache_status(cache: Part2JpipCache, id: Part2JpipDatabin)
    -> Option<Part2JpipStatus> {
    match part2_jpip_find_databin(cache.1, id, 0) {
        None => None,
        Some(index) => if index as nat >= cache.1.len() { None }
            else { Some(part2_jpip_databin_status(cache.1[index as int])) },
    }
}

pub open spec fn part2_jpip_cache_complete(cache: Part2JpipCache, id: Part2JpipDatabin) -> bool {
    match part2_jpip_cache_status(cache, id) {
        None => false, Some(status) => part2_jpip_status_complete(status),
    }
}

pub open spec fn part2_jpip_cache_view(cache: Part2JpipCache, id: Part2JpipDatabin)
    -> Result<Seq<u8>, crate::DecodeError> {
    match part2_jpip_find_databin(cache.1, id, 0) {
        None => Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)),
        Some(index) => if index as nat >= cache.1.len() {
            Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
        } else {
            match part2_jpip_cache_status(cache, id) {
                None => Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)),
                Some(status) => if !part2_jpip_status_complete(status) {
                    Err(part2_jpip_cache_error(status.1, crate::MalformedKind::MissingRequiredStructure))
                } else {
                    let fragments = cache.1[index as int].1;
                    Ok(if fragments.len() == 0 { Seq::empty() } else { fragments[0].1 })
                },
            }
        },
    }
}

pub open spec fn part2_jpip_cache_prefix(cache: Part2JpipCache, id: Part2JpipDatabin) -> Seq<u8> {
    match part2_jpip_find_databin(cache.1, id, 0) {
        None => Seq::empty(),
        Some(index) => if index as nat >= cache.1.len() { Seq::empty() } else {
            let fragments = cache.1[index as int].1;
            if fragments.len() == 0 || fragments[0].0 != 0 { Seq::empty() }
            else { fragments[0].1 }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_reconstruct_prefix(
    cache: Part2JpipCache, layout: Seq<Part2JpipDatabin>, position: nat,
) -> Result<(Seq<Seq<u8>>, u64), crate::DecodeError>
    decreases position,
{
    if position == 0 { Ok((Seq::empty(), 0)) } else {
        match part2_jpip_reconstruct_prefix(cache, layout, (position - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_jpip_cache_view(cache, layout[position as int - 1]) {
                Err(error) => Err(error),
                Ok(bytes) => {
                    let total = previous.1 as nat + (bytes.len() as u64) as nat;
                    if total > u64::MAX as nat {
                        Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
                    } else if total > crate::limits::resource_input_byte_limit(&cache.0) as nat {
                        Err(crate::DecodeError::LimitExceeded {
                            resource: crate::Resource::InputBytes,
                            limit: crate::limits::resource_input_byte_limit(&cache.0),
                            actual: total as u64,
                        })
                    } else { Ok((previous.0.push(bytes), total as u64)) }
                },
            },
        }
    }
}

pub proof fn part2_jpip_reconstruct_error_persists(
    cache: Part2JpipCache, layout: Seq<Part2JpipDatabin>, start: nat, end: nat, error: crate::DecodeError,
)
    requires start <= end <= layout.len(),
        part2_jpip_reconstruct_prefix(cache, layout, start) == Err(error),
    ensures part2_jpip_reconstruct_prefix(cache, layout, end) == Err(error),
    decreases end - start,
{
    if start < end {
        reveal(part2_jpip_reconstruct_prefix);
        part2_jpip_reconstruct_error_persists(cache, layout, start + 1, end, error);
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_flatten_prefix(parts: Seq<Seq<u8>>, position: nat) -> Seq<u8>
    decreases position,
{
    if position == 0 { Seq::empty() }
    else { part2_jpip_flatten_prefix(parts, (position - 1) as nat) + parts[position as int - 1] }
}

pub open spec fn part2_jpip_cache_reconstruct(cache: Part2JpipCache, layout: Seq<Part2JpipDatabin>)
    -> Result<Seq<u8>, crate::DecodeError> {
    match part2_jpip_reconstruct_prefix(cache, layout, layout.len()) {
        Err(error) => Err(error),
        Ok(parts) => {
            let length = part9_reconstruction_length(parts.1 as nat, 0, 0, 0);
            if length > usize::MAX as nat {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::ArithmeticOverflow))
            } else { Ok(part2_jpip_flatten_prefix(parts.0, parts.0.len())) }
        },
    }
}

}
