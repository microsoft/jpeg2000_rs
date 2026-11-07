//! Actual owned JPIP entries, byte copies and empty/cache-lookup foundations.

use super::*;

verus! {

pub type Part2JpipFragment = (Part2JpipDatabin, u64, Seq<u8>, Option<u64>, Option<u64>);
pub type Part2JpipStoredFragment = (u64, Seq<u8>);
pub type Part2JpipDatabinState = (Part2JpipDatabin, Seq<Part2JpipStoredFragment>, Option<u64>);
pub type Part2JpipCache = (crate::ResourceLimits, Seq<Part2JpipDatabinState>, u64, u64);
pub type Part2JpipStatus = (Option<u64>, u64, u64, u64);

pub open spec fn part2_jpip_fragment_error(offset: u64, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset, kind }
}

pub open spec fn part2_jpip_fragment_new(
    databin: Part2JpipDatabin, offset: u64, bytes: Seq<u8>, last: bool, auxiliary: Option<u64>,
    limits: &crate::ResourceLimits,
) -> Result<Part2JpipFragment, crate::DecodeError> {
    if bytes.len() == 0 && !last {
        Err(part2_jpip_fragment_error(offset, crate::MalformedKind::InvalidJpipFragment))
    } else {
        let length = bytes.len() as u64;
        let end = offset as nat + length as nat;
        if end > u64::MAX as nat {
            Err(part2_jpip_fragment_error(offset, crate::MalformedKind::ArithmeticOverflow))
        } else if !valid_jpip_fragment(offset as nat, length as nat, crate::limits::resource_input_byte_limit(limits) as nat) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(limits), actual: end as u64 })
        } else { Ok((databin, offset, bytes, if last { Some(end as u64) } else { None }, auxiliary)) }
    }
}

pub open spec fn part2_jpip_fragment_from_message(
    header: Part2JpipHeader, body: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part2JpipFragment, crate::DecodeError> {
    if body.len() as u64 != header.2 {
        Err(part2_jpip_fragment_error(header.1, crate::MalformedKind::InvalidJpipFragment))
    } else { part2_jpip_fragment_new(header.0, header.1, body, header.3, header.4, limits) }
}

pub open spec fn part2_jpip_stored_end(fragment: Part2JpipStoredFragment) -> u64 {
    let end = fragment.0 as nat + (fragment.1.len() as u64) as nat;
    if end > u64::MAX as nat { u64::MAX } else { end as u64 }
}

pub open spec fn part2_jpip_copy_bytes(input: Seq<u8>) -> Seq<u8> { input }

pub open spec fn part2_jpip_copy_into(
    output: Seq<u8>, start: usize, input: Seq<u8>, offset: u64,
) -> (Result<(), crate::DecodeError>, Seq<u8>) {
    let end = start as nat + input.len();
    if end > usize::MAX as nat || end > output.len() {
        (Err(part2_jpip_fragment_error(offset, crate::MalformedKind::ArithmeticOverflow)), output)
    } else {
        (Ok(()), Seq::new(output.len(), |index: int| if start as int <= index < end as int {
            input[index - start as int]
        } else { output[index] }))
    }
}

pub open spec fn part2_jpip_empty_cache(limits: crate::ResourceLimits) -> Part2JpipCache {
    (limits, Seq::empty(), 0, 0)
}

#[verifier::opaque]
pub open spec fn part2_jpip_find_databin(
    databins: Seq<Part2JpipDatabinState>, id: Part2JpipDatabin, position: nat,
) -> Option<usize>
    decreases if position < databins.len() { databins.len() - position } else { 0 },
{
    if position >= databins.len() { None }
    else if part2_jpip_identity(databins[position as int].0, id) { Some(position as usize) }
    else { part2_jpip_find_databin(databins, id, position + 1) }
}

pub open spec fn part2_jpip_status_complete(status: Part2JpipStatus) -> bool {
    match status.0 { None => false, Some(length) => complete_jpip_databin(status.1 as nat, length as nat) }
}

}
