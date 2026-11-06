//! Actual bounded raw-box traversal, borrowed payloads and sticky failure state.

use super::*;

verus! {

pub struct Part2BoxReaderState {
    pub input: Seq<u8>,
    pub limits: crate::ResourceLimits,
    pub position: usize,
    pub metadata_bytes: u64,
    pub work_units: u64,
    pub failed: bool,
}

pub type Part2BoxHeader = (crate::jp2::BoxType, u64, u64, u64);
pub type Part2BoxReference = (Part2BoxHeader, Seq<u8>);
pub type Part2BoxRead = (Result<Option<Part2BoxReference>, crate::DecodeError>, Part2BoxReaderState);

pub open spec fn part2_box_u16(bytes: [u8; 2]) -> u16 {
    ((bytes[0] as u16) << 8) | bytes[1] as u16
}

pub open spec fn part2_box_u32(bytes: [u8; 4]) -> u32 {
    ((bytes[0] as u32) << 24) | ((bytes[1] as u32) << 16) | ((bytes[2] as u32) << 8) | bytes[3] as u32
}

pub open spec fn part2_box_u64(bytes: [u8; 8]) -> u64 {
    ((bytes[0] as u64) << 56) | ((bytes[1] as u64) << 48) | ((bytes[2] as u64) << 40)
        | ((bytes[3] as u64) << 32) | ((bytes[4] as u64) << 24) | ((bytes[5] as u64) << 16)
        | ((bytes[6] as u64) << 8) | bytes[7] as u64
}

pub open spec fn part2_box_reader_from_input(input: Seq<u8>, limits: crate::ResourceLimits)
    -> Result<Part2BoxReaderState, crate::DecodeError>
{
    let length = input.len() as u64;
    if length > crate::limits::resource_input_byte_limit(&limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
            limit: crate::limits::resource_input_byte_limit(&limits), actual: length })
    } else {
        Ok(Part2BoxReaderState { input, limits, position: 0, metadata_bytes: 0, work_units: 0, failed: false })
    }
}

pub open spec fn part2_box_malformed(position: usize, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: position as u64, kind }
}

pub open spec fn part2_box_payload_offset(header: Part2BoxHeader) -> Result<u64, crate::DecodeError> {
    let offset = header.1 as nat + header.2 as nat;
    if offset > u64::MAX as nat {
        Err(crate::DecodeError::MalformedInput { offset: header.1, kind: crate::MalformedKind::ArithmeticOverflow })
    } else { Ok(offset as u64) }
}

pub open spec fn part2_box_payload_length(header: Part2BoxHeader) -> Result<u64, crate::DecodeError> {
    if header.3 < header.2 {
        Err(crate::DecodeError::MalformedInput { offset: header.1, kind: crate::MalformedKind::InvalidBoxLength })
    } else { Ok((header.3 - header.2) as u64) }
}

pub open spec fn part2_box_byte_at(input: Seq<u8>, position: usize, delta: usize, offset: u64)
    -> Result<u8, crate::DecodeError>
{
    let index = position as nat + delta as nat;
    if index > usize::MAX as nat {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::ArithmeticOverflow })
    } else if index >= input.len() {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
    } else { Ok(input[index as int]) }
}

pub open spec fn part2_box_add_offset(base: u64, relative: u64) -> Result<u64, crate::DecodeError> {
    let offset = base as nat + relative as nat;
    if offset > u64::MAX as nat {
        Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::ArithmeticOverflow })
    } else { Ok(offset as u64) }
}

pub open spec fn part2_box_rebase_error(error: crate::DecodeError, base: u64) -> crate::DecodeError {
    match error {
        crate::DecodeError::MalformedInput { offset, kind } => {
            let rebased = base as nat + offset as nat;
            if rebased > u64::MAX as nat {
                crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::ArithmeticOverflow }
            } else { crate::DecodeError::MalformedInput { offset: rebased as u64, kind } }
        },
        other => other,
    }
}

pub open spec fn part2_box_type_at(input: Seq<u8>, position: usize, offset: u64)
    -> Result<crate::jp2::BoxType, crate::DecodeError>
{
    if position as nat + 1 > usize::MAX as nat || position as nat + 2 > usize::MAX as nat
        || position as nat + 3 > usize::MAX as nat {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::ArithmeticOverflow })
    } else if position as nat + 3 >= input.len() {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
    } else { Ok(crate::jp2::box_type_from_bytes_model([input[position as int], input[position as int + 1],
        input[position as int + 2], input[position as int + 3]])) }
}

#[verifier::opaque]
pub open spec fn part2_box_reader_after_header(
    state: Part2BoxReaderState, kind: crate::jp2::BoxType, header_length: u64, total_length: u64,
) -> Part2BoxRead {
    if total_length < header_length {
        (Err(part2_box_malformed(state.position, crate::MalformedKind::InvalidBoxLength)), state)
    } else if total_length as nat > usize::MAX as nat {
        (Err(part2_box_malformed(state.position, crate::MalformedKind::InvalidBoxLength)), state)
    } else {
        let end = state.position as nat + total_length as nat;
        if end > usize::MAX as nat {
            (Err(part2_box_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
        } else if end > state.input.len() {
            (Err(part2_box_malformed(state.position, crate::MalformedKind::Truncated)), state)
        } else if header_length as nat > usize::MAX as nat {
            (Err(part2_box_malformed(state.position, crate::MalformedKind::InvalidBoxLength)), state)
        } else {
            let payload_start = state.position as nat + header_length as nat;
            if payload_start > usize::MAX as nat {
                (Err(part2_box_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
            } else {
                let metadata = state.metadata_bytes as nat
                    + if kind == crate::jp2::BoxType::CONTIGUOUS_CODESTREAM { 0nat } else { total_length as nat };
                if metadata > u64::MAX as nat {
                    (Err(part2_box_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
                } else {
                    let charged = Part2BoxReaderState { metadata_bytes: metadata as u64, ..state };
                    if kind != crate::jp2::BoxType::CONTIGUOUS_CODESTREAM
                        && metadata > crate::limits::resource_metadata_byte_limit(&state.limits) {
                        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::MetadataBytes,
                            limit: crate::limits::resource_metadata_byte_limit(&state.limits), actual: metadata as u64 }), charged)
                    } else {
                        (Ok(Some(((kind, state.position as u64, header_length, total_length),
                            state.input.subrange(payload_start as int, end as int)))),
                            Part2BoxReaderState { position: end as usize, ..charged })
                    }
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_box_reader_after_work(state: Part2BoxReaderState) -> Part2BoxRead {
    let position = state.position as int;
    if position > state.input.len() {
        (Err(part2_box_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let remaining = (state.input.len() - position) as nat;
        if remaining < 8 {
            (Err(part2_box_malformed(state.position, crate::MalformedKind::Truncated)), state)
        } else {
            let length = part2_box_u32([state.input[position], state.input[position + 1], state.input[position + 2], state.input[position + 3]]);
            let kind = crate::jp2::box_type_from_bytes_model(
                [state.input[position + 4], state.input[position + 5], state.input[position + 6], state.input[position + 7]]);
            if length == 0 { part2_box_reader_after_header(state, kind, 8, remaining as u64) }
            else if length == 1 {
                if remaining < 16 { (Err(part2_box_malformed(state.position, crate::MalformedKind::Truncated)), state) }
                else {
                    let extended = part2_box_u64([state.input[position + 8], state.input[position + 9],
                        state.input[position + 10], state.input[position + 11], state.input[position + 12],
                        state.input[position + 13], state.input[position + 14], state.input[position + 15]]);
                    part2_box_reader_after_header(state, kind, 16, extended)
                }
            } else if length < 8 {
                (Err(part2_box_malformed(state.position, crate::MalformedKind::InvalidBoxLength)), state)
            } else { part2_box_reader_after_header(state, kind, 8, length as u64) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_box_reader_next(state: Part2BoxReaderState) -> Part2BoxRead {
    if state.position == state.input.len() { (Ok(None), state) }
    else if state.work_units == u64::MAX {
        (Err(part2_box_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let work = (state.work_units as nat + 1) as u64;
        let charged = Part2BoxReaderState { work_units: work, ..state };
        if work > crate::limits::resource_work_limit(&state.limits) {
            (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                limit: crate::limits::resource_work_limit(&state.limits), actual: work }), charged)
        } else { part2_box_reader_after_work(charged) }
    }
}

pub open spec fn part2_box_reader_next_ref(state: Part2BoxReaderState)
    -> (Option<Result<Part2BoxReference, crate::DecodeError>>, Part2BoxReaderState)
{
    if state.failed { (None, state) }
    else {
        let next = part2_box_reader_next(state);
        match next.0 {
            Ok(None) => (None, next.1),
            Ok(Some(value)) => (Some(Ok(value)), next.1),
            Err(error) => (Some(Err(error)), Part2BoxReaderState { failed: true, ..next.1 }),
        }
    }
}

pub open spec fn part2_box_reader_required(state: Part2BoxReaderState, expected: u64)
    -> (Result<Part2BoxReference, crate::DecodeError>, Part2BoxReaderState)
{
    let next = part2_box_reader_next_ref(state);
    match next.0 {
        Some(result) => (result, next.1),
        None => (Err(crate::DecodeError::MalformedInput {
            offset: expected, kind: crate::MalformedKind::MissingRequiredStructure }), next.1),
    }
}

}
