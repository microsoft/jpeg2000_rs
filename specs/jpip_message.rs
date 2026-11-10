//! Actual raw JPIP binary messages, inherited context and partial VBAS cursors.

use super::*;

verus! {

pub type Part2JpipContext = (Option<u64>, Option<u64>);
pub type Part2JpipDatabin = (u64, crate::jpip::DatabinClass, u64, u64);
pub type Part2JpipHeader = (Part2JpipDatabin, u64, u64, bool, Option<u64>, usize);

pub enum Part2JpipMessage {
    Data { header: Part2JpipHeader, body: Seq<u8> },
    EndOfResponse { reason: u8, body: Seq<u8>, header_length: usize },
}

pub type Part2JpipParsed = Result<(Part2JpipMessage, usize), crate::DecodeError>;
pub type Part2JpipParse = (Part2JpipParsed, Part2JpipContext);
pub type Part2JpipVbas = (Result<u64, crate::DecodeError>, usize);

pub open spec fn part2_jpip_error(offset: usize, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: offset as u64, kind }
}

pub open spec fn part2_jpip_class(identifier: u64) -> Option<crate::jpip::DatabinClass> {
    match identifier {
        0 | 1 => Some(crate::jpip::DatabinClass::Precinct),
        2 | 3 => Some(crate::jpip::DatabinClass::TileHeader),
        4 | 5 => Some(crate::jpip::DatabinClass::TileData),
        6 | 7 => Some(crate::jpip::DatabinClass::MainHeader),
        8 => Some(crate::jpip::DatabinClass::Metadata),
        _ => None,
    }
}

pub open spec fn part2_jpip_databin(identifier: u64, codestream: u64, bin: u64)
    -> Result<Part2JpipDatabin, crate::DecodeError> {
    match part2_jpip_class(identifier) {
        None => Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)),
        Some(class) => Ok((identifier, class, codestream, bin)),
    }
}

pub open spec fn part2_jpip_auxiliary(identifier: u64) -> bool {
    part9_auxiliary_present(identifier as nat)
}

pub open spec fn part2_jpip_identity(first: Part2JpipDatabin, second: Part2JpipDatabin) -> bool {
    part9_databin_identity(first.0 as nat, first.2 as nat, first.3 as nat,
        second.0 as nat, second.2 as nat, second.3 as nat)
}

pub open spec fn part2_jpip_final_length(header: Part2JpipHeader) -> Option<u64> {
    if !header.3 { None }
    else {
        let end = header.1 as nat + header.2 as nat;
        Some(if end > u64::MAX as nat { u64::MAX } else { end as u64 })
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_vbas_tail(
    input: Seq<u8>, start: usize, position: usize, value: u64, byte: u8, count: usize,
) -> Part2JpipVbas
    decreases if count < 10 { 10 - count } else { 0 },
{
    if byte & 0x80 == 0 { (Ok(value), position) }
    else if count >= 10 { (Err(part2_jpip_error(start, crate::MalformedKind::InvalidJpipVbas)), position) }
    else if position as nat >= input.len() { (Err(part2_jpip_error(position, crate::MalformedKind::Truncated)), position) }
    else {
        let next = input[position as int];
        let group = next & 0x7f;
        let stepped = value as nat * 128 + group as nat;
        if stepped > u64::MAX as nat {
            (Err(part2_jpip_error(start, crate::MalformedKind::InvalidJpipVbas)), position)
        } else if position == usize::MAX {
            (Err(part2_jpip_error(start, crate::MalformedKind::ArithmeticOverflow)), position)
        } else {
            part2_jpip_vbas_tail(input, start, (position + 1) as usize, stepped as u64, next, (count + 1) as usize)
        }
    }
}

pub open spec fn part2_jpip_read_vbas(input: Seq<u8>, start: usize, mask: Option<u8>) -> Part2JpipVbas {
    if start as nat >= input.len() { (Err(part2_jpip_error(start, crate::MalformedKind::Truncated)), start) }
    else {
        let first = input[start as int];
        let value = first & match mask { None => 0x7f, Some(mask) => mask };
        if start == usize::MAX { (Err(part2_jpip_error(start, crate::MalformedKind::ArithmeticOverflow)), start) }
        else { part2_jpip_vbas_tail(input, start, (start + 1) as usize, value as u64, first, 1) }
    }
}

pub open spec fn part2_jpip_body(
    input: Seq<u8>, position: usize, length: u64,
) -> Result<(Seq<u8>, usize), crate::DecodeError> {
    if length as nat > usize::MAX as nat || position as nat + length as nat > usize::MAX as nat {
        Err(part2_jpip_error(position, crate::MalformedKind::ArithmeticOverflow))
    } else {
        let end = (position as nat + length as nat) as usize;
        if end as nat > input.len() { Err(part2_jpip_error(position, crate::MalformedKind::Truncated)) }
        else { Ok((input.subrange(position as int, end as int), end)) }
    }
}

pub open spec fn part2_jpip_eor(input: Seq<u8>) -> Part2JpipParsed {
    if input.len() < 2 { Err(part2_jpip_error(1, crate::MalformedKind::Truncated)) }
    else {
        let length = part2_jpip_read_vbas(input, 2, None);
        match length.0 {
            Err(error) => Err(error),
            Ok(value) => match part2_jpip_body(input, length.1, value) {
                Err(error) => Err(error),
                Ok(body) => Ok((Part2JpipMessage::EndOfResponse {
                    reason: input[1], body: body.0, header_length: length.1,
                }, body.1)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_data_after_identity(
    input: Seq<u8>, position: usize, databin: Part2JpipDatabin, last: bool, limits: &crate::ResourceLimits,
) -> Part2JpipParsed {
    let offset = part2_jpip_read_vbas(input, position, None);
    match offset.0 {
        Err(error) => Err(error),
        Ok(offset_value) => {
            let length = part2_jpip_read_vbas(input, offset.1, None);
            match length.0 {
                Err(error) => Err(error),
                Ok(length_value) => {
                    let auxiliary = if part9_auxiliary_present(databin.0 as nat) {
                        let result = part2_jpip_read_vbas(input, length.1, None);
                        (match result.0 { Err(error) => Err(error), Ok(value) => Ok(Some(value)) }, result.1)
                    } else { (Ok(None), length.1) };
                    match auxiliary.0 {
                        Err(error) => Err(error),
                        Ok(auxiliary_value) => {
                            let end = offset_value as nat + length_value as nat;
                            if end > u64::MAX as nat {
                                Err(part2_jpip_error(auxiliary.1, crate::MalformedKind::ArithmeticOverflow))
                            } else if end > crate::limits::resource_input_byte_limit(limits) {
                                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                                    limit: crate::limits::resource_input_byte_limit(limits), actual: end as u64 })
                            } else {
                                match part2_jpip_body(input, auxiliary.1, length_value) {
                                    Err(error) => Err(error),
                                    Ok(body) => Ok((Part2JpipMessage::Data {
                                        header: (databin, offset_value, length_value, last, auxiliary_value, auxiliary.1), body: body.0,
                                    }, body.1)),
                                }
                            }
                        },
                    }
                },
            }
        },
    }
}

pub open spec fn part2_jpip_data(input: Seq<u8>, context: Part2JpipContext, limits: &crate::ResourceLimits)
    -> Part2JpipParsed {
    let form = (input[0] >> 5) & 3;
    if !part9_header_form_valid(form as nat) { Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)) }
    else {
        let bin = part2_jpip_read_vbas(input, 0, Some(0x0f));
        match bin.0 {
            Err(error) => Err(error),
            Ok(bin_value) => {
                let class = if part9_header_has_explicit_class(form as nat) { part2_jpip_read_vbas(input, bin.1, None) }
                    else { (match context.0 { None => Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)),
                        Some(value) => Ok(value) }, bin.1) };
                match class.0 {
                    Err(error) => Err(error),
                    Ok(class_value) => {
                        let stream = if part9_header_has_explicit_codestream(form as nat) {
                            part2_jpip_read_vbas(input, class.1, None)
                        } else { (match context.1 { Some(value) => Ok(value), None =>
                            if form == 2 { Ok(0) } else { Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)) } }, class.1) };
                        match stream.0 {
                            Err(error) => Err(error),
                            Ok(stream_value) => match part2_jpip_databin(class_value, stream_value, bin_value) {
                                Err(error) => Err(error),
                                Ok(databin) => part2_jpip_data_after_identity(input, stream.1, databin, input[0] & 0x10 != 0, limits),
                            },
                        }
                    },
                }
            },
        }
    }
}

pub(crate) proof fn part2_jpip_data_identity_cut(
    input: Seq<u8>, context: Part2JpipContext, limits: &crate::ResourceLimits,
    bin_value: u64, class_start: usize, class_value: u64, stream_start: usize,
    stream_value: u64, body_start: usize, databin: Part2JpipDatabin,
)
    requires input.len() > 0,
        part9_header_form_valid(((input[0] >> 5) & 3) as nat),
        part2_jpip_read_vbas(input, 0, Some(0x0f)) == (Ok(bin_value), class_start),
        (if part9_header_has_explicit_class(((input[0] >> 5) & 3) as nat) {
            part2_jpip_read_vbas(input, class_start, None)
        } else {
            (match context.0 { None => Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)),
                Some(value) => Ok(value) }, class_start)
        }) == (Ok(class_value), stream_start),
        (if part9_header_has_explicit_codestream(((input[0] >> 5) & 3) as nat) {
            part2_jpip_read_vbas(input, stream_start, None)
        } else {
            (match context.1 { Some(value) => Ok(value), None =>
                if (input[0] >> 5) & 3 == 2 { Ok(0) }
                else { Err(part2_jpip_error(0, crate::MalformedKind::InvalidJpipHeader)) } }, stream_start)
        }) == (Ok(stream_value), body_start),
        part2_jpip_databin(class_value, stream_value, bin_value) == Ok(databin),
    ensures part2_jpip_data(input, context, limits)
        == part2_jpip_data_after_identity(input, body_start, databin, input[0] & 0x10 != 0, limits),
{
}

pub closed spec fn part2_parse_jpip_message(input: Seq<u8>, context: Part2JpipContext, limits: &crate::ResourceLimits)
    -> Part2JpipParse {
    let parsed = if input.len() == 0 { Err(part2_jpip_error(0, crate::MalformedKind::Truncated)) }
        else if input.len() as u64 > crate::limits::resource_input_byte_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(limits), actual: input.len() as u64 })
        } else if input[0] == 0 { part2_jpip_eor(input) } else { part2_jpip_data(input, context, limits) };
    let next = match parsed {
        Ok((Part2JpipMessage::Data { header, .. }, _)) => (Some(header.0.0), Some(header.0.2)),
        _ => context,
    };
    (parsed, next)
}

pub(crate) proof fn part2_parse_jpip_message_unfold(input: Seq<u8>, context: Part2JpipContext, limits: &crate::ResourceLimits)
    ensures part2_parse_jpip_message(input, context, limits) == {
        let parsed = if input.len() == 0 { Err(part2_jpip_error(0, crate::MalformedKind::Truncated)) }
            else if input.len() as u64 > crate::limits::resource_input_byte_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                    limit: crate::limits::resource_input_byte_limit(limits), actual: input.len() as u64 })
            } else if input[0] == 0 { part2_jpip_eor(input) } else { part2_jpip_data(input, context, limits) };
        let next = match parsed {
            Ok((Part2JpipMessage::Data { header, .. }, _)) => (Some(header.0.0), Some(header.0.2)),
            _ => context,
        };
        (parsed, next)
    },
{
}

pub open spec fn part2_jpip_parser_parse(
    input: Seq<u8>, parser: (Part2JpipContext, crate::ResourceLimits),
) -> (Part2JpipParsed, (Part2JpipContext, crate::ResourceLimits)) {
    let parsed = part2_parse_jpip_message(input, parser.0, &parser.1);
    (parsed.0, (parsed.1, parser.1))
}

}
