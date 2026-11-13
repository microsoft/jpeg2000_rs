//! Source-derived structural admission and the one-reservation repair copy.
use super::*;

verus! {
pub(crate) open spec fn raw_repair_response(input: Seq<u8>, reserved: bool)
    -> Result<Seq<u8>, crate::DecodeError>
{
    if input.len() + 2 > usize::MAX {
        Err(crate::DecodeError::MalformedInput {
            offset: 0, kind: crate::MalformedKind::ArithmeticOverflow,
        })
    } else if !reserved {
        Err(crate::DecodeError::AllocationFailed)
    } else { Ok(input + seq![0xffu8, 0xd9u8]) }
}

pub(crate) open spec fn raw_repair_result(
    input: Seq<u8>, result: Result<Seq<u8>, crate::DecodeError>,
) -> bool {
    // Exactly the one accepted reservation response, followed by two std
    // content extensions. There are no independent extension-failure events.
    result == raw_repair_response(input, false) || result == raw_repair_response(input, true)
}

pub(crate) open spec fn raw_recovery_admit(
    input_bytes: usize, work: u64, limits: &crate::ResourceLimits,
) -> Result<(), crate::DecodeError> {
    let total = input_bytes as int + 2;
    if total > usize::MAX {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ArithmeticOverflow })
    } else if total > crate::limits::resource_input_byte_limit(limits) {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::InputBytes,
            limit: crate::limits::resource_input_byte_limit(limits), actual: total as u64,
        })
    } else if work as int + total > u64::MAX {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ArithmeticOverflow })
    } else if work as int + total > crate::limits::resource_work_limit(limits) {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::WorkUnits,
            limit: crate::limits::resource_work_limit(limits), actual: (work as int + total) as u64,
        })
    } else { Ok(()) }
}

pub(crate) open spec fn raw_recovery_finish(
    original: usize, frame: (bool, u64), decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError> {
    match decoded {
        Err(error) => Err(error),
        Ok(image) => if frame.0 && original as int + 2 > u64::MAX {
            Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ArithmeticOverflow })
        } else {
            let effective = (original as u64 + if frame.0 { 2u64 } else { 0u64 }) as u64;
            Ok((image, crate::RawRecoveryReport {
                appended_eoc: frame.0, original_bytes: original as u64, effective_bytes: effective,
                width: image.0.0, height: image.0.1, x_origin: image.0.2, y_origin: image.0.3,
                preflight_work_units: frame.1,
                repair_copy_bytes: if frame.0 { effective } else { 0 },
            }))
        },
    }
}

pub closed spec fn raw_recovery_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError>,
) -> bool {
    raw_recovery_result_body(input, limits, result)
}

pub(crate) proof fn raw_recovery_result_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures forall |result: Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError>|
        raw_recovery_result(input, limits, result) == raw_recovery_result_body(input, limits, result),
{
}

pub(crate) open spec fn raw_recovery_result_body(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError>,
) -> bool {
    match raw_recovery_framing(input, limits) {
        Err(error) => result == Err(error),
        Ok(frame) => if !frame.0 {
            result == raw_recovery_finish(input.len() as usize, frame,
                part2_decode_raw_codestream(input, limits, None))
        } else {
            match raw_recovery_admit(input.len() as usize, frame.1, limits) {
                Err(error) => result == Err(error),
                Ok(()) => result == raw_recovery_reserved_response(input, limits, frame, false)
                    || result == raw_recovery_reserved_response(input, limits, frame, true),
            }
        },
    }
}

pub(crate) open spec fn raw_recovery_reserved_response(
    input: Seq<u8>, limits: &crate::ResourceLimits, frame: (bool, u64), reserved: bool,
) -> Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError> {
    match raw_repair_response(input, reserved) {
        Err(error) => Err(error),
        Ok(bytes) => raw_recovery_finish(input.len() as usize, frame,
            part2_decode_raw_codestream(bytes, limits, None)),
    }
}

pub(crate) type RecoveryFramingResult<'a> =
    (Result<(bool, u64), crate::DecodeError>, Part1CodestreamReader<'a>);

pub(crate) open spec fn recovery_framed(reader: Part1CodestreamReader<'_>, append: bool)
    -> Result<(bool, u64), crate::DecodeError>
{
    Ok((append, reader.work_units))
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_body(reader: Part1CodestreamReader<'_>)
    -> RecoveryFramingResult<'_>
{
    raw_recovery_body_loop(reader, reader.input.len())
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_body_loop(reader: Part1CodestreamReader<'_>, length: nat)
    -> RecoveryFramingResult<'_>
    decreases length as int - reader.position as int,
{
    let start = reader.position as int;
    let remaining = length as int - start;
    if remaining <= 0 { (recovery_framed(reader, true), reader) }
    else {
        let next = if remaining >= 2 { reader.input[start + 1] } else { 0u8 };
        let marked = reader.input[start] == 0xff && remaining >= 2;
        if marked && next > 0x8f && next != 0x91 && next != 0x92 && next != 0xff {
            (recovery_framed(reader, false), reader)
        } else if marked && next == 0x91 && remaining < 6 {
            (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::Truncated)), reader)
        } else if marked && next == 0x91
            && (reader.input[start + 2] != 0 || reader.input[start + 3] != 4) {
            (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidMarkerLength)), reader)
        } else {
            let step: u64 = if marked && next == 0x91 { 6 }
                else if marked && (next <= 0x8f || next == 0x92) { 2 } else { 1 };
            if reader.position as int + step > usize::MAX {
                (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::ArithmeticOverflow)), reader)
            } else {
                let charged = part1_codestream_charge_work(reader, step);
                match charged.0 {
                    Err(error) => (Err(error), charged.1),
                    Ok(()) => raw_recovery_body_loop(Part1CodestreamReader {
                        position: (reader.position + step) as usize, ..charged.1
                    }, length),
                }
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_tile_headers(reader: Part1CodestreamReader<'_>)
    -> RecoveryFramingResult<'_>
{
    raw_recovery_tile_loop(reader, reader.input.len())
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_tile_loop(reader: Part1CodestreamReader<'_>, length: nat)
    -> RecoveryFramingResult<'_>
    decreases length as int - reader.position as int,
{
    let read = part1_read_tile_header_segment(reader);
    match read.0 {
        Err(error) => (Err(error), read.1),
        Ok(None) => raw_recovery_body(read.1),
        Ok(Some(_)) => if read.1.position <= reader.position || read.1.position > length {
            (Err(part1_codestream_malformed(read.1.position, crate::MalformedKind::InvalidMarkerLength)), read.1)
        } else { raw_recovery_tile_loop(read.1, length) },
    }
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_sot(reader: Part1CodestreamReader<'_>)
    -> RecoveryFramingResult<'_>
{
    let read = part1_codestream_read_sot(reader, 1);
    match read.0 {
        Err(error) => (Err(error), read.1),
        Ok(part) => if part.1 != 0 || part.3 != 0 || part.4 > 1 {
            (recovery_framed(read.1, false), read.1)
        } else { raw_recovery_tile_headers(read.1) },
    }
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_main_headers(
    reader: Part1CodestreamReader<'_>, count: u64, cod: bool, qcd: bool,
) -> RecoveryFramingResult<'_>
{
    raw_recovery_main_loop(reader, count, cod, qcd, reader.input.len())
}

#[verifier::opaque]
pub(crate) open spec fn raw_recovery_main_loop(
    reader: Part1CodestreamReader<'_>, count: u64, cod: bool, qcd: bool, length: nat,
) -> RecoveryFramingResult<'_>
    decreases length as int - reader.position as int,
{
    let read = part1_read_main_header_segment(reader, count);
    match read.0 {
        Err(error) => (Err(error), read.1),
        Ok(None) => if !cod || !qcd {
            (Err(part1_codestream_malformed(read.1.position, crate::MalformedKind::MissingRequiredStructure)), read.1)
        } else { raw_recovery_sot(read.1) },
        Ok(Some(segment)) => if read.1.position <= reader.position || read.1.position > length {
            (Err(part1_codestream_malformed(read.1.position, crate::MalformedKind::InvalidMarkerLength)), read.1)
        } else {
            raw_recovery_main_loop(read.1, read.2,
                cod || segment.marker == 0xff52, qcd || segment.marker == 0xff5c, length)
        },
    }
}

pub(crate) open spec fn raw_recovery_framing(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<(bool, u64), crate::DecodeError>
{
    match part1_codestream_reader_new(input, limits) {
        Err(error) => Err(error),
        Ok(reader) => {
            let prologue = part1_parse_layout_prologue(reader);
            match prologue.0 {
                Err(error) => Err(error),
                Ok((size, _, _)) => if size.geometry.8 != 1 || size.geometry.9 != 1 {
                    recovery_framed(prologue.1, false)
                } else { raw_recovery_main_headers(prologue.1, 1, false, false).0 },
            }
        },
    }
}
}
