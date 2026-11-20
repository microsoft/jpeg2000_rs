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

pub(crate) open spec fn raw_recovery_report(
    original: usize, frame: (bool, u64), geometry: (u32, u32, u32, u32),
) -> Result<crate::RawRecoveryReport, crate::DecodeError> {
    if frame.0 && original as int + 2 > u64::MAX {
            Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ArithmeticOverflow })
        } else {
            let effective = (original as u64 + if frame.0 { 2u64 } else { 0u64 }) as u64;
            Ok(crate::RawRecoveryReport {
                appended_eoc: frame.0, original_bytes: original as u64, effective_bytes: effective,
                width: geometry.0, height: geometry.1, x_origin: geometry.2, y_origin: geometry.3,
                preflight_work_units: frame.1,
                repair_copy_bytes: if frame.0 { effective } else { 0 },
            })
        }
}

pub(crate) open spec fn raw_recovery_finish(
    original: usize, frame: (bool, u64), decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError> {
    match decoded {
        Err(error) => Err(error),
        Ok(image) => match raw_recovery_report(original, frame, image.0) {
            Err(error) => Err(error),
            Ok(report) => Ok((image, report)),
        },
    }
}

pub(crate) open spec fn raw_reconstructed_recovery_finish(
    original: usize, frame: (bool, u64), decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
) -> Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError> {
    match decoded {
        Err(error) => Err(error),
        Ok(image) => match raw_recovery_report(original, frame, (image.0, image.1, image.2, image.3)) {
            Err(error) => Err(error),
            Ok(report) => Ok((image, report)),
        },
    }
}

pub closed spec fn raw_reconstructed_recovery_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError>,
) -> bool {
    raw_reconstructed_recovery_result_body(input, limits, result)
}

pub(crate) proof fn raw_reconstructed_recovery_result_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures forall |result: Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError>|
        raw_reconstructed_recovery_result(input, limits, result)
            == raw_reconstructed_recovery_result_body(input, limits, result),
{
}

pub(crate) open spec fn raw_reconstructed_recovery_normal_result_body(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError>,
) -> bool {
    match raw_recovery_framing(input, limits) {
        Err(error) => result == Err(error),
        Ok(frame) => if !frame.0 {
            result == raw_reconstructed_recovery_finish(input.len() as usize, frame,
                part2_decode_raw_reconstructed_codestream(input, limits))
        } else {
            match raw_recovery_admit(input.len() as usize, frame.1, limits) {
                Err(error) => result == Err(error),
                Ok(()) => result == raw_reconstructed_recovery_reserved_response(input, limits, frame, false)
                    || result == raw_reconstructed_recovery_reserved_response(input, limits, frame, true),
            }
        },
    }
}

pub(crate) open spec fn raw_reconstructed_recovery_reserved_response(
    input: Seq<u8>, limits: &crate::ResourceLimits, frame: (bool, u64), reserved: bool,
) -> Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError> {
    match raw_repair_response(input, reserved) {
        Err(error) => Err(error),
        Ok(bytes) => raw_reconstructed_recovery_finish(input.len() as usize, frame,
            part2_decode_raw_reconstructed_codestream(bytes, limits)),
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

pub(crate) open spec fn raw_recovery_normal_result_body(
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

pub(crate) enum RawRecoveryEvent {
    Repair { reserved: bool },
    Decode { calls: Seq<Part2JpipSnapshotEvent> },
}

pub(crate) type RawRecoveryRun<T> =
    Option<(Result<(T, crate::RawRecoveryReport), crate::DecodeError>, Seq<RawRecoveryEvent>)>;

pub(crate) open spec fn raw_recovery_decode_call<T>(
    bytes: Seq<u8>, original: usize, frame: (bool, u64),
    strict: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(usize, (bool, u64), Result<T, crate::DecodeError>)
        -> Result<(T, crate::RawRecoveryReport), crate::DecodeError>,
    events: Seq<RawRecoveryEvent>,
) -> RawRecoveryRun<T> {
    if events.len() == 0 { None } else {
        match events[0] {
            RawRecoveryEvent::Decode { calls } => match strict(bytes, calls) {
                Some((decoded, rest)) => if rest.len() == 0 {
                    Some((finish(original, frame, decoded), events.drop_first()))
                } else { None },
                None => None,
            },
            _ => None,
        }
    }
}

pub(crate) open spec fn raw_recovery_cold_run<T>(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    strict: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(usize, (bool, u64), Result<T, crate::DecodeError>)
        -> Result<(T, crate::RawRecoveryReport), crate::DecodeError>,
    events: Seq<RawRecoveryEvent>,
) -> RawRecoveryRun<T> {
    match raw_recovery_framing(input, limits) {
        Err(error) => Some((Err(error), events)),
        Ok(frame) => if !frame.0 {
            raw_recovery_decode_call(input, input.len() as usize, frame, strict, finish, events)
        } else {
            match raw_recovery_admit(input.len() as usize, frame.1, limits) {
                Err(error) => Some((Err(error), events)),
                Ok(()) => if events.len() == 0 { None } else {
                    match events[0] {
                        RawRecoveryEvent::Repair { reserved } => match raw_repair_response(input, reserved) {
                            Err(error) => Some((Err(error), events.drop_first())),
                            Ok(bytes) => raw_recovery_decode_call(bytes, input.len() as usize,
                                frame, strict, finish, events.drop_first()),
                        },
                        _ => None,
                    }
                },
            }
        },
    }
}

pub(crate) open spec fn raw_recovery_cold_typed(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<RawRecoveryEvent>,
) -> RawRecoveryRun<Part1DecodedTypedImage> {
    raw_recovery_cold_run(input, limits,
        |bytes, calls| part2_decode_raw_cold_run(bytes, limits, None, calls),
        |original, frame, decoded| raw_recovery_finish(original, frame, decoded), events)
}

pub(crate) open spec fn raw_recovery_cold_reconstructed(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<RawRecoveryEvent>,
) -> RawRecoveryRun<Part1DecodedImageModel> {
    raw_recovery_cold_run(input, limits,
        |bytes, calls| part2_decode_reconstructed_cold_run(bytes, limits, calls),
        |original, frame, decoded| raw_reconstructed_recovery_finish(original, frame, decoded), events)
}

pub(crate) open spec fn raw_recovery_result_body(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError>,
) -> bool {
    exists|events: Seq<RawRecoveryEvent>|
        #[trigger] raw_recovery_cold_typed(input, limits, events) == Some((result, Seq::empty()))
}

pub(crate) open spec fn raw_reconstructed_recovery_result_body(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError>,
) -> bool {
    exists|events: Seq<RawRecoveryEvent>|
        #[trigger] raw_recovery_cold_reconstructed(input, limits, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn raw_recovery_preflight_lifts(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures match raw_recovery_framing(input, limits) {
        Err(error) => raw_recovery_result(input, limits, Err(error))
            && raw_reconstructed_recovery_result(input, limits, Err(error)),
        Ok(frame) => match raw_recovery_admit(input.len() as usize, frame.1, limits) {
            Err(error) => frame.0 ==> (raw_recovery_result(input, limits, Err(error))
                && raw_reconstructed_recovery_result(input, limits, Err(error))),
            Ok(()) => true,
        },
    },
{
    reveal(raw_recovery_result);
    reveal(raw_reconstructed_recovery_result);
    match raw_recovery_framing(input, limits) {
        Err(error) => {
            assert(raw_recovery_cold_typed(input, limits, Seq::empty()) == Some((Err(error), Seq::empty())));
            assert(raw_recovery_cold_reconstructed(input, limits, Seq::empty()) == Some((Err(error), Seq::empty())));
        },
        Ok(frame) => if frame.0 {
            if let Err(error) = raw_recovery_admit(input.len() as usize, frame.1, limits) {
                assert(raw_recovery_cold_typed(input, limits, Seq::empty()) == Some((Err(error), Seq::empty())));
                assert(raw_recovery_cold_reconstructed(input, limits, Seq::empty()) == Some((Err(error), Seq::empty())));
            }
        },
    }
}

pub(crate) proof fn raw_recovery_copy_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, frame: (bool, u64), error: crate::DecodeError,
)
    requires raw_recovery_framing(input, limits) == Ok(frame), frame.0,
        raw_recovery_admit(input.len() as usize, frame.1, limits) == Ok(()),
        raw_repair_result(input, Err(error)),
    ensures raw_recovery_result(input, limits, Err(error))
        && raw_reconstructed_recovery_result(input, limits, Err(error)),
{
    reveal(raw_recovery_result);
    reveal(raw_reconstructed_recovery_result);
    let events = seq![RawRecoveryEvent::Repair { reserved: false }];
    assert(events.drop_first() =~= Seq::empty());
    assert(raw_repair_response(input, false) == Err(error));
    assert(raw_recovery_cold_typed(input, limits, events) == Some((Err(error), Seq::empty())));
    assert(raw_recovery_cold_reconstructed(input, limits, events) == Some((Err(error), Seq::empty())));
}

pub(crate) proof fn raw_recovery_decode_actual<T>(
    input: Seq<u8>, limits: &crate::ResourceLimits, frame: (bool, u64), bytes: Seq<u8>,
    strict: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    current: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(usize, (bool, u64), Result<T, crate::DecodeError>)
        -> Result<(T, crate::RawRecoveryReport), crate::DecodeError>,
    decoded: Result<T, crate::DecodeError>,
) -> (events: Seq<RawRecoveryEvent>)
    requires raw_recovery_framing(input, limits) == Ok(frame),
        if frame.0 {
            raw_recovery_admit(input.len() as usize, frame.1, limits) == Ok(())
                && raw_repair_result(input, Ok(bytes))
        } else { bytes == input },
        part2_cold_framed(current, decoded),
        forall|calls: Seq<Part2JpipSnapshotEvent>| #[trigger] current(calls) == strict(bytes, calls),
    ensures raw_recovery_cold_run(input, limits, strict, finish, events)
        == Some((finish(input.len() as usize, frame, decoded), Seq::empty())),
{
    let calls = part2_cold_witness(current, decoded);
    assert(strict(bytes, calls) == Some((decoded, Seq::empty())));
    let decode = RawRecoveryEvent::Decode { calls };
    let events = if frame.0 {
        assert(raw_repair_response(input, true) == Ok(bytes));
        seq![RawRecoveryEvent::Repair { reserved: true }, decode]
    } else { seq![decode] };
    if frame.0 {
        assert(events.drop_first() =~= seq![decode]);
        assert(events.drop_first().drop_first() =~= Seq::empty());
    } else { assert(events.drop_first() =~= Seq::empty()); }
    events
}

pub(crate) proof fn raw_recovery_typed_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, frame: (bool, u64), bytes: Seq<u8>,
    decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires raw_recovery_framing(input, limits) == Ok(frame),
        if frame.0 {
            raw_recovery_admit(input.len() as usize, frame.1, limits) == Ok(())
                && raw_repair_result(input, Ok(bytes))
        } else { bytes == input },
        part2_decode_raw_cold_result(bytes, limits, None, decoded),
    ensures raw_recovery_result(input, limits, raw_recovery_finish(input.len() as usize, frame, decoded)),
{
    reveal(raw_recovery_result);
    part2_decode_raw_cold_frames(bytes, limits, None, decoded);
    let events = raw_recovery_decode_actual(input, limits, frame, bytes,
        |data, calls| part2_decode_raw_cold_run(data, limits, None, calls),
        |calls| part2_decode_raw_cold_run(bytes, limits, None, calls),
        |original, frame, decoded| raw_recovery_finish(original, frame, decoded), decoded);
    assert(raw_recovery_cold_typed(input, limits, events)
        == Some((raw_recovery_finish(input.len() as usize, frame, decoded), Seq::empty())));
}

pub(crate) proof fn raw_recovery_reconstructed_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, frame: (bool, u64), bytes: Seq<u8>,
    decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires raw_recovery_framing(input, limits) == Ok(frame),
        if frame.0 {
            raw_recovery_admit(input.len() as usize, frame.1, limits) == Ok(())
                && raw_repair_result(input, Ok(bytes))
        } else { bytes == input },
        part2_decode_reconstructed_cold_result(bytes, limits, decoded),
    ensures raw_reconstructed_recovery_result(input, limits,
        raw_reconstructed_recovery_finish(input.len() as usize, frame, decoded)),
{
    reveal(raw_reconstructed_recovery_result);
    part2_decode_reconstructed_cold_frames(bytes, limits, decoded);
    let events = raw_recovery_decode_actual(input, limits, frame, bytes,
        |data, calls| part2_decode_reconstructed_cold_run(data, limits, calls),
        |calls| part2_decode_reconstructed_cold_run(bytes, limits, calls),
        |original, frame, decoded| raw_reconstructed_recovery_finish(original, frame, decoded), decoded);
    assert(raw_recovery_cold_reconstructed(input, limits, events)
        == Some((raw_reconstructed_recovery_finish(input.len() as usize, frame, decoded), Seq::empty())));
}

pub(crate) proof fn raw_recovery_normal_admitted(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedTypedImage, crate::RawRecoveryReport), crate::DecodeError>,
)
    requires raw_recovery_normal_result_body(input, limits, result),
    ensures raw_recovery_result(input, limits, result),
{
    raw_recovery_preflight_lifts(input, limits);
    if let Ok(frame) = raw_recovery_framing(input, limits) {
        if !frame.0 {
            let decoded = part2_decode_raw_codestream(input, limits, None);
            part2_decode_raw_cold_normal(input, limits, None);
            raw_recovery_typed_actual(input, limits, frame, input, decoded);
        } else if raw_recovery_admit(input.len() as usize, frame.1, limits).is_ok() {
            match raw_repair_response(input, false) {
                Err(error) => if result == Err(error) {
                    raw_recovery_copy_error(input, limits, frame, error);
                } else {
                    if let Ok(bytes) = raw_repair_response(input, true) {
                        let decoded = part2_decode_raw_codestream(bytes, limits, None);
                        part2_decode_raw_cold_normal(bytes, limits, None);
                        raw_recovery_typed_actual(input, limits, frame, bytes, decoded);
                    }
                },
                Ok(_) => {},
            }
        }
    }
}

pub(crate) proof fn raw_reconstructed_recovery_normal_admitted(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1DecodedImageModel, crate::RawRecoveryReport), crate::DecodeError>,
)
    requires raw_reconstructed_recovery_normal_result_body(input, limits, result),
    ensures raw_reconstructed_recovery_result(input, limits, result),
{
    raw_recovery_preflight_lifts(input, limits);
    if let Ok(frame) = raw_recovery_framing(input, limits) {
        if !frame.0 {
            let decoded = part2_decode_raw_reconstructed_codestream(input, limits);
            part2_decode_reconstructed_cold_normal(input, limits);
            raw_recovery_reconstructed_actual(input, limits, frame, input, decoded);
        } else if raw_recovery_admit(input.len() as usize, frame.1, limits).is_ok() {
            match raw_repair_response(input, false) {
                Err(error) => if result == Err(error) {
                    raw_recovery_copy_error(input, limits, frame, error);
                } else {
                    if let Ok(bytes) = raw_repair_response(input, true) {
                        let decoded = part2_decode_raw_reconstructed_codestream(bytes, limits);
                        part2_decode_reconstructed_cold_normal(bytes, limits);
                        raw_recovery_reconstructed_actual(input, limits, frame, bytes, decoded);
                    }
                },
                Ok(_) => {},
            }
        }
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
        Ok(part) => {
            let sized_final = part.1 != 0 && part.4 == 1 && part.0 <= read.1.input.len()
                && part.1 as nat == read.1.input.len() - part.0;
            if (part.1 != 0 && !sized_final) || part.3 != 0 || part.4 > 1 {
                (recovery_framed(read.1, false), read.1)
            } else { raw_recovery_tile_headers(read.1) }
        },
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
