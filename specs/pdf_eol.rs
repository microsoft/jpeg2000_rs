//! One reported PDF end-of-line recovery after the original validated boundary error.
use super::*;
verus! {

pub(crate) open spec fn part2_pdf_eol_end(input: Seq<u8>, error: crate::DecodeError) -> Option<nat> {
    let count = if input.len() >= 4
        && input[input.len() - 2] == 13 && input[input.len() - 1] == 10 { 2nat }
        else if input.len() >= 3 && (input[input.len() - 1] == 10 || input[input.len() - 1] == 13) { 1nat }
        else { 0nat };
    if count == 0 { None } else {
        let end = (input.len() - count) as nat;
        if end < 2 || end > u64::MAX || input[end - 2] != 255 || input[end - 1] != 217 { None }
        else { match error {
            crate::DecodeError::MalformedInput { offset, kind } =>
                if offset == end && (kind == crate::MalformedKind::TrailingData
                    || kind == crate::MalformedKind::InvalidBoxLength) { Some(end) } else { None },
            _ => None,
        }}
    }
}

pub(crate) open spec fn part2_pdf_eol_report(report: crate::PdfRecovery, count: u8) -> crate::PdfRecovery {
    crate::PdfRecovery {
        appended_eoc: report.appended_eoc,
        ignored_container_dimensions: report.ignored_container_dimensions,
        selected_present_tile: report.selected_present_tile,
        empty_initial_mq_prefixes: report.empty_initial_mq_prefixes,
        discarded_tile_trailer_bytes: report.discarded_tile_trailer_bytes,
        discarded_pdf_eol_bytes: count,
        original_codestream_bytes: report.original_codestream_bytes,
        effective_codestream_bytes: report.effective_codestream_bytes,
        preflight_work_units: report.preflight_work_units,
        repair_copy_bytes: report.repair_copy_bytes,
        full_canvas_sample_bytes: report.full_canvas_sample_bytes,
    }
}

pub(crate) open spec fn part2_pdf_eol_reply<T>(
    reply: Result<T, crate::DecodeError>, count: u8, finish: spec_fn(T, u8) -> T,
) -> Result<T, crate::DecodeError> {
    match reply { Err(error) => Err(error), Ok(value) => Ok(finish(value, count)) }
}

pub(crate) open spec fn part2_pdf_eol_run<T>(
    input: Seq<u8>,
    base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, u8) -> T,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<T> {
    match base(input, events) {
        Some((Err(error), rest)) => match part2_pdf_eol_end(input, error) {
            None => Some((Err(error), rest)),
            Some(end) => match base(input.take(end as int), rest) {
                None => None,
                Some((reply, tail)) => Some((part2_pdf_eol_reply(reply, (input.len() - end) as u8, finish), tail)),
            },
        },
        other => other,
    }
}

pub(crate) proof fn part2_pdf_eol_passthrough<T>(
    input: Seq<u8>, base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, u8) -> T, first: Result<T, crate::DecodeError>,
)
    requires part2_cold_framed(|events| base(input, events), first),
        match first { Err(error) => part2_pdf_eol_end(input, error).is_none(), Ok(_) => true },
    ensures part2_cold_framed(|events| part2_pdf_eol_run(input, base, finish, events), first),
        forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events| #[trigger] other(events) == part2_pdf_eol_run(input, base, finish, events))
                ==> #[trigger] part2_cold_framed(other, first),
{
    let prefix = part2_cold_witness(|events| base(input, events), first);
    assert forall|tail| #[trigger] part2_pdf_eol_run(input, base, finish, prefix + tail)
        == Some((first, tail)) by {
        part2_cold_prefix_at(|events| base(input, events), prefix, first, tail);
    }
    assert(part2_cold_prefix(|events| part2_pdf_eol_run(input, base, finish, events), prefix, first));
    part2_decode_eta(|events| part2_pdf_eol_run(input, base, finish, events), first);
}

pub(crate) proof fn part2_pdf_eol_retried<T>(
    input: Seq<u8>, base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, u8) -> T, error: crate::DecodeError, end: nat,
    second: Result<T, crate::DecodeError>,
)
    requires part2_pdf_eol_end(input, error) == Some(end),
        part2_cold_framed(|events| base(input, events), Err(error)),
        part2_cold_framed(|events| base(input.take(end as int), events), second),
    ensures part2_cold_framed(|events| part2_pdf_eol_run(input, base, finish, events),
        part2_pdf_eol_reply(second, (input.len() - end) as u8, finish)),
        forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events| #[trigger] other(events) == part2_pdf_eol_run(input, base, finish, events))
                ==> #[trigger] part2_cold_framed(other, part2_pdf_eol_reply(second, (input.len() - end) as u8, finish)),
{
    let first_prefix = part2_cold_witness(|events| base(input, events), Err(error));
    let second_prefix = part2_cold_witness(|events| base(input.take(end as int), events), second);
    let prefix = first_prefix + second_prefix;
    let result = part2_pdf_eol_reply(second, (input.len() - end) as u8, finish);
    assert forall|tail| #[trigger] part2_pdf_eol_run(input, base, finish, prefix + tail)
        == Some((result, tail)) by {
        assert(prefix + tail =~= first_prefix + (second_prefix + tail));
        part2_cold_prefix_at(|events| base(input, events), first_prefix, Err(error), second_prefix + tail);
        part2_cold_prefix_at(|events| base(input.take(end as int), events), second_prefix, second, tail);
    }
    assert(part2_cold_prefix(|events| part2_pdf_eol_run(input, base, finish, events), prefix, result));
    part2_decode_eta(|events| part2_pdf_eol_run(input, base, finish, events), result);
}

pub(crate) open spec fn part2_pdf_eol_typed_run(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfTyped> {
    part2_pdf_eol_run(input, |bytes, calls| part2_pdf_typed_run(bytes, requested, limits, calls),
        |value: Part2PdfTyped, count| (value.0, part2_pdf_eol_report(value.1, count)), events)
}
pub(crate) open spec fn part2_pdf_eol_reconstructed_run(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfReconstructed> {
    part2_pdf_eol_run(input, |bytes, calls| part2_pdf_reconstructed_run(bytes, requested, limits, calls),
        |value: Part2PdfReconstructed, count| (value.0, part2_pdf_eol_report(value.1, count)), events)
}
pub(crate) open spec fn part2_pdf_eol_inspect_run(input: Seq<u8>, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2RawCodestreamInfo> {
    part2_pdf_eol_run(input, |bytes, calls| part2_pdf_inspect_run(bytes, limits, calls),
        |value: Part2RawCodestreamInfo, _count| value, events)
}

pub closed spec fn part2_pdf_eol_typed_result(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PdfTyped, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_pdf_eol_typed_run(input, requested, limits, events), result)
}
pub closed spec fn part2_pdf_eol_reconstructed_result(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PdfReconstructed, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_pdf_eol_reconstructed_run(input, requested, limits, events), result)
}
pub closed spec fn part2_pdf_eol_inspect_result(input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part2RawCodestreamInfo, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_pdf_eol_inspect_run(input, limits, events), result)
}

pub closed spec fn part2_pdf_eol_typed_value(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits) -> Result<Part2PdfTyped, crate::DecodeError> {
    match part2_pdf_typed_value(input, requested, limits) {
        Err(error) => match part2_pdf_eol_end(input, error) {
            None => Err(error), Some(end) => part2_pdf_eol_reply(
                part2_pdf_typed_value(input.take(end as int), requested, limits), (input.len() - end) as u8,
                |value: Part2PdfTyped, count| (value.0, part2_pdf_eol_report(value.1, count))),
        }, other => other,
    }
}
pub closed spec fn part2_pdf_eol_reconstructed_value(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits) -> Result<Part2PdfReconstructed, crate::DecodeError> {
    match part2_pdf_reconstructed_value(input, requested, limits) {
        Err(error) => match part2_pdf_eol_end(input, error) {
            None => Err(error), Some(end) => part2_pdf_eol_reply(
                part2_pdf_reconstructed_value(input.take(end as int), requested, limits), (input.len() - end) as u8,
                |value: Part2PdfReconstructed, count| (value.0, part2_pdf_eol_report(value.1, count))),
        }, other => other,
    }
}
pub closed spec fn part2_pdf_eol_inspect_value(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2RawCodestreamInfo, crate::DecodeError> {
    match part2_pdf_inspect_value(input, limits) {
        Err(error) => match part2_pdf_eol_end(input, error) {
            None => Err(error), Some(end) => part2_pdf_inspect_value(input.take(end as int), limits),
        }, other => other,
    }
}

pub(crate) proof fn part2_pdf_eol_contracts_unfold(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits)
    ensures
        forall|reply: Result<Part2PdfTyped, crate::DecodeError>|
            #[trigger] part2_pdf_eol_typed_result(input, requested, limits, reply)
                == part2_cold_framed(|events| part2_pdf_eol_typed_run(input, requested, limits, events), reply),
        forall|reply: Result<Part2PdfReconstructed, crate::DecodeError>|
            #[trigger] part2_pdf_eol_reconstructed_result(input, requested, limits, reply)
                == part2_cold_framed(|events| part2_pdf_eol_reconstructed_run(input, requested, limits, events), reply),
        forall|reply: Result<Part2RawCodestreamInfo, crate::DecodeError>|
            #[trigger] part2_pdf_eol_inspect_result(input, limits, reply)
                == part2_cold_framed(|events| part2_pdf_eol_inspect_run(input, limits, events), reply),
        part2_pdf_eol_typed_value(input, requested, limits) == match part2_pdf_typed_value(input, requested, limits) {
            Err(error) => match part2_pdf_eol_end(input, error) {
                None => Err(error), Some(end) => part2_pdf_eol_reply(
                    part2_pdf_typed_value(input.take(end as int), requested, limits), (input.len() - end) as u8,
                    |value: Part2PdfTyped, count| (value.0, part2_pdf_eol_report(value.1, count))),
            }, other => other,
        },
        part2_pdf_eol_reconstructed_value(input, requested, limits) == match part2_pdf_reconstructed_value(input, requested, limits) {
            Err(error) => match part2_pdf_eol_end(input, error) {
                None => Err(error), Some(end) => part2_pdf_eol_reply(
                    part2_pdf_reconstructed_value(input.take(end as int), requested, limits), (input.len() - end) as u8,
                    |value: Part2PdfReconstructed, count| (value.0, part2_pdf_eol_report(value.1, count))),
            }, other => other,
        },
        part2_pdf_eol_inspect_value(input, limits) == match part2_pdf_inspect_value(input, limits) {
            Err(error) => match part2_pdf_eol_end(input, error) {
                None => Err(error), Some(end) => part2_pdf_inspect_value(input.take(end as int), limits),
            }, other => other,
        },
{}

pub(crate) proof fn part2_pdf_eol_typed_normal(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits)
    ensures part2_pdf_eol_typed_result(input, requested, limits, part2_pdf_eol_typed_value(input, requested, limits)),
{
    part2_pdf_normal(input, requested, limits);
    part2_pdf_contracts_unfold(input, requested, limits);
    part2_pdf_eol_contracts_unfold(input, requested, limits);
    let base = |bytes, calls| part2_pdf_typed_run(bytes, requested, limits, calls);
    let finish = |value: Part2PdfTyped, count| (value.0, part2_pdf_eol_report(value.1, count));
    let first = part2_pdf_typed_value(input, requested, limits);
    part2_decode_eta(|events| part2_pdf_typed_run(input, requested, limits, events), first);
    if let Err(error) = first {
        if let Some(end) = part2_pdf_eol_end(input, error) {
            let prefix = input.take(end as int);
            part2_pdf_normal(prefix, requested, limits);
            part2_pdf_contracts_unfold(prefix, requested, limits);
            let second = part2_pdf_typed_value(prefix, requested, limits);
            part2_decode_eta(|events| part2_pdf_typed_run(prefix, requested, limits, events), second);
            part2_pdf_eol_retried(input, base, finish, error, end, second);
            return;
        }
    }
    part2_pdf_eol_passthrough(input, base, finish, first);
}

pub(crate) proof fn part2_pdf_eol_reconstructed_normal(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits)
    ensures part2_pdf_eol_reconstructed_result(input, requested, limits, part2_pdf_eol_reconstructed_value(input, requested, limits)),
{
    part2_pdf_normal(input, requested, limits);
    part2_pdf_contracts_unfold(input, requested, limits);
    part2_pdf_eol_contracts_unfold(input, requested, limits);
    let base = |bytes, calls| part2_pdf_reconstructed_run(bytes, requested, limits, calls);
    let finish = |value: Part2PdfReconstructed, count| (value.0, part2_pdf_eol_report(value.1, count));
    let first = part2_pdf_reconstructed_value(input, requested, limits);
    part2_decode_eta(|events| part2_pdf_reconstructed_run(input, requested, limits, events), first);
    if let Err(error) = first {
        if let Some(end) = part2_pdf_eol_end(input, error) {
            let prefix = input.take(end as int);
            part2_pdf_normal(prefix, requested, limits);
            part2_pdf_contracts_unfold(prefix, requested, limits);
            let second = part2_pdf_reconstructed_value(prefix, requested, limits);
            part2_decode_eta(|events| part2_pdf_reconstructed_run(prefix, requested, limits, events), second);
            part2_pdf_eol_retried(input, base, finish, error, end, second);
            return;
        }
    }
    part2_pdf_eol_passthrough(input, base, finish, first);
}

pub(crate) proof fn part2_pdf_eol_inspect_normal(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_pdf_eol_inspect_result(input, limits, part2_pdf_eol_inspect_value(input, limits)),
{
    let requested = (Part2TileSelection::All, None, 0u8);
    part2_pdf_normal(input, requested, limits);
    part2_pdf_contracts_unfold(input, requested, limits);
    part2_pdf_eol_contracts_unfold(input, requested, limits);
    let base = |bytes, calls| part2_pdf_inspect_run(bytes, limits, calls);
    let finish = |value: Part2RawCodestreamInfo, _count| value;
    let first = part2_pdf_inspect_value(input, limits);
    part2_decode_eta(|events| part2_pdf_inspect_run(input, limits, events), first);
    if let Err(error) = first {
        if let Some(end) = part2_pdf_eol_end(input, error) {
            let prefix = input.take(end as int);
            part2_pdf_normal(prefix, requested, limits);
            part2_pdf_contracts_unfold(prefix, requested, limits);
            let second = part2_pdf_inspect_value(prefix, limits);
            part2_decode_eta(|events| part2_pdf_inspect_run(prefix, limits, events), second);
            part2_pdf_eol_retried(input, base, finish, error, end, second);
            return;
        }
    }
    part2_pdf_eol_passthrough(input, base, finish, first);
}
}
