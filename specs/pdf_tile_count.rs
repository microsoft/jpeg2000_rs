//! Source-derived bounded correction of a complete off-by-one TNsot declaration.
use super::*;
verus! {

pub(crate) open spec fn part2_count_error(offset: u64) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidTilePart }
}

pub(crate) open spec fn part2_count_retry(error: crate::DecodeError) -> bool {
    match error {
        crate::DecodeError::MalformedInput { kind: crate::MalformedKind::InvalidTilePart, .. } => true,
        _ => false,
    }
}

pub(crate) open spec fn part2_count_report(report: crate::PdfRecovery, fields: u32,
    bytes: u64, work: u64) -> crate::PdfRecovery {
    crate::PdfRecovery {
        appended_eoc: report.appended_eoc,
        ignored_container_dimensions: report.ignored_container_dimensions,
        selected_present_tile: report.selected_present_tile,
        empty_initial_mq_prefixes: report.empty_initial_mq_prefixes,
        discarded_tile_trailer_bytes: report.discarded_tile_trailer_bytes,
        discarded_pdf_eol_bytes: report.discarded_pdf_eol_bytes,
        corrected_tile_part_count_fields: fields,
        tile_part_count_repair_copy_bytes: bytes,
        tile_part_count_repair_work_bound: work,
        original_codestream_bytes: report.original_codestream_bytes,
        effective_codestream_bytes: report.effective_codestream_bytes,
        preflight_work_units: report.preflight_work_units,
        repair_copy_bytes: report.repair_copy_bytes,
        full_canvas_sample_bytes: report.full_canvas_sample_bytes,
    }
}

pub(crate) open spec fn part2_count_finish_typed(value: Part2PdfTyped, repaired: Part2PdfCountRepair)
    -> Part2PdfTyped {
    (value.0, part2_count_report(value.1, repaired.1, repaired.0.len() as u64, repaired.2))
}

pub(crate) open spec fn part2_count_finish_reconstructed(value: Part2PdfReconstructed,
    repaired: Part2PdfCountRepair) -> Part2PdfReconstructed {
    (value.0, part2_count_report(value.1, repaired.1, repaired.0.len() as u64, repaired.2))
}

pub(crate) open spec fn part2_count_reply<T>(reply: Result<T, crate::DecodeError>,
    repaired: Part2PdfCountRepair, finish: spec_fn(T, Part2PdfCountRepair) -> T)
    -> Result<T, crate::DecodeError> {
    match reply { Err(error) => Err(error), Ok(value) => Ok(finish(value, repaired)) }
}

pub(crate) closed spec fn part2_count_finish_run<T>(repaired: Part2PdfCountRepair,
    base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, Part2PdfCountRepair) -> T, events: Seq<Part2JpipSnapshotEvent>)
    -> Part2ColdRun<T> {
    match base(repaired.0, events) {
        None => None,
        Some((reply, tail)) => Some((part2_count_reply(reply, repaired, finish), tail)),
    }
}

pub(crate) closed spec fn part2_pdf_count_run<T>(input: Seq<u8>, limits: &crate::ResourceLimits,
    base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, Part2PdfCountRepair) -> T, events: Seq<Part2JpipSnapshotEvent>)
    -> Part2ColdRun<T> {
    match base(input, events) {
        Some((Err(error), rest)) => if !part2_count_retry(error) { Some((Err(error), rest)) } else {
            part2_jpip_snapshot_bind(part2_count_prepare_run(input, limits, error, rest),
                |repaired, tail| part2_count_finish_run(repaired, base, finish, tail))
        },
        other => other,
    }
}

pub(crate) proof fn part2_count_passthrough<T>(input: Seq<u8>, limits: &crate::ResourceLimits,
    base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, Part2PdfCountRepair) -> T, first: Result<T, crate::DecodeError>)
    requires part2_cold_framed(|events| base(input, events), first),
        match first { Err(error) => !part2_count_retry(error), Ok(_) => true },
    ensures part2_cold_framed(|events| part2_pdf_count_run(input, limits, base, finish, events), first),
        forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events| #[trigger] other(events) == part2_pdf_count_run(input, limits, base, finish, events))
                ==> #[trigger] part2_cold_framed(other, first),
{
    let prefix = part2_cold_witness(|events| base(input, events), first);
    assert forall|tail| #[trigger] part2_pdf_count_run(input, limits, base, finish, prefix + tail)
        == Some((first, tail)) by {
        part2_cold_prefix_at(|events| base(input, events), prefix, first, tail);
    }
    assert(part2_cold_prefix(|events| part2_pdf_count_run(input, limits, base, finish, events), prefix, first));
    part2_decode_eta(|events| part2_pdf_count_run(input, limits, base, finish, events), first);
}

pub(crate) proof fn part2_count_finished<T>(repaired: Part2PdfCountRepair,
    base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, Part2PdfCountRepair) -> T, second: Result<T, crate::DecodeError>)
    requires part2_cold_framed(|events| base(repaired.0, events), second),
    ensures part2_cold_framed(|events| part2_count_finish_run(repaired, base, finish, events),
        part2_count_reply(second, repaired, finish)),
{
    let prefix = part2_cold_witness(|events| base(repaired.0, events), second);
    assert forall|tail| #[trigger] part2_count_finish_run(repaired, base, finish, prefix + tail)
        == Some((part2_count_reply(second, repaired, finish), tail)) by {
        part2_cold_prefix_at(|events| base(repaired.0, events), prefix, second, tail);
    }
    assert(part2_cold_prefix(|events| part2_count_finish_run(repaired, base, finish, events), prefix,
        part2_count_reply(second, repaired, finish)));
}

pub(crate) proof fn part2_count_retried<T>(input: Seq<u8>, limits: &crate::ResourceLimits,
    base: spec_fn(Seq<u8>, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    finish: spec_fn(T, Part2PdfCountRepair) -> T, error: crate::DecodeError,
    repaired: Result<Part2PdfCountRepair, crate::DecodeError>, result: Result<T, crate::DecodeError>)
    requires part2_count_retry(error), part2_cold_framed(|events| base(input, events), Err(error)),
        part2_count_prepare_result(input, limits, error, repaired),
        match repaired {
            Err(failure) => result == Err(failure),
            Ok(value) => part2_cold_framed(|events| part2_count_finish_run(value, base, finish, events), result),
        },
    ensures part2_cold_framed(|events| part2_pdf_count_run(input, limits, base, finish, events), result),
        forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events| #[trigger] other(events) == part2_pdf_count_run(input, limits, base, finish, events))
                ==> #[trigger] part2_cold_framed(other, result),
{
    part2_decode_eta(|events| part2_count_prepare_run(input, limits, error, events), repaired);
    if let Ok(value) = repaired {
        part2_decode_eta(|events| part2_count_finish_run(value, base, finish, events), result);
    }
    part2_cold_bind(|events| part2_count_prepare_run(input, limits, error, events),
        |value, tail| part2_count_finish_run(value, base, finish, tail), repaired, result);
    let after = |events| part2_jpip_snapshot_bind(part2_count_prepare_run(input, limits, error, events),
        |value, tail| part2_count_finish_run(value, base, finish, tail));
    let first_prefix = part2_cold_witness(|events| base(input, events), Err(error));
    let rest_prefix = part2_cold_witness(after, result);
    let prefix = first_prefix + rest_prefix;
    assert forall|tail| #[trigger] part2_pdf_count_run(input, limits, base, finish, prefix + tail)
        == Some((result, tail)) by {
        assert(prefix + tail =~= first_prefix + (rest_prefix + tail));
        part2_cold_prefix_at(|events| base(input, events), first_prefix, Err(error), rest_prefix + tail);
        part2_cold_prefix_at(after, rest_prefix, result, tail);
    }
    assert(part2_cold_prefix(|events| part2_pdf_count_run(input, limits, base, finish, events), prefix, result));
    part2_decode_eta(|events| part2_pdf_count_run(input, limits, base, finish, events), result);
}

pub(crate) open spec fn part2_pdf_count_value<T>(input: Seq<u8>, limits: &crate::ResourceLimits,
    base: spec_fn(Seq<u8>) -> Result<T, crate::DecodeError>,
    finish: spec_fn(T, Part2PdfCountRepair) -> T) -> Result<T, crate::DecodeError> {
    match base(input) {
        Err(error) => if !part2_count_retry(error) { Err(error) } else {
            match part2_count_prepare_value(input, limits, error) {
                Err(failure) => Err(failure),
                Ok(repaired) => part2_count_reply(base(repaired.0), repaired, finish),
            }
        },
        other => other,
    }
}

pub(crate) open spec fn part2_pdf_count_typed_run(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfTyped> {
    part2_pdf_count_run(input, limits, |bytes, calls| part2_pdf_eol_typed_run(bytes, requested, limits, calls),
        |value, repaired| part2_count_finish_typed(value, repaired), events)
}
pub(crate) open spec fn part2_pdf_count_reconstructed_run(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfReconstructed> {
    part2_pdf_count_run(input, limits, |bytes, calls| part2_pdf_eol_reconstructed_run(bytes, requested, limits, calls),
        |value, repaired| part2_count_finish_reconstructed(value, repaired), events)
}
pub(crate) open spec fn part2_pdf_count_inspect_run(input: Seq<u8>, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2RawCodestreamInfo> {
    part2_pdf_count_run(input, limits, |bytes, calls| part2_pdf_eol_inspect_run(bytes, limits, calls),
        |value: Part2RawCodestreamInfo, _repaired| value, events)
}

pub closed spec fn part2_pdf_count_typed_result(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PdfTyped, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_pdf_count_typed_run(input, requested, limits, events), result)
}
pub closed spec fn part2_pdf_count_reconstructed_result(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PdfReconstructed, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_pdf_count_reconstructed_run(input, requested, limits, events), result)
}
pub closed spec fn part2_pdf_count_inspect_result(input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part2RawCodestreamInfo, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_pdf_count_inspect_run(input, limits, events), result)
}

pub closed spec fn part2_pdf_count_typed_value(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits) -> Result<Part2PdfTyped, crate::DecodeError> {
    part2_pdf_count_value(input, limits, |bytes| part2_pdf_eol_typed_value(bytes, requested, limits),
        |value, repaired| part2_count_finish_typed(value, repaired))
}
pub closed spec fn part2_pdf_count_reconstructed_value(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits) -> Result<Part2PdfReconstructed, crate::DecodeError> {
    part2_pdf_count_value(input, limits, |bytes| part2_pdf_eol_reconstructed_value(bytes, requested, limits),
        |value, repaired| part2_count_finish_reconstructed(value, repaired))
}
pub closed spec fn part2_pdf_count_inspect_value(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2RawCodestreamInfo, crate::DecodeError> {
    part2_pdf_count_value(input, limits, |bytes| part2_pdf_eol_inspect_value(bytes, limits),
        |value: Part2RawCodestreamInfo, _repaired| value)
}

pub(crate) proof fn part2_pdf_count_contracts_unfold(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits)
    ensures
        forall|reply: Result<Part2PdfTyped, crate::DecodeError>|
            #[trigger] part2_pdf_count_typed_result(input, requested, limits, reply)
                == part2_cold_framed(|events| part2_pdf_count_typed_run(input, requested, limits, events), reply),
        forall|reply: Result<Part2PdfReconstructed, crate::DecodeError>|
            #[trigger] part2_pdf_count_reconstructed_result(input, requested, limits, reply)
                == part2_cold_framed(|events| part2_pdf_count_reconstructed_run(input, requested, limits, events), reply),
        forall|reply: Result<Part2RawCodestreamInfo, crate::DecodeError>|
            #[trigger] part2_pdf_count_inspect_result(input, limits, reply)
                == part2_cold_framed(|events| part2_pdf_count_inspect_run(input, limits, events), reply),
        part2_pdf_count_typed_value(input, requested, limits)
            == part2_pdf_count_value(input, limits, |bytes| part2_pdf_eol_typed_value(bytes, requested, limits),
                |value, repaired| part2_count_finish_typed(value, repaired)),
        part2_pdf_count_reconstructed_value(input, requested, limits)
            == part2_pdf_count_value(input, limits, |bytes| part2_pdf_eol_reconstructed_value(bytes, requested, limits),
                |value, repaired| part2_count_finish_reconstructed(value, repaired)),
        part2_pdf_count_inspect_value(input, limits)
            == part2_pdf_count_value(input, limits, |bytes| part2_pdf_eol_inspect_value(bytes, limits),
                |value: Part2RawCodestreamInfo, _repaired| value),
{}

pub(crate) open spec fn part2_count_header_start(input: Seq<u8>, pos: nat, error: crate::DecodeError)
    -> Result<usize, crate::DecodeError>
    decreases input.len() as int - pos,
{
    if pos + 2 <= input.len() && input[pos as int] == 255 && input[pos as int + 1] == 144 {
        Ok(pos as usize)
    } else if pos + 4 > input.len() || pos + 4 > usize::MAX
        || input[pos as int] != 255 || input[pos as int + 1] < 0x50 || input[pos as int + 1] > 0x8f {
        Err(error)
    } else {
        let length = part1_marker_value(input[pos as int + 2], input[pos as int + 3]) as nat;
        if length < 2 || pos + 2 + length > input.len() || pos + 2 + length > usize::MAX { Err(error) }
        else { part2_count_header_start(input, pos + 2 + length, error) }
    }
}

pub(crate) open spec fn part2_count_part_length(input: Seq<u8>, pos: nat) -> nat
    recommends pos + 12 <= input.len(),
{
    part1_codestream_u32(input[pos as int + 6], input[pos as int + 7],
        input[pos as int + 8], input[pos as int + 9]) as nat
}

pub(crate) open spec fn part2_count_tile(input: Seq<u8>, pos: nat) -> nat
    recommends pos + 12 <= input.len(),
{
    part1_marker_value(input[pos as int + 4], input[pos as int + 5]) as nat
}

pub(crate) open spec fn part2_count_shape_walk(
    input: Seq<u8>, offset: u64, limits: &crate::ResourceLimits, error: crate::DecodeError,
    pos: nat, first: usize, declared: Option<u8>, parts: nat, max_tile: nat, matched: bool,
) -> Result<crate::pdf_tile_count::CountShape, crate::DecodeError>
    decreases input.len() as int - pos,
{
    if pos + 2 == input.len() && input[pos as int] == 255 && input[pos as int + 1] == 217 {
        if !matched || declared.is_none() { Err(error) } else {
            Ok(crate::pdf_tile_count::CountShape { first, declared: declared.unwrap(),
                parts: parts as usize, max_tile: max_tile as usize })
        }
    } else if pos + 12 > input.len() || pos + 12 > usize::MAX
        || input[pos as int] != 255 || input[pos as int + 1] != 144
        || input[pos as int + 2] != 0 || input[pos as int + 3] != 10
        || input[pos as int + 11] == 0 || input[pos as int + 11] == 255
        || (declared.is_some() && declared.unwrap() != input[pos as int + 11]) {
        Err(error)
    } else if parts >= crate::limits::resource_tile_part_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TileParts,
            limit: crate::limits::resource_tile_part_limit(limits) as u64, actual: (parts + 1) as u64 })
    } else if part2_count_tile(input, pos) >= crate::limits::resource_tile_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Tiles,
            limit: crate::limits::resource_tile_limit(limits) as u64,
            actual: (part2_count_tile(input, pos) + 1) as u64 })
    } else {
        let length = part2_count_part_length(input, pos);
        if length < 14 || pos + length > input.len() || pos + length > usize::MAX
            || parts + 1 > usize::MAX { Err(error) }
        else {
            let tile = part2_count_tile(input, pos);
            part2_count_shape_walk(input, offset, limits, error, pos + length, first,
                Some(input[pos as int + 11]), parts + 1, if tile > max_tile { tile } else { max_tile },
                matched || (input[pos as int + 10] == input[pos as int + 11] && pos == offset))
        }
    }
}

pub(crate) open spec fn part2_count_shape(input: Seq<u8>, offset: u64,
    limits: &crate::ResourceLimits, error: crate::DecodeError)
    -> Result<crate::pdf_tile_count::CountShape, crate::DecodeError> {
    if input.len() < 2 || input[0] != 255 || input[1] != 79 { Err(error) }
    else { match part2_count_header_start(input, 2, error) {
        Err(error) => Err(error),
        Ok(first) => part2_count_shape_walk(input, offset, limits, error, first as nat, first,
            None, 0, 0, false),
    }}
}

pub(crate) open spec fn part2_count_admit(input_bytes: usize,
    shape: crate::pdf_tile_count::CountShape, limits: &crate::ResourceLimits)
    -> Result<u64, crate::DecodeError> {
    let overflow = crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ArithmeticOverflow };
    let table = shape.max_tile as nat + 1;
    let scratch = table * 2 + shape.parts as nat * 8 + input_bytes as nat;
    let work = input_bytes as nat * 4 + table + shape.parts as nat;
    if table > u64::MAX || scratch > u64::MAX { Err(overflow) }
    else if scratch > crate::limits::resource_decoded_bytes_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::DecodedBytes,
            limit: crate::limits::resource_decoded_bytes_limit(limits), actual: scratch as u64 })
    } else if work > u64::MAX { Err(overflow) }
    else if work > crate::limits::resource_work_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
            limit: crate::limits::resource_work_limit(limits), actual: work as u64 })
    } else { Ok(work as u64) }
}

pub(crate) open spec fn part2_count_validate(
    input: Seq<u8>, shape: crate::pdf_tile_count::CountShape, error: crate::DecodeError,
    pos: nat, next: Seq<u16>, fields: Seq<usize>,
) -> Result<Seq<usize>, crate::DecodeError>
    decreases shape.parts as int - fields.len(),
{
    if fields.len() >= shape.parts {
        if pos + 2 == input.len() && input[pos as int] == 255 && input[pos as int + 1] == 217
            && forall|i:int| 0 <= i < next.len() ==> next[i] == 0 || next[i] == shape.declared as nat + 1 {
            Ok(fields)
        } else { Err(error) }
    } else if pos + 12 > input.len() || pos + 12 > usize::MAX
        || input[pos as int] != 255 || input[pos as int + 1] != 144 || input[pos as int + 2] != 0
        || input[pos as int + 3] != 10 || input[pos as int + 11] != shape.declared { Err(error) }
    else {
        let tile = part2_count_tile(input, pos);
        let length = part2_count_part_length(input, pos);
        if tile >= next.len() || next[tile as int] != input[pos as int + 10] as nat
            || input[pos as int + 10] > shape.declared || shape.declared == 255
            || pos + 11 > usize::MAX || length < 14 || pos + length > input.len() || pos + length > usize::MAX {
            Err(error)
        } else {
            part2_count_validate(input, shape, error, pos + length,
                next.update(tile as int, (next[tile as int] + 1) as u16),
                fields.push((pos + 11) as usize))
        }
    }

}

pub(crate) open spec fn part2_count_patch(bytes: Seq<u8>, base: usize, positions: Seq<usize>,
    declared: u8, error: crate::DecodeError, index: nat) -> Result<Seq<u8>, crate::DecodeError>
    decreases positions.len() as int - index,
{
    if index >= positions.len() { Ok(bytes) }
    else {
        let at = base as nat + positions[index as int] as nat;
        if at > usize::MAX || at >= bytes.len() || declared == 255 { Err(error) }
        else { part2_count_patch(bytes.update(at as int, (declared + 1) as u8),
            base, positions, declared, error, index + 1) }
    }
}

pub(crate) open spec fn part2_count_copy_run(input: Seq<u8>, base: usize, positions: Seq<usize>,
    declared: u8, error: crate::DecodeError, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Seq<u8>> {
    part2_jpip_snapshot_bind(part2_count_capacity_run(input, error, 2, input.len() as usize, events),
        |_, rest| Some((part2_count_patch(input, base, positions, declared, error, 0), rest)))
}

pub(crate) closed spec fn part2_count_copy_result(input: Seq<u8>, base: usize, positions: Seq<usize>,
    declared: u8, error: crate::DecodeError, result: Result<Seq<u8>, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_count_copy_run(input, base, positions, declared, error, events), result)
}

pub(crate) proof fn part2_count_copy_normal(input: Seq<u8>, base: usize, positions: Seq<usize>,
    declared: u8, error: crate::DecodeError)
    ensures part2_count_copy_result(input, base, positions, declared, error,
        part2_count_patch(input, base, positions, declared, error, 0)),
{
    let prefix = seq![Part2JpipSnapshotEvent::PdfCountCapacity { input, error, role: 2,
        elements: input.len() as usize, succeeded: true }];
    let value = part2_count_patch(input, base, positions, declared, error, 0);
    assert forall|tail| #[trigger] part2_count_copy_run(input, base, positions, declared, error, prefix + tail)
        == Some((value, tail)) by { assert((prefix + tail).drop_first() =~= tail); }
    assert(part2_cold_prefix(|events| part2_count_copy_run(input, base, positions, declared, error, events), prefix, value));
}

pub(crate) proof fn part2_count_copy_refused(input: Seq<u8>, base: usize, positions: Seq<usize>,
    declared: u8, error: crate::DecodeError)
    ensures part2_count_copy_result(input, base, positions, declared, error, Err(crate::DecodeError::AllocationFailed)),
{
    let prefix = seq![Part2JpipSnapshotEvent::PdfCountCapacity { input, error, role: 2,
        elements: input.len() as usize, succeeded: false }];
    assert forall|tail| #[trigger] part2_count_copy_run(input, base, positions, declared, error, prefix + tail)
        == Some((Err(crate::DecodeError::AllocationFailed), tail)) by { assert((prefix + tail).drop_first() =~= tail); }
    assert(part2_cold_prefix(|events| part2_count_copy_run(input, base, positions, declared, error, events),
        prefix, Err(crate::DecodeError::AllocationFailed)));
}

pub(crate) open spec fn part2_count_initial_admit(bytes: usize, limits: &crate::ResourceLimits,
    error: crate::DecodeError) -> Result<u64, crate::DecodeError> {
    match error {
        crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidTilePart } => {
            if bytes > crate::limits::resource_input_byte_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                    limit: crate::limits::resource_input_byte_limit(limits), actual: bytes as u64 })
            } else if bytes > crate::limits::resource_decoded_bytes_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::DecodedBytes,
                    limit: crate::limits::resource_decoded_bytes_limit(limits), actual: bytes as u64 })
            } else if bytes as nat * 4 > u64::MAX {
                Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ArithmeticOverflow })
            } else if bytes as nat * 4 > crate::limits::resource_work_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                    limit: crate::limits::resource_work_limit(limits), actual: (bytes as nat * 4) as u64 })
            } else { Ok(offset) }
        },
        _ => Err(error),
    }
}

pub(crate) type Part2PdfCountRepair = (Seq<u8>, u32, u64);

pub(crate) open spec fn part2_count_source_matches(input: Seq<u8>, stream: Seq<u8>, base: usize) -> bool {
    base as nat + stream.len() <= input.len()
        && stream == input.subrange(base as int, base as int + stream.len() as int)
}

pub(crate) open spec fn part2_count_repair_after_copy(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    fields: Seq<usize>, work: u64, bytes: Seq<u8>, events: Seq<Part2JpipSnapshotEvent>)
    -> Part2ColdRun<Part2PdfCountRepair> {
    if base as nat + stream.len() > bytes.len() || base as nat + stream.len() > usize::MAX {
        Some((Err(error), events))
    } else {
        part2_jpip_snapshot_bind(part2_cold_parse(bytes.subrange(base as int, base as int + stream.len() as int),
            limits, 14, 0, events), |_, tail| Some((Ok((bytes, fields.len() as u32, work)), tail)))
    }
}

pub(crate) open spec fn part2_count_repair_after_fields(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    shape: crate::pdf_tile_count::CountShape, fields: Seq<usize>, work: u64,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfCountRepair> {
    if fields.len() > u32::MAX { Some((Err(error), events)) } else {
        part2_jpip_snapshot_bind(part2_count_copy_run(input, base, fields, shape.declared, error, events),
            |bytes, rest| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, rest))
    }
}

pub(crate) open spec fn part2_count_repair_run(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfCountRepair> {
    match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(failure) => Some((Err(failure), events)),
        Ok(offset) => if !part2_count_source_matches(input, stream, base) { Some((Err(error), events)) }
        else { match part2_count_shape(stream, offset, limits, error) {
            Err(failure) => Some((Err(failure), events)),
            Ok(shape) => match part2_count_admit(input.len() as usize, shape, limits) {
                Err(failure) => Some((Err(failure), events)),
                Ok(work) => part2_jpip_snapshot_bind(part2_count_fields_run(stream, shape, error, events),
                    |fields, rest| part2_count_repair_after_fields(input, stream, base, limits, error, shape, fields, work, rest)),
            },
        }},
    }
}

pub(crate) closed spec fn part2_count_repair_result(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    result: Result<Part2PdfCountRepair, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_count_repair_run(input, stream, base, limits, error, events), result)
}

pub(crate) open spec fn part2_count_repair_value(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError)
    -> Result<Part2PdfCountRepair, crate::DecodeError> {
    match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(failure) => Err(failure),
        Ok(offset) => if !part2_count_source_matches(input, stream, base) { Err(error) }
        else { match part2_count_shape(stream, offset, limits, error) {
            Err(failure) => Err(failure),
            Ok(shape) => match part2_count_admit(input.len() as usize, shape, limits) {
                Err(failure) => Err(failure),
                Ok(work) => match part2_count_fields_value(stream, shape, error) {
                    Err(failure) => Err(failure),
                    Ok(fields) => if fields.len() > u32::MAX { Err(error) } else {
                        match part2_count_patch(input, base, fields, shape.declared, error, 0) {
                            Err(failure) => Err(failure),
                            Ok(bytes) => if base as nat + stream.len() > bytes.len()
                                || base as nat + stream.len() > usize::MAX { Err(error) }
                            else { match part1_parse_layout(bytes.subrange(base as int, base as int + stream.len() as int), limits) {
                                Err(failure) => Err(failure), Ok(_) => Ok((bytes, fields.len() as u32, work)),
                            }},
                        }
                    },
                },
            },
        }},
    }
}

pub(crate) open spec fn part2_count_prepared_base(prepared: Part2PdfPrepared, error: crate::DecodeError)
    -> Result<usize, crate::DecodeError> {
    if prepared.repaired.is_some() || prepared.ordinary { Err(error) } else { match prepared.file {
        None => Ok(0),
        Some(file) => if file.file_type.0 != crate::jp2::BoxType::JP2_BRAND || file.streams.len() != 1 { Err(error) }
        else { match part2_box_payload_offset(file.streams[0].0) {
            Err(failure) => Err(failure),
            Ok(base) => if base > usize::MAX { Err(error) } else { Ok(base as usize) },
        }},
    }}
}

pub(crate) open spec fn part2_count_prepare_after(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError, prepared: Part2PdfPrepared, events: Seq<Part2JpipSnapshotEvent>)
    -> Part2ColdRun<Part2PdfCountRepair> {
    match part2_count_prepared_base(prepared, error) {
        Err(failure) => Some((Err(failure), events)),
        Ok(base) => part2_count_repair_run(input, prepared.original, base, limits, error, events),
    }
}

pub(crate) closed spec fn part2_count_prepare_run(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfCountRepair> {
    match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(failure) => Some((Err(failure), events)),
        Ok(_) => part2_jpip_snapshot_bind(part2_pdf_prepare_run(input, limits, events),
            |prepared, rest| part2_count_prepare_after(input, limits, error, prepared, rest)),
    }
}

pub(crate) closed spec fn part2_count_prepare_result(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError, result: Result<Part2PdfCountRepair, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_count_prepare_run(input, limits, error, events), result)
}

pub(crate) closed spec fn part2_count_prepare_value(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError) -> Result<Part2PdfCountRepair, crate::DecodeError> {
    match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(failure) => Err(failure),
        Ok(_) => match part2_pdf_prepare_value(input, limits) {
            Err(failure) => Err(failure),
            Ok(prepared) => match part2_count_prepared_base(prepared, error) {
                Err(failure) => Err(failure),
                Ok(base) => part2_count_repair_value(input, prepared.original, base, limits, error),
            },
        },
    }
}

pub(crate) proof fn part2_count_prepare_value_unfold(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError)
    ensures part2_count_prepare_value(input, limits, error) ==
        match part2_count_initial_admit(input.len() as usize, limits, error) {
            Err(failure) => Err(failure),
            Ok(_) => match part2_pdf_prepare_value(input, limits) {
                Err(failure) => Err(failure),
                Ok(prepared) => match part2_count_prepared_base(prepared, error) {
                    Err(failure) => Err(failure),
                    Ok(base) => part2_count_repair_value(input, prepared.original, base, limits, error),
                },
            },
        },
{}

pub(crate) proof fn part2_count_prepare_admission_error(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError, failure: crate::DecodeError)
    requires part2_count_initial_admit(input.len() as usize, limits, error) == Err(failure),
    ensures part2_count_prepare_result(input, limits, error, Err(failure)),
{
    part2_cold_pure::<Part2PdfCountRepair>(Err(failure));
    assert forall|events| #[trigger] part2_count_prepare_run(input, limits, error, events)
        == Some((Err(failure), events)) by {};
}

pub(crate) proof fn part2_count_prepare_lift(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError, offset: u64, prepared: Result<Part2PdfPrepared, crate::DecodeError>,
    result: Result<Part2PdfCountRepair, crate::DecodeError>)
    requires part2_count_initial_admit(input.len() as usize, limits, error) == Ok(offset),
        part2_pdf_prepare_result(input, limits, prepared),
        match prepared {
            Err(failure) => result == Err(failure),
            Ok(value) => match part2_count_prepared_base(value, error) {
                Err(failure) => result == Err(failure),
                Ok(base) => part2_count_repair_result(input, value.original, base, limits, error, result),
            },
        },
    ensures part2_count_prepare_result(input, limits, error, result),
{
    part2_pdf_prepare_frames(input, limits, prepared);
    if let Ok(value) = prepared {
        match part2_count_prepared_base(value, error) {
            Err(failure) => {
                part2_cold_pure::<Part2PdfCountRepair>(Err(failure));
                assert forall|events| #[trigger] part2_count_prepare_after(input, limits, error, value, events)
                    == Some((Err(failure), events)) by {};
            },
            Ok(base) => {
                part2_decode_eta(|events| part2_count_repair_run(input, value.original, base, limits, error, events), result);
            },
        }
        part2_decode_eta(|events| part2_count_prepare_after(input, limits, error, value, events), result);
    }
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value, rest| part2_count_prepare_after(input, limits, error, value, rest), prepared, result);
    part2_decode_eta(|events| part2_jpip_snapshot_bind(part2_pdf_prepare_run(input, limits, events),
        |value, rest| part2_count_prepare_after(input, limits, error, value, rest)), result);
}

pub(crate) proof fn part2_count_repair_preflight_error(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError, failure: crate::DecodeError)
    requires match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(value) => value == failure,
        Ok(offset) => if !part2_count_source_matches(input, stream, base) { failure == error }
        else { match part2_count_shape(stream, offset, limits, error) {
            Err(value) => value == failure,
            Ok(shape) => part2_count_admit(input.len() as usize, shape, limits) == Err(failure),
        }},
    },
    ensures part2_count_repair_result(input, stream, base, limits, error, Err(failure)),
{
    part2_cold_pure::<Part2PdfCountRepair>(Err(failure));
    assert forall|events| #[trigger] part2_count_repair_run(input, stream, base, limits, error, events)
        == Some((Err(failure), events)) by {};
}

pub(crate) proof fn part2_count_repair_normal(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError)
    ensures part2_count_repair_result(input, stream, base, limits, error,
        part2_count_repair_value(input, stream, base, limits, error)),
{
    let result = part2_count_repair_value(input, stream, base, limits, error);
    let offset = match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(failure) => {
            part2_count_repair_preflight_error(input, stream, base, limits, error, failure);
            return;
        },
        Ok(value) => value,
    };
    if !part2_count_source_matches(input, stream, base) {
        part2_count_repair_preflight_error(input, stream, base, limits, error, error);
        return;
    }
    let shape = match part2_count_shape(stream, offset, limits, error) {
        Err(failure) => {
            part2_count_repair_preflight_error(input, stream, base, limits, error, failure);
            return;
        },
        Ok(value) => value,
    };
    let work = match part2_count_admit(input.len() as usize, shape, limits) {
        Err(failure) => {
            part2_count_repair_preflight_error(input, stream, base, limits, error, failure);
            return;
        },
        Ok(value) => value,
    };
    part2_count_fields_normal(stream, shape, error);
    let counted = part2_count_fields_value(stream, shape, error);
    if let Ok(fields) = counted {
        if fields.len() > u32::MAX {
            part2_cold_pure::<Part2PdfCountRepair>(Err(error));
            assert forall|events| #[trigger] part2_count_repair_after_fields(
                input, stream, base, limits, error, shape, fields, work, events) == Some((Err(error), events)) by {};
            part2_decode_eta(|events| part2_count_repair_after_fields(
                input, stream, base, limits, error, shape, fields, work, events), result);
        } else {
            part2_count_copy_normal(input, base, fields, shape.declared, error);
            let copied = part2_count_patch(input, base, fields, shape.declared, error, 0);
            if let Ok(bytes) = copied {
                if base as nat + stream.len() > bytes.len() || base as nat + stream.len() > usize::MAX {
                    part2_cold_pure::<Part2PdfCountRepair>(Err(error));
                    assert forall|events| #[trigger] part2_count_repair_after_copy(
                        input, stream, base, limits, error, fields, work, bytes, events) == Some((Err(error), events)) by {};
                    part2_decode_eta(|events| part2_count_repair_after_copy(
                        input, stream, base, limits, error, fields, work, bytes, events), result);
                } else {
                    let code = bytes.subrange(base as int, base as int + stream.len() as int);
                    part1_parse_layout_cold_normal(code, limits);
                    part2_count_repair_parsed_lift(input, stream, base, limits, error,
                        fields, work, bytes, part1_parse_layout(code, limits));
                }
            }
            part2_count_repair_copy_lift(input, stream, base, limits, error, shape, fields, work, copied, result);
        }
    }
    part2_count_repair_fields_lift(input, stream, base, limits, error, offset, shape, work, counted, result);
}

pub(crate) proof fn part2_count_prepare_normal(input: Seq<u8>, limits: &crate::ResourceLimits,
    error: crate::DecodeError)
    ensures part2_count_prepare_result(input, limits, error, part2_count_prepare_value(input, limits, error)),
{
    match part2_count_initial_admit(input.len() as usize, limits, error) {
        Err(failure) => part2_count_prepare_admission_error(input, limits, error, failure),
        Ok(offset) => {
            part2_pdf_prepare_normal(input, limits);
            let prepared = part2_pdf_prepare_value(input, limits);
            if let Ok(value) = prepared {
                if let Ok(base) = part2_count_prepared_base(value, error) {
                    part2_count_repair_normal(input, value.original, base, limits, error);
                }
            }
            part2_count_prepare_lift(input, limits, error, offset, prepared,
                part2_count_prepare_value(input, limits, error));
        },
    }
}

pub(crate) proof fn part2_pdf_count_typed_normal(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits)
    ensures part2_pdf_count_typed_result(input, requested, limits,
        part2_pdf_count_typed_value(input, requested, limits)),
{
    hide(part2_count_prepare_value);
    let base = |bytes, calls| part2_pdf_eol_typed_run(bytes, requested, limits, calls);
    let finish = |value, repaired| part2_count_finish_typed(value, repaired);
    part2_pdf_eol_typed_normal(input, requested, limits);
    part2_pdf_eol_frames(input, requested, limits);
    let first = part2_pdf_eol_typed_value(input, requested, limits);
    part2_decode_eta(|events| part2_pdf_eol_typed_run(input, requested, limits, events), first);
    let result = part2_pdf_count_typed_value(input, requested, limits);
    if let Err(error) = first {
        if part2_count_retry(error) {
            part2_count_prepare_normal(input, limits, error);
            let repaired = part2_count_prepare_value(input, limits, error);
            if let Ok(value) = repaired {
                part2_pdf_eol_typed_normal(value.0, requested, limits);
                part2_pdf_eol_frames(value.0, requested, limits);
                let second = part2_pdf_eol_typed_value(value.0, requested, limits);
                part2_decode_eta(|events| part2_pdf_eol_typed_run(value.0, requested, limits, events), second);
                part2_count_finished(value, base, finish, second);
            }
            part2_count_retried(input, limits, base, finish, error, repaired, result);
            return;
        }
    }
    part2_count_passthrough(input, limits, base, finish, first);
}

pub(crate) proof fn part2_pdf_count_reconstructed_normal(input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits)
    ensures part2_pdf_count_reconstructed_result(input, requested, limits,
        part2_pdf_count_reconstructed_value(input, requested, limits)),
{
    hide(part2_count_prepare_value);
    let base = |bytes, calls| part2_pdf_eol_reconstructed_run(bytes, requested, limits, calls);
    let finish = |value, repaired| part2_count_finish_reconstructed(value, repaired);
    part2_pdf_eol_reconstructed_normal(input, requested, limits);
    part2_pdf_eol_frames(input, requested, limits);
    let first = part2_pdf_eol_reconstructed_value(input, requested, limits);
    part2_decode_eta(|events| part2_pdf_eol_reconstructed_run(input, requested, limits, events), first);
    let result = part2_pdf_count_reconstructed_value(input, requested, limits);
    if let Err(error) = first {
        if part2_count_retry(error) {
            part2_count_prepare_normal(input, limits, error);
            let repaired = part2_count_prepare_value(input, limits, error);
            if let Ok(value) = repaired {
                part2_pdf_eol_reconstructed_normal(value.0, requested, limits);
                part2_pdf_eol_frames(value.0, requested, limits);
                let second = part2_pdf_eol_reconstructed_value(value.0, requested, limits);
                part2_decode_eta(|events| part2_pdf_eol_reconstructed_run(value.0, requested, limits, events), second);
                part2_count_finished(value, base, finish, second);
            }
            part2_count_retried(input, limits, base, finish, error, repaired, result);
            return;
        }
    }
    part2_count_passthrough(input, limits, base, finish, first);
}

pub(crate) proof fn part2_pdf_count_inspect_normal(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_pdf_count_inspect_result(input, limits, part2_pdf_count_inspect_value(input, limits)),
{
    hide(part2_count_prepare_value);
    let requested = (Part2TileSelection::All, None, 0u8);
    let base = |bytes, calls| part2_pdf_eol_inspect_run(bytes, limits, calls);
    let finish = |value: Part2RawCodestreamInfo, _repaired| value;
    part2_pdf_eol_inspect_normal(input, limits);
    part2_pdf_eol_frames(input, requested, limits);
    let first = part2_pdf_eol_inspect_value(input, limits);
    part2_decode_eta(|events| part2_pdf_eol_inspect_run(input, limits, events), first);
    let result = part2_pdf_count_inspect_value(input, limits);
    if let Err(error) = first {
        if part2_count_retry(error) {
            part2_count_prepare_normal(input, limits, error);
            let repaired = part2_count_prepare_value(input, limits, error);
            if let Ok(value) = repaired {
                part2_pdf_eol_inspect_normal(value.0, limits);
                part2_pdf_eol_frames(value.0, requested, limits);
                let second = part2_pdf_eol_inspect_value(value.0, limits);
                part2_decode_eta(|events| part2_pdf_eol_inspect_run(value.0, limits, events), second);
                part2_count_finished(value, base, finish, second);
            }
            part2_count_retried(input, limits, base, finish, error, repaired, result);
            return;
        }
    }
    part2_count_passthrough(input, limits, base, finish, first);
}

pub(crate) proof fn part2_count_repair_fields_lift(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    offset: u64, shape: crate::pdf_tile_count::CountShape, work: u64,
    fields: Result<Seq<usize>, crate::DecodeError>, result: Result<Part2PdfCountRepair, crate::DecodeError>)
    requires part2_count_initial_admit(input.len() as usize, limits, error) == Ok(offset),
        part2_count_source_matches(input, stream, base),
        part2_count_shape(stream, offset, limits, error) == Ok(shape),
        part2_count_admit(input.len() as usize, shape, limits) == Ok(work),
        part2_count_fields_result(stream, shape, error, fields),
        match fields {
            Err(failure) => result == Err(failure),
            Ok(value) => part2_cold_framed(
                |events| part2_count_repair_after_fields(input, stream, base, limits, error, shape, value, work, events), result),
        },
    ensures part2_count_repair_result(input, stream, base, limits, error, result),
{
    part2_decode_eta(|events| part2_count_fields_run(stream, shape, error, events), fields);
    if let Ok(value) = fields {
        part2_decode_eta(|events| part2_count_repair_after_fields(input, stream, base, limits, error, shape, value, work, events), result);
    }
    part2_cold_bind(|events| part2_count_fields_run(stream, shape, error, events),
        |value, rest| part2_count_repair_after_fields(input, stream, base, limits, error, shape, value, work, rest),
        fields, result);
    part2_decode_eta(|events| part2_jpip_snapshot_bind(part2_count_fields_run(stream, shape, error, events),
        |value, rest| part2_count_repair_after_fields(input, stream, base, limits, error, shape, value, work, rest)), result);
}

pub(crate) proof fn part2_count_repair_copy_lift(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    shape: crate::pdf_tile_count::CountShape, fields: Seq<usize>, work: u64,
    copied: Result<Seq<u8>, crate::DecodeError>, result: Result<Part2PdfCountRepair, crate::DecodeError>)
    requires fields.len() <= u32::MAX,
        part2_count_copy_result(input, base, fields, shape.declared, error, copied),
        match copied {
            Err(failure) => result == Err(failure),
            Ok(bytes) => part2_cold_framed(
                |events| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, events), result),
        },
    ensures part2_cold_framed(
        |events| part2_count_repair_after_fields(input, stream, base, limits, error, shape, fields, work, events), result),
        forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfCountRepair>|
            (forall|events| #[trigger] other(events) == part2_count_repair_after_fields(input, stream, base, limits, error, shape, fields, work, events))
                ==> #[trigger] part2_cold_framed(other, result),
{
    part2_decode_eta(|events| part2_count_copy_run(input, base, fields, shape.declared, error, events), copied);
    if let Ok(bytes) = copied {
        part2_decode_eta(|events| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, events), result);
    }
    part2_cold_bind(|events| part2_count_copy_run(input, base, fields, shape.declared, error, events),
        |bytes, rest| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, rest), copied, result);
    part2_decode_eta(|events| part2_jpip_snapshot_bind(
        part2_count_copy_run(input, base, fields, shape.declared, error, events),
        |bytes, rest| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, rest)), result);
    part2_decode_eta(|events| part2_count_repair_after_fields(input, stream, base, limits, error, shape, fields, work, events), result);
}

pub(crate) open spec fn part2_count_parsed_reply(parsed: Part1CompleteLayoutResult,
    bytes: Seq<u8>, fields: Seq<usize>, work: u64) -> Result<Part2PdfCountRepair, crate::DecodeError> {
    match parsed { Err(failure) => Err(failure), Ok(_) => Ok((bytes, fields.len() as u32, work)) }
}

pub(crate) proof fn part2_count_repair_parsed_lift(input: Seq<u8>, stream: Seq<u8>,
    base: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
    fields: Seq<usize>, work: u64, bytes: Seq<u8>, parsed: Part1CompleteLayoutResult)
    requires base as nat + stream.len() <= bytes.len(), base as nat + stream.len() <= usize::MAX,
        part1_parse_layout_cold_result(bytes.subrange(base as int, base as int + stream.len() as int), limits, parsed),
    ensures part2_cold_framed(
        |events| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, events),
        part2_count_parsed_reply(parsed, bytes, fields, work)),
        forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2PdfCountRepair>|
            (forall|events| #[trigger] other(events) == part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, events))
                ==> #[trigger] part2_cold_framed(other, part2_count_parsed_reply(parsed, bytes, fields, work)),
{
    let code = bytes.subrange(base as int, base as int + stream.len() as int);
    let result = match parsed { Err(failure) => Err(failure), Ok(_) => Ok((bytes, fields.len() as u32, work)) };
    part2_cold_parse_actual(code, limits, 14, 0, parsed);
    if parsed.is_ok() { part2_cold_pure::<Part2PdfCountRepair>(Ok((bytes, fields.len() as u32, work))); }
    part2_cold_bind(|events| part2_cold_parse(code, limits, 14, 0, events),
        |_, tail| Some((Ok((bytes, fields.len() as u32, work)), tail)), parsed, result);
    part2_decode_eta(|events| part2_jpip_snapshot_bind(part2_cold_parse(code, limits, 14, 0, events),
        |_, tail| Some((Ok((bytes, fields.len() as u32, work)), tail))), result);
    part2_decode_eta(|events| part2_count_repair_after_copy(input, stream, base, limits, error, fields, work, bytes, events), result);
}

pub(crate) proof fn part2_count_validate_step(input: Seq<u8>, shape: crate::pdf_tile_count::CountShape,
    error: crate::DecodeError, pos: nat, next: Seq<u16>, fields: Seq<usize>)
    requires fields.len() < shape.parts, pos + 12 <= input.len(), pos + 12 <= usize::MAX,
        input[pos as int] == 255, input[pos as int + 1] == 144,
        input[pos as int + 2] == 0, input[pos as int + 3] == 10,
        input[pos as int + 11] == shape.declared, shape.declared < 255,
        part2_count_tile(input, pos) < next.len(),
        next[part2_count_tile(input, pos) as int] == input[pos as int + 10] as nat,
        input[pos as int + 10] <= shape.declared,
        part2_count_part_length(input, pos) >= 14,
        pos + part2_count_part_length(input, pos) <= input.len(),
        pos + part2_count_part_length(input, pos) <= usize::MAX,
    ensures part2_count_validate(input, shape, error, pos, next, fields)
        == part2_count_validate(input, shape, error, pos + part2_count_part_length(input, pos),
            next.update(part2_count_tile(input, pos) as int,
                (next[part2_count_tile(input, pos) as int] + 1) as u16),
            fields.push((pos + 11) as usize)),
{
    reveal_with_fuel(part2_count_validate, 1);
}

    pub(crate) open spec fn part2_count_capacity_run(input: Seq<u8>, error: crate::DecodeError,
        role: u8, elements: usize, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<()> {
        if events.len() == 0 { None } else {
            match events[0] {
                Part2JpipSnapshotEvent::PdfCountCapacity { input: actual, error: actual_error,
                    role: actual_role, elements: actual_elements, succeeded } =>
                    if actual != input || actual_error != error || actual_role != role || actual_elements != elements { None }
                    else { Some((if succeeded { Ok(()) } else { Err(crate::DecodeError::AllocationFailed) },
                        events.drop_first())) },
                _ => None,
            }
        }
    }

    pub(crate) open spec fn part2_count_fields_value(input: Seq<u8>, shape: crate::pdf_tile_count::CountShape,
        error: crate::DecodeError) -> Result<Seq<usize>, crate::DecodeError> {
        if shape.max_tile as nat + 1 > usize::MAX { Err(error) } else {
            part2_count_validate(input, shape, error, shape.first as nat,
                Seq::new(shape.max_tile as nat + 1, |_: int| 0u16), Seq::empty())
        }
    }

    pub(crate) open spec fn part2_count_fields_run(input: Seq<u8>, shape: crate::pdf_tile_count::CountShape,
        error: crate::DecodeError, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Seq<usize>> {
        if shape.max_tile as nat + 1 > usize::MAX { Some((Err(error), events)) } else {
            part2_jpip_snapshot_bind(
                part2_count_capacity_run(input, error, 0, (shape.max_tile + 1) as usize, events),
                |_, rest| part2_jpip_snapshot_bind(part2_count_capacity_run(input, error, 1, shape.parts, rest),
                    |_, tail| Some((part2_count_fields_value(input, shape, error), tail))))
        }
    }

    pub(crate) closed spec fn part2_count_fields_result(input: Seq<u8>,
        shape: crate::pdf_tile_count::CountShape, error: crate::DecodeError,
        result: Result<Seq<usize>, crate::DecodeError>) -> bool {
        part2_cold_framed(|events| part2_count_fields_run(input, shape, error, events), result)
    }

    pub(crate) proof fn part2_count_fields_normal(input: Seq<u8>, shape: crate::pdf_tile_count::CountShape,
        error: crate::DecodeError)
        ensures part2_count_fields_result(input, shape, error, part2_count_fields_value(input, shape, error)),
    {
        let prefix = if shape.max_tile as nat + 1 > usize::MAX { Seq::empty() } else {
            seq![
                Part2JpipSnapshotEvent::PdfCountCapacity { input, error, role: 0,
                    elements: (shape.max_tile + 1) as usize, succeeded: true },
                Part2JpipSnapshotEvent::PdfCountCapacity { input, error, role: 1,
                    elements: shape.parts, succeeded: true },
            ]
        };
        assert forall|tail| #[trigger] part2_count_fields_run(input, shape, error, prefix + tail)
            == Some((part2_count_fields_value(input, shape, error), tail)) by {
            if prefix.len() == 2 {
                assert((prefix + tail).drop_first().drop_first() =~= tail);
            }
        }
        assert(part2_cold_prefix(|events| part2_count_fields_run(input, shape, error, events),
            prefix, part2_count_fields_value(input, shape, error)));
    }

    pub(crate) proof fn part2_count_fields_refused(input: Seq<u8>, shape: crate::pdf_tile_count::CountShape,
        error: crate::DecodeError, role: u8)
        requires role <= 1, shape.max_tile as nat + 1 <= usize::MAX,
        ensures part2_count_fields_result(input, shape, error, Err(crate::DecodeError::AllocationFailed)),
    {
        let table = Part2JpipSnapshotEvent::PdfCountCapacity { input, error, role: 0,
            elements: (shape.max_tile + 1) as usize, succeeded: role == 1 };
        let prefix = if role == 0 { seq![table] } else {
            seq![table, Part2JpipSnapshotEvent::PdfCountCapacity { input, error, role: 1,
                elements: shape.parts, succeeded: false }]
        };
        assert forall|tail| #[trigger] part2_count_fields_run(input, shape, error, prefix + tail)
            == Some((Err(crate::DecodeError::AllocationFailed), tail)) by {
            if role == 0 { assert((prefix + tail).drop_first() =~= tail); }
            else { assert((prefix + tail).drop_first().drop_first() =~= tail); }
        }
        assert(part2_cold_prefix(|events| part2_count_fields_run(input, shape, error, events),
            prefix, Err(crate::DecodeError::AllocationFailed)));
    }
}
