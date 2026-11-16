//! Common PDF framing uses actual file metadata and one bounded EOC copy.
use super::*;
verus! {
pub(crate) struct Part2PdfPrepared {
    pub file: Option<Part2RawJp2File>,
    pub original: Seq<u8>,
    pub repaired: Option<Seq<u8>>,
    pub preflight_work: u64,
}

pub(crate) open spec fn part2_pdf_invalid_profile() -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidProfile }
}

pub(crate) open spec fn part2_pdf_raw_input(input: Seq<u8>) -> bool {
    input.len() >= 2 && input[0] == 0xff && input[1] == 0x4f
}

pub(crate) open spec fn part2_pdf_file_profile(file: Part2RawJp2File) -> bool {
    part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)
        && !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPX_BRAND)
        && !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPX_BASELINE_BRAND)
        && !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND)
        && file.streams.len() == 1
}

pub(crate) open spec fn part2_pdf_file_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Option<Part2RawJp2File>, crate::DecodeError> {
    if part2_pdf_raw_input(input) { Ok(None) }
    else { match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => if part2_pdf_file_profile(file) { Ok(Some(file)) } else { Err(part2_pdf_invalid_profile()) },
    }}
}

pub(crate) open spec fn part2_pdf_file_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Option<Part2RawJp2File>> {
    if part2_pdf_raw_input(input) { Some((Ok(None), events)) }
    else { part2_jpip_snapshot_bind(part2_parse_container_cold_run(input, *limits, events),
        |file, rest| Some((if part2_pdf_file_profile(file) { Ok(Some(file)) }
            else { Err(part2_pdf_invalid_profile()) }, rest))) }
}

pub(crate) proof fn part2_pdf_file_cold_normal(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_cold_framed(|events| part2_pdf_file_cold_run(input, limits, events),
        part2_pdf_file_value(input, limits)),
{
    if part2_pdf_raw_input(input) {
        part2_cold_pure::<Option<Part2RawJp2File>>(Ok(None));
    } else {
        part2_parse_container_cold_normal(input, *limits, Seq::empty());
        part2_parse_container_cold_frames(input, *limits, part2_parse_container(input, *limits));
        if let Ok(file) = part2_parse_container(input, *limits) {
            part2_cold_pure(if part2_pdf_file_profile(file) { Ok(Some(file)) }
                else { Err(part2_pdf_invalid_profile()) });
        }
        part2_cold_bind(
            |events| part2_parse_container_cold_run(input, *limits, events),
            |file, rest| Some((if part2_pdf_file_profile(file) { Ok(Some(file)) }
                else { Err(part2_pdf_invalid_profile()) }, rest)),
            part2_parse_container(input, *limits), part2_pdf_file_value(input, limits));
    }
}

pub(crate) open spec fn part2_pdf_original_input(input: Seq<u8>, file: Option<Part2RawJp2File>) -> Seq<u8> {
    match file { None => input, Some(file) => file.streams[0].1 }
}

pub(crate) open spec fn part2_pdf_effective_input(prepared: Part2PdfPrepared) -> Seq<u8> {
    match prepared.repaired { None => prepared.original, Some(bytes) => bytes }
}

pub(crate) open spec fn part2_pdf_copy_run(
    input: Seq<u8>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<u8>> {
    if input.len() + 2 > usize::MAX { Some((raw_repair_response(input, true), events)) }
    else if events.len() == 0 { None }
    else { match events[0] {
        Part2JpipSnapshotEvent::PdfEocCopy { input: actual, elements, succeeded } =>
            if actual != input || elements != input.len() + 2 { None }
            else { Some((raw_repair_response(input, succeeded), events.drop_first())) },
        _ => None,
    }}
}

pub(crate) proof fn part2_pdf_copy_actual(input: Seq<u8>, result: Result<Seq<u8>, crate::DecodeError>)
    requires raw_repair_result(input, result),
    ensures part2_cold_framed(|events| part2_pdf_copy_run(input, events), result),
{
    if input.len() + 2 > usize::MAX {
        part2_cold_pure::<Seq<u8>>(result);
    } else {
        let succeeded = result.is_ok();
        let prefix = seq![Part2JpipSnapshotEvent::PdfEocCopy { input, elements: (input.len() + 2) as usize, succeeded }];
        assert(result == raw_repair_response(input, succeeded));
        assert forall|tail| part2_pdf_copy_run(input, prefix + tail) == Some((result, tail)) by {
            assert((prefix + tail).drop_first() =~= tail);
        }
        assert(part2_cold_prefix(|events| part2_pdf_copy_run(input, events), prefix, result));
    }
}

pub(crate) open spec fn part2_pdf_prepared_copy(
    file: Option<Part2RawJp2File>, original: Seq<u8>, frame: (bool, u64), bytes: Seq<u8>,
) -> Part2PdfPrepared {
    Part2PdfPrepared { file, original, repaired: Some(bytes), preflight_work: frame.1 }
}

pub(crate) open spec fn part2_pdf_prepare_after_file_run(
    input: Seq<u8>, file: Option<Part2RawJp2File>, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfPrepared> {
    let original = part2_pdf_original_input(input, file);
    match raw_recovery_framing(original, limits) {
        Err(error) => Some((Err(error), events)),
        Ok(frame) => if !frame.0 {
            Some((Ok(Part2PdfPrepared { file, original, repaired: None, preflight_work: frame.1 }), events))
        } else { match raw_recovery_admit(original.len() as usize, frame.1, limits) {
            Err(error) => Some((Err(error), events)),
            Ok(()) => part2_jpip_snapshot_bind(part2_pdf_copy_run(original, events),
                |bytes: Seq<u8>, rest| Some((Ok(part2_pdf_prepared_copy(file, original, frame, bytes)), rest))),
        }},
    }
}

pub(crate) open spec fn part2_pdf_prepare_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfPrepared> {
    part2_jpip_snapshot_bind(part2_pdf_file_cold_run(input, limits, events),
        |file, rest| part2_pdf_prepare_after_file_run(input, file, limits, rest))
}

pub(crate) open spec fn part2_pdf_prepare_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Result<Part2PdfPrepared, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_pdf_prepare_run(input, limits, events), result)
}

pub(crate) open spec fn part2_pdf_prepare_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part2PdfPrepared, crate::DecodeError> {
    match part2_pdf_file_value(input, limits) {
        Err(error) => Err(error),
        Ok(file) => {
            let original = part2_pdf_original_input(input, file);
            match raw_recovery_framing(original, limits) {
                Err(error) => Err(error),
                Ok(frame) => if !frame.0 {
                    Ok(Part2PdfPrepared { file, original, repaired: None, preflight_work: frame.1 })
                } else { match raw_recovery_admit(original.len() as usize, frame.1, limits) {
                    Err(error) => Err(error),
                    Ok(()) => match raw_repair_response(original, true) {
                        Err(error) => Err(error),
                        Ok(bytes) => Ok(part2_pdf_prepared_copy(file, original, frame, bytes)),
                    },
                }},
            }
        },
    }
}

pub(crate) proof fn part2_pdf_prepare_copy_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, file: Option<Part2RawJp2File>,
    frame: (bool, u64), result: Result<Seq<u8>, crate::DecodeError>,
)
    requires part2_pdf_file_value(input, limits) == Ok(file),
        raw_recovery_framing(part2_pdf_original_input(input, file), limits) == Ok(frame), frame.0,
        raw_recovery_admit(part2_pdf_original_input(input, file).len() as usize, frame.1, limits) == Ok(()),
        raw_repair_result(part2_pdf_original_input(input, file), result),
    ensures part2_pdf_prepare_result(input, limits, match result {
        Err(error) => Err(error), Ok(bytes) => Ok(part2_pdf_prepared_copy(file, part2_pdf_original_input(input, file), frame, bytes)),
    }),
{
    let original = part2_pdf_original_input(input, file);
    part2_pdf_copy_actual(original, result);
    let output = match result { Err(error) => Err(error), Ok(bytes) => Ok(part2_pdf_prepared_copy(file, original, frame, bytes)) };
    if let Ok(bytes) = result { part2_cold_pure(Ok(part2_pdf_prepared_copy(file, original, frame, bytes))); }
    part2_cold_bind(|events| part2_pdf_copy_run(original, events),
        |bytes: Seq<u8>, rest| Some((Ok(part2_pdf_prepared_copy(file, original, frame, bytes)), rest)), result, output);
    part2_pdf_file_cold_normal(input, limits);
    part2_cold_bind(
        |events| part2_pdf_file_cold_run(input, limits, events),
        |parsed_file, rest| part2_pdf_prepare_after_file_run(input, parsed_file, limits, rest),
        Ok(file), output);
}

pub(crate) proof fn part2_pdf_prepare_container_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires !part2_pdf_raw_input(input),
        part2_parse_container_cold_result(input, *limits, Err(error)),
    ensures part2_pdf_prepare_result(input, limits, Err(error)),
{
    part2_parse_container_cold_frames(input, *limits, Err(error));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| Some((if part2_pdf_file_profile(file) { Ok(Some(file)) }
            else { Err(part2_pdf_invalid_profile()) }, rest)), Err(error), Err(error));
    part2_cold_bind(
        |events| part2_pdf_file_cold_run(input, limits, events),
        |file, rest| part2_pdf_prepare_after_file_run(input, file, limits, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_pdf_prepare_normal(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_pdf_prepare_result(input, limits, part2_pdf_prepare_value(input, limits)),
{
    match part2_pdf_file_value(input, limits) {
        Err(_) => part2_cold_pure::<Part2PdfPrepared>(part2_pdf_prepare_value(input, limits)),
        Ok(file) => {
            let original = part2_pdf_original_input(input, file);
            match raw_recovery_framing(original, limits) {
                Err(_) => part2_cold_pure::<Part2PdfPrepared>(part2_pdf_prepare_value(input, limits)),
                Ok(frame) => if !frame.0 {
                    part2_cold_pure::<Part2PdfPrepared>(part2_pdf_prepare_value(input, limits));
                } else { match raw_recovery_admit(original.len() as usize, frame.1, limits) {
                    Err(_) => part2_cold_pure::<Part2PdfPrepared>(part2_pdf_prepare_value(input, limits)),
                    Ok(()) => {
                        part2_pdf_prepare_copy_actual(input, limits, file, frame, raw_repair_response(original, true));
                        return;
                    },
                }},
            }
        },
    }
    part2_pdf_file_cold_normal(input, limits);
    part2_cold_bind(
        |events| part2_pdf_file_cold_run(input, limits, events),
        |file, rest| part2_pdf_prepare_after_file_run(input, file, limits, rest),
        part2_pdf_file_value(input, limits), part2_pdf_prepare_value(input, limits));
}

pub(crate) open spec fn part2_pdf_validate_layout(
    input: Seq<u8>, prepared: Part2PdfPrepared, info: Part2RawCodestreamInfo,
    limits: &crate::ResourceLimits,
) -> Result<bool, crate::DecodeError> {
    if part1_profile_optional_advertises_ht(info.1.2) {
        Err(part2_pdf_invalid_profile())
    } else { match prepared.file {
        None => Ok(false),
        Some(file) => match part2_dimension_validate_header(input, file, info, limits) {
            Err(error) => Err(error), Ok(report) => Ok(report.ignored_container_dimensions),
        },
    }}
}

pub(crate) open spec fn part2_pdf_finish_recovery(
    prepared: Part2PdfPrepared, ignored: bool, selected: Option<u16>, trailer: u8,
    full_canvas_sample_bytes: Option<u64>,
) -> crate::PdfRecovery {
    let effective = part2_pdf_effective_input(prepared).len() as u64;
    crate::PdfRecovery {
        appended_eoc: prepared.repaired.is_some(),
        ignored_container_dimensions: ignored,
        selected_present_tile: selected,
        empty_initial_mq_prefixes: 0,
        discarded_tile_trailer_bytes: trailer as u64,
        original_codestream_bytes: prepared.original.len() as u64,
        effective_codestream_bytes: effective,
        preflight_work_units: prepared.preflight_work,
        repair_copy_bytes: if prepared.repaired.is_some() { effective } else { 0 },
        full_canvas_sample_bytes,
    }
}

pub type Part2PdfTyped = (Part1DecodedTypedImage, crate::PdfRecovery);
pub type Part2PdfReconstructed = (Part1DecodedImageModel, crate::PdfRecovery);

pub(crate) open spec fn part2_pdf_layout_info(layout: Part1CompleteLayout) -> Part2RawCodestreamInfo {
    (layout.0, layout.1, layout.2, layout.3)
}

pub(crate) open spec fn part2_pdf_typed_finish(
    prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    ignored: bool, chosen: Option<u16>, limits: &crate::ResourceLimits, decoded: Part2TrailerReconstructed,
) -> Result<Part2PdfTyped, crate::DecodeError> {
    let source = part2_decoder_input_from_raw(parsed);
    let selected = part2_present_tile_requested(chosen, requested);
    match part2_typed_decode_finish(part2_pdf_effective_input(prepared).len() as usize, source, Some(selected), limits, decoded.0) {
        Err(error) => Err(error),
        Ok(image) => {
            let mapped = match prepared.file {
                None => Ok(image),
                Some(file) => part2_apply_output_header(image, part2_raw_associated_header(file.header).0,
                    crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
            };
            match mapped {
                Err(error) => Err(error),
                Ok(image) => match part2_present_tile_report(crate::codestream::selection_geometry_view(&source.size),
                    requested, chosen, image.1.len() as usize, limits) {
                    Err(error) => Err(error),
                    Ok(report) => Ok((image, part2_pdf_finish_recovery(prepared, ignored, chosen,
                        decoded.1.discarded_tile_trailer_bytes, report.full_canvas_sample_bytes))),
                },
            }
        },
    }
}

pub(crate) open spec fn part2_pdf_reconstructed_finish(
    prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    ignored: bool, chosen: Option<u16>, limits: &crate::ResourceLimits, decoded: Part2TrailerReconstructed,
) -> Result<Part2PdfReconstructed, crate::DecodeError> {
    let source = part2_decoder_input_from_raw(parsed);
    match part2_reconstructed_decode_finish(part2_pdf_effective_input(prepared).len() as usize, source, decoded.0) {
        Err(error) => Err(error),
        Ok(image) => {
            let mapped = match prepared.file {
                None => Ok(image), Some(file) => part2_jp2_reconstructed_file_output(file, image),
            };
            match mapped {
                Err(error) => Err(error),
                Ok(image) => match part2_present_tile_report(crate::codestream::selection_geometry_view(&source.size),
                    requested, chosen, image.4.len() as usize, limits) {
                    Err(error) => Err(error),
                    Ok(report) => Ok((image, part2_pdf_finish_recovery(prepared, ignored, chosen,
                        decoded.1.discarded_tile_trailer_bytes, report.full_canvas_sample_bytes))),
                },
            }
        },
    }
}

pub(crate) open spec fn part2_pdf_inspect_finish(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, limits: &crate::ResourceLimits,
) -> Result<Part2RawCodestreamInfo, crate::DecodeError> {
    let info = part2_pdf_layout_info(parsed);
    match part2_pdf_validate_layout(input, prepared, info, limits) { Err(error) => Err(error), Ok(_) => Ok(info) }
}

pub(crate) open spec fn part2_pdf_typed_after_parse(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout,
    requested: Part2DecodeSelection, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfTyped> {
    let source = part2_decoder_input_from_raw(parsed);
    match part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) {
        Err(error) => Some((Err(error), events)),
        Ok(ignored) => match part2_present_tile_index(source, requested) {
            Err(error) => Some((Err(error), events)),
            Ok(chosen) => part2_jpip_snapshot_bind(
                part2_trailer_layout_run(source, part2_present_tile_requested(chosen, requested), limits, events),
                |decoded: Part2TrailerReconstructed, rest|
                    Some((part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, decoded), rest))),
        },
    }
}

pub(crate) open spec fn part2_pdf_reconstructed_after_parse(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout,
    requested: Part2DecodeSelection, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfReconstructed> {
    let source = part2_decoder_input_from_raw(parsed);
    match part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) {
        Err(error) => Some((Err(error), events)),
        Ok(ignored) => match part2_present_tile_index(source, requested) {
            Err(error) => Some((Err(error), events)),
            Ok(chosen) => part2_jpip_snapshot_bind(
                part2_trailer_layout_run(source, part2_present_tile_requested(chosen, requested), limits, events),
                |decoded: Part2TrailerReconstructed, rest|
                    Some((part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, decoded), rest))),
        },
    }
}

pub(crate) open spec fn part2_pdf_typed_after_prepare(
    input: Seq<u8>, prepared: Part2PdfPrepared, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfTyped> {
    part2_jpip_snapshot_bind(part2_cold_parse(part2_pdf_effective_input(prepared), limits, 13, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_pdf_typed_after_parse(input, prepared, parsed, requested, limits, rest))
}

pub(crate) open spec fn part2_pdf_reconstructed_after_prepare(
    input: Seq<u8>, prepared: Part2PdfPrepared, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfReconstructed> {
    part2_jpip_snapshot_bind(part2_cold_parse(part2_pdf_effective_input(prepared), limits, 13, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_pdf_reconstructed_after_parse(input, prepared, parsed, requested, limits, rest))
}

pub(crate) open spec fn part2_pdf_inspect_after_prepare(
    input: Seq<u8>, prepared: Part2PdfPrepared, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawCodestreamInfo> {
    part2_jpip_snapshot_bind(part2_cold_parse(part2_pdf_effective_input(prepared), limits, 13, 0, events),
        |parsed: Part1CompleteLayout, rest| Some((part2_pdf_inspect_finish(input, prepared, parsed, limits), rest)))
}

pub(crate) open spec fn part2_pdf_typed_run(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfTyped> {
    part2_jpip_snapshot_bind(part2_pdf_prepare_run(input, limits, events),
        |prepared: Part2PdfPrepared, rest| part2_pdf_typed_after_prepare(input, prepared, requested, limits, rest))
}

pub(crate) open spec fn part2_pdf_reconstructed_run(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PdfReconstructed> {
    part2_jpip_snapshot_bind(part2_pdf_prepare_run(input, limits, events),
        |prepared: Part2PdfPrepared, rest| part2_pdf_reconstructed_after_prepare(input, prepared, requested, limits, rest))
}

pub(crate) open spec fn part2_pdf_inspect_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawCodestreamInfo> {
    part2_jpip_snapshot_bind(part2_pdf_prepare_run(input, limits, events),
        |prepared: Part2PdfPrepared, rest| part2_pdf_inspect_after_prepare(input, prepared, limits, rest))
}

pub closed spec fn part2_pdf_typed_result(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, result: Result<Part2PdfTyped, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_pdf_typed_run(input, requested, limits, events), result)
}

pub closed spec fn part2_pdf_reconstructed_result(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, result: Result<Part2PdfReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_pdf_reconstructed_run(input, requested, limits, events), result)
}

pub closed spec fn part2_pdf_inspect_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Result<Part2RawCodestreamInfo, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_pdf_inspect_run(input, limits, events), result)
}

pub(crate) open spec fn part2_pdf_typed_parsed_value(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PdfTyped, crate::DecodeError> {
    let source = part2_decoder_input_from_raw(parsed);
    match part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) {
        Err(error) => Err(error),
        Ok(ignored) => match part2_present_tile_index(source, requested) {
            Err(error) => Err(error),
            Ok(chosen) => match part2_trailer_layout_value(source, part2_present_tile_requested(chosen, requested), limits) {
                Err(error) => Err(error), Ok(decoded) => part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, decoded),
            },
        },
    }
}

pub(crate) open spec fn part2_pdf_reconstructed_parsed_value(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PdfReconstructed, crate::DecodeError> {
    let source = part2_decoder_input_from_raw(parsed);
    match part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) {
        Err(error) => Err(error),
        Ok(ignored) => match part2_present_tile_index(source, requested) {
            Err(error) => Err(error),
            Ok(chosen) => match part2_trailer_layout_value(source, part2_present_tile_requested(chosen, requested), limits) {
                Err(error) => Err(error), Ok(decoded) => part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, decoded),
            },
        },
    }
}

pub(crate) open spec fn part2_pdf_typed_prepared_value(
    input: Seq<u8>, prepared: Part2PdfPrepared, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PdfTyped, crate::DecodeError> {
    match part1_parse_layout(part2_pdf_effective_input(prepared), limits) {
        Err(error) => Err(error), Ok(parsed) => part2_pdf_typed_parsed_value(input, prepared, parsed, requested, limits),
    }
}

pub(crate) open spec fn part2_pdf_reconstructed_prepared_value(
    input: Seq<u8>, prepared: Part2PdfPrepared, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PdfReconstructed, crate::DecodeError> {
    match part1_parse_layout(part2_pdf_effective_input(prepared), limits) {
        Err(error) => Err(error), Ok(parsed) => part2_pdf_reconstructed_parsed_value(input, prepared, parsed, requested, limits),
    }
}

pub(crate) open spec fn part2_pdf_inspect_prepared_value(
    input: Seq<u8>, prepared: Part2PdfPrepared, limits: &crate::ResourceLimits,
) -> Result<Part2RawCodestreamInfo, crate::DecodeError> {
    match part1_parse_layout(part2_pdf_effective_input(prepared), limits) {
        Err(error) => Err(error), Ok(parsed) => part2_pdf_inspect_finish(input, prepared, parsed, limits),
    }
}

pub closed spec fn part2_pdf_typed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PdfTyped, crate::DecodeError> {
    match part2_pdf_prepare_value(input, limits) {
        Err(error) => Err(error), Ok(prepared) => part2_pdf_typed_prepared_value(input, prepared, requested, limits),
    }
}

pub closed spec fn part2_pdf_reconstructed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PdfReconstructed, crate::DecodeError> {
    match part2_pdf_prepare_value(input, limits) {
        Err(error) => Err(error), Ok(prepared) => part2_pdf_reconstructed_prepared_value(input, prepared, requested, limits),
    }
}

pub closed spec fn part2_pdf_inspect_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part2RawCodestreamInfo, crate::DecodeError> {
    match part2_pdf_prepare_value(input, limits) {
        Err(error) => Err(error), Ok(prepared) => part2_pdf_inspect_prepared_value(input, prepared, limits),
    }
}

pub(crate) proof fn part2_pdf_value_unfold(input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits)
    ensures part2_pdf_typed_value(input, requested, limits) == match part2_pdf_prepare_value(input, limits) {
        Err(error) => Err(error), Ok(prepared) => part2_pdf_typed_prepared_value(input, prepared, requested, limits),
    },
        part2_pdf_reconstructed_value(input, requested, limits) == match part2_pdf_prepare_value(input, limits) {
            Err(error) => Err(error), Ok(prepared) => part2_pdf_reconstructed_prepared_value(input, prepared, requested, limits),
        },
        part2_pdf_inspect_value(input, limits) == match part2_pdf_prepare_value(input, limits) {
            Err(error) => Err(error), Ok(prepared) => part2_pdf_inspect_prepared_value(input, prepared, limits),
        },
{}

pub(crate) proof fn part2_pdf_after_parse_decoded_actual(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    ignored: bool, chosen: Option<u16>, limits: &crate::ResourceLimits,
    decoded: Result<Part2TrailerReconstructed, crate::DecodeError>,
)
    requires part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) == Ok(ignored),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Ok(chosen),
        part2_trailer_layout_result(part2_decoder_input_from_raw(parsed), part2_present_tile_requested(chosen, requested), limits, decoded),
    ensures part2_cold_framed(
        |events| part2_pdf_typed_after_parse(input, prepared, parsed, requested, limits, events),
        match decoded { Err(error) => Err(error), Ok(value) => part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, value) }),
        part2_cold_framed(
            |events| part2_pdf_reconstructed_after_parse(input, prepared, parsed, requested, limits, events),
            match decoded { Err(error) => Err(error), Ok(value) => part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, value) }),
{
    let source = part2_decoder_input_from_raw(parsed);
    let selected = part2_present_tile_requested(chosen, requested);
    if let Ok(value) = decoded {
        part2_cold_pure(part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, value));
        part2_cold_pure(part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, value));
    }
    part2_cold_bind(|events| part2_trailer_layout_run(source, selected, limits, events),
        |value: Part2TrailerReconstructed, rest| Some((part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, value), rest)),
        decoded, match decoded { Err(error) => Err(error), Ok(value) => part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, value) });
    part2_cold_bind(|events| part2_trailer_layout_run(source, selected, limits, events),
        |value: Part2TrailerReconstructed, rest| Some((part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, value), rest)),
        decoded, match decoded { Err(error) => Err(error), Ok(value) => part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, value) });
}

pub(crate) proof fn part2_pdf_after_parse_normal(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_cold_framed(|events| part2_pdf_typed_after_parse(input, prepared, parsed, requested, limits, events),
        part2_pdf_typed_parsed_value(input, prepared, parsed, requested, limits)),
        part2_cold_framed(|events| part2_pdf_reconstructed_after_parse(input, prepared, parsed, requested, limits, events),
            part2_pdf_reconstructed_parsed_value(input, prepared, parsed, requested, limits)),
{
    match part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) {
        Err(error) => { part2_cold_pure::<Part2PdfTyped>(Err(error)); part2_cold_pure::<Part2PdfReconstructed>(Err(error)); },
        Ok(ignored) => match part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) {
            Err(error) => { part2_cold_pure::<Part2PdfTyped>(Err(error)); part2_cold_pure::<Part2PdfReconstructed>(Err(error)); },
            Ok(chosen) => {
                let source = part2_decoder_input_from_raw(parsed);
                let selected = part2_present_tile_requested(chosen, requested);
                part2_trailer_layout_normal(source, selected, limits);
                part2_pdf_after_parse_decoded_actual(input, prepared, parsed, requested, ignored, chosen, limits,
                    part2_trailer_layout_value(source, selected, limits));
            },
        },
    }
}

pub(crate) proof fn part2_pdf_after_prepare_normal(
    input: Seq<u8>, prepared: Part2PdfPrepared, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_cold_framed(|events| part2_pdf_typed_after_prepare(input, prepared, requested, limits, events),
        part2_pdf_typed_prepared_value(input, prepared, requested, limits)),
        part2_cold_framed(|events| part2_pdf_reconstructed_after_prepare(input, prepared, requested, limits, events),
            part2_pdf_reconstructed_prepared_value(input, prepared, requested, limits)),
        part2_cold_framed(|events| part2_pdf_inspect_after_prepare(input, prepared, limits, events),
            part2_pdf_inspect_prepared_value(input, prepared, limits)),
{
    let effective = part2_pdf_effective_input(prepared);
    let parsed = part1_parse_layout(effective, limits);
    part1_parse_layout_cold_normal(effective, limits);
    part2_cold_parse_actual(effective, limits, 13, 0, parsed);
    if let Ok(value) = parsed {
        part2_pdf_after_parse_normal(input, prepared, value, requested, limits);
        part2_decode_eta(|events| part2_pdf_typed_after_parse(input, prepared, value, requested, limits, events),
            part2_pdf_typed_parsed_value(input, prepared, value, requested, limits));
        part2_decode_eta(|events| part2_pdf_reconstructed_after_parse(input, prepared, value, requested, limits, events),
            part2_pdf_reconstructed_parsed_value(input, prepared, value, requested, limits));
        part2_cold_pure(part2_pdf_inspect_finish(input, prepared, value, limits));
    }
    part2_cold_bind(|events| part2_cold_parse(effective, limits, 13, 0, events),
        |value: Part1CompleteLayout, rest| part2_pdf_typed_after_parse(input, prepared, value, requested, limits, rest),
        parsed, part2_pdf_typed_prepared_value(input, prepared, requested, limits));
    part2_cold_bind(|events| part2_cold_parse(effective, limits, 13, 0, events),
        |value: Part1CompleteLayout, rest| part2_pdf_reconstructed_after_parse(input, prepared, value, requested, limits, rest),
        parsed, part2_pdf_reconstructed_prepared_value(input, prepared, requested, limits));
    part2_cold_bind(|events| part2_cold_parse(effective, limits, 13, 0, events),
        |value: Part1CompleteLayout, rest| Some((part2_pdf_inspect_finish(input, prepared, value, limits), rest)),
        parsed, part2_pdf_inspect_prepared_value(input, prepared, limits));
}

pub(crate) proof fn part2_pdf_normal(input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits)
    ensures part2_pdf_typed_result(input, requested, limits, part2_pdf_typed_value(input, requested, limits)),
        part2_pdf_reconstructed_result(input, requested, limits, part2_pdf_reconstructed_value(input, requested, limits)),
        part2_pdf_inspect_result(input, limits, part2_pdf_inspect_value(input, limits)),
{
    reveal(part2_pdf_typed_result); reveal(part2_pdf_reconstructed_result); reveal(part2_pdf_inspect_result);
    part2_pdf_value_unfold(input, requested, limits);
    part2_pdf_prepare_normal(input, limits);
    let prepared = part2_pdf_prepare_value(input, limits);
    if let Ok(value) = prepared {
        part2_pdf_after_prepare_normal(input, value, requested, limits);
        part2_decode_eta(|events| part2_pdf_typed_after_prepare(input, value, requested, limits, events),
            part2_pdf_typed_prepared_value(input, value, requested, limits));
        part2_decode_eta(|events| part2_pdf_reconstructed_after_prepare(input, value, requested, limits, events),
            part2_pdf_reconstructed_prepared_value(input, value, requested, limits));
        part2_decode_eta(|events| part2_pdf_inspect_after_prepare(input, value, limits, events),
            part2_pdf_inspect_prepared_value(input, value, limits));
    }
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_typed_after_prepare(input, value, requested, limits, rest),
        prepared, part2_pdf_typed_value(input, requested, limits));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_reconstructed_after_prepare(input, value, requested, limits, rest),
        prepared, part2_pdf_reconstructed_value(input, requested, limits));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_inspect_after_prepare(input, value, limits, rest),
        prepared, part2_pdf_inspect_value(input, limits));
}

pub(crate) proof fn part2_pdf_prepare_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_pdf_prepare_result(input, limits, Err(error)),
    ensures part2_pdf_typed_result(input, requested, limits, Err(error)),
        part2_pdf_reconstructed_result(input, requested, limits, Err(error)), part2_pdf_inspect_result(input, limits, Err(error)),
{
    reveal(part2_pdf_typed_result); reveal(part2_pdf_reconstructed_result); reveal(part2_pdf_inspect_result);
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_typed_after_prepare(input, value, requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_reconstructed_after_prepare(input, value, requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_inspect_after_prepare(input, value, limits, rest), Err(error), Err(error));
}

pub(crate) proof fn part2_pdf_parse_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, prepared: Part2PdfPrepared, error: crate::DecodeError,
)
    requires part2_pdf_prepare_result(input, limits, Ok(prepared)),
        part1_parse_layout_cold_result(part2_pdf_effective_input(prepared), limits, Err(error)),
    ensures part2_pdf_typed_result(input, requested, limits, Err(error)),
        part2_pdf_reconstructed_result(input, requested, limits, Err(error)), part2_pdf_inspect_result(input, limits, Err(error)),
{
    reveal(part2_pdf_typed_result); reveal(part2_pdf_reconstructed_result); reveal(part2_pdf_inspect_result);
    let effective = part2_pdf_effective_input(prepared);
    part2_cold_parse_actual(effective, limits, 13, 0, Err(error));
    part2_cold_bind(|events| part2_cold_parse(effective, limits, 13, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_pdf_typed_after_parse(input, prepared, parsed, requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_cold_parse(effective, limits, 13, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_pdf_reconstructed_after_parse(input, prepared, parsed, requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_cold_parse(effective, limits, 13, 0, events),
        |parsed: Part1CompleteLayout, rest| Some((part2_pdf_inspect_finish(input, prepared, parsed, limits), rest)), Err(error), Err(error));
    part2_decode_eta(|events| part2_pdf_typed_after_prepare(input, prepared, requested, limits, events), Err(error));
    part2_decode_eta(|events| part2_pdf_reconstructed_after_prepare(input, prepared, requested, limits, events), Err(error));
    part2_decode_eta(|events| part2_pdf_inspect_after_prepare(input, prepared, limits, events), Err(error));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_typed_after_prepare(input, value, requested, limits, rest), Ok(prepared), Err(error));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_reconstructed_after_prepare(input, value, requested, limits, rest), Ok(prepared), Err(error));
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_inspect_after_prepare(input, value, limits, rest), Ok(prepared), Err(error));
}

pub(crate) proof fn part2_pdf_decoded_actual(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    ignored: bool, chosen: Option<u16>, limits: &crate::ResourceLimits, decoded: Result<Part2TrailerReconstructed, crate::DecodeError>,
)
    requires part2_pdf_prepare_result(input, limits, Ok(prepared)),
        part1_parse_layout_cold_result(part2_pdf_effective_input(prepared), limits, Ok(parsed)),
        part2_pdf_validate_layout(input, prepared, part2_pdf_layout_info(parsed), limits) == Ok(ignored),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Ok(chosen),
        part2_trailer_layout_result(part2_decoder_input_from_raw(parsed), part2_present_tile_requested(chosen, requested), limits, decoded),
    ensures part2_pdf_typed_result(input, requested, limits, match decoded {
        Err(error) => Err(error), Ok(value) => part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, value),
    }),
        part2_pdf_reconstructed_result(input, requested, limits, match decoded {
            Err(error) => Err(error), Ok(value) => part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, value),
        }),
{
    reveal(part2_pdf_typed_result); reveal(part2_pdf_reconstructed_result);
    part2_pdf_after_parse_decoded_actual(input, prepared, parsed, requested, ignored, chosen, limits, decoded);
    let typed = match decoded { Err(error) => Err(error), Ok(value) => part2_pdf_typed_finish(prepared, parsed, requested, ignored, chosen, limits, value) };
    let wide = match decoded { Err(error) => Err(error), Ok(value) => part2_pdf_reconstructed_finish(prepared, parsed, requested, ignored, chosen, limits, value) };
    part2_decode_eta(|events| part2_pdf_typed_after_parse(input, prepared, parsed, requested, limits, events), typed);
    part2_decode_eta(|events| part2_pdf_reconstructed_after_parse(input, prepared, parsed, requested, limits, events), wide);
    part2_cold_parse_actual(part2_pdf_effective_input(prepared), limits, 13, 0, Ok(parsed));
    part2_cold_bind(|events| part2_cold_parse(part2_pdf_effective_input(prepared), limits, 13, 0, events),
        |value: Part1CompleteLayout, rest| part2_pdf_typed_after_parse(input, prepared, value, requested, limits, rest), Ok(parsed), typed);
    part2_cold_bind(|events| part2_cold_parse(part2_pdf_effective_input(prepared), limits, 13, 0, events),
        |value: Part1CompleteLayout, rest| part2_pdf_reconstructed_after_parse(input, prepared, value, requested, limits, rest), Ok(parsed), wide);
    part2_decode_eta(|events| part2_pdf_typed_after_prepare(input, prepared, requested, limits, events), typed);
    part2_decode_eta(|events| part2_pdf_reconstructed_after_prepare(input, prepared, requested, limits, events), wide);
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_typed_after_prepare(input, value, requested, limits, rest), Ok(prepared), typed);
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_reconstructed_after_prepare(input, value, requested, limits, rest), Ok(prepared), wide);
}

pub(crate) proof fn part2_pdf_inspect_actual(
    input: Seq<u8>, prepared: Part2PdfPrepared, parsed: Part1CompleteLayout, limits: &crate::ResourceLimits,
)
    requires part2_pdf_prepare_result(input, limits, Ok(prepared)),
        part1_parse_layout_cold_result(part2_pdf_effective_input(prepared), limits, Ok(parsed)),
    ensures part2_pdf_inspect_result(input, limits, part2_pdf_inspect_finish(input, prepared, parsed, limits)),
{
    reveal(part2_pdf_inspect_result);
    let result = part2_pdf_inspect_finish(input, prepared, parsed, limits);
    part2_cold_parse_actual(part2_pdf_effective_input(prepared), limits, 13, 0, Ok(parsed));
    part2_cold_pure(result);
    part2_cold_bind(|events| part2_cold_parse(part2_pdf_effective_input(prepared), limits, 13, 0, events),
        |value: Part1CompleteLayout, rest| Some((part2_pdf_inspect_finish(input, prepared, value, limits), rest)), Ok(parsed), result);
    part2_decode_eta(|events| part2_pdf_inspect_after_prepare(input, prepared, limits, events), result);
    part2_cold_bind(|events| part2_pdf_prepare_run(input, limits, events),
        |value: Part2PdfPrepared, rest| part2_pdf_inspect_after_prepare(input, value, limits, rest), Ok(prepared), result);
}
}
