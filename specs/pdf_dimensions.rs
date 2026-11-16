//! Explicit JP2 dimension recovery, retaining source component declarations.
use super::*;
verus! {
pub(crate) proof fn part2_dimension_box_progress(state: Part2BoxReaderState)
    ensures match part2_box_reader_next_ref(state).0 {
        Some(Ok(_)) => part2_box_reader_next_ref(state).1.input == state.input
            && part2_box_reader_next_ref(state).1.position > state.position
            && part2_box_reader_next_ref(state).1.position <= state.input.len(),
        _ => true,
    },
{
    reveal(part2_box_reader_next);
    reveal(part2_box_reader_after_work);
    reveal(part2_box_reader_after_header);
}

#[verifier::opaque]
pub(crate) open spec fn part2_dimension_find_box_from(
    state: Part2BoxReaderState, wanted: crate::jp2::BoxType,
) -> Result<Option<Part2BoxReference>, crate::DecodeError>
    decreases state.input.len() - state.position,
{
    let next = part2_box_reader_next_ref(state);
    match next.0 {
        None => Ok(None),
        Some(Err(error)) => Err(error),
        Some(Ok(item)) => if item.0.0 == wanted { Ok(Some(item)) }
            else if next.1.input == state.input && next.1.position > state.position
                && next.1.position <= state.input.len() {
                part2_dimension_find_box_from(next.1, wanted)
            } else { Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow)) },
    }
}

pub(crate) open spec fn part2_dimension_find_box(
    input: Seq<u8>, wanted: crate::jp2::BoxType, limits: &crate::ResourceLimits,
) -> Result<Option<Part2BoxReference>, crate::DecodeError> {
    match part2_box_reader_from_input(input, *limits) {
        Err(error) => Err(error),
        Ok(state) => part2_dimension_find_box_from(state, wanted),
    }
}

pub(crate) open spec fn part2_dimension_mismatch(offset: u64) -> crate::DecodeError {
    part2_container_error(offset, crate::MalformedKind::ContainerCodestreamMismatch)
}

#[verifier::opaque]
pub(crate) open spec fn part2_dimension_precision_from(
    bytes: Seq<u8>, size: Part1ParsedImageSize, offset: u64, index: nat,
) -> Result<(), crate::DecodeError>
    decreases bytes.len() - index,
{
    if index >= bytes.len() { Ok(()) }
    else {
        match part1_image_size_component(size.components, size.infos, index as u16) {
            Err(error) => Err(error),
            Ok(component) => if (bytes[index as int] % 128) as u16 + 1 != component.precision as u16
                || (bytes[index as int] >= 128) != component.signed {
                Err(part2_dimension_mismatch(offset))
            } else { part2_dimension_precision_from(bytes, size, offset, index + 1) },
        }
    }
}

pub(crate) open spec fn part2_dimension_precision(
    bytes: Seq<u8>, size: Part1ParsedImageSize, offset: u64,
) -> Result<(), crate::DecodeError> {
    if bytes.len() != size.components { Err(part2_dimension_mismatch(offset)) }
    else { part2_dimension_precision_from(bytes, size, offset, 0) }
}

pub(crate) open spec fn part2_dimension_header(
    file: Part2RawJp2File,
) -> Result<Part2RawJp2Header, crate::DecodeError> {
    if file.streams.len() == 0 {
        Err(crate::DecodeError::CodestreamIndexOutOfRange {
            index: 0, codestreams: file.streams.len() as usize,
        })
    } else {
        match file.streams[0].2 {
            None => Ok(file.header),
            Some(association) => match association.2 {
                Some(header) => Ok(header),
                None => Err(crate::DecodeError::UnsupportedFeature {
                    feature: "unparsed JPX header in dimension recovery",
                }),
            },
        }
    }
}

pub(crate) open spec fn part2_dimension_depth_bytes(
    input: Seq<u8>, file: Part2RawJp2File, limits: &crate::ResourceLimits,
) -> Result<Seq<u8>, crate::DecodeError> {
    let offset = file.streams[0].0.1;
    match part2_dimension_find_box(input, crate::jp2::BoxType::JP2_HEADER, limits) {
        Err(error) => Err(error),
        Ok(None) => Err(part2_dimension_mismatch(offset)),
        Ok(Some(main)) => match part2_dimension_find_box(main.1, crate::jp2::BoxType::BITS_PER_COMPONENT, limits) {
            Err(error) => Err(error),
            Ok(inherited) => {
                let selected = match file.streams[0].2 {
                    None => Ok(inherited),
                    Some(association) => match part2_dimension_find_box(
                        association.1, crate::jp2::BoxType::BITS_PER_COMPONENT, limits) {
                        Err(error) => Err(error),
                        Ok(Some(found)) => Ok(Some(found)),
                        Ok(None) => Ok(inherited),
                    },
                };
                match selected {
                    Err(error) => Err(error),
                    Ok(None) => Err(part2_dimension_mismatch(offset)),
                    Ok(Some(value)) => Ok(value.1),
                }
            },
        },
    }
}

pub(crate) open spec fn part2_dimension_report(
    header: Part2RawJp2Header, size: Part1ParsedImageSize,
) -> crate::decode::Jp2DimensionRecoveryReport {
    crate::decode::Jp2DimensionRecoveryReport {
        ignored_container_dimensions: header.image.width != size.geometry.0
            || header.image.height != size.geometry.1,
        header_width: header.image.width, header_height: header.image.height,
        width: size.geometry.0, height: size.geometry.1,
        x_origin: size.geometry.2, y_origin: size.geometry.3,
    }
}

pub(crate) open spec fn part2_dimension_validate_header(
    input: Seq<u8>, file: Part2RawJp2File, info: Part2RawCodestreamInfo,
    limits: &crate::ResourceLimits,
) -> Result<crate::decode::Jp2DimensionRecoveryReport, crate::DecodeError> {
    match part2_dimension_header(file) {
        Err(error) => Err(error),
        Ok(header) => {
            let size = info.0.image_size;
            let corrected = crate::jp2::ImageHeader {
                width: size.geometry.0, height: size.geometry.1, ..header.image
            };
            match part2_validate_selected_header(corrected,
                size.geometry.0, size.geometry.1, size.components,
                size.uniform_bit_depth, size.uniform_signed, file.streams[0].0.1) {
                Err(error) => Err(error),
                Ok(()) => {
                    let checked = if matches!(header.image.bit_depth, crate::jp2::ComponentBitDepth::Variable) {
                        match part2_dimension_depth_bytes(input, file, limits) {
                            Err(error) => Err(error),
                            Ok(bytes) => part2_dimension_precision(bytes, size, file.streams[0].0.1),
                        }
                    } else { Ok(()) };
                    match checked {
                        Err(error) => Err(error),
                        Ok(()) => Ok(part2_dimension_report(header, size)),
                    }
                },
            }
        },
    }
}

pub(crate) type Part2DimensionInspection =
    (Part2RawJp2File, Part2RawCodestreamInfo, crate::decode::Jp2DimensionRecoveryReport);

pub(crate) open spec fn part2_dimension_inspection_finish(
    input: Seq<u8>, file: Part2RawJp2File, info: Part2RawCodestreamInfo,
    limits: &crate::ResourceLimits,
) -> Result<Part2DimensionInspection, crate::DecodeError> {
    if part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND)
        != part1_profile_optional_advertises_ht(info.1.2) {
        Err(part2_container_error(file.streams[0].0.1, crate::MalformedKind::InvalidProfile))
    } else {
        match part2_dimension_validate_header(input, file, info, limits) {
            Err(error) => Err(error),
            Ok(report) => match part2_validate_jp2_display_profile(file) {
                Err(error) => Err(error),
                Ok(()) => Ok((file, info, report)),
            },
        }
    }
}

pub(crate) open spec fn part2_dimension_inspection_after_file(
    input: Seq<u8>, file: Part2RawJp2File, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2DimensionInspection> {
    if file.streams.len() == 0 {
        Some((Err(crate::DecodeError::CodestreamIndexOutOfRange {
            index: 0, codestreams: file.streams.len() as usize,
        }), events))
    } else {
        part2_jpip_snapshot_bind(part2_cold_info(file.streams[0].1, limits, 9, 0, events),
            |info: Part2RawCodestreamInfo, rest|
                Some((part2_dimension_inspection_finish(input, file, info, limits), rest)))
    }
}

pub(crate) open spec fn part2_dimension_inspection_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2DimensionInspection> {
    part2_jpip_snapshot_bind(part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_dimension_inspection_after_file(input, file, limits, rest))
}

pub closed spec fn part2_dimension_inspection_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part2DimensionInspection, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_dimension_inspection_run(input, limits, events), result)
}

pub closed spec fn part2_dimension_inspection_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part2DimensionInspection, crate::DecodeError> {
    match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => if file.streams.len() == 0 {
            Err(crate::DecodeError::CodestreamIndexOutOfRange {
                index: 0, codestreams: file.streams.len() as usize,
            })
        } else {
            match part1_parse_info(file.streams[0].1, limits) {
                Err(error) => Err(error),
                Ok(info) => part2_dimension_inspection_finish(input, file, info, limits),
            }
        },
    }
}

pub(crate) proof fn part2_dimension_inspection_value_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_dimension_inspection_value(input, limits) ==
        match part2_parse_container(input, *limits) {
            Err(error) => Err(error),
            Ok(file) => if file.streams.len() == 0 {
                Err(crate::DecodeError::CodestreamIndexOutOfRange {
                    index: 0, codestreams: file.streams.len() as usize,
                })
            } else {
                match part1_parse_info(file.streams[0].1, limits) {
                    Err(error) => Err(error),
                    Ok(info) => part2_dimension_inspection_finish(input, file, info, limits),
                }
            },
        },
{}

pub(crate) proof fn part2_dimension_inspection_pure_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires match part2_parse_container(input, *limits) {
        Err(found) => error == found,
        Ok(file) => file.streams.len() == 0 && error == crate::DecodeError::CodestreamIndexOutOfRange {
            index: 0, codestreams: file.streams.len() as usize,
        },
    },
    ensures part2_dimension_inspection_result(input, limits, Err(error)),
{
    reveal(part2_dimension_inspection_result);
    part2_cold_pure::<Part2DimensionInspection>(Err(error));
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, part2_parse_container(input, *limits));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_dimension_inspection_after_file(input, file, limits, rest),
        part2_parse_container(input, *limits), Err(error));
}

pub(crate) proof fn part2_dimension_inspection_container_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_parse_container_cold_result(input, *limits, Err(error)),
    ensures part2_dimension_inspection_result(input, limits, Err(error)),
{
    reveal(part2_dimension_inspection_result);
    part2_parse_container_cold_frames(input, *limits, Err(error));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_dimension_inspection_after_file(input, file, limits, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_dimension_inspection_info_join(
    input: Seq<u8>, file: Part2RawJp2File, limits: &crate::ResourceLimits,
    parsed: Result<Part2RawCodestreamInfo, crate::DecodeError>,
)
    requires part2_parse_container(input, *limits) == Ok(file), file.streams.len() > 0,
        part2_cold_framed(|events| part2_cold_info(file.streams[0].1, limits, 9, 0, events), parsed),
    ensures part2_dimension_inspection_result(input, limits, match parsed {
        Err(error) => Err(error), Ok(info) => part2_dimension_inspection_finish(input, file, info, limits),
    }),
{
    reveal(part2_dimension_inspection_result);
    let result = match parsed {
        Err(error) => Err(error), Ok(info) => part2_dimension_inspection_finish(input, file, info, limits),
    };
    if let Ok(info) = parsed { part2_cold_pure(part2_dimension_inspection_finish(input, file, info, limits)); }
    part2_cold_bind(
        |events| part2_cold_info(file.streams[0].1, limits, 9, 0, events),
        |info: Part2RawCodestreamInfo, rest|
            Some((part2_dimension_inspection_finish(input, file, info, limits), rest)),
        parsed, result);
    part2_cold_framed_extensional(
        |events| part2_jpip_snapshot_bind(part2_cold_info(file.streams[0].1, limits, 9, 0, events),
            |info: Part2RawCodestreamInfo, rest|
                Some((part2_dimension_inspection_finish(input, file, info, limits), rest))),
        |events| part2_dimension_inspection_after_file(input, file, limits, events), result);
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, Ok(file));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |parsed_file, rest| part2_dimension_inspection_after_file(input, parsed_file, limits, rest),
        Ok(file), result);
}

pub(crate) proof fn part2_dimension_inspection_info_actual(
    input: Seq<u8>, file: Part2RawJp2File, limits: &crate::ResourceLimits,
    parsed: Result<Part2RawCodestreamInfo, crate::DecodeError>,
)
    requires part2_parse_container(input, *limits) == Ok(file), file.streams.len() > 0,
        part1_parse_info_cold_result(file.streams[0].1, limits, parsed),
    ensures part2_dimension_inspection_result(input, limits, match parsed {
        Err(error) => Err(error), Ok(info) => part2_dimension_inspection_finish(input, file, info, limits),
    }),
{
    part2_cold_info_actual(file.streams[0].1, limits, 9, 0, parsed);
    part2_dimension_inspection_info_join(input, file, limits, parsed);
}

pub(crate) proof fn part2_dimension_inspection_normal(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_dimension_inspection_result(input, limits, part2_dimension_inspection_value(input, limits)),
{
    part2_dimension_inspection_value_unfold(input, limits);
    match part2_parse_container(input, *limits) {
        Err(error) => { part2_dimension_inspection_pure_error(input, limits, error); },
        Ok(file) => if file.streams.len() == 0 {
            part2_dimension_inspection_pure_error(input, limits,
                crate::DecodeError::CodestreamIndexOutOfRange {
                    index: 0, codestreams: file.streams.len() as usize,
                });
        } else {
            part2_cold_info_normal(file.streams[0].1, limits, 9, 0);
            part2_dimension_inspection_info_join(input, file, limits, part1_parse_info(file.streams[0].1, limits));
        },
    }
}

pub(crate) proof fn part2_dimension_inspection_frames(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part2DimensionInspection, crate::DecodeError>,
)
    requires part2_dimension_inspection_result(input, limits, result),
    ensures part2_cold_framed(|events| part2_dimension_inspection_run(input, limits, events), result),
{
    reveal(part2_dimension_inspection_result);
}

pub(crate) type Part2DimensionTyped =
    (Part1DecodedTypedImage, crate::decode::Jp2DimensionRecoveryReport);
pub(crate) type Part2DimensionReconstructed =
    (Part1DecodedImageModel, crate::decode::Jp2DimensionRecoveryReport);

pub(crate) open spec fn part2_dimension_typed_finish(
    inspected: Part2DimensionInspection, image: Part1DecodedTypedImage, limits: &crate::ResourceLimits,
) -> Result<Part2DimensionTyped, crate::DecodeError> {
    match part2_single_output((inspected.0, seq![inspected.1]), limits, image) {
        Err(error) => Err(error), Ok(value) => Ok((value, inspected.2)),
    }
}

pub(crate) open spec fn part2_dimension_reconstructed_finish(
    inspected: Part2DimensionInspection, image: Part1DecodedImageModel,
) -> Result<Part2DimensionReconstructed, crate::DecodeError> {
    match part2_jp2_reconstructed_output((inspected.0, seq![inspected.1]), image) {
        Err(error) => Err(error), Ok(value) => Ok((value, inspected.2)),
    }
}

pub(crate) open spec fn part2_dimension_typed_after_inspection(
    inspected: Part2DimensionInspection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2DimensionTyped> {
    part2_jpip_snapshot_bind(part2_decode_raw_cold_run(inspected.0.streams[0].1, limits, None, events),
        |image: Part1DecodedTypedImage, rest|
            Some((part2_dimension_typed_finish(inspected, image, limits), rest)))
}

pub(crate) open spec fn part2_dimension_reconstructed_after_inspection(
    inspected: Part2DimensionInspection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2DimensionReconstructed> {
    part2_jpip_snapshot_bind(part2_decode_reconstructed_cold_run(inspected.0.streams[0].1, limits, events),
        |image: Part1DecodedImageModel, rest|
            Some((part2_dimension_reconstructed_finish(inspected, image), rest)))
}

pub(crate) open spec fn part2_dimension_typed_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2DimensionTyped> {
    part2_jpip_snapshot_bind(part2_dimension_inspection_run(input, limits, events),
        |inspected: Part2DimensionInspection, rest| part2_dimension_typed_after_inspection(inspected, limits, rest))
}

pub(crate) open spec fn part2_dimension_reconstructed_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2DimensionReconstructed> {
    part2_jpip_snapshot_bind(part2_dimension_inspection_run(input, limits, events),
        |inspected: Part2DimensionInspection, rest| part2_dimension_reconstructed_after_inspection(inspected, limits, rest))
}

pub closed spec fn part2_dimension_typed_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Result<Part2DimensionTyped, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_dimension_typed_run(input, limits, events), result)
}

pub closed spec fn part2_dimension_reconstructed_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Result<Part2DimensionReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_dimension_reconstructed_run(input, limits, events), result)
}

pub closed spec fn part2_dimension_typed_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part2DimensionTyped, crate::DecodeError> {
    match part2_dimension_inspection_value(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_decode_raw_codestream(inspected.0.streams[0].1, limits, None) {
            Err(error) => Err(error), Ok(image) => part2_dimension_typed_finish(inspected, image, limits),
        },
    }
}

pub closed spec fn part2_dimension_reconstructed_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part2DimensionReconstructed, crate::DecodeError> {
    match part2_dimension_inspection_value(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_decode_raw_reconstructed_codestream(inspected.0.streams[0].1, limits) {
            Err(error) => Err(error), Ok(image) => part2_dimension_reconstructed_finish(inspected, image),
        },
    }
}

pub(crate) proof fn part2_dimension_decode_value_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_dimension_typed_value(input, limits) == match part2_dimension_inspection_value(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_decode_raw_codestream(inspected.0.streams[0].1, limits, None) {
            Err(error) => Err(error), Ok(image) => part2_dimension_typed_finish(inspected, image, limits),
        },
    },
    part2_dimension_reconstructed_value(input, limits) == match part2_dimension_inspection_value(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_decode_raw_reconstructed_codestream(inspected.0.streams[0].1, limits) {
            Err(error) => Err(error), Ok(image) => part2_dimension_reconstructed_finish(inspected, image),
        },
    },
{}

pub(crate) proof fn part2_dimension_decode_inspection_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_dimension_inspection_result(input, limits, Err(error)),
    ensures part2_dimension_typed_result(input, limits, Err(error)),
        part2_dimension_reconstructed_result(input, limits, Err(error)),
{
    reveal(part2_dimension_typed_result); reveal(part2_dimension_reconstructed_result);
    part2_dimension_inspection_frames(input, limits, Err(error));
    part2_cold_bind(|events| part2_dimension_inspection_run(input, limits, events),
        |inspected: Part2DimensionInspection, rest| part2_dimension_typed_after_inspection(inspected, limits, rest),
        Err(error), Err(error));
    part2_cold_bind(|events| part2_dimension_inspection_run(input, limits, events),
        |inspected: Part2DimensionInspection, rest| part2_dimension_reconstructed_after_inspection(inspected, limits, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_dimension_typed_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, inspected: Part2DimensionInspection,
    decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_dimension_inspection_result(input, limits, Ok(inspected)), inspected.0.streams.len() > 0,
        part2_decode_raw_cold_result(inspected.0.streams[0].1, limits, None, decoded),
    ensures part2_dimension_typed_result(input, limits, match decoded {
        Err(error) => Err(error), Ok(image) => part2_dimension_typed_finish(inspected, image, limits),
    }),
{
    reveal(part2_dimension_typed_result);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_dimension_typed_finish(inspected, image, limits),
    };
    part2_dimension_inspection_frames(input, limits, Ok(inspected));
    part2_decode_raw_cold_frames(inspected.0.streams[0].1, limits, None, decoded);
    if let Ok(image) = decoded { part2_cold_pure(part2_dimension_typed_finish(inspected, image, limits)); }
    part2_cold_bind(
        |events| part2_decode_raw_cold_run(inspected.0.streams[0].1, limits, None, events),
        |image: Part1DecodedTypedImage, rest| Some((part2_dimension_typed_finish(inspected, image, limits), rest)),
        decoded, result);
    part2_cold_bind(|events| part2_dimension_inspection_run(input, limits, events),
        |value: Part2DimensionInspection, rest| part2_dimension_typed_after_inspection(value, limits, rest),
        Ok(inspected), result);
}

pub(crate) proof fn part2_dimension_reconstructed_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, inspected: Part2DimensionInspection,
    decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part2_dimension_inspection_result(input, limits, Ok(inspected)), inspected.0.streams.len() > 0,
        part2_decode_reconstructed_cold_result(inspected.0.streams[0].1, limits, decoded),
    ensures part2_dimension_reconstructed_result(input, limits, match decoded {
        Err(error) => Err(error), Ok(image) => part2_dimension_reconstructed_finish(inspected, image),
    }),
{
    reveal(part2_dimension_reconstructed_result);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_dimension_reconstructed_finish(inspected, image),
    };
    part2_dimension_inspection_frames(input, limits, Ok(inspected));
    part2_decode_reconstructed_cold_frames(inspected.0.streams[0].1, limits, decoded);
    if let Ok(image) = decoded { part2_cold_pure(part2_dimension_reconstructed_finish(inspected, image)); }
    part2_cold_bind(
        |events| part2_decode_reconstructed_cold_run(inspected.0.streams[0].1, limits, events),
        |image: Part1DecodedImageModel, rest| Some((part2_dimension_reconstructed_finish(inspected, image), rest)),
        decoded, result);
    part2_cold_bind(|events| part2_dimension_inspection_run(input, limits, events),
        |value: Part2DimensionInspection, rest| part2_dimension_reconstructed_after_inspection(value, limits, rest),
        Ok(inspected), result);
}

pub(crate) proof fn part2_dimension_decode_normal(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_dimension_typed_result(input, limits, part2_dimension_typed_value(input, limits)),
        part2_dimension_reconstructed_result(input, limits, part2_dimension_reconstructed_value(input, limits)),
{
    reveal(part2_dimension_typed_result); reveal(part2_dimension_reconstructed_result);
    part2_dimension_decode_value_unfold(input, limits);
    part2_dimension_inspection_normal(input, limits);
    let inspected = part2_dimension_inspection_value(input, limits);
    part2_dimension_inspection_frames(input, limits, inspected);
    if let Ok(value) = inspected {
        let typed = part2_decode_raw_codestream(value.0.streams[0].1, limits, None);
        part2_decode_raw_cold_normal(value.0.streams[0].1, limits, None);
        part2_decode_raw_cold_frames(value.0.streams[0].1, limits, None, typed);
        if let Ok(image) = typed { part2_cold_pure(part2_dimension_typed_finish(value, image, limits)); }
        part2_cold_bind(
            |events| part2_decode_raw_cold_run(value.0.streams[0].1, limits, None, events),
            |image: Part1DecodedTypedImage, rest| Some((part2_dimension_typed_finish(value, image, limits), rest)),
            typed, part2_dimension_typed_value(input, limits));
        let reconstructed = part2_decode_raw_reconstructed_codestream(value.0.streams[0].1, limits);
        part2_decode_reconstructed_cold_normal(value.0.streams[0].1, limits);
        part2_decode_reconstructed_cold_frames(value.0.streams[0].1, limits, reconstructed);
        if let Ok(image) = reconstructed { part2_cold_pure(part2_dimension_reconstructed_finish(value, image)); }
        part2_cold_bind(
            |events| part2_decode_reconstructed_cold_run(value.0.streams[0].1, limits, events),
            |image: Part1DecodedImageModel, rest| Some((part2_dimension_reconstructed_finish(value, image), rest)),
            reconstructed, part2_dimension_reconstructed_value(input, limits));
    }
    part2_cold_bind(|events| part2_dimension_inspection_run(input, limits, events),
        |value: Part2DimensionInspection, rest| part2_dimension_typed_after_inspection(value, limits, rest),
        inspected, part2_dimension_typed_value(input, limits));
    part2_cold_bind(|events| part2_dimension_inspection_run(input, limits, events),
        |value: Part2DimensionInspection, rest| part2_dimension_reconstructed_after_inspection(value, limits, rest),
        inspected, part2_dimension_reconstructed_value(input, limits));
}
}
