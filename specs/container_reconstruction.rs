//! Strict JP2 reconstruction composes actual inspection and raw reconstruction.
use super::*;
verus! {
pub(crate) open spec fn part2_validate_jp2_reconstruction_output(
    header: Part2RawJp2Header,
) -> Result<(), crate::DecodeError> {
    if header.palette.is_some() || header.mappings.len() != 0 || header.definitions.len() != 0 {
        Err(crate::DecodeError::UnsupportedFeature {
            feature: "JP2 output transforms on reconstruction samples",
        })
    } else { Ok(()) }
}

pub(crate) open spec fn part2_jp2_reconstructed_output(
    inspected: Part2RawInspectedContainer, image: Part1DecodedImageModel,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_validate_jp2_reconstruction_output(inspected.0.header) {
        Err(error) => Err(error),
        Ok(()) => match inspected.0.streams[0].2 {
            None => Ok(image),
            Some(association) => match association.2 {
                None => Err(crate::DecodeError::UnsupportedFeature {
                    feature: "unparsed JPX header on reconstruction samples",
                }),
                Some(header) => match part2_validate_jp2_reconstruction_output(header) {
                    Err(error) => Err(error), Ok(()) => Ok(image),
                },
            },
        },
    }
}

pub(crate) open spec fn part2_jp2_reconstructed_after_inspection(
    inspected: Part2RawInspectedContainer, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    match part2_single_profile(inspected, false) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(
            part2_decode_reconstructed_cold_run(inspected.0.streams[0].1, limits, events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_jp2_reconstructed_output(inspected, image), rest))),
    }
}

pub(crate) open spec fn part2_decode_jp2_reconstructed_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_jp2_reconstructed_after_inspection(inspected, limits, rest))
}

pub closed spec fn part2_decode_jp2_reconstructed_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part1DecodedImageModel, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_decode_jp2_reconstructed_run(input, limits, events), result)
}

pub closed spec fn part2_decode_jp2_reconstructed_value(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_single_profile(inspected, false) {
            Err(error) => Err(error),
            Ok(()) => match part2_decode_raw_reconstructed_codestream(inspected.0.streams[0].1, limits) {
                Err(error) => Err(error),
                Ok(image) => part2_jp2_reconstructed_output(inspected, image),
            },
        },
    }
}

pub(crate) proof fn part2_decode_jp2_reconstructed_value_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_decode_jp2_reconstructed_value(input, limits) ==
        match part2_parse_and_inspect_container_mode(input, limits, true) {
            Err(error) => Err(error),
            Ok(inspected) => match part2_single_profile(inspected, false) {
                Err(error) => Err(error),
                Ok(()) => match part2_decode_raw_reconstructed_codestream(inspected.0.streams[0].1, limits) {
                    Err(error) => Err(error),
                    Ok(image) => part2_jp2_reconstructed_output(inspected, image),
                },
            },
        },
{
}

pub(crate) proof fn part2_decode_jp2_reconstructed_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_decode_jp2_reconstructed_result(
        input, limits, part2_decode_jp2_reconstructed_value(input, limits)),
{
    reveal(part2_decode_jp2_reconstructed_result);
    part2_decode_jp2_reconstructed_value_unfold(input, limits);
    let inspected = part2_parse_and_inspect_container_mode(input, limits, true);
    part2_single_inspection_normal(input, limits, false);
    if let Ok(value) = inspected {
        match part2_single_profile(value, false) {
            Err(error) => { part2_cold_pure::<Part1DecodedImageModel>(Err(error)); },
            Ok(()) => {
                let decoded = part2_decode_raw_reconstructed_codestream(value.0.streams[0].1, limits);
                part2_decode_reconstructed_cold_normal(value.0.streams[0].1, limits);
                part2_decode_reconstructed_cold_frames(value.0.streams[0].1, limits, decoded);
                if let Ok(image) = decoded { part2_cold_pure(part2_jp2_reconstructed_output(value, image)); }
                part2_cold_bind(
                    |events| part2_decode_reconstructed_cold_run(value.0.streams[0].1, limits, events),
                    |image: Part1DecodedImageModel, rest|
                        Some((part2_jp2_reconstructed_output(value, image), rest)),
                    decoded, match decoded {
                        Err(error) => Err(error), Ok(image) => part2_jp2_reconstructed_output(value, image),
                    });
            },
        }
    }
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_jp2_reconstructed_after_inspection(value, limits, rest),
        inspected, part2_decode_jp2_reconstructed_value(input, limits));
}

pub(crate) proof fn part2_jp2_reconstructed_inspection_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Err(error)),
    ensures part2_decode_jp2_reconstructed_result(input, limits, Err(error)),
{
    reveal(part2_decode_jp2_reconstructed_result);
    part2_single_inspection_actual(input, limits, false, Err(error));
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_jp2_reconstructed_after_inspection(inspected, limits, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_jp2_reconstructed_profile_error(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Err(error),
    ensures part2_decode_jp2_reconstructed_result(input, limits, Err(error)),
{
    reveal(part2_decode_jp2_reconstructed_result);
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_pure::<Part1DecodedImageModel>(Err(error));
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_jp2_reconstructed_after_inspection(value, limits, rest),
        Ok(inspected), Err(error));
}

pub(crate) proof fn part2_jp2_reconstructed_image_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer,
    decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Ok(()),
        part2_decode_reconstructed_cold_result(inspected.0.streams[0].1, limits, decoded),
    ensures part2_decode_jp2_reconstructed_result(input, limits, match decoded {
        Err(error) => Err(error), Ok(image) => part2_jp2_reconstructed_output(inspected, image),
    }),
{
    reveal(part2_decode_jp2_reconstructed_result);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_jp2_reconstructed_output(inspected, image),
    };
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_decode_reconstructed_cold_frames(inspected.0.streams[0].1, limits, decoded);
    if let Ok(image) = decoded { part2_cold_pure(part2_jp2_reconstructed_output(inspected, image)); }
    part2_cold_bind(
        |events| part2_decode_reconstructed_cold_run(inspected.0.streams[0].1, limits, events),
        |image: Part1DecodedImageModel, rest|
            Some((part2_jp2_reconstructed_output(inspected, image), rest)),
        decoded, result);
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_jp2_reconstructed_after_inspection(value, limits, rest),
        Ok(inspected), result);
}
}
