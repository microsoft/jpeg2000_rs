//! Public raw single-container typed image and actual selection composition.

use super::*;

verus! {

pub(crate) open spec fn part2_single_inspection_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, jph: bool, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawInspectedContainer> {
    if jph { part2_inspect_jph_cold_run(input, limits, events) }
    else { part2_inspection_cold_run(input, limits, true, events) }
}

pub(crate) open spec fn part2_single_profile(
    inspected: Part2RawInspectedContainer, jph: bool,
) -> Result<(), crate::DecodeError> {
    if (jph && inspected.0.streams.len() != 1)
        || (!jph && part2_validate_jp2_display_profile(inspected.0).is_err()) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else { Ok(()) }
}

pub(crate) open spec fn part2_single_output(
    inspected: Part2RawInspectedContainer, limits: &crate::ResourceLimits, image: Part1DecodedTypedImage,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    part2_apply_output_header(image, part2_raw_associated_header(inspected.0.header).0,
        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits))
}

pub(crate) open spec fn part2_single_after_inspection(
    inspected: Part2RawInspectedContainer, limits: &crate::ResourceLimits,
    selection: Option<&crate::DecodeSelection>, jph: bool, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedTypedImage> {
    match part2_single_profile(inspected, jph) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(
            part2_decode_raw_cold_run(inspected.0.streams[0].1, limits, selection, events),
            |image: Part1DecodedTypedImage, rest| Some((part2_single_output(inspected, limits, image), rest))),
    }
}

pub(crate) open spec fn part2_decode_single_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: Option<&crate::DecodeSelection>,
    jph: bool, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, jph, events),
        |inspected: Part2RawInspectedContainer, rest| part2_single_after_inspection(inspected, limits, selection, jph, rest))
}

pub closed spec fn part2_decode_single_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: Option<&crate::DecodeSelection>, jph: bool,
    result: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_decode_single_cold_run(input, limits, selection, jph, events), result)
}

pub(crate) proof fn part2_single_inspection_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, jph: bool,
    inspected: Result<Part2RawInspectedContainer, crate::DecodeError>,
)
    requires if jph { part2_inspect_jph_cold_result(input, limits, inspected) }
        else { part2_inspection_cold_result(input, limits, true, inspected) },
    ensures part2_cold_framed(|events| part2_single_inspection_run(input, limits, jph, events), inspected),
{
    if jph {
        part2_inspect_jph_cold_frames(input, limits, inspected);
        part2_cold_framed_extensional(
            |events| part2_inspect_jph_cold_run(input, limits, events),
            |events| part2_single_inspection_run(input, limits, jph, events), inspected);
    } else {
        part2_inspection_cold_frames(input, limits, true, inspected);
        part2_cold_framed_extensional(
            |events| part2_inspection_cold_run(input, limits, true, events),
            |events| part2_single_inspection_run(input, limits, jph, events), inspected);
    }
}

pub(crate) proof fn part2_single_inspection_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, jph: bool,
)
    ensures part2_cold_framed(|events| part2_single_inspection_run(input, limits, jph, events),
        if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) }),
{
    let inspected = if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) };
    if jph {
        part2_inspection_cold_normal(input, limits, false);
        part2_parse_and_inspect_container_unfold(input, limits);
        part2_inspect_jph_cold_actual(input, limits, part2_parse_and_inspect_container(input, limits));
        part2_inspect_jph_container_unfold(input, limits);
    } else { part2_inspection_cold_normal(input, limits, true); }
    part2_single_inspection_actual(input, limits, jph, inspected);
}

pub(crate) proof fn part2_decode_single_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: Option<&crate::DecodeSelection>, jph: bool,
)
    ensures part2_decode_single_cold_result(input, limits, selection, jph,
        part2_decode_raw_single_container(input, limits, selection, jph)),
{
    reveal(part2_decode_single_cold_result);
    part2_decode_raw_single_container_unfold(input, limits, selection, jph);
    let inspected = if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) };
    if jph {
        part2_inspection_cold_normal(input, limits, false);
        part2_parse_and_inspect_container_unfold(input, limits);
        part2_inspect_jph_cold_actual(input, limits, part2_parse_and_inspect_container(input, limits));
        part2_inspect_jph_container_unfold(input, limits);
    } else { part2_inspection_cold_normal(input, limits, true); }
    part2_single_inspection_actual(input, limits, jph, inspected);
    if let Ok(value) = inspected {
        match part2_single_profile(value, jph) {
            Err(error) => { part2_cold_pure::<Part1DecodedTypedImage>(Err(error)); },
            Ok(()) => {
                let decoded = part2_decode_raw_codestream(value.0.streams[0].1, limits, selection);
                part2_decode_raw_cold_normal(value.0.streams[0].1, limits, selection);
                part2_decode_raw_cold_frames(value.0.streams[0].1, limits, selection, decoded);
                if let Ok(image) = decoded { part2_cold_pure(part2_single_output(value, limits, image)); }
                part2_cold_bind(
                    |events| part2_decode_raw_cold_run(value.0.streams[0].1, limits, selection, events),
                    |image: Part1DecodedTypedImage, rest| Some((part2_single_output(value, limits, image), rest)),
                    decoded, match decoded { Err(error) => Err(error), Ok(image) => part2_single_output(value, limits, image) });
            },
        }
    }
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, jph, events),
        |value: Part2RawInspectedContainer, rest| part2_single_after_inspection(value, limits, selection, jph, rest),
        inspected, part2_decode_raw_single_container(input, limits, selection, jph));
}

pub(crate) proof fn part2_decode_single_inspection_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: Option<&crate::DecodeSelection>, jph: bool,
    error: crate::DecodeError,
)
    requires if jph { part2_inspect_jph_cold_result(input, limits, Err(error)) }
        else { part2_inspection_cold_result(input, limits, true, Err(error)) },
    ensures part2_decode_single_cold_result(input, limits, selection, jph, Err(error)),
{
    reveal(part2_decode_single_cold_result);
    part2_single_inspection_actual(input, limits, jph, Err(error));
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, jph, events),
        |value: Part2RawInspectedContainer, rest| part2_single_after_inspection(value, limits, selection, jph, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_decode_single_image_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: Option<&crate::DecodeSelection>, jph: bool,
    inspected: Part2RawInspectedContainer, decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires if jph { part2_inspect_jph_cold_result(input, limits, Ok(inspected)) }
        else { part2_inspection_cold_result(input, limits, true, Ok(inspected)) },
        part2_single_profile(inspected, jph) == Ok(()),
        part2_decode_raw_cold_result(inspected.0.streams[0].1, limits, selection, decoded),
    ensures part2_decode_single_cold_result(input, limits, selection, jph, match decoded {
        Err(error) => Err(error), Ok(image) => part2_single_output(inspected, limits, image),
    }),
{
    reveal(part2_decode_single_cold_result);
    let result = match decoded { Err(error) => Err(error), Ok(image) => part2_single_output(inspected, limits, image) };
    part2_single_inspection_actual(input, limits, jph, Ok(inspected));
    part2_decode_raw_cold_frames(inspected.0.streams[0].1, limits, selection, decoded);
    if let Ok(image) = decoded { part2_cold_pure(part2_single_output(inspected, limits, image)); }
    part2_cold_bind(
        |events| part2_decode_raw_cold_run(inspected.0.streams[0].1, limits, selection, events),
        |image: Part1DecodedTypedImage, rest| Some((part2_single_output(inspected, limits, image), rest)), decoded, result);
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, jph, events),
        |value: Part2RawInspectedContainer, rest| part2_single_after_inspection(value, limits, selection, jph, rest),
        Ok(inspected), result);
}

pub closed spec fn part2_decode_raw_single_container(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    selection: Option<&crate::DecodeSelection>, jph: bool,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    let inspected = if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) };
    match inspected {
        Err(error) => Err(error),
        Ok(inspected) => {
            let file = inspected.0;
            if (jph && file.streams.len() != 1)
                || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
                Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
            } else {
                match part2_decode_raw_codestream(file.streams[0].1, limits, selection) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_apply_output_header(decoded, part2_raw_associated_header(file.header).0,
                        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
                }
            }
        },
    }
}

pub(crate) proof fn part2_decode_raw_single_container_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    selection: Option<&crate::DecodeSelection>, jph: bool,
)
    ensures part2_decode_raw_single_container(input, limits, selection, jph) == {
        let inspected = if jph { part2_inspect_jph_container(input, limits) }
            else { part2_parse_and_inspect_container_mode(input, limits, true) };
        match inspected {
            Err(error) => Err(error),
            Ok(inspected) => {
                let file = inspected.0;
                if (jph && file.streams.len() != 1)
                    || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
                    Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
                } else {
                    match part2_decode_raw_codestream(file.streams[0].1, limits, selection) {
                        Err(error) => Err(error),
                        Ok(decoded) => part2_apply_output_header(decoded, part2_raw_associated_header(file.header).0,
                            crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
                    }
                }
            },
        }
    },
{
}

}
