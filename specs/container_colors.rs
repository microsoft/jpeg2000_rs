//! Raw color output and source-derived expanded selection composition.

use super::*;

verus! {

pub(crate) open spec fn part2_color_selection_layout(
    layout: Part1CompleteLayout, requested: Part2DecodeSelection,
) -> Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError> {
    let size = part2_decoder_input_from_raw(layout).size;
    part2_color_selection_requested(crate::codestream::selection_geometry_view(&size),
        crate::codestream::image_size_component_infos(&size),
        crate::codestream::image_size_component_count(&size), requested)
}

pub(crate) open spec fn part2_color_selection_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodeSelection, Seq<u32>)> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 3, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_color_selection_layout(layout, requested), rest)))
}

pub(crate) open spec fn part2_color_selection_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    result: Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_color_selection_cold_run(input, limits, requested, events), result)
}

pub(crate) proof fn part2_color_selection_cold_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    parsed: Part1CompleteLayoutResult,
)
    requires part1_parse_layout_cold_result(input, limits, parsed),
    ensures part2_color_selection_cold_result(input, limits, requested, match parsed {
        Err(error) => Err(error), Ok(layout) => part2_color_selection_layout(layout, requested),
    }),
{
    let result = match parsed {
        Err(error) => Err(error), Ok(layout) => part2_color_selection_layout(layout, requested),
    };
    part2_cold_parse_then_actual(input, limits, 3, 0, parsed,
        |layout: Part1CompleteLayout| part2_color_selection_layout(layout, requested));
    part2_cold_framed_extensional(
        |events| part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 3, 0, events),
            |layout: Part1CompleteLayout, rest| Some((part2_color_selection_layout(layout, requested), rest))),
        |events| part2_color_selection_cold_run(input, limits, requested, events), result);
}

pub(crate) proof fn part2_color_selection_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
)
    ensures part2_color_selection_cold_result(input, limits, requested,
        part2_color_selection_raw(input, limits, requested)),
{
    part1_parse_layout_cold_normal(input, limits);
    part2_color_selection_raw_unfold(input, limits, requested);
    part2_color_selection_cold_actual(input, limits, requested, part1_parse_layout(input, limits));
}

pub(crate) open spec fn part2_color_cold_finish(
    file: Part2RawJp2File, limits: &crate::ResourceLimits,
    target: Option<Seq<u32>>, decoded: Part1DecodedTypedImage,
) -> Part2ConvertedImageResult {
    let header = part2_raw_associated_header(file.header);
    match target {
        None => match part2_apply_output_header(decoded, header.0,
            crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)) {
            Err(error) => Err(error),
            Ok(mapped) => color_convert_jp2(mapped.1, mapped.2, mapped.0, header.2,
                crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
        },
        Some(target) => part2_finish_associated_selected_output(decoded, Some(header),
            [target[0], target[1], target[2], target[3]], crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
    }
}

pub(crate) open spec fn part2_color_after_selection_cold(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, expanded: (Part2DecodeSelection, Seq<u32>),
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_decode_raw_value_cold_run(file.streams[0].1, limits, Some(expanded.0), events),
        |decoded: Part1DecodedTypedImage, tail| Some((part2_color_cold_finish(file, limits, Some(expanded.1), decoded), tail)))
}

pub(crate) open spec fn part2_color_file_cold_run(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    jph: bool, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    if (jph && file.streams.len() != 1) || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
        Some((Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)), events))
    } else {
        match requested {
            None => part2_jpip_snapshot_bind(part2_decode_raw_value_cold_run(file.streams[0].1, limits, None, events),
                |decoded: Part1DecodedTypedImage, tail| Some((part2_color_cold_finish(file, limits, None, decoded), tail))),
            Some(requested) => part2_jpip_snapshot_bind(
                part2_color_selection_cold_run(file.streams[0].1, limits, requested, events),
                |expanded: (Part2DecodeSelection, Seq<u32>), tail|
                    part2_color_after_selection_cold(file, limits, expanded, tail)),
        }
    }
}

pub(crate) open spec fn part2_decode_color_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    jph: bool, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, jph, events),
        |inspected: Part2RawInspectedContainer, tail|
            part2_color_file_cold_run(inspected.0, limits, requested, jph, tail))
}

pub closed spec fn part2_decode_color_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    jph: bool, result: Part2ConvertedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_decode_color_cold_run(input, limits, requested, jph, events), result)
}

pub(crate) proof fn part2_color_cold_after_image_normal(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, expanded: (Part2DecodeSelection, Seq<u32>),
)
    ensures part2_cold_framed(|events| part2_color_after_selection_cold(file, limits, expanded, events),
        match part2_decode_raw_codestream_value(file.streams[0].1, limits, Some(expanded.0)) {
            Err(error) => Err(error), Ok(decoded) => part2_color_cold_finish(file, limits, Some(expanded.1), decoded),
        }),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2ConvertedImage>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_color_after_selection_cold(file, limits, expanded, events))
                ==> #[trigger] part2_cold_framed(run, part2_color_after_selection_normal_result(file, limits, expanded)),
{
    let decoded = part2_decode_raw_codestream_value(file.streams[0].1, limits, Some(expanded.0));
    part2_decode_raw_value_cold_normal(file.streams[0].1, limits, Some(expanded.0));
    if let Ok(image) = decoded { part2_cold_pure(part2_color_cold_finish(file, limits, Some(expanded.1), image)); }
    part2_cold_bind(
        |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, Some(expanded.0), events),
        |image: Part1DecodedTypedImage, tail| Some((part2_color_cold_finish(file, limits, Some(expanded.1), image), tail)),
        decoded, match decoded { Err(error) => Err(error),
            Ok(image) => part2_color_cold_finish(file, limits, Some(expanded.1), image) });
}

pub(crate) open spec fn part2_color_after_selection_normal_result(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, expanded: (Part2DecodeSelection, Seq<u32>),
) -> Part2ConvertedImageResult {
    match part2_decode_raw_codestream_value(file.streams[0].1, limits, Some(expanded.0)) {
        Err(error) => Err(error), Ok(decoded) => part2_color_cold_finish(file, limits, Some(expanded.1), decoded),
    }
}

pub(crate) proof fn part2_color_file_cold_normal(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
)
    ensures part2_cold_framed(|events| part2_color_file_cold_run(file, limits, requested, jph, events),
        part2_decode_file_color(file, limits, requested, jph)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2ConvertedImage>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_color_file_cold_run(file, limits, requested, jph, events))
                ==> #[trigger] part2_cold_framed(run, part2_decode_file_color(file, limits, requested, jph)),
{
    if (jph && file.streams.len() != 1) || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
        part2_cold_pure::<Part2ConvertedImage>(Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)));
    } else {
        match requested {
            None => {
                let decoded = part2_decode_raw_codestream_value(file.streams[0].1, limits, None);
                part2_decode_raw_value_cold_normal(file.streams[0].1, limits, None);
                if let Ok(image) = decoded { part2_cold_pure(part2_color_cold_finish(file, limits, None, image)); }
                part2_decode_raw_codestream_selection_none(file.streams[0].1, limits);
                part2_cold_bind(
                    |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, None, events),
                    |image: Part1DecodedTypedImage, tail| Some((part2_color_cold_finish(file, limits, None, image), tail)),
                    decoded, part2_decode_file_color(file, limits, requested, jph));
            },
            Some(selected) => {
                let expanded = part2_color_selection_raw(file.streams[0].1, limits, selected);
                part2_color_selection_cold_normal(file.streams[0].1, limits, selected);
                if let Ok(value) = expanded { part2_color_cold_after_image_normal(file, limits, value); }
                part2_cold_bind(
                    |events| part2_color_selection_cold_run(file.streams[0].1, limits, selected, events),
                    |value, tail| part2_color_after_selection_cold(file, limits, value, tail),
                    expanded, part2_decode_file_color(file, limits, requested, jph));
            },
        }
    }
}

pub(crate) proof fn part2_decode_color_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
)
    ensures part2_decode_color_cold_result(input, limits, requested, jph,
        part2_decode_raw_color_container(input, limits, requested, jph)),
{
    reveal(part2_decode_color_cold_result);
    part2_decode_raw_color_container_unfold(input, limits, requested, jph);
    let inspected = if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) };
    part2_single_inspection_normal(input, limits, jph);
    if let Ok(value) = inspected { part2_color_file_cold_normal(value.0, limits, requested, jph); }
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, jph, events),
        |value: Part2RawInspectedContainer, tail| part2_color_file_cold_run(value.0, limits, requested, jph, tail),
        inspected, part2_decode_raw_color_container(input, limits, requested, jph));
}

pub(crate) proof fn part2_decode_color_inspection_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
    error: crate::DecodeError,
)
    requires if jph { part2_inspect_jph_cold_result(input, limits, Err(error)) }
        else { part2_inspection_cold_result(input, limits, true, Err(error)) },
    ensures part2_decode_color_cold_result(input, limits, requested, jph, Err(error)),
{
    reveal(part2_decode_color_cold_result);
    part2_single_inspection_actual(input, limits, jph, Err(error));
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, jph, events),
        |value: Part2RawInspectedContainer, tail| part2_color_file_cold_run(value.0, limits, requested, jph, tail),
        Err(error), Err(error));
}

pub(crate) proof fn part2_decode_color_source_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
    inspected: Part2RawInspectedContainer, expanded: Option<(Part2DecodeSelection, Seq<u32>)>,
    error: crate::DecodeError,
)
    requires if jph { part2_inspect_jph_cold_result(input, limits, Ok(inspected)) }
        else { part2_inspection_cold_result(input, limits, true, Ok(inspected)) },
        part2_single_profile(inspected, jph) == Ok(()),
        match requested {
            None => expanded.is_none() &&
                part2_decode_raw_value_cold_result(inspected.0.streams[0].1, limits, None, Err(error)),
            Some(selected) => match expanded {
                None => part2_color_selection_cold_result(inspected.0.streams[0].1, limits, selected, Err(error)),
                Some(value) => part2_color_selection_cold_result(inspected.0.streams[0].1, limits, selected, Ok(value))
                    && part2_decode_raw_value_cold_result(inspected.0.streams[0].1, limits, Some(value.0), Err(error)),
            },
        },
    ensures part2_decode_color_cold_result(input, limits, requested, jph, Err(error)),
{
    reveal(part2_decode_color_cold_result);
    part2_single_inspection_actual(input, limits, jph, Ok(inspected));
    let file = inspected.0;
    match requested {
        None => {
            part2_cold_bind(
                |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, None, events),
                |image: Part1DecodedTypedImage, tail| Some((part2_color_cold_finish(file, limits, None, image), tail)),
                Err(error), Err(error));
        },
        Some(selected) => {
            let intermediate = match expanded {
                None => Err(error), Some(value) => Ok(value),
            };
            if let Some(value) = expanded {
                part2_cold_bind(
                    |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, Some(value.0), events),
                    |image: Part1DecodedTypedImage, tail| Some((part2_color_cold_finish(file, limits, Some(value.1), image), tail)),
                    Err(error), Err(error));
            }
            part2_cold_bind(
                |events| part2_color_selection_cold_run(file.streams[0].1, limits, selected, events),
                |value, tail| part2_color_after_selection_cold(file, limits, value, tail), intermediate, Err(error));
        },
    }
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, jph, events),
        |value: Part2RawInspectedContainer, tail| part2_color_file_cold_run(value.0, limits, requested, jph, tail),
        Ok(inspected), Err(error));
}

pub(crate) closed spec fn part2_color_selection_raw(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
) -> Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_color_selection_layout(layout, requested),
    }
}

pub(crate) proof fn part2_color_selection_raw_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
)
    ensures part2_color_selection_raw(input, limits, requested) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_color_selection_layout(layout, requested),
    },
{
}

pub(crate) open spec fn part2_decode_file_color(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
) -> Part2ConvertedImageResult {
    if (jph && file.streams.len() != 1)
        || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else {
        let header = part2_raw_associated_header(file.header);
        match requested {
            None => match part2_decode_raw_codestream(file.streams[0].1, limits, None) {
                Err(error) => Err(error),
                Ok(decoded) => match part2_apply_output_header(decoded, header.0,
                    crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)) {
                    Err(error) => Err(error),
                    Ok(mapped) => color_convert_jp2(mapped.1, mapped.2, mapped.0, header.2,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
                },
            },
            Some(requested) => match part2_color_selection_raw(file.streams[0].1, limits, requested) {
                Err(error) => Err(error),
                Ok(expanded) => match part2_decode_raw_codestream_value(file.streams[0].1, limits, Some(expanded.0)) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_finish_associated_selected_output(decoded, Some(header),
                        [expanded.1[0], expanded.1[1], expanded.1[2], expanded.1[3]],
                        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
                        crate::limits::resource_work_limit(limits)),
                },
            },
        }
    }
}

pub closed spec fn part2_decode_raw_color_container(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
) -> Part2ConvertedImageResult {
    let inspected = if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) };
    match inspected {
        Err(error) => Err(error),
        Ok(inspected) => part2_decode_file_color(inspected.0, limits, requested, jph),
    }
}

pub(crate) proof fn part2_decode_raw_color_container_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>, jph: bool,
)
    ensures part2_decode_raw_color_container(input, limits, requested, jph) == {
        let inspected = if jph { part2_inspect_jph_container(input, limits) }
            else { part2_parse_and_inspect_container_mode(input, limits, true) };
        match inspected {
            Err(error) => Err(error),
            Ok(inspected) => part2_decode_file_color(inspected.0, limits, requested, jph),
        }
    },
{
}

}
