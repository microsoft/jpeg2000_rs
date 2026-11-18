//! Raw color output and source-derived expanded selection composition.

use super::*;

verus! {

pub(crate) open spec fn part2_color_selection_size_run(
    size: Part2SelectionGeometry, components: Seq<crate::codestream::ComponentInfo>, count: u16,
    requested: Part2DecodeSelection, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodeSelection, Seq<u32>)> {
    part2_jpip_snapshot_bind(part2_validate_selection_run(size, requested, events),
        |selected: Part2ValidatedSelection, rest|
            Some((part2_color_selection_context(size.2, size.3, components, count, selected), rest)))
}

pub(crate) open spec fn part2_color_selection_size_result(
    size: Part2SelectionGeometry, components: Seq<crate::codestream::ComponentInfo>, count: u16,
    requested: Part2DecodeSelection, result: Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_color_selection_size_run(size, components, count, requested, events), result)
}

pub(crate) proof fn part2_color_selection_size_actual(
    size: Part2SelectionGeometry, components: Seq<crate::codestream::ComponentInfo>, count: u16,
    requested: Part2DecodeSelection, selected: Result<Part2ValidatedSelection, crate::DecodeError>,
)
    requires part2_validate_selection_result(size, requested, selected),
    ensures part2_color_selection_size_result(size, components, count, requested, match selected {
        Err(error) => Err(error), Ok(value) => part2_color_selection_context(size.2, size.3, components, count, value),
    }),
{
    let result = match selected {
        Err(error) => Err(error), Ok(value) => part2_color_selection_context(size.2, size.3, components, count, value),
    };
    part2_cold_pure(result);
    part2_cold_bind(|events| part2_validate_selection_run(size, requested, events),
        |selected: Part2ValidatedSelection, rest|
            Some((part2_color_selection_context(size.2, size.3, components, count, selected), rest)), selected, result);
}

pub(crate) proof fn part2_color_selection_size_normal(
    size: Part2SelectionGeometry, components: Seq<crate::codestream::ComponentInfo>, count: u16,
    requested: Part2DecodeSelection,
)
    ensures part2_color_selection_size_result(size, components, count, requested,
        part2_color_selection_requested(size, components, count, requested)),
{
    part2_validate_selection_normal(size, requested);
    part2_color_selection_size_actual(size, components, count, requested, part2_validate_selection(size, requested));
}

pub(crate) open spec fn part2_color_selection_layout_run(
    layout: Part1CompleteLayout, requested: Part2DecodeSelection, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodeSelection, Seq<u32>)> {
    let size = part2_decoder_input_from_raw(layout).size;
    part2_color_selection_size_run(crate::codestream::selection_geometry_view(&size),
        crate::codestream::image_size_component_infos(&size),
        crate::codestream::image_size_component_count(&size), requested, events)
}

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
        |layout: Part1CompleteLayout, rest| part2_color_selection_layout_run(layout, requested, rest))
}

pub(crate) open spec fn part2_color_selection_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    result: Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_color_selection_cold_run(input, limits, requested, events), result)
}

pub(crate) proof fn part2_color_selection_cold_observed(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    parsed: Part1CompleteLayoutResult, result: Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError>,
)
    requires part1_parse_layout_cold_result(input, limits, parsed),
        match parsed {
            Err(error) => result == Err(error),
            Ok(layout) => {
                let size = part2_decoder_input_from_raw(layout).size;
                part2_color_selection_size_result(crate::codestream::selection_geometry_view(&size),
                    crate::codestream::image_size_component_infos(&size),
                    crate::codestream::image_size_component_count(&size), requested, result)
            },
        },
    ensures part2_color_selection_cold_result(input, limits, requested, result),
{
    part2_cold_parse_actual(input, limits, 3, 0, parsed);
    if let Ok(layout) = parsed {
        let size = part2_decoder_input_from_raw(layout).size;
        part2_cold_framed_extensional(
            |events| part2_color_selection_size_run(crate::codestream::selection_geometry_view(&size),
                crate::codestream::image_size_component_infos(&size),
                crate::codestream::image_size_component_count(&size), requested, events),
            |events| part2_color_selection_layout_run(layout, requested, events), result);
    }
    part2_cold_bind(|events| part2_cold_parse(input, limits, 3, 0, events),
        |layout: Part1CompleteLayout, rest| part2_color_selection_layout_run(layout, requested, rest), parsed, result);
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
    if let Ok(layout) = parsed {
        let size = part2_decoder_input_from_raw(layout).size;
        part2_color_selection_size_normal(crate::codestream::selection_geometry_view(&size),
            crate::codestream::image_size_component_infos(&size),
            crate::codestream::image_size_component_count(&size), requested);
    }
    part2_color_selection_cold_observed(input, limits, requested, parsed, result);
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

pub(crate) open spec fn part2_color_cold_finish_run(file:Part2RawJp2File,limits:&crate::ResourceLimits,target:Option<Seq<u32>>,decoded:Part1DecodedTypedImage,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    let header=part2_raw_associated_header(file.header);
    match target {
        None=>part2_jpip_snapshot_bind(part2_apply_output_run(decoded,header.0,crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),events),
            |mapped:Part1DecodedTypedImage,rest|part2_color_convert_storage_run(Part2ColorConvertContext {
                image:mapped,method:header.2,bytes:crate::limits::resource_decoded_bytes_limit(limits),
                work:crate::limits::resource_work_limit(limits)},rest)),
        Some(target)=>part2_selected_output_run(decoded,Some(header),[target[0],target[1],target[2],target[3]],
            crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),events),
    }
}
pub(crate) proof fn part2_color_cold_finish_normal(file:Part2RawJp2File,limits:&crate::ResourceLimits,target:Option<Seq<u32>>,decoded:Part1DecodedTypedImage)
    ensures part2_cold_framed(|events|part2_color_cold_finish_run(file,limits,target,decoded,events),part2_color_cold_finish(file,limits,target,decoded)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage>|
            (forall|events| #[trigger] other(events)==part2_color_cold_finish_run(file,limits,target,decoded,events)) ==> #[trigger] part2_cold_framed(other,part2_color_cold_finish(file,limits,target,decoded)),
{
    let header=part2_raw_associated_header(file.header);
    let components=crate::limits::resource_component_limit(limits);let maximum=crate::limits::resource_decoded_bytes_limit(limits);let work=crate::limits::resource_work_limit(limits);
    match target {
        None=>{
            let mapped=part2_apply_output_header(decoded,header.0,components,maximum);part2_apply_output_normal(decoded,header.0,components,maximum);
            if let Ok(value)=mapped{
                let context=Part2ColorConvertContext {image:value,method:header.2,bytes:maximum,work};
                part2_color_convert_storage_normal(context);
                part2_color_convert_storage_frames(context,part2_color_convert_value(context));
            }
            part2_cold_bind(|events|part2_apply_output_run(decoded,header.0,components,maximum,events),
                |mapped:Part1DecodedTypedImage,rest|part2_color_convert_storage_run(Part2ColorConvertContext {image:mapped,method:header.2,bytes:maximum,work},rest),
                mapped,part2_color_cold_finish(file,limits,target,decoded));
        },
        Some(value)=>{
            let region=[value[0],value[1],value[2],value[3]];
            part2_selected_output_normal(decoded,Some(header),region,components,maximum,work);
            part2_selected_output_frames(decoded,Some(header),region,components,maximum,work,part2_finish_associated_selected_output(decoded,Some(header),region,components,maximum,work));
        },
    }
    part2_decode_eta(|events|part2_color_cold_finish_run(file,limits,target,decoded,events),part2_color_cold_finish(file,limits,target,decoded));
}
pub(crate) open spec fn part2_color_after_selection_cold(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, expanded: (Part2DecodeSelection, Seq<u32>),
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_decode_raw_value_cold_run(file.streams[0].1, limits, Some(expanded.0), events),
        |decoded: Part1DecodedTypedImage, tail|part2_color_cold_finish_run(file,limits,Some(expanded.1),decoded,tail))
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
                |decoded: Part1DecodedTypedImage, tail|part2_color_cold_finish_run(file,limits,None,decoded,tail)),
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
    if let Ok(image) = decoded {part2_color_cold_finish_normal(file,limits,Some(expanded.1),image);}
    part2_cold_bind(
        |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, Some(expanded.0), events),
        |image: Part1DecodedTypedImage, tail|part2_color_cold_finish_run(file,limits,Some(expanded.1),image,tail),
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
                if let Ok(image) = decoded {part2_color_cold_finish_normal(file,limits,None,image);}
                part2_decode_raw_codestream_selection_none(file.streams[0].1, limits);
                part2_cold_bind(
                    |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, None, events),
                    |image: Part1DecodedTypedImage, tail|part2_color_cold_finish_run(file,limits,None,image,tail),
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
                |image: Part1DecodedTypedImage, tail|part2_color_cold_finish_run(file,limits,None,image,tail),
                Err(error), Err(error));
        },
        Some(selected) => {
            let intermediate = match expanded {
                None => Err(error), Some(value) => Ok(value),
            };
            if let Some(value) = expanded {
                part2_cold_bind(
                    |events| part2_decode_raw_value_cold_run(file.streams[0].1, limits, Some(value.0), events),
                    |image: Part1DecodedTypedImage, tail|part2_color_cold_finish_run(file,limits,Some(value.1),image,tail),
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

pub(crate) proof fn part2_decode_color_output_error(input:Seq<u8>,limits:&crate::ResourceLimits,requested:Option<Part2DecodeSelection>,jph:bool,
    inspected:Part2RawInspectedContainer,expanded:Option<(Part2DecodeSelection,Seq<u32>)>,image:Part1DecodedTypedImage,error:crate::DecodeError)
    requires if jph{part2_inspect_jph_cold_result(input,limits,Ok(inspected))}else{part2_inspection_cold_result(input,limits,true,Ok(inspected))},
        part2_single_profile(inspected,jph)==Ok(()),
        match requested {
            None=>expanded.is_none() && part2_decode_raw_value_cold_result(inspected.0.streams[0].1,limits,None,Ok(image))
                &&part2_output_storage_result(Part2OutputStorageContext {image,header:part2_raw_associated_header(inspected.0.header).0,
                    components:crate::limits::resource_component_limit(limits),maximum:crate::limits::resource_decoded_bytes_limit(limits)},Err(error)),
            Some(selected)=>match expanded {
                None=>false,
                Some(value)=>part2_color_selection_cold_result(inspected.0.streams[0].1,limits,selected,Ok(value))
                    &&part2_decode_raw_value_cold_result(inspected.0.streams[0].1,limits,Some(value.0),Ok(image))
                    &&part2_selected_output_result(image,Some(part2_raw_associated_header(inspected.0.header)),[value.1[0],value.1[1],value.1[2],value.1[3]],
                        crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),Err(error)),
            },
        },
    ensures part2_decode_color_cold_result(input,limits,requested,jph,Err(error)),
{
    reveal(part2_decode_color_cold_result);
    part2_single_inspection_actual(input,limits,jph,Ok(inspected));
    let file=inspected.0;let header=part2_raw_associated_header(file.header);
    let components=crate::limits::resource_component_limit(limits);let maximum=crate::limits::resource_decoded_bytes_limit(limits);let work=crate::limits::resource_work_limit(limits);
    match requested {
        None=>{
            part2_apply_output_observed(image,header.0,components,maximum,Err(error));
            part2_cold_bind(|events|part2_apply_output_run(image,header.0,components,maximum,events),
                |mapped:Part1DecodedTypedImage,rest|part2_color_convert_storage_run(Part2ColorConvertContext {image:mapped,method:header.2,bytes:maximum,work},rest),Err(error),Err(error));
            part2_decode_eta(|events|part2_color_cold_finish_run(file,limits,None,image,events),Err(error));
            part2_cold_bind(|events|part2_decode_raw_value_cold_run(file.streams[0].1,limits,None,events),
                |image:Part1DecodedTypedImage,rest|part2_color_cold_finish_run(file,limits,None,image,rest),Ok(image),Err(error));
        },
        Some(selected)=>{
            if let Some(value)=expanded {
                part2_selected_output_frames(image,Some(header),[value.1[0],value.1[1],value.1[2],value.1[3]],components,maximum,work,Err(error));
                part2_decode_eta(|events|part2_color_cold_finish_run(file,limits,Some(value.1),image,events),Err(error));
                part2_cold_bind(|events|part2_decode_raw_value_cold_run(file.streams[0].1,limits,Some(value.0),events),
                    |image:Part1DecodedTypedImage,rest|part2_color_cold_finish_run(file,limits,Some(value.1),image,rest),Ok(image),Err(error));
                part2_decode_eta(|events|part2_color_after_selection_cold(file,limits,value,events),Err(error));
                part2_cold_bind(|events|part2_color_selection_cold_run(file.streams[0].1,limits,selected,events),
                    |value,rest|part2_color_after_selection_cold(file,limits,value,rest),Ok(value),Err(error));
            }
        },
    }
    part2_decode_eta(|events|part2_color_file_cold_run(file,limits,requested,jph,events),Err(error));
    part2_cold_bind(|events|part2_single_inspection_run(input,limits,jph,events),
        |value:Part2RawInspectedContainer,rest|part2_color_file_cold_run(value.0,limits,requested,jph,rest),Ok(inspected),Err(error));
}
pub(crate) proof fn part2_decode_color_conversion_error(input:Seq<u8>,limits:&crate::ResourceLimits,jph:bool,
    inspected:Part2RawInspectedContainer,image:Part1DecodedTypedImage,mapped:Part1DecodedTypedImage,error:crate::DecodeError)
    requires if jph{part2_inspect_jph_cold_result(input,limits,Ok(inspected))}else{part2_inspection_cold_result(input,limits,true,Ok(inspected))},
        part2_single_profile(inspected,jph)==Ok(()),
        part2_decode_raw_value_cold_result(inspected.0.streams[0].1,limits,None,Ok(image)),
        part2_output_storage_result(Part2OutputStorageContext {image,header:part2_raw_associated_header(inspected.0.header).0,
            components:crate::limits::resource_component_limit(limits),maximum:crate::limits::resource_decoded_bytes_limit(limits)},Ok(mapped)),
        part2_color_convert_storage_result(Part2ColorConvertContext {image:mapped,method:part2_raw_associated_header(inspected.0.header).2,
            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)},Err(error)),
    ensures part2_decode_color_cold_result(input,limits,None,jph,Err(error)),
{
    reveal(part2_decode_color_cold_result);
    let file=inspected.0;let header=part2_raw_associated_header(file.header);
    let components=crate::limits::resource_component_limit(limits);let maximum=crate::limits::resource_decoded_bytes_limit(limits);
    let work=crate::limits::resource_work_limit(limits);
    part2_single_inspection_actual(input,limits,jph,Ok(inspected));
    part2_apply_output_observed(image,header.0,components,maximum,Ok(mapped));
    part2_color_convert_storage_frames(Part2ColorConvertContext {image:mapped,method:header.2,bytes:maximum,work},Err(error));
    part2_cold_bind(|events|part2_apply_output_run(image,header.0,components,maximum,events),
        |mapped:Part1DecodedTypedImage,rest|part2_color_convert_storage_run(Part2ColorConvertContext {image:mapped,method:header.2,bytes:maximum,work},rest),
        Ok(mapped),Err(error));
    part2_decode_eta(|events|part2_color_cold_finish_run(file,limits,None,image,events),Err(error));
    part2_cold_bind(|events|part2_decode_raw_value_cold_run(file.streams[0].1,limits,None,events),
        |image:Part1DecodedTypedImage,rest|part2_color_cold_finish_run(file,limits,None,image,rest),Ok(image),Err(error));
    part2_decode_eta(|events|part2_color_file_cold_run(file,limits,None,jph,events),Err(error));
    part2_cold_bind(|events|part2_single_inspection_run(input,limits,jph,events),
        |value:Part2RawInspectedContainer,rest|part2_color_file_cold_run(value.0,limits,None,jph,rest),Ok(inspected),Err(error));
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
