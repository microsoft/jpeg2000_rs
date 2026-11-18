//! Raw public JPX codestream results and actual selected-file traversal.

use super::*;

verus! {

pub(crate) open spec fn part2_jpx_request_cold_run(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)> {
    match requested {
        None => part2_jpx_cold_run(file, index, limits, events),
        Some(value) => part2_jpx_selected_cold_run(file, index, limits, value, events),
    }
}

pub(crate) proof fn part2_jpx_request_cold_normal(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>,
)
    ensures part2_cold_framed(|events| part2_jpx_request_cold_run(file, index, limits, requested, events),
        part2_decode_jpx_file_request(file, index, limits, requested)),
{
    match requested {
        None => { part2_jpx_cold_normal(file, index, limits); },
        Some(value) => { part2_jpx_selected_cold_normal(file, index, limits, value); },
    }
    part2_jpx_request_cold_actual(file, index, limits, requested,
        part2_decode_jpx_file_request(file, index, limits, requested));
}

pub(crate) proof fn part2_jpx_request_cold_actual(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, decoded: Part2AssociatedImageResult,
)
    requires match requested {
        None => part2_jpx_cold_result(file, index, limits, decoded),
        Some(value) => part2_jpx_selected_cold_result(file, index, limits, value, decoded),
    },
    ensures part2_cold_framed(|events| part2_jpx_request_cold_run(file, index, limits, requested, events), decoded),
{
    match requested {
        None => {
            part2_cold_framed_extensional(
                |events| part2_jpx_cold_run(file, index, limits, events),
                |events| part2_jpx_request_cold_run(file, index, limits, requested, events), decoded);
        },
        Some(value) => {
            part2_cold_framed_extensional(
                |events| part2_jpx_selected_cold_run(file, index, limits, value, events),
                |events| part2_jpx_request_cold_run(file, index, limits, requested, events), decoded);
        },
    }
}

pub(crate) open spec fn part2_decode_jpx_typed_after_container(
    raw: Part2RawJp2File, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(
        part2_jpx_request_cold_run(part2_raw_jpx_decode_input(raw), index, limits, requested, events),
        |decoded: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>), tail| Some((Ok(decoded.0), tail)))
}

pub(crate) open spec fn part2_decode_jpx_typed_cold_run(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_parse_container_cold_run(input, *limits, events),
        |raw, rest| part2_decode_jpx_typed_after_container(raw, index, limits, requested, rest))
}

pub closed spec fn part2_decode_jpx_typed_cold_result(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, result: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_decode_jpx_typed_cold_run(input, index, limits, requested, events), result)
}

pub(crate) proof fn part2_decode_jpx_typed_cold_normal(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
)
    ensures part2_decode_jpx_typed_cold_result(input, index, limits, requested,
        part2_decode_raw_jpx_typed(input, index, limits, requested)),
{
    reveal(part2_decode_jpx_typed_cold_result);
    part2_decode_raw_jpx_typed_unfold(input, index, limits, requested);
    match part2_parse_container(input, *limits) {
        Err(error) => { part2_cold_pure::<Part1DecodedTypedImage>(Err(error)); },
        Ok(raw) => {
            let file = part2_raw_jpx_decode_input(raw);
            let decoded = part2_decode_jpx_file_request(file, index, limits, requested);
            part2_jpx_request_cold_normal(file, index, limits, requested);
            if let Ok(value) = decoded { part2_cold_pure(Ok(value.0)); }
            part2_cold_bind(
                |events| part2_jpx_request_cold_run(file, index, limits, requested, events),
                |value: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>), tail| Some((Ok(value.0), tail)),
                decoded, part2_decode_raw_jpx_typed(input, index, limits, requested));
        },
    }
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, part2_parse_container(input, *limits));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |raw, rest| part2_decode_jpx_typed_after_container(raw, index, limits, requested, rest),
        part2_parse_container(input, *limits), part2_decode_raw_jpx_typed(input, index, limits, requested));
}

pub(crate) proof fn part2_decode_jpx_typed_cold_actual(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    raw: Part2RawJp2File, decoded: Part2AssociatedImageResult,
)
    requires part2_parse_container(input, *limits) == Ok(raw),
        match requested {
            None => part2_jpx_cold_result(part2_raw_jpx_decode_input(raw), index, limits, decoded),
            Some(value) => part2_jpx_selected_cold_result(part2_raw_jpx_decode_input(raw), index, limits, value, decoded),
        },
    ensures part2_decode_jpx_typed_cold_result(input, index, limits, requested,
        match decoded { Err(error) => Err(error), Ok(value) => Ok(value.0) }),
{
    reveal(part2_decode_jpx_typed_cold_result);
    let file = part2_raw_jpx_decode_input(raw);
    part2_jpx_request_cold_actual(file, index, limits, requested, decoded);
    if let Ok(value) = decoded { part2_cold_pure(Ok(value.0)); }
    part2_cold_bind(
        |events| part2_jpx_request_cold_run(file, index, limits, requested, events),
        |value: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>), tail| Some((Ok(value.0), tail)),
        decoded, match decoded { Err(error) => Err(error), Ok(value) => Ok(value.0) });
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, Ok(raw));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_decode_jpx_typed_after_container(file, index, limits, requested, rest),
        Ok(raw), match decoded { Err(error) => Err(error), Ok(value) => Ok(value.0) });
}

pub(crate) proof fn part2_decode_jpx_typed_container_error(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, error: crate::DecodeError,
)
    requires part2_parse_container_cold_result(input, *limits, Err(error)),
    ensures part2_decode_jpx_typed_cold_result(input, index, limits, requested, Err(error)),
{
    reveal(part2_decode_jpx_typed_cold_result);
    part2_parse_container_cold_frames(input, *limits, Err(error));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |raw, rest| part2_decode_jpx_typed_after_container(raw, index, limits, requested, rest),
        Err(error), Err(error));
}

pub(crate) open spec fn part2_jpx_color_cold_finish(
    decoded: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>),
    target: Option<Seq<u32>>, limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    match target {
        None => part2_convert_associated(decoded.0, decoded.1,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
        Some(target) => part2_convert_associated_selected(decoded.0, decoded.1,
            [target[0], target[1], target[2], target[3]],
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
    }
}

pub(crate) open spec fn part2_jpx_color_cold_finish_run(decoded:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),
    target:Option<Seq<u32>>,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage> {
    part2_color_associated_storage_run(decoded.0,decoded.1,
        match target {None=>None,Some(target)=>Some([target[0],target[1],target[2],target[3]])},
        crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),events)
}
pub(crate) proof fn part2_jpx_color_cold_finish_normal(decoded:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),
    target:Option<Seq<u32>>,limits:&crate::ResourceLimits)
    ensures part2_cold_framed(|events|part2_jpx_color_cold_finish_run(decoded,target,limits,events),part2_jpx_color_cold_finish(decoded,target,limits)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2ConvertedImage>|
            (forall|events|#[trigger]other(events)==part2_jpx_color_cold_finish_run(decoded,target,limits,events))
                ==>#[trigger]part2_cold_framed(other,part2_jpx_color_cold_finish(decoded,target,limits)),
{
    let selected=match target {None=>None,Some(target)=>Some([target[0],target[1],target[2],target[3]])};
    part2_color_associated_storage_normal(decoded.0,decoded.1,selected,crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits));
    part2_decode_eta(|events|part2_color_associated_storage_run(decoded.0,decoded.1,selected,
        crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),events),part2_jpx_color_cold_finish(decoded,target,limits));
    part2_decode_eta(|events|part2_jpx_color_cold_finish_run(decoded,target,limits,events),part2_jpx_color_cold_finish(decoded,target,limits));
}
pub(crate) open spec fn part2_jpx_color_after_selection_cold(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    expanded: (Part2DecodeSelection, Seq<u32>), events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_jpx_selected_cold_run(file, index, limits, expanded.0, events),
        |decoded: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>), tail|
            part2_jpx_color_cold_finish_run(decoded, Some(expanded.1), limits,tail))
}

pub(crate) open spec fn part2_jpx_color_file_cold_run(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    match requested {
        None => part2_jpip_snapshot_bind(part2_jpx_cold_run(file, index, limits, events),
            |decoded: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>), tail|
                part2_jpx_color_cold_finish_run(decoded, None, limits,tail)),
        Some(selected) => if !part2_file_type_jpx(file.0) {
            Some((Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)), events))
        } else {
            match part2_jpx_codestream_lookup(file.1, index) {
                Err(error) => Some((Err(error), events)),
                Ok(source) => part2_jpip_snapshot_bind(part2_color_selection_cold_run(source.0, limits, selected, events),
                    |expanded, tail| part2_jpx_color_after_selection_cold(file, index, limits, expanded, tail)),
            }
        },
    }
}

pub(crate) open spec fn part2_decode_jpx_color_cold_run(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_parse_container_cold_run(input, *limits, events),
        |raw, rest| part2_jpx_color_file_cold_run(part2_raw_jpx_decode_input(raw), index, limits, requested, rest))
}

pub closed spec fn part2_decode_jpx_color_cold_result(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, result: Part2ConvertedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_decode_jpx_color_cold_run(input, index, limits, requested, events), result)
}

pub(crate) proof fn part2_jpx_color_after_selection_normal(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, expanded: (Part2DecodeSelection, Seq<u32>),
)
    ensures part2_cold_framed(|events| part2_jpx_color_after_selection_cold(file, index, limits, expanded, events),
        match part2_decode_jpx_selected_file(file, index, limits, expanded.0) {
            Err(error) => Err(error), Ok(decoded) => part2_jpx_color_cold_finish(decoded, Some(expanded.1), limits),
        }),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2ConvertedImage>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_jpx_color_after_selection_cold(file, index, limits, expanded, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_jpx_color_after_selection_normal_result(file, index, limits, expanded)),
{
    let decoded = part2_decode_jpx_selected_file(file, index, limits, expanded.0);
    part2_jpx_selected_cold_normal(file, index, limits, expanded.0);
    if let Ok(value) = decoded { part2_jpx_color_cold_finish_normal(value, Some(expanded.1), limits); }
    part2_cold_bind(
        |events| part2_jpx_selected_cold_run(file, index, limits, expanded.0, events),
        |value, tail| part2_jpx_color_cold_finish_run(value, Some(expanded.1), limits,tail),
        decoded, match decoded { Err(error) => Err(error),
            Ok(value) => part2_jpx_color_cold_finish(value, Some(expanded.1), limits) });
}

pub(crate) open spec fn part2_jpx_color_after_selection_normal_result(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    expanded: (Part2DecodeSelection, Seq<u32>),
) -> Part2ConvertedImageResult {
    match part2_decode_jpx_selected_file(file, index, limits, expanded.0) {
        Err(error) => Err(error), Ok(decoded) => part2_jpx_color_cold_finish(decoded, Some(expanded.1), limits),
    }
}

pub(crate) proof fn part2_decode_jpx_color_cold_normal(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
)
    ensures part2_decode_jpx_color_cold_result(input, index, limits, requested,
        part2_decode_raw_jpx_color(input, index, limits, requested)),
{
    reveal(part2_decode_jpx_color_cold_result);
    part2_decode_raw_jpx_color_unfold(input, index, limits, requested);
    match part2_parse_container(input, *limits) {
        Err(error) => { part2_cold_pure::<Part2ConvertedImage>(Err(error)); },
        Ok(raw) => {
            let file = part2_raw_jpx_decode_input(raw);
            match requested {
                None => {
                    let decoded = part2_decode_jpx_codestream(file, index, limits);
                    part2_jpx_cold_normal(file, index, limits);
                    if let Ok(value) = decoded { part2_jpx_color_cold_finish_normal(value, None, limits); }
                    part2_cold_bind(
                        |events| part2_jpx_cold_run(file, index, limits, events),
                        |value, tail| part2_jpx_color_cold_finish_run(value, None, limits,tail),
                        decoded, part2_decode_raw_jpx_color(input, index, limits, requested));
                },
                Some(selected) => if !part2_file_type_jpx(file.0) {
                    part2_cold_pure::<Part2ConvertedImage>(Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)));
                } else {
                    match part2_jpx_codestream_lookup(file.1, index) {
                        Err(error) => { part2_cold_pure::<Part2ConvertedImage>(Err(error)); },
                        Ok(source) => {
                            let expanded = part2_color_selection_raw(source.0, limits, selected);
                            part2_color_selection_cold_normal(source.0, limits, selected);
                            if let Ok(value) = expanded { part2_jpx_color_after_selection_normal(file, index, limits, value); }
                            part2_cold_bind(
                                |events| part2_color_selection_cold_run(source.0, limits, selected, events),
                                |value, tail| part2_jpx_color_after_selection_cold(file, index, limits, value, tail),
                                expanded, part2_decode_raw_jpx_color(input, index, limits, requested));
                        },
                    }
                },
            }
        },
    }
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, part2_parse_container(input, *limits));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |raw, rest| part2_jpx_color_file_cold_run(part2_raw_jpx_decode_input(raw), index, limits, requested, rest),
        part2_parse_container(input, *limits), part2_decode_raw_jpx_color(input, index, limits, requested));
}

pub(crate) proof fn part2_decode_jpx_color_container_error(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>, error: crate::DecodeError,
)
    requires part2_parse_container_cold_result(input, *limits, Err(error)),
    ensures part2_decode_jpx_color_cold_result(input, index, limits, requested, Err(error)),
{
    reveal(part2_decode_jpx_color_cold_result);
    part2_parse_container_cold_frames(input, *limits, Err(error));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |raw, rest| part2_jpx_color_file_cold_run(part2_raw_jpx_decode_input(raw), index, limits, requested, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_decode_jpx_color_converted_actual(input:Seq<u8>,index:usize,limits:&crate::ResourceLimits,
    requested:Option<Part2DecodeSelection>,raw:Part2RawJp2File,expanded:Option<(Part2DecodeSelection,Seq<u32>)>,
    decoded:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),result:Part2ConvertedImageResult)
    requires part2_parse_container(input,*limits)==Ok(raw),
        match requested {
            None=>expanded.is_none() && part2_jpx_cold_result(part2_raw_jpx_decode_input(raw),index,limits,Ok(decoded))
                &&part2_color_associated_storage_result(decoded.0,decoded.1,None,
                    crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),result),
            Some(selected)=>part2_file_type_jpx(part2_raw_jpx_decode_input(raw).0) && index<part2_raw_jpx_decode_input(raw).1.len()
                &&match expanded {
                    None=>false,Some(value)=>part2_color_selection_cold_result(part2_raw_jpx_decode_input(raw).1[index as int].0,limits,selected,Ok(value))
                        &&part2_jpx_selected_cold_result(part2_raw_jpx_decode_input(raw),index,limits,value.0,Ok(decoded))
                        &&part2_color_associated_storage_result(decoded.0,decoded.1,Some([value.1[0],value.1[1],value.1[2],value.1[3]]),
                            crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),result),
                },
        },
    ensures part2_decode_jpx_color_cold_result(input,index,limits,requested,result),
{
    reveal(part2_decode_jpx_color_cold_result);
    let file=part2_raw_jpx_decode_input(raw);
    match requested {
        None=>{
            part2_decode_eta(|events|part2_color_associated_storage_run(decoded.0,decoded.1,None,
                crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),events),result);
            part2_cold_bind(|events|part2_jpx_cold_run(file,index,limits,events),
                |decoded,tail|part2_jpx_color_cold_finish_run(decoded,None,limits,tail),Ok(decoded),result);
        },
        Some(selected)=>{
            if let Some(value)=expanded {
                part2_decode_eta(|events|part2_color_associated_storage_run(decoded.0,decoded.1,Some([value.1[0],value.1[1],value.1[2],value.1[3]]),
                    crate::limits::resource_decoded_bytes_limit(limits),crate::limits::resource_work_limit(limits),events),result);
                part2_cold_bind(|events|part2_jpx_selected_cold_run(file,index,limits,value.0,events),
                    |decoded,tail|part2_jpx_color_cold_finish_run(decoded,Some(value.1),limits,tail),Ok(decoded),result);
                part2_decode_eta(|events|part2_jpx_color_after_selection_cold(file,index,limits,value,events),result);
                part2_cold_bind(|events|part2_color_selection_cold_run(file.1[index as int].0,limits,selected,events),
                    |value,tail|part2_jpx_color_after_selection_cold(file,index,limits,value,tail),Ok(value),result);
            }
        },
    }
    part2_decode_eta(|events|part2_jpx_color_file_cold_run(file,index,limits,requested,events),result);
    part2_parse_container_cold_normal(input,*limits,Seq::empty());
    part2_parse_container_cold_frames(input,*limits,Ok(raw));
    part2_cold_bind(|events|part2_parse_container_cold_run(input,*limits,events),
        |source,rest|part2_jpx_color_file_cold_run(part2_raw_jpx_decode_input(source),index,limits,requested,rest),Ok(raw),result);
}
pub(crate) proof fn part2_decode_jpx_color_source_error(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    raw: Part2RawJp2File, expanded: Option<(Part2DecodeSelection, Seq<u32>)>, error: crate::DecodeError,
)
    requires part2_parse_container(input, *limits) == Ok(raw),
        match requested {
            None => part2_jpx_cold_result(part2_raw_jpx_decode_input(raw), index, limits, Err(error)),
            Some(selected) => part2_file_type_jpx(part2_raw_jpx_decode_input(raw).0)
                && index < part2_raw_jpx_decode_input(raw).1.len()
                && match expanded {
                    None => part2_color_selection_cold_result(part2_raw_jpx_decode_input(raw).1[index as int].0,
                        limits, selected, Err(error)),
                    Some(value) => part2_color_selection_cold_result(part2_raw_jpx_decode_input(raw).1[index as int].0,
                        limits, selected, Ok(value))
                        && part2_jpx_selected_cold_result(part2_raw_jpx_decode_input(raw), index, limits, value.0, Err(error)),
                },
        },
    ensures part2_decode_jpx_color_cold_result(input, index, limits, requested, Err(error)),
{
    reveal(part2_decode_jpx_color_cold_result);
    let file = part2_raw_jpx_decode_input(raw);
    match requested {
        None => {
            part2_cold_bind(
                |events| part2_jpx_cold_run(file, index, limits, events),
                |value, tail| part2_jpx_color_cold_finish_run(value, None, limits,tail), Err(error), Err(error));
        },
        Some(selected) => {
            let intermediate = match expanded { None => Err(error), Some(value) => Ok(value) };
            if let Some(value) = expanded {
                part2_cold_bind(
                    |events| part2_jpx_selected_cold_run(file, index, limits, value.0, events),
                    |decoded, tail| part2_jpx_color_cold_finish_run(decoded, Some(value.1), limits,tail),
                    Err(error), Err(error));
            }
            part2_cold_bind(
                |events| part2_color_selection_cold_run(file.1[index as int].0, limits, selected, events),
                |value, tail| part2_jpx_color_after_selection_cold(file, index, limits, value, tail),
                intermediate, Err(error));
        },
    }
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, Ok(raw));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |source, rest| part2_jpx_color_file_cold_run(part2_raw_jpx_decode_input(source), index, limits, requested, rest),
        Ok(raw), Err(error));
}

pub(crate) open spec fn part2_decode_jpx_selected_layout(
    source: Part2CodestreamSource, header: Part2AssociatedHeader, layout: Part1CompleteLayout,
    limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
) -> Part2AssociatedImageResult {
    let size = layout.0.image_size;
    match part2_validate_selected_header(header.1, size.geometry.0, size.geometry.1, size.components,
        size.uniform_bit_depth, size.uniform_signed, source.1) {
        Err(error) => Err(error),
        Ok(()) => {
            let input = part2_decoder_input_from_raw(layout);
            match part2_decode_layout_selected_value_input(input, requested, limits) {
                Err(error) => Err(error),
                Ok(decoded) => match part2_typed_layout_input(input, decoded, requested.2, limits) {
                    Err(error) => Err(error),
                    Ok(image) => match part2_apply_output_header(image, header.0,
                        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)) {
                        Err(error) => Err(error),
                        Ok(mapped) => Ok((mapped, Some(header))),
                    },
                },
            }
        },
    }
}

pub(crate) open spec fn part2_decode_jpx_selected_source(
    source: Part2CodestreamSource, fallback: Part2AssociatedHeader, limits: &crate::ResourceLimits,
    requested: Part2DecodeSelection,
) -> Part2AssociatedImageResult {
    match part2_associated_codestream_header(source.2, fallback) {
        Err(error) => Err(error),
        Ok(header) => match part1_parse_layout(source.0, limits) {
            Err(error) => Err(error),
            Ok(layout) => part2_decode_jpx_selected_layout(source, header, layout, limits, requested),
        },
    }
}

pub closed spec fn part2_decode_jpx_selected_file(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
) -> Part2AssociatedImageResult {
    if !part2_file_type_jpx(input.0) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else {
        match part2_jpx_codestream_lookup(input.1, index) {
            Err(error) => Err(error),
            Ok(source) => part2_decode_jpx_selected_source(source, input.2, limits, requested),
        }
    }
}

pub(crate) proof fn part2_decode_jpx_selected_file_unfold(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
)
    ensures part2_decode_jpx_selected_file(input, index, limits, requested) == {
        if !part2_file_type_jpx(input.0) {
            Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
        } else {
            match part2_jpx_codestream_lookup(input.1, index) {
                Err(error) => Err(error),
                Ok(source) => part2_decode_jpx_selected_source(source, input.2, limits, requested),
            }
        }
    },
{
}

pub(crate) open spec fn part2_decode_jpx_file_request(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
) -> Part2AssociatedImageResult {
    match requested {
        None => part2_decode_jpx_codestream(file, index, limits),
        Some(requested) => part2_decode_jpx_selected_file(file, index, limits, requested),
    }
}

pub closed spec fn part2_decode_raw_jpx_typed(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => match part2_decode_jpx_file_request(part2_raw_jpx_decode_input(file), index, limits, requested) {
            Err(error) => Err(error), Ok(decoded) => Ok(decoded.0),
        },
    }
}

pub(crate) proof fn part2_decode_raw_jpx_typed_unfold(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
)
    ensures part2_decode_raw_jpx_typed(input, index, limits, requested) == match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => match part2_decode_jpx_file_request(part2_raw_jpx_decode_input(file), index, limits, requested) {
            Err(error) => Err(error), Ok(decoded) => Ok(decoded.0),
        },
    },
{
}

pub(crate) open spec fn part2_decode_jpx_selected_color(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
) -> Part2ConvertedImageResult {
    if !part2_file_type_jpx(file.0) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else {
        match part2_jpx_codestream_lookup(file.1, index) {
            Err(error) => Err(error),
            Ok(source) => match part2_color_selection_raw(source.0, limits, requested) {
                Err(error) => Err(error),
                Ok(expanded) => match part2_decode_jpx_selected_file(file, index, limits, expanded.0) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_convert_associated_selected(decoded.0, decoded.1,
                        [expanded.1[0], expanded.1[1], expanded.1[2], expanded.1[3]],
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
                },
            },
        }
    }
}

pub closed spec fn part2_decode_raw_jpx_color(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
) -> Part2ConvertedImageResult {
    match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(raw) => {
            let file = part2_raw_jpx_decode_input(raw);
            match requested {
                Some(requested) => part2_decode_jpx_selected_color(file, index, limits, requested),
                None => match part2_decode_jpx_codestream(file, index, limits) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_convert_associated(decoded.0, decoded.1,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
                },
            }
        },
    }
}

pub(crate) proof fn part2_decode_raw_jpx_color_unfold(
    input: Seq<u8>, index: usize, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
)
    ensures part2_decode_raw_jpx_color(input, index, limits, requested) == match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(raw) => {
            let file = part2_raw_jpx_decode_input(raw);
            match requested {
                Some(requested) => part2_decode_jpx_selected_color(file, index, limits, requested),
                None => match part2_decode_jpx_codestream(file, index, limits) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_convert_associated(decoded.0, decoded.1,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
                },
            }
        },
    },
{
}

}
