//! Actual JPX file-to-codestream/associated-image composition.

use super::*;

verus! {

pub(crate) open spec fn part2_jpx_cold_header(
    input: Part2JpxDecodeInput, index: usize,
) -> Result<(Part2CodestreamSource, Part2AssociatedHeader), crate::DecodeError> {
    if !part2_file_type_jpx(input.0) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else {
        match part2_jpx_codestream_lookup(input.1, index) {
            Err(error) => Err(error),
            Ok(source) => match part2_associated_codestream_header(source.2, input.2) {
                Err(error) => Err(error), Ok(header) => Ok((source, header)),
            },
        }
    }
}

pub(crate) open spec fn part2_jpx_cold_validate(
    source: Part2CodestreamSource, header: Part2AssociatedHeader, info: Part2RawCodestreamInfo,
) -> Result<(), crate::DecodeError> {
    part2_validate_selected_header(header.1, info.0.image_size.geometry.0,
        info.0.image_size.geometry.1, info.0.image_size.components,
        info.0.image_size.uniform_bit_depth, info.0.image_size.uniform_signed, source.1)
}

pub(crate) open spec fn part2_jpx_cold_image(
    source: Part2CodestreamSource, header: Part2AssociatedHeader, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)> {
    part2_jpip_snapshot_bind(part2_decode_raw_cold_run(source.0, limits, None, events),
        |image: Part1DecodedTypedImage, rest|part2_associated_output_run(image, Some(header),
            crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest))
}

pub(crate) open spec fn part2_jpx_cold_run(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)> {
    match part2_jpx_cold_header(input, index) {
        Err(error) => Some((Err(error), events)),
        Ok((source, header)) => part2_jpip_snapshot_bind(part2_cold_info(source.0, limits, 5, index, events),
            |info: Part2RawCodestreamInfo, rest| match part2_jpx_cold_validate(source, header, info) {
                Err(error) => Some((Err(error), rest)),
                Ok(()) => part2_jpx_cold_image(source, header, limits, rest),
            }),
    }
}

pub(crate) open spec fn part2_jpx_selected_finish(input: Part2DecoderLayoutInput, header: Part2AssociatedHeader,
    requested: Part2DecodeSelection, limits: &crate::ResourceLimits, decoded: Part1DecodedImageModel) -> Part2AssociatedImageResult {
    match part2_typed_layout_input(input, decoded, requested.2, limits) {
        Err(error) => Err(error),
        Ok(image) => part2_apply_associated_output(image,Some(header),crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits)),
    }
}
pub(crate) open spec fn part2_jpx_selected_finish_run(input:Part2DecoderLayoutInput,header:Part2AssociatedHeader,requested:Part2DecodeSelection,
    limits:&crate::ResourceLimits,decoded:Part1DecodedImageModel,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(Part1DecodedTypedImage,Option<Part2AssociatedHeader>)> {
    part2_jpip_snapshot_bind(part2_typed_layout_run(input,decoded,requested.2,limits,events),
        |image:Part1DecodedTypedImage,rest|part2_associated_output_run(image,Some(header),crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest))
}
pub(crate) proof fn part2_jpx_selected_finish_normal(input:Part2DecoderLayoutInput,header:Part2AssociatedHeader,requested:Part2DecodeSelection,limits:&crate::ResourceLimits,decoded:Part1DecodedImageModel)
    ensures part2_cold_framed(|events|part2_jpx_selected_finish_run(input,header,requested,limits,decoded,events),part2_jpx_selected_finish(input,header,requested,limits,decoded)),
{
    let typed=part2_typed_layout_input(input,decoded,requested.2,limits);
    part2_typed_layout_normal(input,decoded,requested.2,limits);part2_typed_layout_frames(input,decoded,requested.2,limits,typed);
    if let Ok(image)=typed{
        part2_associated_output_normal(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));
        part2_associated_output_frames(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
            part2_apply_associated_output(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits)));
    }
    part2_cold_bind(|events|part2_typed_layout_run(input,decoded,requested.2,limits,events),
        |image:Part1DecodedTypedImage,rest|part2_associated_output_run(image,Some(header),crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest),typed,part2_jpx_selected_finish(input,header,requested,limits,decoded));
}
pub(crate) open spec fn part2_jpx_selected_layout_run(source: Part2CodestreamSource, header: Part2AssociatedHeader,
    layout: Part1CompleteLayout, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)> {
    let size=layout.0.image_size;
    match part2_validate_selected_header(header.1,size.geometry.0,size.geometry.1,size.components,size.uniform_bit_depth,size.uniform_signed,source.1) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>part2_jpip_snapshot_bind(part2_layout_decode_run(part2_decoder_input_from_raw(layout),Some(requested),limits,events),
            |decoded:Part1DecodedImageModel,rest|part2_jpx_selected_finish_run(part2_decoder_input_from_raw(layout),header,requested,limits,decoded,rest)),
    }
}
pub(crate) proof fn part2_jpx_selected_layout_normal(source: Part2CodestreamSource, header: Part2AssociatedHeader,
    layout: Part1CompleteLayout, limits: &crate::ResourceLimits, requested: Part2DecodeSelection)
    ensures part2_cold_framed(|events|part2_jpx_selected_layout_run(source,header,layout,limits,requested,events),
        part2_decode_jpx_selected_layout(source,header,layout,limits,requested)),
{
    reveal(part2_layout_decode_result);
    let size=layout.0.image_size;
    let result=part2_decode_jpx_selected_layout(source,header,layout,limits,requested);
    if part2_validate_selected_header(header.1,size.geometry.0,size.geometry.1,size.components,size.uniform_bit_depth,size.uniform_signed,source.1).is_err() {
        part2_cold_pure::<(Part1DecodedTypedImage,Option<Part2AssociatedHeader>)>(result);
    }else{
        let input=part2_decoder_input_from_raw(layout);
        part2_layout_decode_normal(input,Some(requested),limits);
        let decoded=part2_decode_layout_selected_value_input(input,requested,limits);
        if let Ok(value)=decoded {
            part2_jpx_selected_finish_normal(input,header,requested,limits,value);
            part2_decode_eta(|events|part2_jpx_selected_finish_run(input,header,requested,limits,value,events),part2_jpx_selected_finish(input,header,requested,limits,value));
        }
        part2_cold_bind(|events|part2_layout_decode_run(input,Some(requested),limits,events),
            |decoded:Part1DecodedImageModel,rest|part2_jpx_selected_finish_run(input,header,requested,limits,decoded,rest),decoded,result);
    }
}
pub(crate) open spec fn part2_jpx_selected_cold_run(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    requested: Part2DecodeSelection, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)> {
    match part2_jpx_cold_header(input, index) {
        Err(error) => Some((Err(error), events)),
        Ok((source, header)) => part2_jpip_snapshot_bind(part2_cold_parse(source.0, limits, 6, index, events),
            |layout: Part1CompleteLayout, rest|part2_jpx_selected_layout_run(source, header, layout, limits, requested,rest)),
    }
}

pub(crate) open spec fn part2_jpx_cold_result(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    result: Part2AssociatedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_jpx_cold_run(input, index, limits, events), result)
}

pub(crate) open spec fn part2_jpx_selected_cold_result(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    requested: Part2DecodeSelection, result: Part2AssociatedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_jpx_selected_cold_run(input, index, limits, requested, events), result)
}

pub(crate) proof fn part2_jpx_cold_normal(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
)
    ensures part2_jpx_cold_result(input, index, limits, part2_decode_jpx_codestream(input, index, limits)),
{
    part2_decode_jpx_codestream_unfold(input, index, limits);
    reveal(part2_decode_jpx_source);
    reveal(part2_decode_jpx_associated);
    match part2_jpx_cold_header(input, index) {
        Err(error) => { part2_cold_pure::<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)>(Err(error)); },
        Ok((source, header)) => {
            part2_decode_jpx_source_unfold(source, input.2, limits);
            part2_decode_jpx_associated_unfold(source, header, limits);
            let parsed = part1_parse_info(source.0, limits);
            part2_cold_info_normal(source.0, limits, 5, index);
            if let Ok(info) = parsed {
                match part2_jpx_cold_validate(source, header, info) {
                    Err(error) => { part2_cold_pure::<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)>(Err(error)); },
                    Ok(()) => {
                        let decoded = part2_decode_raw_codestream(source.0, limits, None);
                        part2_decode_raw_cold_normal(source.0, limits, None);
                        part2_decode_raw_cold_frames(source.0, limits, None, decoded);
                        if let Ok(image) = decoded {
                            part2_associated_output_normal(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));
                            part2_associated_output_frames(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
                                part2_apply_associated_output(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits)));
                        }
                        part2_cold_bind(
                            |events| part2_decode_raw_cold_run(source.0, limits, None, events),
                            |image: Part1DecodedTypedImage, rest|part2_associated_output_run(image, Some(header),
                                crate::limits::resource_component_limit(limits),
                                crate::limits::resource_decoded_bytes_limit(limits),rest),
                            decoded, match decoded { Err(error) => Err(error), Ok(image) =>
                                part2_apply_associated_output(image, Some(header),
                                    crate::limits::resource_component_limit(limits),
                                    crate::limits::resource_decoded_bytes_limit(limits)) });
                    },
                }
            }
            part2_cold_bind(
                |events| part2_cold_info(source.0, limits, 5, index, events),
                |info: Part2RawCodestreamInfo, rest| match part2_jpx_cold_validate(source, header, info) {
                    Err(error) => Some((Err(error), rest)),
                    Ok(()) => part2_jpx_cold_image(source, header, limits, rest),
                }, parsed, part2_decode_jpx_codestream(input, index, limits));
        },
    }
}

pub(crate) proof fn part2_jpx_selected_cold_normal(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
)
    ensures part2_jpx_selected_cold_result(
        input, index, limits, requested, part2_decode_jpx_selected_file(input, index, limits, requested)),
{
    part2_decode_jpx_selected_file_unfold(input, index, limits, requested);
    match part2_jpx_cold_header(input, index) {
        Err(error) => { part2_cold_pure::<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>)>(Err(error)); },
        Ok((source, header)) => {
            part1_parse_layout_cold_normal(source.0, limits);
            let parsed=part1_parse_layout(source.0,limits);
            part2_cold_parse_actual(source.0,limits,6,index,parsed);
            if let Ok(layout)=parsed {
                part2_jpx_selected_layout_normal(source,header,layout,limits,requested);
                part2_decode_eta(|events|part2_jpx_selected_layout_run(source,header,layout,limits,requested,events),
                    part2_decode_jpx_selected_layout(source,header,layout,limits,requested));
            }
            part2_cold_bind(|events|part2_cold_parse(source.0,limits,6,index,events),
                |layout:Part1CompleteLayout,rest|part2_jpx_selected_layout_run(source,header,layout,limits,requested,rest),parsed,
                part2_decode_jpx_selected_file(input,index,limits,requested));
        },
    }
}

pub(crate) proof fn part2_jpx_cold_info_error(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    source: Part2CodestreamSource, header: Part2AssociatedHeader, error: crate::DecodeError,
)
    requires part2_jpx_cold_header(input, index) == Ok((source, header)),
        part1_parse_info_cold_result(source.0, limits, Err(error)),
    ensures part2_jpx_cold_result(input, index, limits, Err(error)),
{
    part2_cold_info_actual(source.0, limits, 5, index, Err(error));
    part2_cold_bind(
        |events| part2_cold_info(source.0, limits, 5, index, events),
        |info: Part2RawCodestreamInfo, rest| match part2_jpx_cold_validate(source, header, info) {
            Err(error) => Some((Err(error), rest)),
            Ok(()) => part2_jpx_cold_image(source, header, limits, rest),
        }, Err(error), Err(error));
}

pub(crate) proof fn part2_jpx_cold_image_actual(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
    source: Part2CodestreamSource, header: Part2AssociatedHeader, info: Part2RawCodestreamInfo,
    decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_jpx_cold_header(input, index) == Ok((source, header)),
        part1_parse_info_cold_result(source.0, limits, Ok(info)),
        part2_jpx_cold_validate(source, header, info) == Ok(()),
        part2_decode_raw_cold_result(source.0, limits, None, decoded),
    ensures part2_jpx_cold_result(input, index, limits, match decoded {
        Err(error) => Err(error), Ok(image) => part2_apply_associated_output(image, Some(header),
            crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
    }),
{
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_apply_associated_output(image, Some(header),
            crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
    };
    part2_cold_info_actual(source.0, limits, 5, index, Ok(info));
    part2_decode_raw_cold_frames(source.0, limits, None, decoded);
    if let Ok(image) = decoded {
        part2_associated_output_normal(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));
        part2_associated_output_frames(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
            part2_apply_associated_output(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits)));
    }
    part2_cold_bind(
        |events| part2_decode_raw_cold_run(source.0, limits, None, events),
        |image: Part1DecodedTypedImage, rest|part2_associated_output_run(image, Some(header),
            crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest), decoded, result);
    part2_cold_bind(
        |events| part2_cold_info(source.0, limits, 5, index, events),
        |info: Part2RawCodestreamInfo, rest| match part2_jpx_cold_validate(source, header, info) {
            Err(error) => Some((Err(error), rest)),
            Ok(()) => part2_jpx_cold_image(source, header, limits, rest),
        }, Ok(info), result);
}

pub(crate) proof fn part2_jpx_selected_cold_actual(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    source: Part2CodestreamSource, header: Part2AssociatedHeader, parsed: Part1CompleteLayoutResult,
)
    requires part2_jpx_cold_header(input, index) == Ok((source, header)),
        part1_parse_layout_cold_result(source.0, limits, parsed),
    ensures part2_jpx_selected_cold_result(input, index, limits, requested, match parsed {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_jpx_selected_layout(source, header, layout, limits, requested),
    }),
{
    part2_cold_parse_actual(source.0,limits,6,index,parsed);
    if let Ok(layout)=parsed {
        part2_jpx_selected_layout_normal(source,header,layout,limits,requested);
        part2_decode_eta(|events|part2_jpx_selected_layout_run(source,header,layout,limits,requested,events),
            part2_decode_jpx_selected_layout(source,header,layout,limits,requested));
    }
    part2_cold_bind(|events|part2_cold_parse(source.0,limits,6,index,events),
        |layout:Part1CompleteLayout,rest|part2_jpx_selected_layout_run(source,header,layout,limits,requested,rest),parsed,
        match parsed {Err(error)=>Err(error),Ok(layout)=>part2_decode_jpx_selected_layout(source,header,layout,limits,requested)});
}

pub(crate) proof fn part2_jpx_selected_decode_error(input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, requested: Part2DecodeSelection,
    source: Part2CodestreamSource, header: Part2AssociatedHeader, error: crate::DecodeError)
    requires part2_jpx_cold_header(input,index)==Ok((source,header)),part1_parse_layout(source.0,limits).is_ok(),
        part1_parse_layout_cold_result(source.0,limits,part1_parse_layout(source.0,limits)),
        match part1_parse_layout(source.0,limits) {
            Err(_)=>false,Ok(layout)=>part2_jpx_cold_validate(source,header,(layout.0,layout.1,layout.2,layout.3))==Ok(())
                &&part2_layout_decode_result(part2_decoder_input_from_raw(layout),Some(requested),limits,Err(error)),
        },
    ensures part2_jpx_selected_cold_result(input,index,limits,requested,Err(error)),
{
    reveal(part2_layout_decode_result);
    let parsed=part1_parse_layout(source.0,limits);
    part2_cold_parse_actual(source.0,limits,6,index,parsed);
    if let Ok(layout)=parsed {
        let decoded=part2_decoder_input_from_raw(layout);
        part2_cold_bind(|events|part2_layout_decode_run(decoded,Some(requested),limits,events),
            |image:Part1DecodedImageModel,rest|part2_jpx_selected_finish_run(decoded,header,requested,limits,image,rest),Err(error),Err(error));
    }
    part2_cold_bind(|events|part2_cold_parse(source.0,limits,6,index,events),
        |layout:Part1CompleteLayout,rest|part2_jpx_selected_layout_run(source,header,layout,limits,requested,rest),parsed,Err(error));
}

pub(crate) proof fn part2_jpx_selected_conversion_error(input:Part2JpxDecodeInput,index:usize,limits:&crate::ResourceLimits,requested:Part2DecodeSelection,
    source:Part2CodestreamSource,header:Part2AssociatedHeader,layout:Part1CompleteLayout,decoded:Part1DecodedImageModel,error:crate::DecodeError)
    requires part2_jpx_cold_header(input,index)==Ok((source,header)),
        part1_parse_layout_cold_result(source.0,limits,Ok(layout)),
        part2_jpx_cold_validate(source,header,(layout.0,layout.1,layout.2,layout.3))==Ok(()),
        part2_layout_decode_result(part2_decoder_input_from_raw(layout),Some(requested),limits,Ok(decoded)),
        part2_typed_layout_result(part2_decoder_input_from_raw(layout),decoded,requested.2,limits,Err(error)),
    ensures part2_jpx_selected_cold_result(input,index,limits,requested,Err(error)),
{
    reveal(part2_layout_decode_result);
    let parsed=part2_decoder_input_from_raw(layout);
    part2_typed_layout_frames(parsed,decoded,requested.2,limits,Err(error));
    part2_cold_bind(|events|part2_typed_layout_run(parsed,decoded,requested.2,limits,events),
        |image:Part1DecodedTypedImage,rest|part2_associated_output_run(image,Some(header),crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest),Err(error),Err(error));
    part2_cold_bind(|events|part2_layout_decode_run(parsed,Some(requested),limits,events),
        |image:Part1DecodedImageModel,rest|part2_jpx_selected_finish_run(parsed,header,requested,limits,image,rest),Ok(decoded),Err(error));
    part2_decode_eta(|events|part2_jpx_selected_layout_run(source,header,layout,limits,requested,events),Err(error));
    part2_cold_parse_actual(source.0,limits,6,index,Ok(layout));
    part2_cold_bind(|events|part2_cold_parse(source.0,limits,6,index,events),
        |layout:Part1CompleteLayout,rest|part2_jpx_selected_layout_run(source,header,layout,limits,requested,rest),Ok(layout),Err(error));
}
pub(crate) proof fn part2_jpx_cold_output_error(input:Part2JpxDecodeInput,index:usize,limits:&crate::ResourceLimits,
    source:Part2CodestreamSource,header:Part2AssociatedHeader,info:Part2RawCodestreamInfo,image:Part1DecodedTypedImage,error:crate::DecodeError)
    requires part2_jpx_cold_header(input,index)==Ok((source,header)),part1_parse_info_cold_result(source.0,limits,Ok(info)),
        part2_jpx_cold_validate(source,header,info)==Ok(()),part2_decode_raw_cold_result(source.0,limits,None,Ok(image)),
        part2_associated_output_result(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),Err(error)),
    ensures part2_jpx_cold_result(input,index,limits,Err(error)),
{
    part2_cold_info_actual(source.0,limits,5,index,Ok(info));
    part2_decode_raw_cold_frames(source.0,limits,None,Ok(image));
    part2_associated_output_frames(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),Err(error));
    part2_cold_bind(|events|part2_decode_raw_cold_run(source.0,limits,None,events),
        |image:Part1DecodedTypedImage,rest|part2_associated_output_run(image,Some(header),crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest),Ok(image),Err(error));
    part2_decode_eta(|events|part2_jpx_cold_image(source,header,limits,events),Err(error));
    part2_cold_bind(|events|part2_cold_info(source.0,limits,5,index,events),
        |info:Part2RawCodestreamInfo,rest|match part2_jpx_cold_validate(source,header,info){
            Err(error)=>Some((Err(error),rest)),Ok(())=>part2_jpx_cold_image(source,header,limits,rest),
        },Ok(info),Err(error));
}
pub(crate) proof fn part2_jpx_selected_output_error(input:Part2JpxDecodeInput,index:usize,limits:&crate::ResourceLimits,requested:Part2DecodeSelection,
    source:Part2CodestreamSource,header:Part2AssociatedHeader,layout:Part1CompleteLayout,centered:Part1DecodedImageModel,image:Part1DecodedTypedImage,error:crate::DecodeError)
    requires part2_jpx_cold_header(input,index)==Ok((source,header)),part1_parse_layout_cold_result(source.0,limits,Ok(layout)),
        part2_jpx_cold_validate(source,header,(layout.0,layout.1,layout.2,layout.3))==Ok(()),
        part2_layout_decode_result(part2_decoder_input_from_raw(layout),Some(requested),limits,Ok(centered)),
        part2_typed_layout_result(part2_decoder_input_from_raw(layout),centered,requested.2,limits,Ok(image)),
        part2_associated_output_result(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),Err(error)),
    ensures part2_jpx_selected_cold_result(input,index,limits,requested,Err(error)),
{
    reveal(part2_layout_decode_result);
    let parsed=part2_decoder_input_from_raw(layout);
    part2_associated_output_frames(image,Some(header),crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),Err(error));
    part2_typed_layout_frames(parsed,centered,requested.2,limits,Ok(image));
    part2_cold_bind(|events|part2_typed_layout_run(parsed,centered,requested.2,limits,events),
        |image:Part1DecodedTypedImage,rest|part2_associated_output_run(image,Some(header),crate::limits::resource_component_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits),rest),Ok(image),Err(error));
    part2_decode_eta(|events|part2_jpx_selected_finish_run(parsed,header,requested,limits,centered,events),Err(error));
    part2_cold_bind(|events|part2_layout_decode_run(parsed,Some(requested),limits,events),
        |centered:Part1DecodedImageModel,rest|part2_jpx_selected_finish_run(parsed,header,requested,limits,centered,rest),Ok(centered),Err(error));
    part2_decode_eta(|events|part2_jpx_selected_layout_run(source,header,layout,limits,requested,events),Err(error));
    part2_cold_parse_actual(source.0,limits,6,index,Ok(layout));
    part2_cold_bind(|events|part2_cold_parse(source.0,limits,6,index,events),
        |layout:Part1CompleteLayout,rest|part2_jpx_selected_layout_run(source,header,layout,limits,requested,rest),Ok(layout),Err(error));
}
pub type Part2FileType = (crate::jp2::BoxType, u32, Seq<crate::jp2::BoxType>);
pub type Part2CodestreamSource = (Seq<u8>, u64, Option<(u64, Option<Part2AssociatedHeader>)>);
pub type Part2JpxDecodeInput = (Part2FileType, Seq<Part2CodestreamSource>, Part2AssociatedHeader);
pub type Part2AssociatedImageResult =
    Result<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>), crate::DecodeError>;

pub open spec fn part2_file_type_compatible(input: Part2FileType, brand: crate::jp2::BoxType) -> bool {
    input.0 == brand || input.2.contains(brand)
}

pub open spec fn part2_file_type_jpx(input: Part2FileType) -> bool {
    part2_file_type_compatible(input, crate::jp2::BoxType::JPX_BRAND)
        || part2_file_type_compatible(input, crate::jp2::BoxType::JPX_BASELINE_BRAND)
}

pub open spec fn part2_jpx_codestream_lookup(input: Seq<Part2CodestreamSource>, index: usize)
    -> Result<Part2CodestreamSource, crate::DecodeError>
{
    if index < input.len() { Ok(input[index as int]) }
    else { Err(crate::DecodeError::CodestreamIndexOutOfRange { index, codestreams: input.len() as usize }) }
}

#[verifier::opaque]
pub(crate) open spec fn part2_decode_jpx_associated(
    source: Part2CodestreamSource, header: Part2AssociatedHeader, limits: &crate::ResourceLimits,
) -> Part2AssociatedImageResult {
    match part1_parse_info(source.0, limits) {
        Err(error) => Err(error),
        Ok(info) => match part2_validate_selected_header(
            header.1, info.0.image_size.geometry.0, info.0.image_size.geometry.1,
            info.0.image_size.components, info.0.image_size.uniform_bit_depth,
            info.0.image_size.uniform_signed, source.1,
        ) {
            Err(error) => Err(error),
            Ok(()) => match part2_decode_raw_codestream(source.0, limits, None) {
                Err(error) => Err(error),
                Ok(image) => part2_apply_associated_output(image, Some(header),
                    crate::limits::resource_component_limit(limits),
                    crate::limits::resource_decoded_bytes_limit(limits)),
            },
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_decode_jpx_source(
    source: Part2CodestreamSource, fallback: Part2AssociatedHeader, limits: &crate::ResourceLimits,
) -> Part2AssociatedImageResult {
    match part2_associated_codestream_header(source.2, fallback) {
        Err(error) => Err(error),
        Ok(header) => part2_decode_jpx_associated(source, header, limits),
    }
}

pub(crate) proof fn part2_decode_jpx_source_unfold(
    source: Part2CodestreamSource, fallback: Part2AssociatedHeader, limits: &crate::ResourceLimits,
)
    ensures part2_decode_jpx_source(source, fallback, limits) ==
        match part2_associated_codestream_header(source.2, fallback) {
            Err(error) => Err(error),
            Ok(header) => part2_decode_jpx_associated(source, header, limits),
        },
{
    reveal(part2_decode_jpx_source);
}

pub(crate) proof fn part2_decode_jpx_associated_unfold(
    source: Part2CodestreamSource, header: Part2AssociatedHeader, limits: &crate::ResourceLimits,
)
    ensures part2_decode_jpx_associated(source, header, limits) == match part1_parse_info(source.0, limits) {
        Err(error) => Err(error),
        Ok(info) => match part2_validate_selected_header(
            header.1, info.0.image_size.geometry.0, info.0.image_size.geometry.1,
            info.0.image_size.components, info.0.image_size.uniform_bit_depth,
            info.0.image_size.uniform_signed, source.1,
        ) {
            Err(error) => Err(error),
            Ok(()) => match part2_decode_raw_codestream(source.0, limits, None) {
                Err(error) => Err(error),
                Ok(image) => part2_apply_associated_output(image, Some(header),
                    crate::limits::resource_component_limit(limits),
                    crate::limits::resource_decoded_bytes_limit(limits)),
            },
        },
    },
{
    reveal(part2_decode_jpx_associated);
}

pub closed spec fn part2_decode_jpx_codestream(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
) -> Part2AssociatedImageResult {
    if !part2_file_type_jpx(input.0) {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidProfile })
    } else {
        match part2_jpx_codestream_lookup(input.1, index) {
            Err(error) => Err(error),
            Ok(source) => part2_decode_jpx_source(source, input.2, limits),
        }
    }
}

pub(crate) proof fn part2_decode_jpx_codestream_unfold(
    input: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits,
)
    ensures part2_decode_jpx_codestream(input, index, limits) == {
        if !part2_file_type_jpx(input.0) {
            Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidProfile })
        } else {
            match part2_jpx_codestream_lookup(input.1, index) {
                Err(error) => Err(error),
                Ok(source) => part2_decode_jpx_source(source, input.2, limits),
            }
        }
    },
{
}

pub closed spec fn part2_decode_jpx_layer(
    input: Part2JpxDecodeInput, index: usize, color_override: Option<crate::jp2::ColorMethod>,
    limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    match part2_decode_jpx_codestream(input, index, limits) {
        Err(error) => Err(error),
        Ok(decoded) => {
            let color = match color_override {
                Some(color) => color,
                None => match decoded.1 { Some(header) => header.2, None => input.2.2 },
            };
            color_convert_jp2(decoded.0.1, decoded.0.2, decoded.0.0, color,
                crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits))
        },
    }
}

pub(crate) open spec fn part2_jpx_layer_cold_finish(
    input: Part2JpxDecodeInput, color_override: Option<crate::jp2::ColorMethod>,
    decoded: (Part1DecodedTypedImage, Option<Part2AssociatedHeader>), limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    let color = match color_override {
        Some(color) => color,
        None => match decoded.1 { Some(header) => header.2, None => input.2.2 },
    };
    color_convert_jp2(decoded.0.1, decoded.0.2, decoded.0.0, color,
        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits))
}

pub(crate) open spec fn part2_jpx_layer_color_context(input:Part2JpxDecodeInput,color_override:Option<crate::jp2::ColorMethod>,
    decoded:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),limits:&crate::ResourceLimits)->Part2ColorConvertContext {
    let method=match color_override {Some(color)=>color,None=>match decoded.1 {Some(header)=>header.2,None=>input.2.2}};
    Part2ColorConvertContext {image:decoded.0,method,bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits)}
}
pub(crate) open spec fn part2_jpx_layer_cold_run(
    input: Part2JpxDecodeInput, index: usize, color_override: Option<crate::jp2::ColorMethod>,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_jpx_cold_run(input, index, limits, events),
        |decoded, tail| part2_color_convert_storage_run(part2_jpx_layer_color_context(input,color_override,decoded,limits),tail))
}

pub(crate) open spec fn part2_jpx_layer_cold_result(
    input: Part2JpxDecodeInput, index: usize, color_override: Option<crate::jp2::ColorMethod>,
    limits: &crate::ResourceLimits, result: Part2ConvertedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_jpx_layer_cold_run(input, index, color_override, limits, events), result)
}

pub(crate) proof fn part2_jpx_layer_cold_actual(
    input: Part2JpxDecodeInput, index: usize, color_override: Option<crate::jp2::ColorMethod>,
    limits: &crate::ResourceLimits, decoded: Part2AssociatedImageResult,
)
    requires part2_jpx_cold_result(input, index, limits, decoded),
    ensures part2_jpx_layer_cold_result(input, index, color_override, limits, match decoded {
        Err(error) => Err(error), Ok(value) => part2_jpx_layer_cold_finish(input, color_override, value, limits),
    }),
{
    if let Ok(value) = decoded {
        let context=part2_jpx_layer_color_context(input,color_override,value,limits);
        part2_color_convert_storage_normal(context);
        part2_color_convert_storage_frames(context,part2_jpx_layer_cold_finish(input,color_override,value,limits));
    }
    part2_cold_bind(
        |events| part2_jpx_cold_run(input, index, limits, events),
        |value, tail| part2_color_convert_storage_run(part2_jpx_layer_color_context(input,color_override,value,limits),tail),
        decoded, match decoded { Err(error) => Err(error),
            Ok(value) => part2_jpx_layer_cold_finish(input, color_override, value, limits) });
}
pub(crate) proof fn part2_jpx_layer_color_actual(input:Part2JpxDecodeInput,index:usize,color_override:Option<crate::jp2::ColorMethod>,
    limits:&crate::ResourceLimits,decoded:(Part1DecodedTypedImage,Option<Part2AssociatedHeader>),result:Part2ConvertedImageResult)
    requires part2_jpx_cold_result(input,index,limits,Ok(decoded)),
        part2_color_convert_storage_result(part2_jpx_layer_color_context(input,color_override,decoded,limits),result),
    ensures part2_jpx_layer_cold_result(input,index,color_override,limits,result),
{
    part2_color_convert_storage_frames(part2_jpx_layer_color_context(input,color_override,decoded,limits),result);
    part2_cold_bind(|events|part2_jpx_cold_run(input,index,limits,events),
        |decoded,tail|part2_color_convert_storage_run(part2_jpx_layer_color_context(input,color_override,decoded,limits),tail),Ok(decoded),result);
}

pub(crate) proof fn part2_jpx_layer_cold_normal(
    input: Part2JpxDecodeInput, index: usize, color_override: Option<crate::jp2::ColorMethod>,
    limits: &crate::ResourceLimits,
)
    ensures part2_jpx_layer_cold_result(input, index, color_override, limits,
        part2_decode_jpx_layer(input, index, color_override, limits)),
{
    part2_decode_jpx_layer_unfold(input, index, color_override, limits);
    part2_jpx_cold_normal(input, index, limits);
    part2_jpx_layer_cold_actual(input, index, color_override, limits, part2_decode_jpx_codestream(input, index, limits));
}

pub(crate) proof fn part2_decode_jpx_layer_unfold(
    input: Part2JpxDecodeInput, index: usize, color_override: Option<crate::jp2::ColorMethod>,
    limits: &crate::ResourceLimits,
)
    ensures part2_decode_jpx_layer(input, index, color_override, limits)
        == match part2_decode_jpx_codestream(input, index, limits) {
            Err(error) => Err(error),
            Ok(decoded) => {
                let color = match color_override {
                    Some(color) => color,
                    None => match decoded.1 { Some(header) => header.2, None => input.2.2 },
                };
                color_convert_jp2(decoded.0.1, decoded.0.2, decoded.0.0, color,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits))
            },
        },
{
}

}
