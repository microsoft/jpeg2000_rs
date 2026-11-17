//! Output continuations after source-derived packet preparation and decoding.
use super::*;
verus! {
pub(crate) open spec fn part2_typed_decode_finish(bytes: usize, input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>,
    limits: &crate::ResourceLimits, decoded: Part1DecodedImageModel) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    let discard = match requested { None => 0u8, Some(selection) => selection.2 };
    match part2_typed_layout_input(input, decoded, discard, limits) {
        Err(error) => Err(error),
        Ok(image) => part2_typed_decode_output(bytes,input,image),
    }
}
pub(crate) open spec fn part2_typed_decode_output(bytes:usize,input:Part2DecoderLayoutInput,image:Part1DecodedTypedImage)->Result<Part1DecodedTypedImage,crate::DecodeError> {
    match part1_validate_typed_output_shape(bytes, input.parts.len() as usize, input.size.components, image) {
            Err(error) => Err(error), Ok(()) => Ok(image),
    }
}
pub(crate) open spec fn part2_typed_decode_finish_run(bytes:usize,input:Part2DecoderLayoutInput,requested:Option<Part2DecodeSelection>,limits:&crate::ResourceLimits,
    decoded:Part1DecodedImageModel,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1DecodedTypedImage> {
    let discard=match requested{None=>0u8,Some(selection)=>selection.2};
    part2_jpip_snapshot_bind(part2_typed_layout_run(input,decoded,discard,limits,events),
        |image:Part1DecodedTypedImage,rest|Some((part2_typed_decode_output(bytes,input,image),rest)))
}
pub(crate) proof fn part2_typed_decode_finish_normal(bytes:usize,input:Part2DecoderLayoutInput,requested:Option<Part2DecodeSelection>,limits:&crate::ResourceLimits,decoded:Part1DecodedImageModel)
    ensures part2_cold_framed(|events|part2_typed_decode_finish_run(bytes,input,requested,limits,decoded,events),part2_typed_decode_finish(bytes,input,requested,limits,decoded)),
{
    let discard=match requested{None=>0u8,Some(selection)=>selection.2};
    let typed=part2_typed_layout_input(input,decoded,discard,limits);
    part2_typed_layout_normal(input,decoded,discard,limits);part2_typed_layout_frames(input,decoded,discard,limits,typed);
    if let Ok(image)=typed{part2_cold_pure(part2_typed_decode_output(bytes,input,image));}
    part2_cold_bind(|events|part2_typed_layout_run(input,decoded,discard,limits,events),
        |image:Part1DecodedTypedImage,rest|Some((part2_typed_decode_output(bytes,input,image),rest)),typed,part2_typed_decode_finish(bytes,input,requested,limits,decoded));
}
pub(crate) proof fn part2_typed_decode_finish_error(bytes:usize,input:Part2DecoderLayoutInput,requested:Option<Part2DecodeSelection>,limits:&crate::ResourceLimits,
    decoded:Part1DecodedImageModel,error:crate::DecodeError)
    requires part2_typed_layout_result(input,decoded,match requested{None=>0u8,Some(selection)=>selection.2},limits,Err(error)),
    ensures part2_cold_framed(|events|part2_typed_decode_finish_run(bytes,input,requested,limits,decoded,events),Err(error)),
{
    let discard=match requested{None=>0u8,Some(selection)=>selection.2};
    part2_typed_layout_frames(input,decoded,discard,limits,Err(error));
    part2_cold_bind(|events|part2_typed_layout_run(input,decoded,discard,limits,events),
        |image:Part1DecodedTypedImage,rest|Some((part2_typed_decode_output(bytes,input,image),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_typed_decode_run(bytes: usize, input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_layout_decode_run(input, requested, limits, events),
        |decoded: Part1DecodedImageModel, rest| part2_typed_decode_finish_run(bytes,input,requested,limits,decoded,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_typed_decode_result(bytes: usize, input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>,
    limits: &crate::ResourceLimits, result: Result<Part1DecodedTypedImage, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_typed_decode_run(bytes, input, requested, limits, events), result)
}
pub(crate) proof fn part2_typed_decode_normal(bytes: usize, input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>, limits: &crate::ResourceLimits)
    ensures part2_typed_decode_result(bytes, input, requested, limits, part2_decode_typed_layout_value_input(bytes, input, limits, requested)),
{
    reveal(part2_typed_decode_result); reveal(part2_layout_decode_result);
    part2_layout_decode_normal(input, requested, limits);
    let decoded = match requested { None => part2_decode_layout_input(input, limits), Some(selection) => part2_decode_layout_selected_value_input(input, selection, limits) };
    if let Ok(value) = decoded {
        part2_typed_decode_finish_normal(bytes,input,requested,limits,value);
        part2_decode_eta(|events|part2_typed_decode_finish_run(bytes,input,requested,limits,value,events),part2_typed_decode_finish(bytes,input,requested,limits,value));
    }
    part2_cold_bind(|events| part2_layout_decode_run(input, requested, limits, events),
        |decoded: Part1DecodedImageModel, rest| part2_typed_decode_finish_run(bytes,input,requested,limits,decoded,rest),
        decoded, part2_decode_typed_layout_value_input(bytes, input, limits, requested));
}
pub(crate) proof fn part2_typed_decode_error(bytes: usize, input: Part2DecoderLayoutInput, requested: Option<Part2DecodeSelection>,
    limits: &crate::ResourceLimits, error: crate::DecodeError)
    requires part2_layout_decode_result(input, requested, limits, Err(error)),
    ensures part2_typed_decode_result(bytes, input, requested, limits, Err(error)),
{
    reveal(part2_typed_decode_result); reveal(part2_layout_decode_result);
    part2_cold_bind(|events| part2_layout_decode_run(input, requested, limits, events),
        |decoded: Part1DecodedImageModel, rest| part2_typed_decode_finish_run(bytes,input,requested,limits,decoded,rest), Err(error), Err(error));
}
pub(crate) proof fn part2_typed_decode_conversion_error(bytes:usize,input:Part2DecoderLayoutInput,requested:Option<Part2DecodeSelection>,limits:&crate::ResourceLimits,
    decoded:Part1DecodedImageModel,error:crate::DecodeError)
    requires part2_layout_decode_result(input,requested,limits,Ok(decoded)),
        part2_typed_layout_result(input,decoded,match requested{None=>0u8,Some(selection)=>selection.2},limits,Err(error)),
    ensures part2_typed_decode_result(bytes,input,requested,limits,Err(error)),
{
    reveal(part2_typed_decode_result);reveal(part2_layout_decode_result);
    part2_typed_decode_finish_error(bytes,input,requested,limits,decoded,error);
    part2_decode_eta(|events|part2_typed_decode_finish_run(bytes,input,requested,limits,decoded,events),Err(error));
    part2_cold_bind(|events|part2_layout_decode_run(input,requested,limits,events),
        |image:Part1DecodedImageModel,rest|part2_typed_decode_finish_run(bytes,input,requested,limits,image,rest),Ok(decoded),Err(error));
}
pub(crate) open spec fn part2_reconstructed_decode_finish(bytes: usize, input: Part2DecoderLayoutInput, decoded: Part1DecodedImageModel)
    -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_validate_reconstruction_transforms(input) {
        Err(error) => Err(error), Ok(()) => match part1_validate_reconstructed_output_shape(bytes, input.parts.len() as usize, input.size.components, decoded) {
            Err(error) => Err(error), Ok(()) => Ok(decoded),
        },
    }
}
pub(crate) open spec fn part2_reconstructed_decode_run(bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_layout_decode_run(input, None, limits, events),
        |decoded: Part1DecodedImageModel, rest| Some((part2_reconstructed_decode_finish(bytes, input, decoded), rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_reconstructed_decode_result(bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
    result: Result<Part1DecodedImageModel, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_reconstructed_decode_run(bytes, input, limits, events), result)
}
pub(crate) proof fn part2_reconstructed_decode_normal(bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits)
    ensures part2_reconstructed_decode_result(bytes, input, limits, part2_decode_reconstructed_layout_input(bytes, input, limits)),
{
    reveal(part2_reconstructed_decode_result); reveal(part2_layout_decode_result);
    part2_layout_decode_normal(input, None, limits);
    let decoded = part2_decode_layout_input(input, limits);
    if let Ok(value) = decoded { part2_cold_pure(part2_reconstructed_decode_finish(bytes, input, value)); }
    part2_cold_bind(|events| part2_layout_decode_run(input, None, limits, events),
        |decoded: Part1DecodedImageModel, rest| Some((part2_reconstructed_decode_finish(bytes, input, decoded), rest)),
        decoded, part2_decode_reconstructed_layout_input(bytes, input, limits));
}
pub(crate) proof fn part2_reconstructed_decode_error(bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits, error: crate::DecodeError)
    requires part2_layout_decode_result(input, None, limits, Err(error)),
    ensures part2_reconstructed_decode_result(bytes, input, limits, Err(error)),
{
    reveal(part2_reconstructed_decode_result); reveal(part2_layout_decode_result);
    part2_cold_bind(|events| part2_layout_decode_run(input, None, limits, events),
        |decoded: Part1DecodedImageModel, rest| Some((part2_reconstructed_decode_finish(bytes, input, decoded), rest)), Err(error), Err(error));
}
}
