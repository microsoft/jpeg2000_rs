use super::*;
verus! {
pub open spec fn color_esrgb8_compatible(image: Part1DecodedTypedImage, method: crate::jp2::ColorMethod) -> bool {
    method == (crate::jp2::ColorMethod::Enumerated { color_space: 20 })
        && image.1.len() == 3
        && forall|i: int| 0 <= i < image.1.len() ==> {
            let component = #[trigger] image.1[i];
            component.info.precision == 8 && !component.info.signed
                && component.info.x_subsampling == 1 && component.info.y_subsampling == 1
                && component.info.x_registration == 0 && component.info.y_registration == 0
                && component.width == image.0.0 && component.height == image.0.1
        }
}
pub open spec fn color_compatible_context(context: Part2ColorConvertContext) -> Part2ColorConvertContext {
    if color_esrgb8_compatible(context.image, context.method) {
        Part2ColorConvertContext { method: crate::jp2::ColorMethod::Enumerated { color_space: 16 }, ..context }
    } else { context }
}
pub open spec fn color_compatible_wrap(
    result: Part2ConvertedImageResult, assumed: bool,
) -> Result<(Part2ConvertedImage, crate::color::ColorRecovery), crate::DecodeError> {
    match result {
        Err(error) => Err(error),
        Ok(image) => Ok((image, crate::color::ColorRecovery { assumed_srgb_for_8bit_esrgb: assumed })),
    }
}
pub open spec fn color_compatible_value(context: Part2ColorConvertContext)
    -> Result<(Part2ConvertedImage, crate::color::ColorRecovery), crate::DecodeError> {
    let interpreted = color_compatible_context(context);
    color_compatible_wrap(color_convert_jp2(interpreted.image.1, interpreted.image.2,
        interpreted.image.0, interpreted.method, interpreted.bytes, interpreted.work),
        color_esrgb8_compatible(context.image,context.method))
}
pub(crate) open spec fn color_compatible_run(context: Part2ColorConvertContext, events: Seq<Part2JpipSnapshotEvent>)
    -> Part2ColdRun<(Part2ConvertedImage, crate::color::ColorRecovery)> {
    part2_jpip_snapshot_bind(part2_color_convert_storage_run(color_compatible_context(context),events),
        |image: Part2ConvertedImage, rest| Some((Ok((image,crate::color::ColorRecovery {
            assumed_srgb_for_8bit_esrgb: color_esrgb8_compatible(context.image,context.method) })),rest)))
}
pub closed spec fn color_compatible_result(context: Part2ColorConvertContext,
    result: Result<(Part2ConvertedImage, crate::color::ColorRecovery), crate::DecodeError>) -> bool {
    part2_cold_framed(|events|color_compatible_run(context,events),result)
}
pub(crate) proof fn color_compatible_frames(context: Part2ColorConvertContext,
    result: Result<(Part2ConvertedImage, crate::color::ColorRecovery), crate::DecodeError>)
    requires color_compatible_result(context,result),
    ensures part2_cold_framed(|events|color_compatible_run(context,events),result),
{
    reveal(color_compatible_result);
}
pub(crate) proof fn color_compatible_actual(context: Part2ColorConvertContext,result: Part2ConvertedImageResult)
    requires part2_color_convert_storage_result(color_compatible_context(context),result),
    ensures color_compatible_result(context,color_compatible_wrap(result,color_esrgb8_compatible(context.image,context.method))),
{
    reveal(color_compatible_result);
    part2_color_convert_storage_frames(color_compatible_context(context),result);
    let wrapped=color_compatible_wrap(result,color_esrgb8_compatible(context.image,context.method));
    if let Ok(image)=result {
        part2_cold_pure(Ok((image,crate::color::ColorRecovery {
            assumed_srgb_for_8bit_esrgb: color_esrgb8_compatible(context.image,context.method) })));
    }
    part2_cold_bind(|events|part2_color_convert_storage_run(color_compatible_context(context),events),
        |image: Part2ConvertedImage,rest|Some((Ok((image,crate::color::ColorRecovery {
            assumed_srgb_for_8bit_esrgb: color_esrgb8_compatible(context.image,context.method) })),rest)),
        result,wrapped);
}
}
