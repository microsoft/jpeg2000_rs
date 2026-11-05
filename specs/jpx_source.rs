//! Actual JPX file-to-codestream/associated-image composition.

use super::*;

verus! {

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
