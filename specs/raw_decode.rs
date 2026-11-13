//! Compressed-byte typed and strict reconstruction composition, without native-layout banks.

use super::*;

verus! {

pub open spec fn part1_validate_reconstructed_output_components(
    components: Seq<Part1DecodedComponentModel>, component: nat,
) -> Result<(), crate::DecodeError>
    decreases components.len() - component,
{
    if component >= components.len() { Ok(()) } else {
        let output = components[component as int];
        if !part1_component_output_shape_valid(output.0, output.1, output.4.len() as usize) {
            Err(part1_block_placement_error(false))
        } else { part1_validate_reconstructed_output_components(components, component + 1) }
    }
}

pub open spec fn part1_validate_reconstructed_output_shape(
    input_bytes: usize, tile_parts: usize, expected_components: u16, image: Part1DecodedImageModel,
) -> Result<(), crate::DecodeError> {
    if !part1_decode_output_shape_valid(
        input_bytes, tile_parts, expected_components, image.4.len() as usize, image.0, image.1,
    ) { Err(part1_block_placement_error(false)) }
    else { part1_validate_reconstructed_output_components(image.4, 0) }
}

pub(crate) open spec fn part2_validate_reconstruction_transforms(
    input: Part2DecoderLayoutInput,
) -> Result<(), crate::DecodeError> {
    if input.main_extensions.nonlinear.len() != 0
        || exists |i: int| 0 <= i < input.parts.len()
            && input.parts[i].part2_extensions.nonlinear.len() != 0
    {
        Err(crate::DecodeError::UnsupportedFeature {
            feature: "nonlinear transforms on reconstruction samples",
        })
    } else { Ok(()) }
}

pub(crate) open spec fn part2_decode_reconstructed_layout_input(
    input_bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_decode_layout_input(input, limits) {
        Err(error) => Err(error),
        Ok(image) => match part2_validate_reconstruction_transforms(input) {
            Err(error) => Err(error),
            Ok(()) => match part1_validate_reconstructed_output_shape(
                input_bytes, input.parts.len() as usize, input.size.components, image,
            ) {
                Err(error) => Err(error), Ok(()) => Ok(image),
            },
        },
    }
}

pub closed spec fn part2_decode_raw_codestream(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
    }
}

pub(crate) proof fn part2_decode_raw_codestream_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
)
    ensures part2_decode_raw_codestream(input, limits, requested) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
    },
{
}

pub(crate) closed spec fn part2_decode_raw_codestream_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_typed_layout_value_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
    }
}

pub(crate) proof fn part2_decode_raw_codestream_selection_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: &crate::DecodeSelection,
)
    ensures part2_decode_raw_codestream(input, limits, Some(requested))
        == part2_decode_raw_codestream_value(input, limits, Some(crate::options::decode_selection_view(requested))),
{
    reveal(part2_decode_raw_codestream);
    reveal(part2_decode_raw_codestream_value);
}

pub closed spec fn part2_decode_raw_reconstructed_codestream(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_reconstructed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits),
    }
}

pub(crate) proof fn part2_decode_raw_reconstructed_codestream_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_decode_raw_reconstructed_codestream(input, limits)
        == match part1_parse_layout(input, limits) {
            Err(error) => Err(error),
            Ok(layout) => part2_decode_reconstructed_layout_input(
                input.len() as usize, part2_decoder_input_from_raw(layout), limits),
        },
{
}

}
