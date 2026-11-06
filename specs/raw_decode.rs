//! Compressed-byte full/selected typed-image composition, without native-layout banks.

use super::*;

verus! {

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

}
