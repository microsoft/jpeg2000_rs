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

}
