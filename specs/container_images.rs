//! Public raw single-container typed image and actual selection composition.

use super::*;

verus! {

pub closed spec fn part2_decode_raw_single_container(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    selection: Option<&crate::DecodeSelection>, jph: bool,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    let inspected = if jph { part2_inspect_jph_container(input, limits) }
        else { part2_parse_and_inspect_container_mode(input, limits, true) };
    match inspected {
        Err(error) => Err(error),
        Ok(inspected) => {
            let file = inspected.0;
            if (jph && file.streams.len() != 1)
                || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
                Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
            } else {
                match part2_decode_raw_codestream(file.streams[0].1, limits, selection) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_apply_output_header(decoded, part2_raw_associated_header(file.header).0,
                        crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
                }
            }
        },
    }
}

pub(crate) proof fn part2_decode_raw_single_container_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    selection: Option<&crate::DecodeSelection>, jph: bool,
)
    ensures part2_decode_raw_single_container(input, limits, selection, jph) == {
        let inspected = if jph { part2_inspect_jph_container(input, limits) }
            else { part2_parse_and_inspect_container_mode(input, limits, true) };
        match inspected {
            Err(error) => Err(error),
            Ok(inspected) => {
                let file = inspected.0;
                if (jph && file.streams.len() != 1)
                    || (!jph && part2_validate_jp2_display_profile(file).is_err()) {
                    Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
                } else {
                    match part2_decode_raw_codestream(file.streams[0].1, limits, selection) {
                        Err(error) => Err(error),
                        Ok(decoded) => part2_apply_output_header(decoded, part2_raw_associated_header(file.header).0,
                            crate::limits::resource_component_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
                    }
                }
            },
        }
    },
{
}

}
