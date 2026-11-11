//! Raw color output and source-derived expanded selection composition.

use super::*;

verus! {

pub(crate) open spec fn part2_color_selection_layout(
    layout: Part1CompleteLayout, requested: Part2DecodeSelection,
) -> Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError> {
    let size = part2_decoder_input_from_raw(layout).size;
    part2_color_selection_requested(crate::codestream::selection_geometry_view(&size),
        crate::codestream::image_size_component_infos(&size),
        crate::codestream::image_size_component_count(&size), requested)
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
