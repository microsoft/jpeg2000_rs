//! Raw public JPX codestream results and actual selected-file traversal.

use super::*;

verus! {

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
