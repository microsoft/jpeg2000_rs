//! Logical decoder inputs shared by native layouts and raw parser results.

use super::*;

verus! {

pub(crate) struct Part2DecoderLayoutInput {
    pub size: crate::codestream::ImageSize,
    pub main_execution: Part2ExecutionHeader,
    pub main_extensions: Part2OwnedExtensions,
    pub parts: Seq<Part2OwnedTilePart>,
    pub capabilities: Option<(u32, Seq<u16>)>,
}

pub(crate) open spec fn part2_decoder_execution_header(
    styles: crate::codestream::ComponentCodingStyles, extensions: Part2OwnedExtensions,
) -> Part2ExecutionHeader {
    (
        styles,
        (extensions.decompositions.map_values(|value: (u8, Seq<crate::codestream::DecompositionDirection>)| value.0),
         extensions.arbitrary.map_values(|value: (u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)| value.0)),
        part2_owned_kernel_registry(extensions),
        extensions.depths.map_values(|value: crate::codestream::ComponentBitDepth| (value.precision, value.signed)),
    )
}

pub(crate) open spec fn part2_decoder_tile_from_raw(raw: Part1TilePartPayload) -> Part2OwnedTilePart {
    Part2OwnedTilePart {
        tile_index: raw.tile_index, tile_part_index: raw.tile_part_index, tile_part_count: raw.tile_part_count,
        coding_style: crate::codestream::decoder_native_style(raw.coding_style),
        quantization: crate::codestream::decoder_native_quantization(raw.quantization),
        component_coding_styles: crate::codestream::tile_part_native_styles(raw.component_coding_styles),
        component_quantizations: (raw.component_quantizations.0,
            raw.component_quantizations.1.map_values(|value: Part2Quantization| crate::codestream::decoder_native_quantization(value))),
        roi_shifts: crate::codestream::decoder_native_roi(raw.roi_shifts),
        progression_changes: raw.progression_changes, multiple_component_transform: raw.multiple_component_transform,
        part2_extensions: raw.part2_extensions, packet_lengths: raw.packet_lengths,
        packed_packet_headers: raw.packed_packet_headers,
        has_functional_header_marker: raw.has_functional_header_marker, has_roi_marker: raw.has_roi_marker,
        data: raw.data,
    }
}

pub(crate) open spec fn part2_decoder_input_from_raw(raw: Part1CompleteLayout) -> Part2DecoderLayoutInput {
    Part2DecoderLayoutInput {
        size: crate::codestream::decoder_native_size(raw.0.image_size),
        main_execution: part2_decoder_execution_header(
            crate::codestream::tile_part_native_styles(raw.0.styles), raw.0.extensions),
        main_extensions: raw.0.extensions,
        parts: raw.4.map_values(|value: Part1TilePartPayload| part2_decoder_tile_from_raw(value)),
        capabilities: raw.1.2,
    }
}

pub(crate) open spec fn part2_decoder_execution_tiles(parts: Seq<Part2OwnedTilePart>) -> Seq<Part2ExecutionHeader> {
    parts.map_values(|part: Part2OwnedTilePart| part2_decoder_execution_header(part.component_coding_styles, part.part2_extensions))
}

pub(crate) open spec fn part2_decoder_execution_admission(input: Part2DecoderLayoutInput) -> Result<(), crate::DecodeError> {
    part2_validate_execution_layout(input.size.components, input.main_execution, part2_decoder_execution_tiles(input.parts))
}

pub(crate) open spec fn part2_nonlinear_tile_region_input(
    input: Part2DecoderLayoutInput, component: u16, tile: u16, extent: (u32, u32, u32, u32), scale: u32,
) -> Result<Option<Part2NonlinearRegion>, crate::DecodeError> {
    let extensions = part2_nonlinear_tile_extensions(input.main_extensions, input.parts, tile, input.parts.len());
    match part2_nonlinear_transform_for(extensions.nonlinear, component) {
        None => Ok(None),
        Some(transform) => match part2_tile_component_bounds(
            crate::codestream::selection_geometry_view(&input.size),
            crate::codestream::image_size_component_count(&input.size),
            crate::codestream::image_size_component_infos(&input.size), tile, component,
        ) {
            Err(error) => Err(error),
            Ok(bounds) => match part2_selection_ceil(bounds.x0, scale) {
                Err(error) => Err(error),
                Ok(bx0) => match part2_selection_ceil(bounds.y0, scale) {
                    Err(error) => Err(error),
                    Ok(by0) => match part2_selection_ceil(bounds.x1, scale) {
                        Err(error) => Err(error),
                        Ok(bx1) => match part2_selection_ceil(bounds.y1, scale) {
                            Err(error) => Err(error),
                            Ok(by1) => {
                                let x0 = if bx0 > extent.0 { bx0 } else { extent.0 };
                                let y0 = if by0 > extent.1 { by0 } else { extent.1 };
                                let x1 = if bx1 < extent.2 { bx1 } else { extent.2 };
                                let y1 = if by1 < extent.3 { by1 } else { extent.3 };
                                if x0 >= x1 || y0 >= y1 { Ok(None) } else {
                                    Ok(Some(Part2NonlinearRegion {
                                        component, x0: (x0 - extent.0) as u32, y0: (y0 - extent.1) as u32,
                                        x1: (x1 - extent.0) as u32, y1: (y1 - extent.1) as u32, transform,
                                    }))
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

pub(crate) open spec fn part2_nonlinear_tile_regions_input(
    input: Part2DecoderLayoutInput, component: u16, extent: (u32, u32, u32, u32),
    scale: u32, count: u64, tile: nat, regions: Seq<Part2NonlinearRegion>,
) -> Result<Seq<Part2NonlinearRegion>, crate::DecodeError>
    decreases count - tile,
{
    if tile >= count { Ok(regions) }
    else if tile > u16::MAX { Err(part1_block_placement_error(true)) }
    else {
        match part2_nonlinear_tile_region_input(input, component, tile as u16, extent, scale) {
            Err(error) => Err(error),
            Ok(region) => part2_nonlinear_tile_regions_input(input, component, extent, scale, count, tile + 1,
                match region { None => regions, Some(region) => regions.push(region) }),
        }
    }
}

pub(crate) open spec fn part2_nonlinear_component_regions_input(
    input: Part2DecoderLayoutInput, image: Part1DecodedTypedImage, scale: u32, component: nat, regions: Seq<Part2NonlinearRegion>,
) -> Result<Seq<Part2NonlinearRegion>, crate::DecodeError>
    decreases input.size.components - component,
{
    if component >= input.size.components { Ok(regions) } else {
        match part2_nonlinear_component_extent(&input.size, image, component as u16) {
            Err(error) => Err(error),
            Ok((extent, count)) => match part2_nonlinear_tile_regions_input(input, component as u16, extent, scale, count, 0, regions) {
                Err(error) => Err(error),
                Ok(regions) => part2_nonlinear_component_regions_input(input, image, scale, component + 1, regions),
            },
        }
    }
}

pub(crate) open spec fn part2_collect_nonlinear_regions_input(
    input: Part2DecoderLayoutInput, image: Part1DecodedTypedImage, discard_levels: u8,
) -> Result<Seq<Part2NonlinearRegion>, crate::DecodeError> {
    if discard_levels >= 32 {
        Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
    } else {
        part2_nonlinear_component_regions_input(input, image, 1u32 << (discard_levels as u32), 0, Seq::empty())
    }
}

pub(crate) open spec fn part2_typed_layout_input(
    input: Part2DecoderLayoutInput, decoded: Part1DecodedImageModel, discard_levels: u8, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part1_decoded_image_typed(decoded, crate::limits::resource_decoded_bytes_limit(limits)) {
        Err(error) => Err(error),
        Ok(image) => match part2_collect_nonlinear_regions_input(input, image, discard_levels) {
            Err(error) => Err(error),
            Ok(regions) => if regions.len() == 0 { Ok(image) } else {
                let outcome = part2_apply_nonlinear_regions(image, regions,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits));
                match outcome.0 { Err(error) => Err(error), Ok(()) => Ok(outcome.1) }
            },
        },
    }
}

pub(crate) open spec fn part2_decode_layout_input(
    input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_decoder_execution_admission(input) {
        Err(error) => Err(error),
        Ok(()) => match part2_selection_tile_count(crate::codestream::selection_geometry_view(&input.size)) {
            Err(error) => Err(error),
            Ok(count) => if count > u16::MAX as u64 + 1 {
                Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidImageGeometry })
            } else {
                part2_full_layout_tiles(&input.size, input.parts, input.capabilities, limits, count, 0,
                    Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 })
            },
        },
    }
}

pub(crate) open spec fn part2_decode_layout_selected_input(
    input: Part2DecoderLayoutInput, requested: &crate::DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    part2_decode_layout_selected_value_input(input, crate::options::decode_selection_view(requested), limits)
}

pub(crate) open spec fn part2_decode_layout_selected_value_input(
    input: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_decoder_execution_admission(input) {
        Err(error) => Err(error),
        Ok(()) => match part2_validate_selection(crate::codestream::selection_geometry_view(&input.size), requested) {
            Err(error) => Err(error),
            Ok(selection) => if selection.1.len() != 4 { Err(part1_block_placement_error(false)) } else {
                part2_selected_layout_tiles(&input.size, input.parts, input.capabilities, selection.0,
                    [selection.1[0], selection.1[1], selection.1[2], selection.1[3]], selection.2, limits, 0,
                    Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 })
            },
        },
    }
}

pub(crate) open spec fn part2_decode_typed_layout_input(
    input_bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
    requested: Option<&crate::DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    part2_decode_typed_layout_value_input(input_bytes, input, limits, match requested {
        None => None, Some(requested) => Some(crate::options::decode_selection_view(requested)),
    })
}

pub(crate) open spec fn part2_decode_typed_layout_value_input(
    input_bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
    requested: Option<Part2DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    let decoded = match requested {
        None => part2_decode_layout_input(input, limits),
        Some(requested) => part2_decode_layout_selected_value_input(input, requested, limits),
    };
    let discard_levels = match requested { None => 0u8, Some(selection) => selection.2 };
    match decoded {
        Err(error) => Err(error),
        Ok(decoded) => match part2_typed_layout_input(input, decoded, discard_levels, limits) {
            Err(error) => Err(error),
            Ok(image) => match part1_validate_typed_output_shape(input_bytes, input.parts.len() as usize, input.size.components, image) {
                Err(error) => Err(error), Ok(()) => Ok(image),
            },
        },
    }
}

}
