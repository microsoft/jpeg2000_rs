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
    match part2_nonlinear_transform_for(extensions.nonlinear, component, extensions.nonlinear_local_count) {
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
        Ok(image) => part2_typed_layout_after_typed(input,image,discard_levels,limits),
    }
}
pub(crate) open spec fn part2_typed_layout_after_typed(
    input: Part2DecoderLayoutInput, image: Part1DecodedTypedImage, discard_levels: u8, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part2_collect_nonlinear_regions_input(input, image, discard_levels) {
            Err(error) => Err(error),
            Ok(regions) => if regions.len() == 0 { Ok(image) } else {
                let outcome = part2_apply_nonlinear_regions(image, regions,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits));
                match outcome.0 { Err(error) => Err(error), Ok(()) => Ok(outcome.1) }
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

pub(crate) open spec fn part2_payload_copy_run(
    source: Part2OwnedTilePart, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2OwnedTilePart> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipSnapshotEvent::CollectedPayloadCopy { source: actual, calls } => if actual != source { None } else {
                match part1_mct_copy_run(part2_payload_duplicate_tail(source, 0), calls) {
                    Some((response, rest)) => if rest.len() != 0 { None } else {
                        Some((match response { Err(error) => Err(error), Ok(()) => Ok(source) }, events.drop_first()))
                    },
                    None => None,
                }
            },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_payload_copy_result(
    source: Part2OwnedTilePart, result: Result<Part2OwnedTilePart, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_payload_copy_run(source, events), result)
}

pub(crate) proof fn part2_payload_copy_observed(
    source: Part2OwnedTilePart, result: Result<Part2OwnedTilePart, crate::DecodeError>,
)
    requires part1_mct_copy_result(part2_payload_duplicate_tail(source, 0),
        match result { Err(error) => Err(error), Ok(_) => Ok(()) }),
        result.is_ok() ==> result == Ok(source),
    ensures part2_payload_copy_result(source, result),
{
    reveal(part1_mct_copy_result);
    let response = match result { Err(error) => Err(error), Ok(_) => Ok(()) };
    let calls = choose|calls| part1_mct_copy_run(part2_payload_duplicate_tail(source, 0), calls)
        == Some((response, Seq::empty()));
    let prefix = seq![Part2JpipSnapshotEvent::CollectedPayloadCopy { source, calls }];
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_payload_copy_run(source, prefix + tail) == Some((result, tail)) by {
        assert((prefix + tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events| part2_payload_copy_run(source, events), prefix, result));
}

pub(crate) proof fn part2_payload_copy_normal(source: Part2OwnedTilePart)
    ensures part2_payload_copy_result(source, Ok(source)),
{
    reveal(part1_mct_copy_result);
    let requests = part2_payload_duplicate_tail(source, 0);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(part1_mct_copy_run(requests, part1_mct_copy_normal_calls(requests)) == Some((Ok(()), Seq::empty())));
    part2_payload_copy_observed(source, Ok(source));
}

#[verifier::opaque]
pub(crate) open spec fn part2_collected_part_count(parts: Seq<Part2OwnedTilePart>, tile: u16, index: nat) -> nat
    decreases if index < parts.len() { parts.len() - index } else { 0int },
{
    if index >= parts.len() { 0 } else {
        (if parts[index as int].tile_index == tile { 1nat } else { 0nat })
            + part2_collected_part_count(parts, tile, index + 1)
    }
}

pub(crate) proof fn part2_collected_count_matches(
    parts: Seq<Part2OwnedTilePart>, tile: u16, index: nat, before: Seq<Part2OwnedTilePart>,
)
    ensures part2_collect_tile_parts_run(parts, tile, index, before).len()
        == before.len() + part2_collected_part_count(parts, tile, index),
    decreases if index < parts.len() { parts.len() - index } else { 0int },
{
    reveal_with_fuel(part2_collect_tile_parts_run, 1);
    reveal_with_fuel(part2_collected_part_count, 1);
    if index < parts.len() {
        let next = if parts[index as int].tile_index == tile { before.push(parts[index as int]) } else { before };
        part2_collected_count_matches(parts, tile, index + 1, next);
    }
}

pub(crate) open spec fn part2_collected_capacity_run(
    parts: Seq<Part2OwnedTilePart>, tile: u16, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<()> {
    let count = part2_collected_part_count(parts, tile, 0);
    if count == 0 { Some((Ok(()), events)) } else if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipSnapshotEvent::CollectedPartsCapacity { source, tile: actual_tile, elements, succeeded } =>
                if source != parts || actual_tile != tile || elements != count { None } else {
                    Some((if succeeded { Ok(()) } else { Err(crate::DecodeError::AllocationFailed) }, events.drop_first()))
                },
            _ => None,
        }
    }
}

pub(crate) open spec fn part2_collected_capacity_result(
    parts: Seq<Part2OwnedTilePart>, tile: u16, result: Result<(), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_collected_capacity_run(parts, tile, events), result)
}

pub(crate) proof fn part2_collected_capacity_observed(
    parts: Seq<Part2OwnedTilePart>, tile: u16, elements: usize, response: Result<(), crate::DecodeError>,
)
    requires elements == part2_collected_part_count(parts, tile, 0),
        response == Ok(()) || (elements > 0 && response == Err(crate::DecodeError::AllocationFailed)),
    ensures part2_collected_capacity_result(parts, tile, response),
{
    if elements == 0 { part2_cold_pure::<()>(response); } else {
        let prefix = seq![Part2JpipSnapshotEvent::CollectedPartsCapacity {
            source: parts, tile, elements: elements as nat, succeeded: response.is_ok(),
        }];
        assert forall|tail: Seq<Part2JpipSnapshotEvent>|
            part2_collected_capacity_run(parts, tile, prefix + tail) == Some((response, tail)) by {
            assert((prefix + tail).drop_first() =~= tail);
        }
        assert(part2_cold_prefix(|events| part2_collected_capacity_run(parts, tile, events), prefix, response));
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_collected_loop_run(
    parts: Seq<Part2OwnedTilePart>, tile: u16, index: nat, before: Seq<Part2OwnedTilePart>,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<Part2OwnedTilePart>>
    decreases if index < parts.len() { parts.len() - index } else { 0int },
{
    if index >= parts.len() { Some((Ok(before), events)) }
    else if parts[index as int].tile_index != tile {
        part2_collected_loop_run(parts, tile, index + 1, before, events)
    } else {
        part2_jpip_snapshot_bind(part2_payload_copy_run(parts[index as int], events),
            |copied: Part2OwnedTilePart, rest| part2_collected_loop_run(parts, tile, index + 1, before.push(copied), rest))
    }
}

pub(crate) open spec fn part2_collected_parts_run(
    parts: Seq<Part2OwnedTilePart>, tile: u16, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<Part2OwnedTilePart>> {
    part2_jpip_snapshot_bind(part2_collected_capacity_run(parts, tile, events),
        |_: (), rest| part2_collected_loop_run(parts, tile, 0, Seq::empty(), rest))
}

pub(crate) open spec fn part2_collected_parts_result(
    parts: Seq<Part2OwnedTilePart>, tile: u16, result: Result<Seq<Part2OwnedTilePart>, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_collected_parts_run(parts, tile, events), result)
}

pub(crate) proof fn part2_collected_loop_normal(
    parts: Seq<Part2OwnedTilePart>, tile: u16, index: nat, before: Seq<Part2OwnedTilePart>,
)
    ensures part2_cold_framed(|events| part2_collected_loop_run(parts, tile, index, before, events),
        Ok(part2_collect_tile_parts_run(parts, tile, index, before))),
    decreases if index < parts.len() { parts.len() - index } else { 0int },
{
    reveal_with_fuel(part2_collected_loop_run, 1);
    reveal_with_fuel(part2_collect_tile_parts_run, 1);
    let result = Ok(part2_collect_tile_parts_run(parts, tile, index, before));
    if index >= parts.len() { part2_cold_pure(result); }
    else if parts[index as int].tile_index != tile {
        part2_collected_loop_normal(parts, tile, index + 1, before);
        part2_decode_eta(|events| part2_collected_loop_run(parts, tile, index + 1, before, events), result);
    } else {
        part2_payload_copy_normal(parts[index as int]);
        part2_collected_loop_normal(parts, tile, index + 1, before.push(parts[index as int]));
        part2_decode_eta(|events| part2_collected_loop_run(parts, tile, index + 1, before.push(parts[index as int]), events), result);
        part2_cold_bind(|events| part2_payload_copy_run(parts[index as int], events),
            |copied: Part2OwnedTilePart, rest| part2_collected_loop_run(parts, tile, index + 1, before.push(copied), rest),
            Ok(parts[index as int]), result);
    }
}

pub(crate) proof fn part2_collected_parts_normal(parts: Seq<Part2OwnedTilePart>, tile: u16)
    ensures part2_collected_parts_result(parts, tile, part2_collect_tile_parts(parts, tile)),
{
    let count = part2_collected_part_count(parts, tile, 0);
    if count == 0 { part2_cold_pure::<()>(Ok(())); } else {
        let prefix = seq![Part2JpipSnapshotEvent::CollectedPartsCapacity { source: parts, tile, elements: count, succeeded: true }];
        assert forall|tail: Seq<Part2JpipSnapshotEvent>|
            part2_collected_capacity_run(parts, tile, prefix + tail) == Some((Ok(()), tail)) by {
            assert((prefix + tail).drop_first() =~= tail);
        }
        assert(part2_cold_prefix(|events| part2_collected_capacity_run(parts, tile, events), prefix, Ok(())));
    }
    part2_collected_loop_normal(parts, tile, 0, Seq::empty());
    part2_decode_eta(|events| part2_collected_loop_run(parts, tile, 0, Seq::empty(), events),
        part2_collect_tile_parts(parts, tile));
    part2_cold_bind(|events| part2_collected_capacity_run(parts, tile, events),
        |_: (), rest| part2_collected_loop_run(parts, tile, 0, Seq::empty(), rest),
        Ok(()), part2_collect_tile_parts(parts, tile));
}

pub(crate) open spec fn part2_intersecting_tile_count(
    size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: u64,
) -> Result<usize, crate::DecodeError> {
    match part2_select_intersecting_tiles(size, explicit, region, count) {
        Err(error) => Err(error), Ok(tiles) => Ok(tiles.len() as usize),
    }
}

pub(crate) open spec fn part2_select_tiles_run(
    size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: u64,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<u16>> {
    let normal = part2_select_intersecting_tiles(size, explicit, region, count);
    match normal {
        Err(error) => Some((Err(error), events)),
        Ok(tiles) => if events.len() == 0 { None } else {
            match events[0] {
                Part2JpipSnapshotEvent::SelectionCapacity {
                    size: actual_size, explicit: actual_explicit, region: actual_region, count: actual_count,
                    elements, succeeded,
                } => if actual_size != size || actual_explicit != explicit || actual_region != region
                    || actual_count != count || elements != tiles.len() {
                    None
                } else {
                    Some((if succeeded { normal } else { Err(crate::DecodeError::AllocationFailed) },
                        events.drop_first()))
                },
                _ => None,
            }
        },
    }
}

pub(crate) open spec fn part2_select_tiles_result(
    size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: u64,
    result: Result<Seq<u16>, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_select_tiles_run(size, explicit, region, count, events), result)
}

pub(crate) proof fn part2_select_tiles_normal(
    size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: u64,
)
    ensures part2_select_tiles_result(size, explicit, region, count,
        part2_select_intersecting_tiles(size, explicit, region, count)),
{
    let normal = part2_select_intersecting_tiles(size, explicit, region, count);
    match normal {
        Err(_) => { part2_cold_pure::<Seq<u16>>(normal); },
        Ok(tiles) => {
            let calls = seq![Part2JpipSnapshotEvent::SelectionCapacity {
                size, explicit, region, count, elements: tiles.len(), succeeded: true,
            }];
            assert forall|tail: Seq<Part2JpipSnapshotEvent>|
                part2_select_tiles_run(size, explicit, region, count, calls + tail) == Some((normal, tail)) by {
                assert((calls + tail).drop_first() =~= tail);
            }
            assert(part2_cold_prefix(|events| part2_select_tiles_run(size, explicit, region, count, events), calls, normal));
        },
    }
}

pub(crate) proof fn part2_select_tiles_capacity_observed(
    size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: u64,
    elements: usize, response: Result<(), crate::DecodeError>,
)
    requires part2_select_intersecting_tiles(size, explicit, region, count).is_ok(),
        part2_select_intersecting_tiles(size, explicit, region, count).get_Ok_0().len() == elements,
        response.is_err() ==> response == Err(crate::DecodeError::AllocationFailed),
    ensures part2_select_tiles_result(size, explicit, region, count, match response {
        Err(error) => Err(error), Ok(()) => part2_select_intersecting_tiles(size, explicit, region, count),
    }),
{
    let normal = part2_select_intersecting_tiles(size, explicit, region, count);
    let result = match response { Err(error) => Err(error), Ok(()) => normal };
    let calls = seq![Part2JpipSnapshotEvent::SelectionCapacity {
        size, explicit, region, count, elements: elements as nat, succeeded: response.is_ok(),
    }];
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_select_tiles_run(size, explicit, region, count, calls + tail) == Some((result, tail)) by {
        assert((calls + tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events| part2_select_tiles_run(size, explicit, region, count, events), calls, result));
}

pub(crate) open spec fn part2_validate_selection_run(
    size: Part2SelectionGeometry, requested: Part2DecodeSelection, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ValidatedSelection> {
    match part2_validate_selection(size, requested) {
        Err(error) => Some((Err(error), events)),
        Ok(selected) => part2_jpip_snapshot_bind(
            part2_select_tiles_run(size, part2_selection_explicit(requested.0).get_Ok_0(),
                selected.1, part2_selection_tile_count(size).get_Ok_0(), events),
            |tiles: Seq<u16>, rest| Some((Ok((tiles, selected.1, selected.2)), rest))),
    }
}

pub(crate) open spec fn part2_validate_selection_result(
    size: Part2SelectionGeometry, requested: Part2DecodeSelection,
    result: Result<Part2ValidatedSelection, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_validate_selection_run(size, requested, events), result)
}

pub(crate) proof fn part2_validate_selection_normal(
    size: Part2SelectionGeometry, requested: Part2DecodeSelection,
)
    ensures part2_validate_selection_result(size, requested, part2_validate_selection(size, requested)),
{
    reveal(part2_validate_selection);
    let normal = part2_validate_selection(size, requested);
    match normal {
        Err(_) => { part2_cold_pure::<Part2ValidatedSelection>(normal); },
        Ok(selected) => {
            let explicit = part2_selection_explicit(requested.0).get_Ok_0();
            let count = part2_selection_tile_count(size).get_Ok_0();
            part2_select_tiles_normal(size, explicit, selected.1, count);
            part2_cold_pure(Ok(selected));
            part2_cold_bind(|events| part2_select_tiles_run(size, explicit, selected.1, count, events),
                |tiles: Seq<u16>, rest| Some((Ok((tiles, selected.1, selected.2)), rest)),
                Ok(selected.0), Ok(selected));
        },
    }
}

pub(crate) proof fn part2_validate_selection_from_tiles(
    size: Part2SelectionGeometry, requested: Part2DecodeSelection, explicit: Seq<u16>,
    region: Seq<u32>, count: u64, result: Result<Seq<u16>, crate::DecodeError>,
)
    requires part2_selection_explicit(requested.0) == Ok(explicit),
        part2_selection_tile_count(size) == Ok(count),
        part2_validate_selection(size, requested) == match part2_select_intersecting_tiles(size, explicit, region, count) {
            Err(error) => Err(error), Ok(tiles) => Ok((tiles, region, requested.2)),
        },
        part2_select_tiles_result(size, explicit, region, count, result),
    ensures part2_validate_selection_result(size, requested, match result {
        Err(error) => Err(error), Ok(tiles) => Ok((tiles, region, requested.2)),
    }),
{
    let mapped = match result { Err(error) => Err(error), Ok(tiles) => Ok((tiles, region, requested.2)) };
    let child = |events| part2_select_tiles_run(size, explicit, region, count, events);
    let next = |tiles: Seq<u16>, rest| Some((Ok((tiles, region, requested.2)), rest));
    part2_cold_pure(mapped);
    part2_cold_bind(child, next, result, mapped);
    assert forall|events: Seq<Part2JpipSnapshotEvent>|
        part2_validate_selection_run(size, requested, events) == part2_jpip_snapshot_bind(child(events), next) by {};
    part2_cold_framed_extensional(|events| part2_jpip_snapshot_bind(child(events), next),
        |events| part2_validate_selection_run(size, requested, events), mapped);
}

}
