//! Actual composition dimensions and raw non-timeline source-layer fallback.

use super::*;

verus! {

#[verifier::opaque]
pub open spec fn part2_composition_extent_prefix(layers: Seq<Part2LayerInspection>, count: nat)
    -> Result<(u32, u32), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((0, 0)) }
    else {
        match part2_composition_extent_prefix(layers, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let layer = layers[count as int - 1];
                let width = layer.offset.0 as nat + layer.geometry.0 as nat;
                let height = layer.offset.1 as nat + layer.geometry.1 as nat;
                if width > u32::MAX as nat { Err(part2_composition_error(true)) }
                else if height > u32::MAX as nat { Err(part2_composition_error(true)) }
                else { Ok((if (previous.0 as nat) < width { width as u32 } else { previous.0 },
                    if (previous.1 as nat) < height { height as u32 } else { previous.1 })) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_composition_dimensions(metadata: Part2JpxInspection, limits: &crate::ResourceLimits)
    -> Result<(u32, u32), crate::DecodeError>
{
    let dimensions = match metadata.composition {
        Some(composition) => Ok((composition.source.0, composition.source.1)),
        None => part2_composition_extent_prefix(metadata.layers, metadata.layers.len()),
    };
    match dimensions {
        Err(error) => Err(error),
        Ok((width, height)) => {
            if width == 0 || height == 0 { Err(part2_composition_error(false)) }
            else if width > crate::limits::resource_width_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Width,
                    limit: crate::limits::resource_width_limit(limits) as u64, actual: width as u64 })
            } else if height > crate::limits::resource_height_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Height,
                    limit: crate::limits::resource_height_limit(limits) as u64, actual: height as u64 })
            } else if width as nat * height as nat > u64::MAX as nat {
                Err(part2_composition_error(true))
            } else if width as nat * height as nat > crate::limits::resource_pixel_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Pixels,
                    limit: crate::limits::resource_pixel_limit(limits), actual: (width as nat * height as nat) as u64 })
            } else { Ok((width, height)) }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_composition_source_prefix(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    count: nat, limits: &crate::ResourceLimits,
) -> Result<Seq<Part2Placement>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_composition_source_prefix(file, layers, metadata, (count - 1) as nat, limits) {
            Err(error) => Err(error),
            Ok(previous) => {
                let index = (count - 1) as usize;
                match part2_decode_effective_layer(file, layers, index, limits) {
                    Err(error) => Err(error),
                    Ok(owned) => if index >= metadata.layers.len() {
                        Err(crate::DecodeError::LayerIndexOutOfRange { index, layers: metadata.layers.len() as usize })
                    } else {
                        Ok(previous.push((owned, (index, 0, 0, metadata.layers[index as int].geometry.0,
                            metadata.layers[index as int].geometry.1, 0, 0, 0, 0, true, 0))))
                    },
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_render_source_composition(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>,
    metadata: Part2JpxInspection, limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    if match metadata.composition { None => false, Some(composition) => composition.source.3.len() > 0 } {
        part2_render_inspected_source_frame(file, layers,
            match metadata.composition { None => None, Some(composition) => Some(composition.source) }, 0, limits)
    } else {
        match part2_composition_dimensions(metadata, limits) {
            Err(error) => Err(error),
            Ok(dimensions) => {
                let count = effective_jpx_layer_count(layers.len(), file.1.len());
                match part2_composition_source_prefix(file, layers, metadata, count, limits) {
                    Err(error) => Err(error),
                    Ok(decoded) => part2_render_layers(dimensions.0, dimensions.1, decoded,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)),
                }
            },
        }
    }
}

pub closed spec fn part2_render_raw_jpx_composition(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Part2ConvertedImageResult
{
    match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => match part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)) {
                Err(error) => Err(error),
                Ok(metadata) => part2_render_source_composition(part2_raw_jpx_decode_input(inspected.0),
                    part2_raw_layer_routings(inspected.0), metadata, limits),
            },
        },
    }
}

pub(crate) proof fn part2_render_raw_jpx_composition_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_render_raw_jpx_composition(input, limits) == match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => match part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)) {
                Err(error) => Err(error),
                Ok(metadata) => part2_render_source_composition(part2_raw_jpx_decode_input(inspected.0),
                    part2_raw_layer_routings(inspected.0), metadata, limits),
            },
        },
    },
{
}

pub(crate) proof fn part2_composition_extent_error(layers: Seq<Part2LayerInspection>, count: nat, total: nat)
    requires count <= total,
    ensures match part2_composition_extent_prefix(layers, count) {
        Err(error) => part2_composition_extent_prefix(layers, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_composition_extent_prefix);
    if count < total {
        part2_composition_extent_error(layers, count, (total - 1) as nat);
    }
}

pub(crate) proof fn part2_composition_source_error(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    count: nat, total: nat, limits: &crate::ResourceLimits,
)
    requires count <= total,
    ensures match part2_composition_source_prefix(file, layers, metadata, count, limits) {
        Err(error) => part2_composition_source_prefix(file, layers, metadata, total, limits) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_composition_source_prefix);
    if count < total {
        part2_composition_source_error(file, layers, metadata, count, (total - 1) as nat, limits);
    }
}

}
