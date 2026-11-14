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

pub(crate) open spec fn part2_composition_cold_finish(
    metadata: Part2JpxInspection, index: usize, previous: Seq<Part2Placement>, owned: Part2OwnedLayer,
) -> Result<Seq<Part2Placement>, crate::DecodeError> {
    if index >= metadata.layers.len() {
        Err(crate::DecodeError::LayerIndexOutOfRange { index, layers: metadata.layers.len() as usize })
    } else {
        Ok(previous.push((owned, (index, 0, 0, metadata.layers[index as int].geometry.0,
            metadata.layers[index as int].geometry.1, 0, 0, 0, 0, true, 0))))
    }
}

pub(crate) open spec fn part2_composition_cold_step(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    index: usize, previous: Seq<Part2Placement>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<Part2Placement>> {
    part2_jpip_snapshot_bind(part2_effective_layer_cold_run(file, layers, index, limits, events),
        |owned, tail| Some((part2_composition_cold_finish(metadata, index, previous, owned), tail)))
}

#[verifier::opaque]
pub(crate) open spec fn part2_composition_cold_prefix(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    count: nat, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<Part2Placement>>
    decreases count,
{
    if count == 0 { Some((Ok(Seq::empty()), events)) } else {
        part2_jpip_snapshot_bind(part2_composition_cold_prefix(file, layers, metadata, (count - 1) as nat, limits, events),
            |previous, tail| part2_composition_cold_step(file, layers, metadata, (count - 1) as usize, previous, limits, tail))
    }
}

pub(crate) proof fn part2_composition_cold_step_normal(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    index: usize, previous: Seq<Part2Placement>, limits: &crate::ResourceLimits,
)
    ensures part2_cold_framed(
        |events| part2_composition_cold_step(file, layers, metadata, index, previous, limits, events),
        match part2_decode_effective_layer(file, layers, index, limits) {
            Err(error) => Err(error), Ok(owned) => part2_composition_cold_finish(metadata, index, previous, owned),
        }),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Seq<Part2Placement>>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_composition_cold_step(file, layers, metadata, index, previous, limits, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_composition_cold_step_normal_result(file, layers, metadata, index, previous, limits)),
{
    let decoded = part2_decode_effective_layer(file, layers, index, limits);
    part2_effective_layer_cold_normal(file, layers, index, limits);
    if let Ok(value) = decoded { part2_cold_pure(part2_composition_cold_finish(metadata, index, previous, value)); }
    part2_cold_bind(
        |events| part2_effective_layer_cold_run(file, layers, index, limits, events),
        |owned, tail| Some((part2_composition_cold_finish(metadata, index, previous, owned), tail)), decoded,
        match decoded { Err(error) => Err(error), Ok(value) => part2_composition_cold_finish(metadata, index, previous, value) });
}

pub(crate) open spec fn part2_composition_cold_step_normal_result(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    index: usize, previous: Seq<Part2Placement>, limits: &crate::ResourceLimits,
) -> Result<Seq<Part2Placement>, crate::DecodeError> {
    match part2_decode_effective_layer(file, layers, index, limits) {
        Err(error) => Err(error), Ok(owned) => part2_composition_cold_finish(metadata, index, previous, owned),
    }
}

pub(crate) proof fn part2_composition_cold_normal(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    count: nat, limits: &crate::ResourceLimits,
)
    ensures part2_cold_framed(
        |events| part2_composition_cold_prefix(file, layers, metadata, count, limits, events),
        part2_composition_source_prefix(file, layers, metadata, count, limits)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Seq<Part2Placement>>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_composition_cold_prefix(file, layers, metadata, count, limits, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_composition_source_prefix(file, layers, metadata, count, limits)),
    decreases count,
{
    reveal_with_fuel(part2_composition_cold_prefix, 1);
    reveal_with_fuel(part2_composition_source_prefix, 1);
    if count == 0 { part2_cold_pure(Ok(Seq::<Part2Placement>::empty())); } else {
        let previous = part2_composition_source_prefix(file, layers, metadata, (count - 1) as nat, limits);
        part2_composition_cold_normal(file, layers, metadata, (count - 1) as nat, limits);
        if let Ok(value) = previous {
            part2_composition_cold_step_normal(file, layers, metadata, (count - 1) as usize, value, limits);
        }
        part2_cold_bind(
            |events| part2_composition_cold_prefix(file, layers, metadata, (count - 1) as nat, limits, events),
            |value, tail| part2_composition_cold_step(file, layers, metadata, (count - 1) as usize, value, limits, tail),
            previous, part2_composition_source_prefix(file, layers, metadata, count, limits));
    }
}

pub(crate) open spec fn part2_render_composition_cold_run(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    let composition = match metadata.composition { None => None, Some(value) => Some(value.source) };
    if match metadata.composition { None => false, Some(value) => value.source.3.len() > 0 } {
        part2_render_inspected_cold_run(file, layers, composition, 0, limits, events)
    } else {
        match part2_composition_dimensions(metadata, limits) {
            Err(error) => Some((Err(error), events)),
            Ok(dimensions) => part2_jpip_snapshot_bind(
                part2_composition_cold_prefix(file, layers, metadata,
                    effective_jpx_layer_count(layers.len(), file.1.len()), limits, events),
                |decoded, tail| Some((part2_render_layers(dimensions.0, dimensions.1, decoded,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)), tail))),
        }
    }
}

pub(crate) open spec fn part2_render_composition_cold_result(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    limits: &crate::ResourceLimits, result: Part2ConvertedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_render_composition_cold_run(file, layers, metadata, limits, events), result)
}

pub(crate) proof fn part2_render_composition_cold_normal(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    limits: &crate::ResourceLimits,
)
    ensures part2_render_composition_cold_result(file, layers, metadata, limits,
        part2_render_source_composition(file, layers, metadata, limits)),
{
    reveal(part2_render_source_composition);
    if match metadata.composition { None => false, Some(value) => value.source.3.len() > 0 } {
        let composition = match metadata.composition { None => None, Some(value) => Some(value.source) };
        part2_render_inspected_cold_normal(file, layers, composition, 0, limits);
        part2_cold_framed_extensional(
            |events| part2_render_inspected_cold_run(file, layers, composition, 0, limits, events),
            |events| part2_render_composition_cold_run(file, layers, metadata, limits, events),
            part2_render_source_composition(file, layers, metadata, limits));
    } else {
        match part2_composition_dimensions(metadata, limits) {
            Err(error) => { part2_cold_pure::<Part2ConvertedImage>(Err(error)); },
            Ok(dimensions) => {
                let count = effective_jpx_layer_count(layers.len(), file.1.len());
                let decoded = part2_composition_source_prefix(file, layers, metadata, count, limits);
                part2_composition_cold_normal(file, layers, metadata, count, limits);
                if let Ok(value) = decoded {
                    part2_cold_pure(part2_render_layers(dimensions.0, dimensions.1, value,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)));
                }
                part2_cold_bind(
                    |events| part2_composition_cold_prefix(file, layers, metadata, count, limits, events),
                    |value, tail| Some((part2_render_layers(dimensions.0, dimensions.1, value,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)), tail)),
                    decoded, part2_render_source_composition(file, layers, metadata, limits));
            },
        }
    }
}

pub(crate) proof fn part2_render_composition_cold_frame_actual(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    limits: &crate::ResourceLimits, result: Part2ConvertedImageResult,
)
    requires match metadata.composition { None => false, Some(value) => value.source.3.len() > 0 },
        part2_render_inspected_cold_result(file, layers,
            match metadata.composition { None => None, Some(value) => Some(value.source) }, 0, limits, result),
    ensures part2_render_composition_cold_result(file, layers, metadata, limits, result),
{
    let composition = match metadata.composition { None => None, Some(value) => Some(value.source) };
    part2_cold_framed_extensional(
        |events| part2_render_inspected_cold_run(file, layers, composition, 0, limits, events),
        |events| part2_render_composition_cold_run(file, layers, metadata, limits, events), result);
}

pub(crate) proof fn part2_composition_cold_error_extend(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    limits: &crate::ResourceLimits, count: nat, total: nat, error: crate::DecodeError,
)
    requires count <= total, part2_cold_framed(
        |events| part2_composition_cold_prefix(file, layers, metadata, count, limits, events), Err(error)),
    ensures part2_cold_framed(
        |events| part2_composition_cold_prefix(file, layers, metadata, total, limits, events), Err(error)),
    decreases total - count,
{
    if count < total {
        part2_composition_cold_error_extend(file, layers, metadata, limits, count, (total - 1) as nat, error);
        reveal_with_fuel(part2_composition_cold_prefix, 1);
        part2_cold_bind(
            |events| part2_composition_cold_prefix(file, layers, metadata, (total - 1) as nat, limits, events),
            |previous, tail| part2_composition_cold_step(file, layers, metadata, (total - 1) as usize, previous, limits, tail),
            Err(error), Err(error));
    }
}

pub(crate) proof fn part2_render_composition_cold_source_error(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, metadata: Part2JpxInspection,
    limits: &crate::ResourceLimits, index: usize, previous: Seq<Part2Placement>,
    dimensions: (u32, u32), error: crate::DecodeError,
)
    requires !(match metadata.composition { None => false, Some(value) => value.source.3.len() > 0 }),
        part2_composition_dimensions(metadata, limits) == Ok(dimensions),
        index < effective_jpx_layer_count(layers.len(), file.1.len()),
        part2_composition_source_prefix(file, layers, metadata, index as nat, limits) == Ok(previous),
        part2_effective_layer_cold_result(file, layers, index, limits, Err(error)),
    ensures part2_render_composition_cold_result(file, layers, metadata, limits, Err(error)),
{
    part2_composition_cold_normal(file, layers, metadata, index as nat, limits);
    part2_cold_bind(
        |events| part2_effective_layer_cold_run(file, layers, index, limits, events),
        |owned, tail| Some((part2_composition_cold_finish(metadata, index, previous, owned), tail)), Err(error), Err(error));
    reveal_with_fuel(part2_composition_cold_prefix, 1);
    part2_cold_bind(
        |events| part2_composition_cold_prefix(file, layers, metadata, index as nat, limits, events),
        |value, tail| part2_composition_cold_step(file, layers, metadata, index, value, limits, tail),
        Ok(previous), Err(error));
    let count = effective_jpx_layer_count(layers.len(), file.1.len());
    part2_composition_cold_error_extend(file, layers, metadata, limits, index as nat + 1, count, error);
    part2_cold_bind(
        |events| part2_composition_cold_prefix(file, layers, metadata, count, limits, events),
        |value, tail| Some((part2_render_layers(dimensions.0, dimensions.1, value,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)), tail)),
        Err(error), Err(error));
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
