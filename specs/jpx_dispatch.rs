//! Actual compositing-layer routing across general and registered fast producers.

use super::*;

verus! {

pub type Part2LayerRoutingConfig = (Part2GeneralLayerConfig, Option<crate::jp2::ColorMethod>, (u64, u16, u16));

pub open spec fn part2_layer_config_lookup(
    layers: Seq<Part2LayerRoutingConfig>, index: usize,
) -> Result<Part2LayerRoutingConfig, crate::DecodeError> {
    if index >= layers.len() {
        Err(crate::DecodeError::LayerIndexOutOfRange { index, layers: layers.len() as usize })
    } else { Ok(layers[index as int]) }
}

pub open spec fn part2_dispatch_owned_image(
    file: Part2JpxDecodeInput, index: usize, color: Option<crate::jp2::ColorMethod>, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    match part2_decode_jpx_layer(file, index, color, limits) {
        Err(error) => Err(error),
        Ok(image) => part2_owned_layer_input(image.0, image.1, image.2, image.4),
    }
}

pub open spec fn part2_dispatch_opacity_result(
    applied: (Result<(), crate::DecodeError>, Part2OwnedLayer),
) -> Part2OwnedLayerResult {
    match applied.0 { Err(error) => Err(error), Ok(()) => Ok(applied.1) }
}

pub open spec fn part2_dispatch_registration(value: crate::jp2::CodestreamRegistration) -> Part2LayerRegistration {
    (value.codestream_index, value.horizontal_subsampling, value.vertical_subsampling,
        value.horizontal_offset, value.vertical_offset)
}

pub(crate) open spec fn part2_dispatch_fast_finish(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, geometry: (u64, u16, u16),
    layer_index: usize, image: Part2ConvertedImage, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    match part2_owned_layer_input(image.0, image.1, image.2, image.4) {
        Err(error) => Err(error),
        Ok(owned) => if config.registrations.len() == 0 {
            part2_dispatch_opacity_result(part2_apply_source_layer_opacity(
                file, config.opacity, geometry, layer_index, owned, None, limits))
        } else {
            let registration = part2_dispatch_registration(config.registrations[0]);
            match part2_register_layer(owned, registration, geometry.1, geometry.2) {
                Err(error) => Err(error),
                Ok(registered) => part2_dispatch_opacity_result(part2_apply_source_layer_opacity(
                    file, config.opacity, geometry, registration.0 as usize, registered, None, limits)),
            }
        },
    }
}

pub(crate) open spec fn part2_dispatch_general(config: Part2GeneralLayerConfig) -> bool {
    config.definitions.len() > 0 || config.registrations.len() > 1
        || matches!(config.opacity, Some(Part2SourceOpacity::ChromaKey { .. }))
}

pub(crate) open spec fn part2_dispatch_source(config: Part2GeneralLayerConfig, layer_index: usize) -> usize {
    if config.registrations.len() == 0 { layer_index }
    else { config.registrations[0].codestream_index as usize }
}

pub(crate) open spec fn part2_compositing_layer_cold_run(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, color: Option<crate::jp2::ColorMethod>,
    geometry: (u64, u16, u16), layer_index: usize, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2OwnedLayer> {
    if part2_dispatch_general(config) {
        part2_general_layer_cold_run(file, config, layer_index, limits, events)
    } else {
        part2_jpip_snapshot_bind(part2_jpx_layer_cold_run(file, part2_dispatch_source(config, layer_index), color, limits, events),
            |image, tail| Some((part2_dispatch_fast_finish(file, config, geometry, layer_index, image, limits), tail)))
    }
}

pub(crate) open spec fn part2_compositing_layer_cold_result(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, color: Option<crate::jp2::ColorMethod>,
    geometry: (u64, u16, u16), layer_index: usize, limits: &crate::ResourceLimits, result: Part2OwnedLayerResult,
) -> bool {
    part2_cold_framed(|events| part2_compositing_layer_cold_run(file, config, color, geometry, layer_index, limits, events), result)
}

pub(crate) proof fn part2_compositing_layer_cold_normal(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, color: Option<crate::jp2::ColorMethod>,
    geometry: (u64, u16, u16), layer_index: usize, limits: &crate::ResourceLimits,
)
    ensures part2_compositing_layer_cold_result(file, config, color, geometry, layer_index, limits,
        part2_decode_compositing_layer(file, config, color, geometry, layer_index, limits)),
{
    reveal(part2_decode_compositing_layer);
    if part2_dispatch_general(config) {
        part2_general_layer_cold_normal(file, config, layer_index, limits);
        part2_cold_framed_extensional(
            |events| part2_general_layer_cold_run(file, config, layer_index, limits, events),
            |events| part2_compositing_layer_cold_run(file, config, color, geometry, layer_index, limits, events),
            part2_decode_compositing_layer(file, config, color, geometry, layer_index, limits));
    } else {
        let index = part2_dispatch_source(config, layer_index);
        let image = part2_decode_jpx_layer(file, index, color, limits);
        part2_jpx_layer_cold_normal(file, index, color, limits);
        if let Ok(value) = image { part2_cold_pure(part2_dispatch_fast_finish(file, config, geometry, layer_index, value, limits)); }
        part2_cold_bind(
            |events| part2_jpx_layer_cold_run(file, index, color, limits, events),
            |value, tail| Some((part2_dispatch_fast_finish(file, config, geometry, layer_index, value, limits), tail)),
            image, part2_decode_compositing_layer(file, config, color, geometry, layer_index, limits));
    }
}

pub(crate) proof fn part2_compositing_layer_cold_general_actual(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, color: Option<crate::jp2::ColorMethod>,
    geometry: (u64, u16, u16), layer_index: usize, limits: &crate::ResourceLimits, result: Part2OwnedLayerResult,
)
    requires part2_dispatch_general(config), part2_general_layer_cold_result(file, config, layer_index, limits, result),
    ensures part2_compositing_layer_cold_result(file, config, color, geometry, layer_index, limits, result),
{
    part2_cold_framed_extensional(
        |events| part2_general_layer_cold_run(file, config, layer_index, limits, events),
        |events| part2_compositing_layer_cold_run(file, config, color, geometry, layer_index, limits, events), result);
}

pub(crate) proof fn part2_compositing_layer_cold_source_error(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, color: Option<crate::jp2::ColorMethod>,
    geometry: (u64, u16, u16), layer_index: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires !part2_dispatch_general(config),
        part2_jpx_layer_cold_result(file, part2_dispatch_source(config, layer_index), color, limits, Err(error)),
    ensures part2_compositing_layer_cold_result(file, config, color, geometry, layer_index, limits, Err(error)),
{
    part2_cold_bind(
        |events| part2_jpx_layer_cold_run(file, part2_dispatch_source(config, layer_index), color, limits, events),
        |image, tail| Some((part2_dispatch_fast_finish(file, config, geometry, layer_index, image, limits), tail)),
        Err(error), Err(error));
}

pub(crate) open spec fn part2_effective_layer_cold_run(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, index: usize,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2OwnedLayer> {
    if layers.len() == 0 {
        if index >= file.1.len() {
            Some((Err(crate::DecodeError::LayerIndexOutOfRange { index, layers: file.1.len() as usize }), events))
        } else {
            part2_jpip_snapshot_bind(part2_jpx_layer_cold_run(file, index, None, limits, events),
                |image: Part2ConvertedImage, tail| Some((part2_owned_layer_input(image.0, image.1, image.2, image.4), tail)))
        }
    } else {
        match part2_layer_config_lookup(layers, index) {
            Err(error) => Some((Err(error), events)),
            Ok(config) => part2_compositing_layer_cold_run(file, config.0, config.1, config.2, index, limits, events),
        }
    }
}

pub(crate) open spec fn part2_effective_layer_cold_result(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, index: usize,
    limits: &crate::ResourceLimits, result: Part2OwnedLayerResult,
) -> bool {
    part2_cold_framed(|events| part2_effective_layer_cold_run(file, layers, index, limits, events), result)
}

pub(crate) proof fn part2_effective_layer_cold_normal(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, index: usize, limits: &crate::ResourceLimits,
)
    ensures part2_effective_layer_cold_result(file, layers, index, limits,
        part2_decode_effective_layer(file, layers, index, limits)),
{
    reveal(part2_decode_effective_layer);
    if layers.len() == 0 {
        if index >= file.1.len() {
            part2_cold_pure::<Part2OwnedLayer>(Err(crate::DecodeError::LayerIndexOutOfRange {
                index, layers: file.1.len() as usize }));
        } else {
            let image = part2_decode_jpx_layer(file, index, None, limits);
            part2_jpx_layer_cold_normal(file, index, None, limits);
            if let Ok(value) = image { part2_cold_pure(part2_owned_layer_input(value.0, value.1, value.2, value.4)); }
            part2_cold_bind(
                |events| part2_jpx_layer_cold_run(file, index, None, limits, events),
                |value: Part2ConvertedImage, tail| Some((part2_owned_layer_input(value.0, value.1, value.2, value.4), tail)),
                image, part2_decode_effective_layer(file, layers, index, limits));
        }
    } else {
        match part2_layer_config_lookup(layers, index) {
            Err(error) => { part2_cold_pure::<Part2OwnedLayer>(Err(error)); },
            Ok(config) => {
                part2_compositing_layer_cold_normal(file, config.0, config.1, config.2, index, limits);
                part2_cold_framed_extensional(
                    |events| part2_compositing_layer_cold_run(file, config.0, config.1, config.2, index, limits, events),
                    |events| part2_effective_layer_cold_run(file, layers, index, limits, events),
                    part2_decode_effective_layer(file, layers, index, limits));
            },
        }
    }
}

pub(crate) proof fn part2_effective_layer_cold_bare_actual(
    file: Part2JpxDecodeInput, index: usize, limits: &crate::ResourceLimits, image: Part2ConvertedImageResult,
)
    requires index < file.1.len(), part2_jpx_layer_cold_result(file, index, None, limits, image),
    ensures part2_effective_layer_cold_result(file, Seq::empty(), index, limits, match image {
        Err(error) => Err(error), Ok(value) => part2_owned_layer_input(value.0, value.1, value.2, value.4),
    }),
{
    if let Ok(value) = image { part2_cold_pure(part2_owned_layer_input(value.0, value.1, value.2, value.4)); }
    part2_cold_bind(
        |events| part2_jpx_layer_cold_run(file, index, None, limits, events),
        |value: Part2ConvertedImage, tail| Some((part2_owned_layer_input(value.0, value.1, value.2, value.4), tail)),
        image, match image { Err(error) => Err(error),
            Ok(value) => part2_owned_layer_input(value.0, value.1, value.2, value.4) });
}

pub(crate) proof fn part2_effective_layer_cold_routed_actual(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, index: usize,
    limits: &crate::ResourceLimits, config: Part2LayerRoutingConfig, result: Part2OwnedLayerResult,
)
    requires layers.len() != 0, part2_layer_config_lookup(layers, index) == Ok(config),
        part2_compositing_layer_cold_result(file, config.0, config.1, config.2, index, limits, result),
    ensures part2_effective_layer_cold_result(file, layers, index, limits, result),
{
    part2_cold_framed_extensional(
        |events| part2_compositing_layer_cold_run(file, config.0, config.1, config.2, index, limits, events),
        |events| part2_effective_layer_cold_run(file, layers, index, limits, events), result);
}

#[verifier::opaque]
pub open spec fn part2_decode_compositing_layer(
    file: Part2JpxDecodeInput, config: Part2GeneralLayerConfig, color: Option<crate::jp2::ColorMethod>,
    geometry: (u64, u16, u16), layer_index: usize, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    if config.definitions.len() > 0 || config.registrations.len() > 1
        || matches!(config.opacity, Some(Part2SourceOpacity::ChromaKey { .. })) {
        part2_decode_general_layer(file, config, layer_index, limits)
    } else if config.registrations.len() == 0 {
        match part2_dispatch_owned_image(file, layer_index, color, limits) {
            Err(error) => Err(error),
            Ok(owned) => part2_dispatch_opacity_result(part2_apply_source_layer_opacity(
                file, config.opacity, geometry, layer_index, owned, None, limits)),
        }
    } else {
        let registration = part2_dispatch_registration(config.registrations[0]);
        match part2_dispatch_owned_image(file, registration.0 as usize, color, limits) {
            Err(error) => Err(error),
            Ok(owned) => match part2_register_layer(owned, registration, geometry.1, geometry.2) {
                Err(error) => Err(error),
                Ok(registered) => part2_dispatch_opacity_result(part2_apply_source_layer_opacity(
                    file, config.opacity, geometry, registration.0 as usize, registered,
                    if config.registrations.len() > 1 {
                        Some(part2_dispatch_registration(config.registrations[1]))
                    } else { None }, limits)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_decode_effective_layer(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, index: usize, limits: &crate::ResourceLimits,
) -> Part2OwnedLayerResult {
    if layers.len() == 0 {
        if index >= file.1.len() {
            Err(crate::DecodeError::LayerIndexOutOfRange { index, layers: file.1.len() as usize })
        } else { part2_dispatch_owned_image(file, index, None, limits) }
    } else {
        match part2_layer_config_lookup(layers, index) {
            Err(error) => Err(error),
            Ok(config) => part2_decode_compositing_layer(file, config.0, config.1, config.2, index, limits),
        }
    }
}

}
