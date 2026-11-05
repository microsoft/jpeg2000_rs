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
