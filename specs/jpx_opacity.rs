//! Actual source-derived opacity decisions and complete mutation/error frames.

use super::*;

verus! {

pub enum Part2SourceOpacity {
    Straight,
    Premultiplied,
    ChromaKey { channels: u8, values: Seq<u8> },
}

pub open spec fn part2_opacity_header_depth(file: Part2JpxDecodeInput, index: usize)
    -> Result<crate::jp2::ComponentBitDepth, crate::DecodeError>
{
    match part2_jpx_codestream_lookup(file.1, index) {
        Err(error) => Err(error),
        Ok(source) => {
            let header = match source.2 {
                None => file.2,
                Some(association) => match association.1 { None => file.2, Some(header) => header },
            };
            Ok(header.1.bit_depth)
        },
    }
}

pub open spec fn part2_source_registered_opacity(
    file: Part2JpxDecodeInput, registration: Part2LayerRegistration, grid: (u16, u16),
    owned: Part2OwnedLayer, premultiplied: bool, limits: &crate::ResourceLimits,
) -> (Result<(), crate::DecodeError>, Part2OwnedLayer) {
    match part2_decode_jpx_layer(file, registration.0 as usize, None, limits) {
        Err(error) => (Err(error), owned),
        Ok(image) => part2_registered_opacity_finish(image, registration, grid, owned, premultiplied),
    }
}

pub open spec fn part2_registered_opacity_finish(
    image: Part2ConvertedImage, registration: Part2LayerRegistration, grid: (u16, u16),
    owned: Part2OwnedLayer, premultiplied: bool,
) -> (Result<(), crate::DecodeError>, Part2OwnedLayer) {
    match part2_owned_layer_input(image.0, image.1, image.2, image.4) {
            Err(error) => (Err(error), owned),
            Ok(source) => match part2_register_layer(source, registration, grid.0, grid.1) {
                Err(error) => (Err(error), owned),
                Ok(registered) => part2_copy_registered_opacity(owned, registered, premultiplied),
            },
    }
}

pub(crate) open spec fn part2_opacity_cold_run(
    file: Part2JpxDecodeInput, opacity: Option<Part2SourceOpacity>, geometry: (u64, u16, u16),
    color_codestream: usize, owned: Part2OwnedLayer, registration: Option<Part2LayerRegistration>,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Result<(), crate::DecodeError>, Part2OwnedLayer)> {
    if matches!(opacity, Some(Part2SourceOpacity::Straight) | Some(Part2SourceOpacity::Premultiplied)) {
        match registration {
            None => Some((Ok(part2_apply_source_layer_opacity(
                file, opacity, geometry, color_codestream, owned, registration, limits)), events)),
            Some(registration) => match part2_jpx_layer_cold_run(file, registration.0 as usize, None, limits, events) {
                None => None,
                Some((Err(error), tail)) => Some((Ok((Err(error), owned)), tail)),
                Some((Ok(image), tail)) => Some((Ok(part2_registered_opacity_finish(image, registration,
                    (geometry.1, geometry.2), owned, opacity == Some(Part2SourceOpacity::Premultiplied))), tail)),
            },
        }
    } else {
        Some((Ok(part2_apply_source_layer_opacity(
            file, opacity, geometry, color_codestream, owned, registration, limits)), events))
    }
}

pub(crate) open spec fn part2_opacity_cold_result(
    file: Part2JpxDecodeInput, opacity: Option<Part2SourceOpacity>, geometry: (u64, u16, u16),
    color_codestream: usize, owned: Part2OwnedLayer, registration: Option<Part2LayerRegistration>,
    limits: &crate::ResourceLimits, result: (Result<(), crate::DecodeError>, Part2OwnedLayer),
) -> bool {
    part2_cold_framed(|events| part2_opacity_cold_run(
        file, opacity, geometry, color_codestream, owned, registration, limits, events), Ok(result))
}

pub(crate) proof fn part2_opacity_cold_normal(
    file: Part2JpxDecodeInput, opacity: Option<Part2SourceOpacity>, geometry: (u64, u16, u16),
    color_codestream: usize, owned: Part2OwnedLayer, registration: Option<Part2LayerRegistration>,
    limits: &crate::ResourceLimits,
)
    ensures part2_opacity_cold_result(file, opacity, geometry, color_codestream, owned, registration, limits,
        part2_apply_source_layer_opacity(file, opacity, geometry, color_codestream, owned, registration, limits)),
{
    part2_apply_source_layer_opacity_unfold(file, opacity, geometry, color_codestream, owned, registration, limits);
    let result = part2_apply_source_layer_opacity(file, opacity, geometry, color_codestream, owned, registration, limits);
    if matches!(opacity, Some(Part2SourceOpacity::Straight) | Some(Part2SourceOpacity::Premultiplied))
        && registration.is_some() {
        let alpha = registration.unwrap();
        let decoded = part2_decode_jpx_layer(file, alpha.0 as usize, None, limits);
        part2_jpx_layer_cold_normal(file, alpha.0 as usize, None, limits);
        let run = |events| part2_jpx_layer_cold_run(file, alpha.0 as usize, None, limits, events);
        let prefix = part2_cold_witness(run, decoded);
        assert forall|tail: Seq<Part2JpipSnapshotEvent>|
            #[trigger] part2_opacity_cold_run(file, opacity, geometry, color_codestream,
                owned, registration, limits, prefix + tail) == Some((Ok(result), tail)) by {
            part2_cold_prefix_at(run, prefix, decoded, tail);
        }
        assert(part2_cold_prefix(|events| part2_opacity_cold_run(
            file, opacity, geometry, color_codestream, owned, registration, limits, events), prefix, Ok(result)));
    } else {
        part2_cold_pure(Ok(result));
    }
}

pub(crate) proof fn part2_opacity_cold_decode_error(
    file: Part2JpxDecodeInput, opacity: Option<Part2SourceOpacity>, geometry: (u64, u16, u16),
    color_codestream: usize, owned: Part2OwnedLayer, registration: Part2LayerRegistration,
    limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires matches!(opacity, Some(Part2SourceOpacity::Straight) | Some(Part2SourceOpacity::Premultiplied)),
        part2_jpx_layer_cold_result(file, registration.0 as usize, None, limits, Err(error)),
    ensures part2_opacity_cold_result(file, opacity, geometry, color_codestream, owned,
        Some(registration), limits, (Err(error), owned)),
{
    let run = |events| part2_jpx_layer_cold_run(file, registration.0 as usize, None, limits, events);
    let prefix = part2_cold_witness(run, Err(error));
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_opacity_cold_run(file, opacity, geometry, color_codestream,
            owned, Some(registration), limits, prefix + tail) == Some((Ok((Err(error), owned)), tail)) by {
        part2_cold_prefix_at(run, prefix, Err(error), tail);
    }
    assert(part2_cold_prefix(|events| part2_opacity_cold_run(
        file, opacity, geometry, color_codestream, owned, Some(registration), limits, events),
        prefix, Ok((Err(error), owned))));
}

pub closed spec fn part2_apply_source_layer_opacity(
    file: Part2JpxDecodeInput, opacity: Option<Part2SourceOpacity>, geometry: (u64, u16, u16),
    color_codestream: usize, owned: Part2OwnedLayer, registration: Option<Part2LayerRegistration>,
    limits: &crate::ResourceLimits,
) -> (Result<(), crate::DecodeError>, Part2OwnedLayer) {
    match opacity {
        None => (Ok(()), owned),
        Some(Part2SourceOpacity::Straight) | Some(Part2SourceOpacity::Premultiplied) => {
            let premultiplied = opacity == Some(Part2SourceOpacity::Premultiplied);
            match registration {
                None => part2_set_layer_alpha_mode(owned, premultiplied, geometry.0),
                Some(registration) => part2_source_registered_opacity(
                    file, registration, (geometry.1, geometry.2), owned, premultiplied, limits),
            }
        },
        Some(Part2SourceOpacity::ChromaKey { channels, values }) => {
            if channels as usize != owned.3.len() {
                (Err(crate::DecodeError::MalformedInput {
                    offset: geometry.0, kind: crate::MalformedKind::InvalidBoxContents,
                }), owned)
            } else {
                match part2_opacity_header_depth(file, color_codestream) {
                    Err(error) => (Err(error), owned),
                    Ok(depth) => match part2_normalized_chroma_keys(values, channels, depth) {
                        Err(error) => (Err(error), owned),
                        Ok(keys) => part2_apply_chroma_key_policy(owned, keys, true),
                    },
                }
            }
        },
    }
}

pub(crate) proof fn part2_apply_source_layer_opacity_unfold(
    file: Part2JpxDecodeInput, opacity: Option<Part2SourceOpacity>, geometry: (u64, u16, u16),
    color_codestream: usize, owned: Part2OwnedLayer, registration: Option<Part2LayerRegistration>,
    limits: &crate::ResourceLimits,
)
    ensures part2_apply_source_layer_opacity(file, opacity, geometry, color_codestream, owned, registration, limits)
        == match opacity {
            None => (Ok(()), owned),
            Some(Part2SourceOpacity::Straight) | Some(Part2SourceOpacity::Premultiplied) => {
                let premultiplied = opacity == Some(Part2SourceOpacity::Premultiplied);
                match registration {
                    None => part2_set_layer_alpha_mode(owned, premultiplied, geometry.0),
                    Some(registration) => part2_source_registered_opacity(
                        file, registration, (geometry.1, geometry.2), owned, premultiplied, limits),
                }
            },
            Some(Part2SourceOpacity::ChromaKey { channels, values }) => {
                if channels as usize != owned.3.len() {
                    (Err(crate::DecodeError::MalformedInput {
                        offset: geometry.0, kind: crate::MalformedKind::InvalidBoxContents,
                    }), owned)
                } else {
                    match part2_opacity_header_depth(file, color_codestream) {
                        Err(error) => (Err(error), owned),
                        Ok(depth) => match part2_normalized_chroma_keys(values, channels, depth) {
                            Err(error) => (Err(error), owned),
                            Ok(keys) => part2_apply_chroma_key_policy(owned, keys, true),
                        },
                    }
                }
            },
        },
{
}

}
