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
        Ok(image) => match part2_owned_layer_input(image.0, image.1, image.2, image.4) {
            Err(error) => (Err(error), owned),
            Ok(source) => match part2_register_layer(source, registration, grid.0, grid.1) {
                Err(error) => (Err(error), owned),
                Ok(registered) => part2_copy_registered_opacity(owned, registered, premultiplied),
            },
        },
    }
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
