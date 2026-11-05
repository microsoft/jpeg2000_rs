//! Layer alpha modes and registered opacity application.
use super::chroma::{apply_chroma_key_with_policy, normalized_chroma_keys};
use super::layer_decode::{decode_layer, owned_layer_from_image};
use super::registration::register_layer;
use super::resources::{arithmetic_overflow, checked_area, index_of, invalid_layer};
use super::{
    CompositingLayer, DecodeError, DecodeOptions, Jp2File, LayerOpacity, MalformedKind, OwnedLayer,
    jp2,
};
#[cfg(verus_keep_ghost)]
use super::{layer_registration_view, owned_layer_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, owned_layer_view(final(owned))) == crate::specs::part2_set_layer_alpha_mode(
            owned_layer_view(old(owned)), premultiplied, offset),
    )
)]
pub(super) fn set_layer_alpha_mode(
    owned: &mut OwnedLayer,
    premultiplied: bool,
    offset: u64,
) -> Result<(), DecodeError> {
    match owned.alpha.as_mut() {
        Some(alpha) => {
            alpha.1 = premultiplied;
            Ok(())
        }
        None => Err(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::MissingRequiredStructure,
        }),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, final(alpha)@) == crate::specs::part2_opacity_pixel(
            (samples@, geometry.0, geometry.1), geometry.2, geometry.3, old(alpha)@),
            final(alpha)@.len() == old(alpha)@.len(),
    )
)]
pub(super) fn copy_opacity_pixel(
    samples: &[u16],
    geometry: (u32, u32, u32, u32),
    alpha: &mut [u16],
) -> Result<(), DecodeError> {
    let (source_width, width, x, y) = geometry;
    let destination = index_of(width, x, y)?;
    *alpha.get_mut(destination).ok_or_else(invalid_layer)? = *samples
        .get(index_of(source_width, x, y)?)
        .ok_or_else(invalid_layer)?;
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, final(alpha)@) == crate::specs::part2_opacity_columns_prefix(
            (samples@, source_width, destination.0), destination.1, old(alpha)@, destination.2 as nat),
    )
)]
pub(super) fn copy_opacity_row(
    samples: &[u16],
    source_width: u32,
    destination: (u32, u32, u32),
    alpha: &mut [u16],
) -> Result<(), DecodeError> {
    let (width, y, copy_width) = destination;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost context = (samples@, source_width, width); let ghost initial = alpha@; }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_opacity_columns_empty(context, y, initial); }
    let mut x = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant x <= copy_width, destination == (width, y, copy_width),
                context == (samples@, source_width, width), initial == old(alpha)@,
                crate::specs::part2_opacity_columns_prefix(context, y, initial, x as nat) == (Ok(()), alpha@),
            decreases copy_width - x,
        )
    )]
    while x < copy_width {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_opacity_columns_step(context, y, initial, x as nat); }
        let result = copy_opacity_pixel(samples, (source_width, width, x, y), alpha);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = result {
                assert(crate::specs::part2_opacity_columns_prefix(context, y, initial, x as nat + 1) == (Err(error), alpha@));
                crate::proofs::production_impl::production_opacity_columns_error(context, y, initial, x as nat + 1, copy_width as nat);
            } else { crate::proofs::production_impl::production_mct_unit_result(result); }
        }
        result?;
        x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (result, owned_layer_view(final(owned))) == crate::specs::part2_copy_registered_opacity(
            owned_layer_view(old(owned)), owned_layer_view(source), premultiplied),
    )
)]
pub(super) fn copy_registered_layer_opacity(
    owned: &mut OwnedLayer,
    source: &OwnedLayer,
    premultiplied: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = owned_layer_view(owned); let ghost registered = owned_layer_view(source); }
    let samples = source.colors.first().ok_or_else(invalid_layer)?;
    let pixels = checked_area(owned.width, owned.height)?;
    let mut alpha = vec![0_u16; pixels];
    let copy_width = owned.width.min(source.width);
    let copy_height = owned.height.min(source.height);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = alpha@;
        let ghost context = (samples@, source.width, owned.width);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(initial =~= Seq::new(pixels as nat, |_index: int| 0u16));
        crate::proofs::production_impl::production_opacity_rows_empty(context, copy_width, initial);
    }
    let mut y = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant y <= copy_height, input == owned_layer_view(old(owned)), input == owned_layer_view(owned),
                registered == owned_layer_view(source), registered.3.len() > 0,
                samples@ == registered.3[0],
                context == (registered.3[0], registered.0, input.0),
                crate::specs::part2_layer_area(input.0, input.1) == Ok(pixels),
                initial == Seq::new(pixels as nat, |_index: int| 0u16),
                copy_width == if input.0 < registered.0 { input.0 } else { registered.0 },
                copy_height == if input.1 < registered.1 { input.1 } else { registered.1 },
                crate::specs::part2_opacity_rows_prefix(context, copy_width, initial, y as nat) == (Ok(()), alpha@),
            decreases copy_height - y,
        )
    )]
    while y < copy_height {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_opacity_rows_step(context, copy_width, initial, y as nat); }
        let result = copy_opacity_row(
            samples,
            source.width,
            (owned.width, y, copy_width),
            &mut alpha,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = result {
                assert(crate::specs::part2_opacity_rows_prefix(context, copy_width, initial, y as nat + 1)
                    == (Err(error), alpha@));
                crate::proofs::production_impl::production_opacity_rows_error(
                    context, copy_width, initial, y as nat + 1, copy_height as nat);
            } else { crate::proofs::production_impl::production_mct_unit_result(result); }
        }
        result?;
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    owned.alpha = Some((alpha, premultiplied));
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, owned_layer_view(final(owned))) == crate::specs::part2_apply_source_layer_opacity(
        jp2::jpx_file_decode_view(file), jp2::source_layer_opacity(layer), jp2::source_layer_geometry(layer),
        color_codestream, owned_layer_view(old(owned)),
        match alpha_registration { None => None, Some(registration) => Some(layer_registration_view(registration)) },
        crate::options::decode_options_limits(options)),
))]
pub(super) fn apply_layer_opacity(
    file: &Jp2File<'_>,
    layer: &CompositingLayer<'_>,
    color_codestream: usize,
    owned: &mut OwnedLayer,
    alpha_registration: Option<&jp2::CodestreamRegistration>,
    options: &DecodeOptions,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_apply_source_layer_opacity_unfold(
            jp2::jpx_file_decode_view(file), jp2::source_layer_opacity(layer), jp2::source_layer_geometry(layer),
            color_codestream, owned_layer_view(owned),
            match alpha_registration { None => None, Some(registration) => Some(layer_registration_view(registration)) },
            crate::options::decode_options_limits(options));
    }
    let Some(opacity) = layer.opacity() else {
        return Ok(());
    };
    #[cfg(verus_keep_ghost)]
    proof! { jp2::source_opacity_known(opacity); }
    match opacity {
        LayerOpacity::Straight | LayerOpacity::Premultiplied => {
            let premultiplied = matches!(opacity, LayerOpacity::Premultiplied);
            if let Some(registration) = alpha_registration {
                let image = decode_layer(
                    file,
                    usize::from(registration.codestream_index),
                    None,
                    options,
                )?;
                let alpha_source = owned_layer_from_image(&image)?;
                let alpha_registered = register_layer(
                    &alpha_source,
                    registration,
                    layer.horizontal_grid_size(),
                    layer.vertical_grid_size(),
                )?;
                copy_registered_layer_opacity(owned, &alpha_registered, premultiplied)?;
            } else {
                set_layer_alpha_mode(owned, premultiplied, layer.box_header().offset())?;
            }
        }
        LayerOpacity::ChromaKey { channels, values } => {
            if usize::from(*channels) != owned.colors.len() {
                return Err(DecodeError::malformed(
                    layer.box_header().offset(),
                    MalformedKind::InvalidBoxContents,
                ));
            }
            let header = file
                .codestream(color_codestream)?
                .codestream_header()
                .and_then(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: (Option<&jp2::Jp2Header>) =>
                        ensures jp2::associated_header_option(result) == jp2::source_association_header_view(association).1,
                    ))]
                    |association| association.parsed_header(),
                )
                .unwrap_or(file.header());
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_opacity_header_depth(jp2::jpx_file_decode_view(file), color_codestream)
                    == Ok(header.image.bit_depth));
            }
            let keys = normalized_chroma_keys(values, *channels, header.image.bit_depth)?;
            apply_chroma_key_with_policy(owned, &keys, true)?;
        }
    }
    Ok(())
}
