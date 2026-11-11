use super::admission::{channel_layout, validate_components, validate_output_size};
use super::geometry::{arithmetic_overflow, checked_area, invalid_color_input, unsupported};
use super::normalization::{
    normalize_component, normalized_at, normalized_difference_at, pixel_coordinates,
};
use super::{
    ConvertedChannel, ConvertedChannelType, ConvertedColorSpace, ConvertedImage, FIXED_ONE,
};
#[cfg(verus_keep_ghost)]
use super::{
    converted_channel_result, converted_channel_views, converted_channel_views_push,
    converted_image_result,
};
use crate::image::{ChannelAssociation, TypedImage};
use crate::jp2::{
    ColorMethod, ColorSpecification, ENUMERATED_GRAYSCALE, ENUMERATED_SRGB, ENUMERATED_SYCC,
};
use crate::{DecodeError, ResourceLimits, UnsupportedColorConversion};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures converted_image_result(result) == crate::specs::color_convert_jp2(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_definition_views(image),
            crate::image::typed_image_geometry(image), crate::jp2::color_specification_method(color),
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub fn convert_jp2_color(
    image: &TypedImage,
    color: &ColorSpecification,
    limits: &ResourceLimits,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = crate::image::typed_image_component_views(image);
        let ghost geometry = crate::image::typed_image_geometry(image);
    }
    if image.width() == 0 || image.height() == 0 {
        return Err(invalid_color_input());
    }
    let (color_count, output_space, sycc) = match color.method() {
        ColorMethod::Unspecified => {
            return Err(unsupported(
                UnsupportedColorConversion::UnspecifiedColorSpace,
            ));
        }
        ColorMethod::Enumerated {
            color_space: ENUMERATED_SRGB,
        } => (3_usize, ConvertedColorSpace::Srgb, false),
        ColorMethod::Enumerated {
            color_space: ENUMERATED_GRAYSCALE,
        } => (1_usize, ConvertedColorSpace::Grayscale, false),
        ColorMethod::Enumerated {
            color_space: ENUMERATED_SYCC,
        } => (3_usize, ConvertedColorSpace::Srgb, true),
        ColorMethod::Enumerated { .. } => {
            return Err(unsupported(
                UnsupportedColorConversion::EnumeratedColorSpace,
            ));
        }
        ColorMethod::RestrictedIcc { .. } | ColorMethod::AnyIcc { .. } => {
            return Err(unsupported(UnsupportedColorConversion::IccProfile));
        }
    };
    let layout = channel_layout(image, color_count)?;
    validate_components(image, &layout)?;
    validate_output_size(image, color_count, layout.alphas.len(), limits)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost colors = layout.colors@; }

    let pixel_count = checked_area(image.width(), image.height())?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::proofs::internal_specs::color_conversion_ready(
            input, crate::image::typed_image_definition_views(image), geometry,
            crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
            (color_count, output_space, sycc), pixel_count,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
        ));
    }
    let mut channels = Vec::with_capacity(
        color_count
            .checked_add(layout.alphas.len())
            .ok_or_else(arithmetic_overflow)?,
    );
    if sycc {
        let width = usize::try_from(image.width()).map_err(|_| arithmetic_overflow())?;
        if width == 0 {
            return Err(invalid_color_input());
        }
        let mut red = Vec::with_capacity(pixel_count);
        let mut green = Vec::with_capacity(pixel_count);
        let mut blue = Vec::with_capacity(pixel_count);
        let mut pixel = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_sycc_empty(input, geometry, colors, width);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant pixel <= pixel_count,
                    sycc,
                    input == crate::image::typed_image_component_views(image),
                    geometry == crate::image::typed_image_geometry(image),
                    colors == layout.colors@,
                    width as nat == geometry.0 as nat,
                    width > 0,
                    crate::specs::part2_layer_area(geometry.0, geometry.1) == Ok(pixel_count),
                    crate::specs::color_sycc_planes_prefix(input, geometry, colors, width, pixel as nat)
                        == Ok((red@, green@, blue@)),
                    crate::proofs::internal_specs::color_conversion_ready(
                        input, crate::image::typed_image_definition_views(image), geometry,
                        crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
                        (color_count, output_space, sycc), pixel_count,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
                    ),
                decreases pixel_count - pixel,
            )
        )]
        while pixel < pixel_count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_color_sycc_step(input, geometry, colors, width, pixel as nat);
            }
            let (r, g, b) = match convert_sycc_pixel(image, &layout.colors, pixel, width) {
                Ok(value) => value,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_color_sycc_error(
                            input, geometry, colors, width, pixel as nat + 1, pixel_count as nat, error,
                        );
                    }
                    return Err(error);
                }
            };
            red.push(r);
            green.push(g);
            blue.push(b);
            pixel = pixel.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost sycc_planes = (red@, green@, blue@); }
        channels.push(ConvertedChannel {
            channel_type: ConvertedChannelType::Red,
            samples: red,
        });
        channels.push(ConvertedChannel {
            channel_type: ConvertedChannelType::Green,
            samples: green,
        });
        channels.push(ConvertedChannel {
            channel_type: ConvertedChannelType::Blue,
            samples: blue,
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(converted_channel_views(channels@) =~= seq![
                (ConvertedChannelType::Red, sycc_planes.0),
                (ConvertedChannelType::Green, sycc_planes.1),
                (ConvertedChannelType::Blue, sycc_planes.2),
            ]);
        }
    } else {
        let mut color_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_channels_empty(input, geometry, colors, color_count);
            assert(converted_channel_views(channels@) =~= Seq::<crate::specs::ColorChannelModel>::empty());
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant color_index <= color_count,
                    !sycc,
                    input == crate::image::typed_image_component_views(image),
                    geometry == crate::image::typed_image_geometry(image),
                    colors == layout.colors@,
                    crate::specs::color_convert_channels_prefix(input, geometry, colors, color_count, color_index as nat)
                        == Ok(converted_channel_views(channels@)),
                    crate::proofs::internal_specs::color_conversion_ready(
                        input, crate::image::typed_image_definition_views(image), geometry,
                        crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
                        (color_count, output_space, sycc), pixel_count,
                        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
                    ),
                decreases color_count - color_index,
            )
        )]
        while color_index < color_count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_color_channels_step(
                    input, geometry, colors, color_count, color_index as nat,
                );
            }
            let channel = match convert_color_channel(
                image,
                &layout.colors,
                color_count,
                color_index,
            ) {
                Ok(channel) => channel,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_color_channels_error(
                            input, geometry, colors, color_count, color_index as nat + 1, color_count as nat, error,
                        );
                    }
                    return Err(error);
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! { converted_channel_views_push(channels@, channel); }
            channels.push(channel);
            color_index = color_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
    }

    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = converted_channel_views(channels@);
        let ghost alphas = layout.alphas@;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::color_convert_colors(input, geometry, colors, color_count, sycc) == Ok(initial));
        crate::proofs::production_impl::production_color_alphas_empty(input, geometry, alphas, initial);
    }
    let mut alpha_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant alpha_index <= layout.alphas.len(),
                input == crate::image::typed_image_component_views(image),
                geometry == crate::image::typed_image_geometry(image),
                colors == layout.colors@,
                alphas == layout.alphas@,
                crate::specs::color_convert_colors(input, geometry, colors, color_count, sycc) == Ok(initial),
                crate::specs::color_append_alphas_prefix(input, geometry, alphas, initial, alpha_index as nat)
                    == Ok(converted_channel_views(channels@)),
                crate::proofs::internal_specs::color_conversion_ready(
                    input, crate::image::typed_image_definition_views(image), geometry,
                    crate::jp2::color_specification_method(color), (layout.colors@, layout.alphas@),
                    (color_count, output_space, sycc), pixel_count,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits),
                ),
            decreases layout.alphas.len() - alpha_index,
        )
    )]
    while alpha_index < layout.alphas.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_alphas_step(input, geometry, alphas, initial, alpha_index as nat);
        }
        let alpha = *layout
            .alphas
            .get(alpha_index)
            .ok_or_else(invalid_color_input)?;
        let channel = match convert_alpha_channel(image, alpha) {
            Ok(channel) => channel,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_color_alphas_error(
                        input, geometry, alphas, initial, alpha_index as nat + 1, alphas.len(), error,
                    );
                }
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! { converted_channel_views_push(channels@, channel); }
        channels.push(channel);
        alpha_index = alpha_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }

    Ok(ConvertedImage {
        width: image.width(),
        height: image.height(),
        color_space: output_space,
        precision: 16,
        channels,
    })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures converted_channel_result(result) == crate::specs::color_convert_channel(
            crate::image::typed_image_component_views(image), crate::image::typed_image_geometry(image),
            colors@, color_count, index,
        ),
    )
)]
fn convert_color_channel(
    image: &TypedImage,
    colors: &[usize],
    color_count: usize,
    index: usize,
) -> Result<ConvertedChannel, DecodeError> {
    let component_index = *colors.get(index).ok_or_else(invalid_color_input)?;
    let component = image
        .components()
        .get(component_index)
        .ok_or_else(invalid_color_input)?;
    let samples = normalize_component(
        component,
        image.width(),
        image.height(),
        image.x_origin(),
        image.y_origin(),
    )?;
    let channel_type = match (color_count, index) {
        (1, 0) => ConvertedChannelType::Gray,
        (3, 0) => ConvertedChannelType::Red,
        (3, 1) => ConvertedChannelType::Green,
        (3, 2) => ConvertedChannelType::Blue,
        _ => return Err(invalid_color_input()),
    };
    Ok(ConvertedChannel {
        channel_type,
        samples,
    })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures converted_channel_result(result) == crate::specs::color_convert_alpha(
            crate::image::typed_image_component_views(image), crate::image::typed_image_geometry(image), alpha,
        ),
    )
)]
fn convert_alpha_channel(
    image: &TypedImage,
    alpha: (usize, bool, ChannelAssociation),
) -> Result<ConvertedChannel, DecodeError> {
    let component = image
        .components()
        .get(alpha.0)
        .ok_or_else(invalid_color_input)?;
    let samples = normalize_component(
        component,
        image.width(),
        image.height(),
        image.x_origin(),
        image.y_origin(),
    )?;
    Ok(ConvertedChannel {
        channel_type: ConvertedChannelType::Alpha {
            premultiplied: alpha.1,
            association: alpha.2,
        },
        samples,
    })
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_sycc_pixel(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image).2, crate::image::typed_image_geometry(image).3,
            colors@, pixel, width,
        ),
    )
)]
fn convert_sycc_pixel(
    image: &TypedImage,
    colors: &[usize],
    pixel: usize,
    width: usize,
) -> Result<(u16, u16, u16), DecodeError> {
    let (x, y) = pixel_coordinates(pixel, width)?;
    let luminance = normalized_at(
        image,
        *colors.first().ok_or_else(invalid_color_input)?,
        x,
        y,
    )?;
    let cb =
        normalized_difference_at(image, *colors.get(1).ok_or_else(invalid_color_input)?, x, y)?;
    let cr =
        normalized_difference_at(image, *colors.get(2).ok_or_else(invalid_color_input)?, x, y)?;
    sycc_to_srgb(luminance, cb, cr)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_sycc_to_srgb(y, cb, cr),)
)]
pub(super) fn sycc_to_srgb(y: u16, cb: i32, cr: i32) -> Result<(u16, u16, u16), DecodeError> {
    let y = i128::from(y);
    let cb = i128::from(cb);
    let cr = i128::from(cr);
    let red_delta = rounded_fixed(
        91_881_i128
            .checked_mul(cr)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let green_blue_delta = rounded_fixed(
        22_554_i128
            .checked_mul(cb)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let green_red_delta = rounded_fixed(
        46_802_i128
            .checked_mul(cr)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let blue_delta = rounded_fixed(
        116_130_i128
            .checked_mul(cb)
            .ok_or_else(arithmetic_overflow)?,
    )?;
    let red = y.checked_add(red_delta).ok_or_else(arithmetic_overflow)?;
    let green = y
        .checked_sub(green_blue_delta)
        .ok_or_else(arithmetic_overflow)?;
    let green = green
        .checked_sub(green_red_delta)
        .ok_or_else(arithmetic_overflow)?;
    let blue = y.checked_add(blue_delta).ok_or_else(arithmetic_overflow)?;
    Ok((clamp_u16(red), clamp_u16(green), clamp_u16(blue)))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_rounded_fixed(value),)
)]
pub(super) fn rounded_fixed(value: i128) -> Result<i128, DecodeError> {
    if value < 0 {
        Ok(value
            .checked_sub(FIXED_ONE / 2)
            .ok_or_else(arithmetic_overflow)?
            / FIXED_ONE)
    } else {
        Ok(value
            .checked_add(FIXED_ONE / 2)
            .ok_or_else(arithmetic_overflow)?
            / FIXED_ONE)
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_clamp_u16(value as int),)
)]
fn clamp_u16(value: i128) -> u16 {
    if value <= 0 {
        0
    } else if value >= i128::from(u16::MAX) {
        u16::MAX
    } else {
        value as u16
    }
}
