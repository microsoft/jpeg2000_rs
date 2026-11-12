use super::OUTPUT_MAXIMUM;
use super::geometry::{
    arithmetic_overflow, checked_area, invalid_color_input, registered_ceil_div,
    registered_floor_div,
};
#[cfg(verus_keep_ghost)]
use super::normalized_plane_result;
use crate::DecodeError;
use crate::image::{TypedComponent, TypedImage, TypedSamples};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures normalized_plane_result(result) == crate::specs::color_normalize_component(
            crate::image::typed_component_view(component), width, height, x_origin, y_origin,
        ),
    )
)]
pub(crate) fn normalize_component(
    component: &TypedComponent,
    width: u32,
    height: u32,
    x_origin: u32,
    y_origin: u32,
) -> Result<Vec<u16>, DecodeError> {
    if width == 0 {
        return Err(invalid_color_input());
    }
    let row_width = usize::try_from(width).map_err(|_| arithmetic_overflow())?;
    if row_width == 0 {
        return Err(invalid_color_input());
    }
    let count = checked_area(width, height)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = crate::image::typed_component_view(component);
    }
    let mut output = Vec::with_capacity(count);
    let mut pixel = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_color_plane_empty(input, width, x_origin, y_origin);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant pixel <= count,
                input == crate::image::typed_component_view(component),
                width > 0,
                width as nat <= usize::MAX as nat,
                row_width as nat == width as nat,
                crate::specs::part2_layer_area(width, height) == Ok(count),
                crate::specs::color_normalize_component_prefix(input, width, x_origin, y_origin, pixel as nat)
                    == Ok(output@),
            decreases count - pixel,
        )
    )]
    while pixel < count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_color_plane_step(
                input, width, x_origin, y_origin, pixel as nat,
            );
        }
        let (x, y) = match pixel_coordinates(pixel, row_width) {
            Ok(coordinates) => coordinates,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_color_plane_error(
                        input, width, x_origin, y_origin, pixel as nat + 1, count as nat, error,
                    );
                }
                return Err(error);
            }
        };
        let value = match normalized_component_at(component, x_origin, y_origin, x, y) {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_color_plane_error(
                        input, width, x_origin, y_origin, pixel as nat + 1, count as nat, error,
                    );
                }
                return Err(error);
            }
        };
        output.push(value);
        pixel = pixel.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(output)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_pixel_coordinates(pixel, width),)
)]
pub(super) fn pixel_coordinates(pixel: usize, width: usize) -> Result<(u32, u32), DecodeError> {
    if width == 0 {
        return Err(invalid_color_input());
    }
    let x = match u32::try_from(pixel % width) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let y = match u32::try_from(pixel / width) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    Ok((x, y))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_image_normalized(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image).2,
            crate::image::typed_image_geometry(image).3, component_index, x, y,
        ),
    )
)]
pub(super) fn normalized_at(
    image: &TypedImage,
    component_index: usize,
    x: u32,
    y: u32,
) -> Result<u16, DecodeError> {
    let component = image
        .components()
        .get(component_index)
        .ok_or_else(invalid_color_input)?;
    normalized_component_at(component, image.x_origin(), image.y_origin(), x, y)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_image_difference(
            crate::image::typed_image_component_views(image),
            crate::image::typed_image_geometry(image).2,
            crate::image::typed_image_geometry(image).3, component_index, x, y,
        ),
    )
)]
pub(super) fn normalized_difference_at(
    image: &TypedImage,
    component_index: usize,
    x: u32,
    y: u32,
) -> Result<i32, DecodeError> {
    let component = image
        .components()
        .get(component_index)
        .ok_or_else(invalid_color_input)?;
    let info = component.info();
    if info.precision == 0 || info.precision > 38 {
        return Err(invalid_color_input());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::spec_properties::color_precision_binary_bounds(info.precision);
    }
    let value = nominal_component_at(component, image.x_origin(), image.y_origin(), x, y)?;
    let maximum = (1_u64 << info.precision)
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    if maximum == 0 {
        return Err(invalid_color_input());
    }
    if value > maximum {
        return Err(invalid_color_input());
    }
    let midpoint = 1_u64 << (info.precision - 1);
    let difference = i128::from(value) - i128::from(midpoint);
    let scaled = difference
        .checked_mul(i128::from(OUTPUT_MAXIMUM))
        .ok_or_else(arithmetic_overflow)?;
    let rounded = if scaled < 0 {
        (scaled - i128::from(maximum / 2)) / i128::from(maximum)
    } else {
        (scaled + i128::from(maximum / 2)) / i128::from(maximum)
    };
    match i32::try_from(rounded) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_component_normalized(
            crate::image::typed_component_view(component), image_x_origin, image_y_origin, x, y,
        ),
    )
)]
fn normalized_component_at(
    component: &TypedComponent,
    image_x_origin: u32,
    image_y_origin: u32,
    x: u32,
    y: u32,
) -> Result<u16, DecodeError> {
    let info = component.info();
    let value = nominal_component_at(component, image_x_origin, image_y_origin, x, y)?;
    normalize_unsigned(value, info.precision)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_component_nominal(
            crate::image::typed_component_view(component), image_x_origin, image_y_origin, x, y,
        ),
    )
)]
pub(super) fn nominal_component_at(
    component: &TypedComponent,
    image_x_origin: u32,
    image_y_origin: u32,
    x: u32,
    y: u32,
) -> Result<u64, DecodeError> {
    let info = component.info();
    if info.precision == 0
        || info.precision > 38
        || info.x_subsampling == 0
        || info.y_subsampling == 0
    {
        return Err(invalid_color_input());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::spec_properties::color_precision_binary_bounds(info.precision);
    }
    if component.width() == 0 || component.height() == 0 {
        return Err(invalid_color_input());
    }
    let absolute_x = image_x_origin
        .checked_add(x)
        .ok_or_else(arithmetic_overflow)?;
    let absolute_y = image_y_origin
        .checked_add(y)
        .ok_or_else(arithmetic_overflow)?;
    let x_step = u32::from(info.x_subsampling);
    let y_step = u32::from(info.y_subsampling);
    // Coded window origins follow SIZ; CRG shifts only the physical sample lookup.
    let component_x0 = registered_ceil_div(image_x_origin, x_step, info.x_registration)?;
    let component_y0 = registered_ceil_div(image_y_origin, y_step, info.y_registration)?;
    let component_x1 = component_x0
        .checked_add(component.width())
        .ok_or_else(arithmetic_overflow)?;
    let component_y1 = component_y0
        .checked_add(component.height())
        .ok_or_else(arithmetic_overflow)?;
    let absolute_sample_x = registered_floor_div(absolute_x, x_step, info.x_registration)?
        .max(component_x0)
        .min(
            component_x1
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?,
        );
    let absolute_sample_y = registered_floor_div(absolute_y, y_step, info.y_registration)?
        .max(component_y0)
        .min(
            component_y1
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?,
        );
    let sample_x = absolute_sample_x
        .checked_sub(component_x0)
        .ok_or_else(arithmetic_overflow)?;
    let sample_y = absolute_sample_y
        .checked_sub(component_y0)
        .ok_or_else(arithmetic_overflow)?;
    let row = (sample_y as usize)
        .checked_mul(component.width() as usize)
        .ok_or_else(arithmetic_overflow)?;
    let index = row
        .checked_add(sample_x as usize)
        .ok_or_else(arithmetic_overflow)?;
    match component.samples() {
        TypedSamples::Unsigned(samples) if !info.signed => {
            let value = *samples.get(index).ok_or_else(invalid_color_input)?;
            let maximum = (1_u64 << info.precision)
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
            if value > maximum {
                return Err(invalid_color_input());
            }
            Ok(value)
        }
        TypedSamples::Signed(samples) if info.signed => {
            let value = *samples.get(index).ok_or_else(invalid_color_input)?;
            let shift = info
                .precision
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
            let level = 1_i64 << u32::from(shift);
            let minimum = 0_i64.checked_sub(level).ok_or_else(arithmetic_overflow)?;
            let maximum = level.checked_sub(1).ok_or_else(arithmetic_overflow)?;
            if value < minimum || value > maximum {
                return Err(invalid_color_input());
            }
            if value > i64::MAX - level {
                return Err(arithmetic_overflow());
            }
            u64::try_from(crate::refinement::signed_to_nominal(value, level))
                .map_err(|_| arithmetic_overflow())
        }
        _ => Err(invalid_color_input()),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::color_normalize_unsigned(value, precision),)
)]
pub(crate) fn normalize_unsigned(value: u64, precision: u8) -> Result<u16, DecodeError> {
    if precision == 0 || precision > 38 {
        return Err(invalid_color_input());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::spec_properties::color_precision_binary_bounds(precision);
    }
    let maximum = (1_u64 << precision)
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    if maximum == 0 {
        return Err(invalid_color_input());
    }
    if value > maximum {
        return Err(invalid_color_input());
    }
    let scaled = value
        .checked_mul(OUTPUT_MAXIMUM)
        .ok_or_else(arithmetic_overflow)?;
    let numerator = scaled
        .checked_add(maximum / 2)
        .ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(scaled as nat <= 65535 * (maximum as nat));
        crate::proofs::spec_properties::source_over_rounding_preserves_sample_bound(scaled, maximum);
        assert(numerator / maximum <= 65535);
    }
    match u16::try_from(numerator / maximum) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}
