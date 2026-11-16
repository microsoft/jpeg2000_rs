use super::arithmetic::{arithmetic_overflow, fixed_mul, invalid_image};
#[cfg(verus_keep_ghost)]
use super::decoded_component_view;
use super::{DecodedImage, FIXED_BITS};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(image)@) == crate::specs::part1_apply_component_transform(old(image)@, false),
))]
pub fn apply_reversible_component_transform(image: &mut DecodedImage) -> Result<(), DecodeError> {
    apply_component_transform(image, false)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(image)@) == crate::specs::part1_apply_component_transform(old(image)@, true),
))]
pub fn apply_irreversible_component_transform(image: &mut DecodedImage) -> Result<(), DecodeError> {
    apply_component_transform(image, true)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(image)@) == crate::specs::part1_apply_component_transform(old(image)@, irreversible),
))]
fn apply_component_transform(
    image: &mut DecodedImage,
    irreversible: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = image@; }
    validate_transform_components(image, if irreversible { FIXED_BITS } else { 0 })?;
    if image.components.len() < 3 {
        return Err(invalid_image());
    }
    let length = image.components[0].samples.len();
    if image.components[1].samples.len() != length || image.components[2].samples.len() != length {
        return Err(invalid_image());
    }
    let mut index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= length,
            original == old(image)@,
            crate::specs::part1_validate_transform_components(original, if irreversible { 16u8 } else { 0u8 }) == Ok(()),
            original.4.len() >= 3,
            original.4[1].4.len() == length,
            original.4[2].4.len() == length,
            length == original.4[0].4.len(),
            crate::specs::part1_component_transform_prefix(original, irreversible, index as nat) == (Ok(()), image@),
            decreases length - index,
        )
    )]
    while index < length {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        match apply_component_pixel(image, index, irreversible) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_component_transform_error_persists(
                        original, irreversible, index as nat + 1, length as nat,
                    );
                }
                return Err(error);
            }
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(image)@) == crate::specs::part1_component_pixel_state(old(image)@, index, irreversible),
))]
pub(super) fn apply_component_pixel(
    image: &mut DecodedImage,
    index: usize,
    irreversible: bool,
) -> Result<(), DecodeError> {
    let y = component_sample(image, 0, index)?;
    let cb = component_sample(image, 1, index)?;
    let cr = component_sample(image, 2, index)?;
    let (red, green, blue) = inverse_component_values(y, cb, cr, irreversible)?;
    set_component_sample(image, 0, index, red)?;
    set_component_sample(image, 1, index, green)?;
    set_component_sample(image, 2, index, blue)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_component_values(y, cb, cr, irreversible),
))]
pub(crate) fn inverse_component_values(
    y: i64,
    cb: i64,
    cr: i64,
    irreversible: bool,
) -> Result<(i64, i64, i64), DecodeError> {
    if irreversible {
        let red = y
            .checked_add(fixed_mul(cr, 91_881)?)
            .ok_or_else(arithmetic_overflow)?;
        let green_first = y
            .checked_sub(fixed_mul(cb, 22_553)?)
            .ok_or_else(arithmetic_overflow)?;
        let green = green_first
            .checked_sub(fixed_mul(cr, 46_797)?)
            .ok_or_else(arithmetic_overflow)?;
        let blue = y
            .checked_add(fixed_mul(cb, 116_130)?)
            .ok_or_else(arithmetic_overflow)?;
        Ok((red, green, blue))
    } else {
        let chroma_sum = cb.checked_add(cr).ok_or_else(arithmetic_overflow)?;
        y.checked_sub(chroma_sum >> 2)
            .ok_or_else(arithmetic_overflow)?;
        let green = crate::refinement::rct_green(y, chroma_sum);
        green.checked_add(cr).ok_or_else(arithmetic_overflow)?;
        green.checked_add(cb).ok_or_else(arithmetic_overflow)?;
        let red = crate::refinement::rct_red(green, cr);
        let blue = crate::refinement::rct_blue(green, cb);
        Ok((red, green, blue))
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_validate_transform_components(image@, fraction_bits),
))]
fn validate_transform_components(
    image: &DecodedImage,
    fraction_bits: u8,
) -> Result<(), DecodeError> {
    if image.components.len() < 3 {
        return Err(invalid_image());
    }

    let first = &image.components[0];
    let mut index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= 3,
            image.components.len() >= 3,
            decoded_component_view(*first) == image@.4[0],
            forall |i: int| 0 <= i < index ==> crate::specs::part1_component_transform_compatible(
                image@.4[0], image@.4[i], fraction_bits,
            ),
            decreases 3 - index,
        )
    )]
    while index < 3 {
        if index >= image.components.len() {
            return Err(invalid_image());
        }
        let component = &image.components[index];
        if component.width != first.width
            || component.height != first.height
            || component.fraction_bits != fraction_bits
            || component.info.x_subsampling != first.info.x_subsampling
            || component.info.y_subsampling != first.info.y_subsampling
        {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(!crate::specs::part1_component_transform_compatible(
                    image@.4[0], image@.4[index as int], fraction_bits,
                ));
                assert(exists |i: int| 0 <= i < 3 && !crate::specs::part1_component_transform_compatible(
                    image@.4[0], image@.4[i], fraction_bits,
                ));
            }
            return Err(invalid_image());
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_decoded_component_sample(image@, component, index),
))]
pub(super) fn component_sample(
    image: &DecodedImage,
    component: usize,
    index: usize,
) -> Result<i64, DecodeError> {
    let component = image.components.get(component).ok_or_else(invalid_image)?;
    let sample = component.samples.get(index).ok_or_else(invalid_image)?;
    Ok(*sample)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(image)@) == crate::specs::part1_set_decoded_component_sample(
        old(image)@, component, index, value,
    ),
))]
pub(super) fn set_component_sample(
    image: &mut DecodedImage,
    component: usize,
    index: usize,
    value: i64,
) -> Result<(), DecodeError> {
    let component = image
        .components
        .get_mut(component)
        .ok_or_else(invalid_image)?;
    let sample = component.samples.get_mut(index).ok_or_else(invalid_image)?;
    *sample = value;
    Ok(())
}
