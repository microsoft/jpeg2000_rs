use super::ReconstructedPlane;
use super::arithmetic::{arithmetic_overflow, invalid_transform, validate_output_size};
#[cfg(verus_keep_ghost)]
use super::{reconstructed_plane_view, sequence_outcome};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl ReconstructedPlane {
    #[cfg(test)]
    pub(crate) fn for_test(width: u32, height: u32, fraction_bits: u8, samples: Vec<i64>) -> Self {
        Self {
            width,
            height,
            fraction_bits,
            samples,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == reconstructed_plane_view(*self).0,
    ))]
    pub const fn width(&self) -> u32 {
        self.width
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == reconstructed_plane_view(*self).1,
    ))]
    pub const fn height(&self) -> u32 {
        self.height
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == reconstructed_plane_view(*self).2,
    ))]
    pub const fn fraction_bits(&self) -> u8 {
        self.fraction_bits
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == reconstructed_plane_view(*self).3,
    ))]
    pub fn samples(&self) -> &[i64] {
        &self.samples
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures sequence_outcome(result) == crate::specs::part1_convert_samples(
        reconstructed_plane_view(*plane), precision, signed, crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn convert_samples(
    plane: &ReconstructedPlane,
    precision: u8,
    signed: bool,
    limits: &ResourceLimits,
) -> Result<Vec<i64>, DecodeError> {
    if precision == 0 || precision > 38 || plane.fraction_bits > 62 {
        return Err(invalid_transform());
    }
    validate_output_size(plane.samples.len(), limits)?;
    let signed_shift = precision.checked_sub(1).ok_or_else(arithmetic_overflow)?;
    let maximum_shift = if signed { signed_shift } else { precision };
    let maximum_power = 1_i64 << (maximum_shift as u32);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(maximum_power > 0) by(bit_vector)
            requires maximum_shift <= 38, maximum_power == 1i64 << (maximum_shift as u32);
    }
    let maximum = maximum_power
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    let minimum = if signed {
        0_i64
            .checked_sub(1_i64 << (signed_shift as u32))
            .ok_or_else(arithmetic_overflow)?
    } else {
        0
    };
    let level_shift = crate::refinement::level_shift(precision, signed);
    let mut converted = Vec::with_capacity(plane.samples.len());
    let mut index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= plane.samples.len(),
            0 < precision <= 38,
            plane.fraction_bits <= 62,
            crate::specs::part1_quantization_budget(
                plane.samples.len() as nat, crate::limits::resource_decoded_bytes_limit(limits),
            ) == Ok(()),
            maximum == crate::specs::part1_output_maximum(precision, signed),
            minimum == crate::specs::part1_output_minimum(precision, signed),
            level_shift == crate::specs::part1_level_shift(precision, signed),
            crate::specs::part1_conversion_prefix(
                plane.samples@, plane.fraction_bits, level_shift, minimum, maximum, index as nat,
            ) == Ok(converted@),
            decreases plane.samples.len() - index,
        )
    )]
    while index < plane.samples.len() {
        let value = match convert_sample(
            plane.samples[index],
            plane.fraction_bits,
            level_shift,
            minimum,
            maximum,
        ) {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_conversion_error_persists(
                        plane.samples@, plane.fraction_bits, level_shift, minimum, maximum,
                        index as nat + 1, plane.samples.len() as nat, error,
                    );
                }
                return Err(error);
            }
        };
        converted.push(value);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(converted)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_convert_sample(value, fraction_bits, shift, minimum, maximum),
))]
fn convert_sample(
    value: i64,
    fraction_bits: u8,
    shift: i64,
    minimum: i64,
    maximum: i64,
) -> Result<i64, DecodeError> {
    let rounded = round_fixed(value, fraction_bits)?;
    let shifted = rounded.checked_add(shift).ok_or_else(arithmetic_overflow)?;
    Ok(crate::refinement::clip_sample(shifted, minimum, maximum))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_round_fixed(value, fraction_bits),
))]
fn round_fixed(value: i64, fraction_bits: u8) -> Result<i64, DecodeError> {
    if fraction_bits == 0 {
        return Ok(value);
    }
    if fraction_bits > 62 {
        return Err(invalid_transform());
    }
    let half_shift = fraction_bits
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    let half = 1_i64 << (half_shift as u32);
    Ok(value.checked_add(half).ok_or_else(arithmetic_overflow)? >> (fraction_bits as u32))
}
