use super::NonlinearLutCoordinates;
use super::arithmetic::{arithmetic_overflow, invalid_image, invalid_transform};
use crate::codestream::{ComponentInfo, NonlinearPointTransform};
use crate::{DecodeError, MalformedKind};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_gamma_parameter(raw),
))]
pub(super) fn nlt_gamma_parameter(raw: u32) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(raw >> 16 <= 65535) by(bit_vector);
        assert(raw & 65535 <= 65535) by(bit_vector);
        assert(1i128 << 32 == 4294967296) by(bit_vector);
    }
    let integer = i128::from(raw >> 16)
        .checked_mul(1_i128 << 32)
        .ok_or_else(arithmetic_overflow)?;
    let fraction = i128::from(raw & 0xffff)
        .checked_mul(1_i128 << 32)
        .ok_or_else(arithmetic_overflow)?;
    let fraction = fraction
        .checked_div(i128::from(u16::MAX))
        .ok_or_else(arithmetic_overflow)?;
    integer
        .checked_add(fraction)
        .ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_gamma_curve(normalized, exponent, slope, threshold, a, b),
))]
pub(super) fn nlt_gamma_curve(
    normalized: i128,
    exponent: i128,
    slope: i128,
    threshold: i128,
    a: i128,
    b: i128,
) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_nlt_gamma_curve); }
    let negative_threshold = 0_i128
        .checked_sub(threshold)
        .ok_or_else(arithmetic_overflow)?;
    if normalized < negative_threshold {
        let magnitude = 0_i128
            .checked_sub(normalized)
            .ok_or_else(arithmetic_overflow)?;
        let base = nlt_fixed_div_q32(magnitude.checked_add(b).ok_or_else(arithmetic_overflow)?, a)?;
        0_i128
            .checked_sub(nlt_fixed_pow_reciprocal_q32(base, exponent)?)
            .ok_or_else(arithmetic_overflow)
    } else if normalized <= threshold {
        nlt_fixed_div_q32(normalized, slope)
    } else {
        let base = nlt_fixed_div_q32(
            normalized.checked_add(b).ok_or_else(arithmetic_overflow)?,
            a,
        )?;
        nlt_fixed_pow_reciprocal_q32(base, exponent)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_gamma_sample(
        source, source_info, crate::codestream::owned_nonlinear_view(transform),
    ),
))]
pub(super) fn inverse_nlt_gamma_sample(
    source: i128,
    source_info: ComponentInfo,
    transform: &NonlinearPointTransform,
) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_nlt_gamma_sample); }
    if source_info.precision == 0 || source_info.precision > 38 {
        return Err(invalid_image());
    }
    let parameters = transform.gamma_parameters().ok_or_else(invalid_transform)?;
    let exponent = nlt_gamma_parameter(parameters[0])?;
    let slope = nlt_gamma_parameter(parameters[1])?;
    let threshold = nlt_gamma_parameter(parameters[2])?;
    let a = nlt_gamma_parameter(parameters[3])?;
    let b = nlt_gamma_parameter(parameters[4])?;
    if exponent <= 0 || slope <= 0 || a <= 0 {
        return Err(invalid_transform());
    }
    let source_scale = if source_info.signed {
        nlt_power_of_two(source_info.precision - 1)?
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?
    } else {
        nlt_power_of_two(source_info.precision)?
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?
    };
    let target_precision = transform.precision();
    if target_precision == 0 {
        return Err(invalid_transform());
    }
    let target_scale = if transform.signed() {
        nlt_power_of_two(
            target_precision
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?,
        )?
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?
    } else {
        nlt_power_of_two(transform.precision())?
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?
    };
    if source_scale <= 0 || target_scale <= 0 {
        return Err(invalid_transform());
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(1i128 << 32 == 4294967296) by(bit_vector); }
    let product = source
        .checked_mul(1_i128 << 32)
        .ok_or_else(arithmetic_overflow)?;
    let normalized = product
        .checked_div(source_scale)
        .ok_or_else(arithmetic_overflow)?;
    let decoded = nlt_gamma_curve(normalized, exponent, slope, threshold, a, b)?;
    nlt_round_ratio(
        decoded
            .checked_mul(target_scale)
            .ok_or_else(arithmetic_overflow)?,
        1_i128 << 32,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_inverse_sample(
        source, source_info, crate::codestream::owned_nonlinear_view(transform),
    ),
))]
pub(super) fn inverse_nlt_sample(
    source: i128,
    source_info: ComponentInfo,
    transform: &NonlinearPointTransform,
) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_nlt_inverse_sample); }
    let target_precision = transform.precision();
    if target_precision == 0 || target_precision > 38 {
        return Err(invalid_image());
    }
    let target_half = nlt_power_of_two(target_precision - 1)?;
    let target_min = if transform.signed() {
        0_i128
            .checked_sub(target_half)
            .ok_or_else(arithmetic_overflow)?
    } else {
        0
    };
    let target_max = if transform.signed() {
        target_half.checked_sub(1).ok_or_else(arithmetic_overflow)?
    } else {
        nlt_power_of_two(target_precision)?
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?
    };
    let value = match transform.transform_type() {
        0 => {
            if source_info.precision != target_precision || source_info.signed != transform.signed()
            {
                return Err(invalid_transform());
            }
            source
        }
        3 => {
            if source_info.precision != target_precision || source_info.signed != transform.signed()
            {
                return Err(invalid_transform());
            }
            if source < 0 {
                if source == i128::MIN || target_half < 0 || target_half == i128::MAX {
                    return Err(arithmetic_overflow());
                }
                crate::refinement::nlt_binary_complement(source, target_half)
            } else {
                source
            }
        }
        2 | 4 => inverse_nlt_lut_sample(source, source_info, transform)?,
        1 => inverse_nlt_gamma_sample(source, source_info, transform)?,
        _ => return Err(invalid_transform()),
    };
    if value < target_min || value > target_max {
        return Err(invalid_transform());
    }
    Ok(value)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_ln_normalize(initial),
))]
pub(super) fn nlt_ln_normalize(initial: i128) -> Result<(i128, i32), DecodeError> {
    let mut value = initial;
    let one = 1_i128 << 32;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(1i128 << 32 == 4294967296) by(bit_vector);
        assert(2i128 << 32 == 8589934592) by(bit_vector);
    }
    let two = one.checked_mul(2).ok_or_else(arithmetic_overflow)?;
    let mut scale = 0_i32;
    let mut normalization_passes = 128_u16;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_nlt_ln_normalize(initial); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant goal == crate::specs::part2_nlt_ln_normalize(initial),
            goal == crate::specs::part2_nlt_ln_normalize_high(value, scale, normalization_passes),
            two == 8589934592, one == 4294967296,
        decreases normalization_passes,
    ))]
    while value >= two {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_nlt_ln_normalize_high, 1); }
        value >>= 1;
        scale = scale.checked_add(1).ok_or_else(arithmetic_overflow)?;
        normalization_passes = normalization_passes
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_nlt_ln_normalize_high, 1); }
    normalization_passes = 128;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant goal == crate::specs::part2_nlt_ln_normalize(initial),
            goal == crate::specs::part2_nlt_ln_normalize_low(value, scale, normalization_passes),
            one == 4294967296,
        decreases normalization_passes,
    ))]
    while value < one {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_nlt_ln_normalize_low, 1); }
        value = value.checked_mul(2).ok_or_else(arithmetic_overflow)?;
        scale = scale.checked_sub(1).ok_or_else(arithmetic_overflow)?;
        normalization_passes = normalization_passes
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_nlt_ln_normalize_low, 1); }
    Ok((value, scale))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_ln_series(squared, scale, 0, initial, 0),
))]
pub(super) fn nlt_ln_series(initial: i128, squared: i128, scale: i32) -> Result<i128, DecodeError> {
    let mut term = initial;
    let mut sum = 0_i128;
    let mut iteration = 0_u32;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_nlt_ln_series(squared, scale, 0, initial, 0); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant iteration <= 20,
            goal == crate::specs::part2_nlt_ln_series(squared, scale, 0, initial, 0),
            goal == crate::specs::part2_nlt_ln_series(squared, scale, iteration as nat, term, sum),
        decreases 20 - iteration,
    ))]
    while iteration < 20 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_nlt_ln_series, 1); }
        let doubled = iteration.checked_mul(2).ok_or_else(arithmetic_overflow)?;
        let divisor = doubled.checked_add(1).ok_or_else(arithmetic_overflow)?;
        if divisor == 0 {
            return Err(arithmetic_overflow());
        }
        sum = sum
            .checked_add(term / i128::from(divisor))
            .ok_or_else(arithmetic_overflow)?;
        term = nlt_fixed_mul_q32(term, squared)?;
        iteration += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_nlt_ln_series, 1); }
    let doubled = sum.checked_mul(2).ok_or_else(arithmetic_overflow)?;
    let shifted = i128::from(scale)
        .checked_mul(2_977_044_471)
        .ok_or_else(arithmetic_overflow)?;
    doubled.checked_add(shifted).ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_fixed_ln_q32(value),
))]
pub(super) fn nlt_fixed_ln_q32(value: i128) -> Result<i128, DecodeError> {
    let (value, scale) = nlt_ln_normalize(value)?;
    let one = 1_i128 << 32;
    #[cfg(verus_keep_ghost)]
    proof! { assert(1i128 << 32 == 4294967296) by(bit_vector); }
    let z = nlt_fixed_div_q32(
        value.checked_sub(one).ok_or_else(arithmetic_overflow)?,
        value.checked_add(one).ok_or_else(arithmetic_overflow)?,
    )?;
    let squared = nlt_fixed_mul_q32(z, z)?;
    nlt_ln_series(z, squared, scale)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_exp_series(remainder, 1, 4294967296, 4294967296),
))]
pub(super) fn nlt_exp_series(remainder: i128) -> Result<i128, DecodeError> {
    let mut sum = 1_i128 << 32;
    let mut term = sum;
    let mut iteration = 1_u32;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_nlt_exp_series(remainder, 1, 4294967296, 4294967296); }
    #[cfg(verus_keep_ghost)]
    proof! { assert(1i128 << 32 == 4294967296) by(bit_vector); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= iteration <= 25,
            goal == crate::specs::part2_nlt_exp_series(remainder, 1, 4294967296, 4294967296),
            goal == crate::specs::part2_nlt_exp_series(remainder, iteration as nat, term, sum),
        decreases 25 - iteration,
    ))]
    while iteration <= 24 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_nlt_exp_series, 1); }
        term = nlt_fixed_mul_q32(term, remainder)?
            .checked_div(i128::from(iteration))
            .ok_or_else(arithmetic_overflow)?;
        sum = sum.checked_add(term).ok_or_else(arithmetic_overflow)?;
        iteration += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_nlt_exp_series, 1); }
    Ok(sum)
}

#[allow(clippy::manual_range_contains)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_fixed_exp_q32(value),
))]
pub(super) fn nlt_fixed_exp_q32(value: i128) -> Result<i128, DecodeError> {
    const LN_2_Q32: i128 = 2_977_044_471;
    let scale = value / LN_2_Q32;
    if scale < -62 || scale > 62 {
        return Err(invalid_transform());
    }
    let remainder = value - scale * LN_2_Q32;
    let sum = nlt_exp_series(remainder)?;
    if scale >= 0 {
        let shift = match u32::try_from(scale) {
            Ok(shift) => shift,
            Err(_) => return Err(arithmetic_overflow()),
        };
        if sum < 0 || sum > (i128::MAX >> shift) {
            return Err(arithmetic_overflow());
        }
        Ok(sum << shift)
    } else {
        let shift = match u32::try_from(-scale) {
            Ok(shift) => shift,
            Err(_) => return Err(arithmetic_overflow()),
        };
        Ok(sum >> shift)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_fixed_pow_reciprocal_q32(base, exponent),
))]
pub(super) fn nlt_fixed_pow_reciprocal_q32(
    base: i128,
    exponent: i128,
) -> Result<i128, DecodeError> {
    if base <= 0 || exponent <= 0 {
        return Err(invalid_transform());
    }
    nlt_fixed_exp_q32(nlt_fixed_div_q32(nlt_fixed_ln_q32(base)?, exponent)?)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_lut_sample(
        source, source_info, crate::codestream::owned_nonlinear_view(transform),
    ),
))]
pub(super) fn inverse_nlt_lut_sample(
    source: i128,
    source_info: ComponentInfo,
    transform: &NonlinearPointTransform,
) -> Result<i128, DecodeError> {
    let output_precision = transform.precision();
    if output_precision == 0 || output_precision > 38 {
        return Err(invalid_image());
    }
    let minimum = transform.d_min().ok_or_else(invalid_transform)?;
    let maximum = transform.d_max().ok_or_else(invalid_transform)?;
    let points = transform.points();
    if points.len() < 2 || minimum >= maximum {
        return Err(invalid_transform());
    }
    if source_info.precision == 0 || source_info.precision > 38 {
        return Err(invalid_image());
    }
    let source_scale = nlt_power_of_two(source_info.precision)?
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    let source_offset = if source_info.signed {
        nlt_power_of_two(source_info.precision - 1)?
    } else {
        0
    };
    let nominal = source
        .checked_add(source_offset)
        .ok_or_else(arithmetic_overflow)?;
    if nominal < 0 || nominal > source_scale {
        return Err(invalid_image());
    }
    let raw = nlt_lut_position(points, source_scale, nominal, minimum, maximum)?;
    let half = nlt_power_of_two(output_precision - 1)?;
    let mut value = if transform.signed() {
        raw.checked_sub(half).ok_or_else(arithmetic_overflow)?
    } else {
        raw
    };
    if transform.transform_type() == 4 && value < 0 {
        let bias = half.checked_add(1).ok_or_else(arithmetic_overflow)?;
        let magnitude = 0_i128.checked_sub(value).ok_or_else(arithmetic_overflow)?;
        value = magnitude
            .checked_sub(bias)
            .ok_or_else(arithmetic_overflow)?;
    }
    Ok(value)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_lut_position(points@, source_scale, nominal, minimum, maximum),
))]
pub(super) fn nlt_lut_position(
    points: &[u32],
    source_scale: i128,
    nominal: i128,
    minimum: u32,
    maximum: u32,
) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_nlt_lut_position);
        reveal(crate::specs::part2_nlt_lut_interpolate);
    }
    if points.is_empty() {
        return Err(invalid_image());
    }
    let (interval_index, denominator, remainder) =
        nlt_lut_coordinates(source_scale, nominal, minimum, maximum, points.len() - 1)?;
    if interval_index >= points.len() - 1 {
        #[cfg(verus_keep_ghost)]
        proof! { assert(points@.last() == points@[points@.len() - 1]); }
        Ok(i128::from(*points.last().ok_or_else(invalid_image)?))
    } else {
        let left = i128::from(*points.get(interval_index).ok_or_else(invalid_image)?);
        let right = i128::from(
            *points
                .get(
                    interval_index
                        .checked_add(1)
                        .ok_or_else(arithmetic_overflow)?,
                )
                .ok_or_else(invalid_image)?,
        );
        nlt_lut_interpolate_values(left, right, denominator, remainder)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_lut_coordinates(source_scale, nominal, minimum, maximum, last_index as nat),
))]
pub(super) fn nlt_lut_coordinates(
    source_scale: i128,
    nominal: i128,
    minimum: u32,
    maximum: u32,
    last_index: usize,
) -> Result<NonlinearLutCoordinates, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_nlt_lut_coordinates); }
    let normalized = nominal
        .checked_mul(i128::from(u32::MAX))
        .ok_or_else(arithmetic_overflow)?;
    let minimum_scaled = i128::from(minimum)
        .checked_mul(source_scale)
        .ok_or_else(arithmetic_overflow)?;
    let maximum_scaled = i128::from(maximum)
        .checked_mul(source_scale)
        .ok_or_else(arithmetic_overflow)?;
    let clamped = normalized.max(minimum_scaled).min(maximum_scaled);
    let interval_count = last_index as u128;
    if interval_count > i128::MAX as u128 {
        return Err(arithmetic_overflow());
    }
    let interval_count = interval_count as i128;
    let denominator = maximum_scaled
        .checked_sub(minimum_scaled)
        .ok_or_else(arithmetic_overflow)?;
    let offset = clamped
        .checked_sub(minimum_scaled)
        .ok_or_else(arithmetic_overflow)?;
    let position_numerator = offset
        .checked_mul(interval_count)
        .ok_or_else(arithmetic_overflow)?;
    let interval = position_numerator
        .checked_div(denominator)
        .ok_or_else(arithmetic_overflow)?;
    let remainder = nlt_checked_rem(position_numerator, denominator)?;
    let interval_index = match usize::try_from(interval) {
        Ok(index) => index,
        Err(_) => return Err(arithmetic_overflow()),
    };
    Ok((interval_index, denominator, remainder))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_checked_rem(numerator, denominator),
))]
pub(super) fn nlt_checked_rem(numerator: i128, denominator: i128) -> Result<i128, DecodeError> {
    match numerator.checked_rem(denominator) {
        Some(value) => Ok(value),
        None => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_lut_interpolate_values(left, right, denominator, remainder),
))]
pub(super) fn nlt_lut_interpolate_values(
    left: i128,
    right: i128,
    denominator: i128,
    remainder: i128,
) -> Result<i128, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_nlt_lut_interpolate_values); }
    let base = left
        .checked_mul(denominator)
        .ok_or_else(arithmetic_overflow)?;
    let difference = right.checked_sub(left).ok_or_else(arithmetic_overflow)?;
    let offset = difference
        .checked_mul(remainder)
        .ok_or_else(arithmetic_overflow)?;
    let numerator = base.checked_add(offset).ok_or_else(arithmetic_overflow)?;
    nlt_round_ratio(numerator, denominator)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_round_ratio(numerator, denominator),
))]
pub(super) fn nlt_round_ratio(numerator: i128, denominator: i128) -> Result<i128, DecodeError> {
    if denominator <= 0 {
        return Err(arithmetic_overflow());
    }
    if numerator >= 0 {
        let adjusted = match numerator.checked_add(denominator / 2) {
            Some(value) => value,
            None => return Err(arithmetic_overflow()),
        };
        Ok(adjusted / denominator)
    } else {
        let magnitude = match 0_i128.checked_sub(numerator) {
            Some(value) => value,
            None => return Err(arithmetic_overflow()),
        };
        let adjusted = match magnitude.checked_add(denominator / 2) {
            Some(value) => value,
            None => return Err(arithmetic_overflow()),
        };
        let rounded = match adjusted.checked_div(denominator) {
            Some(value) => value,
            None => return Err(arithmetic_overflow()),
        };
        0_i128.checked_sub(rounded).ok_or_else(arithmetic_overflow)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_power_of_two(exponent),
))]
pub(super) fn nlt_power_of_two(exponent: u8) -> Result<i128, DecodeError> {
    if exponent > 38 {
        return Err(arithmetic_overflow());
    }
    let mut value = 1_i128;
    let mut bit = 0_u8;
    #[cfg(verus_keep_ghost)]
    proof! { assert(1i128 << 0 == 1) by(bit_vector); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant bit <= exponent, exponent <= 38, value == 1i128 << bit,
        decreases exponent - bit,
    ))]
    while bit < exponent {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((1i128 << bit) * 2 == 1i128 << (bit + 1)) by(bit_vector)
                requires bit < 38;
        }
        value = value.checked_mul(2).ok_or_else(arithmetic_overflow)?;
        bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(value)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_fixed_mul_q32(left, right),
))]
pub(super) fn nlt_fixed_mul_q32(left: i128, right: i128) -> Result<i128, DecodeError> {
    nlt_round_ratio(
        left.checked_mul(right).ok_or_else(arithmetic_overflow)?,
        1_i128 << 32,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_nlt_fixed_div_q32(left, right),
))]
pub(super) fn nlt_fixed_div_q32(left: i128, right: i128) -> Result<i128, DecodeError> {
    if right <= 0 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        });
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(1i128 << 32 == 4294967296) by(bit_vector); }
    let product = match left.checked_mul(1_i128 << 32) {
        Some(value) => value,
        None => return Err(arithmetic_overflow()),
    };
    product.checked_div(right).ok_or_else(arithmetic_overflow)
}
