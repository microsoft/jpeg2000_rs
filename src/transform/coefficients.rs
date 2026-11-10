use super::arithmetic::{arithmetic_overflow, invalid_transform};
use crate::DecodeError;
use crate::codestream::KernelCoefficient;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_integer(crate::codestream::raw_kernel_coefficient_view(coefficient), coefficient_type),
))]
pub(super) fn coefficient_integer(
    coefficient: KernelCoefficient,
    coefficient_type: u8,
) -> Result<i128, DecodeError> {
    if coefficient_type > 1 {
        return Err(invalid_transform());
    }
    Ok(bytes_to_u128(coefficient.bytes()) as i128)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_fixed_coefficient(crate::codestream::raw_kernel_coefficient_view(coefficient), coefficient_type),
))]
pub(super) fn coefficient_fixed(
    coefficient: KernelCoefficient,
    coefficient_type: u8,
) -> Result<i64, DecodeError> {
    let bytes = coefficient.bytes();
    match coefficient_type {
        0 | 1 => {
            let value = coefficient_integer(coefficient, coefficient_type)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((1i128 << 32u32) == 0x1_0000_0000i128) by (bit_vector);
            }
            let scaled = value
                .checked_mul(1_i128 << 32)
                .ok_or_else(arithmetic_overflow)?;
            match i64::try_from(scaled) {
                Ok(converted) => Ok(converted),
                Err(_) => Err(arithmetic_overflow()),
            }
        }
        2 => binary_to_fixed(bytes_to_u128(bytes), 32, 8, 23, 127),
        3 => binary_to_fixed(bytes_to_u128(bytes), 64, 11, 52, 1023),
        4 => binary_to_fixed(bytes_to_u128(bytes), 128, 15, 112, 16383),
        _ => Err(invalid_transform()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_bytes_prefix(bytes@, 16),
))]
fn bytes_to_u128(bytes: &[u8; 16]) -> u128 {
    let mut value = 0_u128;
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= bytes.len(),
            value == crate::specs::part2_atk_bytes_prefix(bytes@, index as nat),
            decreases bytes.len() - index,
        )
    )]
    while index < bytes.len() {
        value = (value << 8) | u128::from(bytes[index]);
        index += 1;
    }
    value
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_binary_format(bits, total_bits, exponent_bits, fraction_bits, bias),
))]
pub(super) fn binary_to_fixed(
    bits: u128,
    total_bits: u32,
    exponent_bits: u32,
    fraction_bits: u32,
    bias: i32,
) -> Result<i64, DecodeError> {
    if total_bits == 0
        || total_bits > 128
        || exponent_bits == 0
        || exponent_bits >= 128
        || fraction_bits >= 128
    {
        return Err(invalid_transform());
    }
    let negative = bits >> (total_bits - 1) != 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((1u128 << exponent_bits) > 0) by (bit_vector)
            requires exponent_bits < 128;
        assert((1u128 << fraction_bits) > 0) by (bit_vector)
            requires fraction_bits < 128;
    }
    let exponent_mask = (1_u128 << exponent_bits)
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    let exponent = (bits >> fraction_bits) & exponent_mask;
    let fraction = bits
        & (1_u128 << fraction_bits)
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
    if exponent == exponent_mask {
        return Err(invalid_transform());
    }
    if exponent == 0 && fraction == 0 {
        return Ok(0);
    }
    let (significand, exponent_base) = if exponent == 0 {
        (fraction, 1_i32)
    } else {
        let exponent_base = match i32::try_from(exponent) {
            Ok(value) => value,
            Err(_) => return Err(arithmetic_overflow()),
        };
        ((1_u128 << fraction_bits) | fraction, exponent_base)
    };
    let fraction_exponent = match i32::try_from(fraction_bits) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let unbiased = exponent_base
        .checked_sub(bias)
        .ok_or_else(arithmetic_overflow)?;
    let binary_exponent = unbiased
        .checked_sub(fraction_exponent)
        .ok_or_else(arithmetic_overflow)?;
    fixed_from_binary_q32(negative, significand, binary_exponent)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_binary_q32(negative, significand, binary_exponent),
))]
pub(super) fn fixed_from_binary_q32(
    negative: bool,
    significand: u128,
    binary_exponent: i32,
) -> Result<i64, DecodeError> {
    let shift = binary_exponent
        .checked_add(32)
        .ok_or_else(arithmetic_overflow)?;
    let magnitude = if shift >= 0 {
        let shift = u32::try_from(shift).map_err(|_| arithmetic_overflow())?;
        if shift >= 128 || significand > (u128::MAX >> shift) {
            return Err(arithmetic_overflow());
        }
        significand << shift
    } else {
        let right = u32::try_from(0_i32.checked_sub(shift).ok_or_else(arithmetic_overflow)?)
            .map_err(|_| arithmetic_overflow())?;
        if right >= 128 {
            0
        } else {
            let truncated = significand >> right;
            let mask = if right == 0 {
                0
            } else {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert((1u128 << right) > 0) by (bit_vector)
                        requires right < 128;
                }
                (1_u128 << right)
                    .checked_sub(1)
                    .ok_or_else(arithmetic_overflow)?
            };
            let remainder = significand & mask;
            let half = if right == 0 { 0 } else { 1_u128 << (right - 1) };
            let increment = if remainder > half || (remainder == half && truncated & 1 != 0) {
                1_u128
            } else {
                0_u128
            };
            truncated
                .checked_add(increment)
                .ok_or_else(arithmetic_overflow)?
        }
    };
    let signed = match i128::try_from(magnitude) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let signed = if negative {
        0_i128.checked_sub(signed).ok_or_else(arithmetic_overflow)?
    } else {
        signed
    };
    match i64::try_from(signed) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_fixed_mul(value, factor),
))]
pub(super) fn fixed_mul_q32(value: i64, factor: i64) -> Result<i64, DecodeError> {
    let product = i128::from(value)
        .checked_mul(i128::from(factor))
        .ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_atk_checked_i128(value as int * factor as int) == Ok(product));
    }
    let rounded = round_shift_i128(product, 32)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_atk_fixed_mul(value, factor) == crate::specs::part1_checked_sample(rounded as int));
    }
    let conversion = i64::try_from(rounded);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(conversion.is_ok() == (i64::MIN <= rounded <= i64::MAX));
        assert(conversion.is_ok() ==> conversion->Ok_0 == rounded as i64);
    }
    match conversion {
        Ok(converted) => Ok(converted),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_fixed_div(value, divisor),
))]
pub(super) fn fixed_div_q32(value: i64, divisor: i64) -> Result<i64, DecodeError> {
    if divisor == 0 {
        return Err(arithmetic_overflow());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((1i128 << 32u32) == 0x1_0000_0000i128) by (bit_vector);
    }
    let numerator = i128::from(value)
        .checked_mul(1_i128 << 32)
        .ok_or_else(arithmetic_overflow)?;
    if numerator == i128::MIN && divisor == -1 {
        return Err(arithmetic_overflow());
    }
    let quotient = numerator
        .checked_div(i128::from(divisor))
        .ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_atk_checked_i128(value as int * 0x1_0000_0000int) == Ok(numerator));
        assert(quotient == vstd::arithmetic::div_mod::rust_div(numerator as int, divisor as int) as i128);
        assert(crate::specs::part2_atk_fixed_div(value, divisor) == crate::specs::part1_checked_sample(quotient as int));
    }
    let conversion = i64::try_from(quotient);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(conversion.is_ok() == (i64::MIN <= quotient <= i64::MAX));
        assert(conversion.is_ok() ==> conversion->Ok_0 == quotient as i64);
    }
    match conversion {
        Ok(converted) => Ok(converted),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_round_shift(value, shift),
))]
pub(super) fn round_shift_i128(value: i128, shift: u32) -> Result<i128, DecodeError> {
    if shift == 0 || shift >= 128 {
        return Err(arithmetic_overflow());
    }
    let half = 1_i128 << (shift - 1);
    let adjusted = if value >= 0 {
        value.checked_add(half)
    } else {
        let bias = half.checked_sub(1).ok_or_else(arithmetic_overflow)?;
        value.checked_add(bias)
    }
    .ok_or_else(arithmetic_overflow)?;
    Ok(adjusted >> shift)
}
