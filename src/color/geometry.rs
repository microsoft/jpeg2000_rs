use crate::{DecodeError, MalformedKind, UnsupportedColorConversion};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_registered_coordinate(value, divisor, registration, true),
    )
)]
pub(super) fn registered_ceil_div(
    value: u32,
    divisor: u32,
    registration: u16,
) -> Result<u32, DecodeError> {
    if divisor == 0 {
        return Err(invalid_color_input());
    }
    let scale = 65_536_u64;
    let numerator = u64::from(value)
        .checked_mul(scale)
        .ok_or_else(arithmetic_overflow)?;
    if numerator <= u64::from(registration) {
        return Ok(0);
    }
    let adjusted = numerator
        .checked_sub(u64::from(registration))
        .ok_or_else(arithmetic_overflow)?;
    let denominator = u64::from(divisor)
        .checked_mul(scale)
        .ok_or_else(arithmetic_overflow)?;
    let rounded = crate::refinement::registered_extent(adjusted, denominator);
    match u32::try_from(rounded) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_registered_coordinate(value, divisor, registration, false),
    )
)]
pub(super) fn registered_floor_div(
    value: u32,
    divisor: u32,
    registration: u16,
) -> Result<u32, DecodeError> {
    if divisor == 0 {
        return Err(invalid_color_input());
    }
    let predecessor = crate::refinement::crg_component_predecessor(value, divisor, registration);
    match u32::try_from(predecessor) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(area => ensures area == crate::specs::part2_layer_area(width, height),)
)]
pub(super) fn checked_area(width: u32, height: u32) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_layer_area);
        assert((width as int) * (height as int) <= 18446744065119617025) by(nonlinear_arith);
    }
    let area = u64::from(width)
        .checked_mul(u64::from(height))
        .ok_or_else(arithmetic_overflow)?;
    match usize::try_from(area) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(error => ensures error == (DecodeError::UnsupportedColorConversion { reason }),)
)]
pub(super) const fn unsupported(reason: UnsupportedColorConversion) -> DecodeError {
    DecodeError::UnsupportedColorConversion { reason }
}

#[cfg_attr(verus_keep_ghost, verus_spec(error => ensures error == crate::specs::color_layout_error(),))]
pub(super) const fn invalid_channel_layout() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidChannelLayout,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(error => ensures error == crate::specs::part2_color_input_error(),))]
pub(super) fn invalid_color_input() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ContainerCodestreamMismatch,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(error => ensures error == crate::specs::part2_composition_error(true),))]
pub(super) fn arithmetic_overflow() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    }
}
