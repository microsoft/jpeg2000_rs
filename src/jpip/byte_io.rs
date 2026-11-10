//! Checked big-endian reads and writes for JPIP reconstruction.

use super::{DecodeError, MalformedKind};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) fn write_u64_be(
    output: &mut [u8],
    position: usize,
    value: u64,
) -> Result<(), DecodeError> {
    let high = u32::try_from(value >> 32)
        .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    let low = u32::try_from(value & u64::from(u32::MAX))
        .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    write_u32_be(output, position, high)?;
    write_u32_be(
        output,
        position
            .checked_add(4)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        low,
    )
}

pub(super) fn read_u64_be(input: &[u8], position: usize) -> Result<u64, DecodeError> {
    let high = u64::from(read_u32_be(input, position)?);
    let low = u64::from(read_u32_be(
        input,
        position
            .checked_add(4)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
    )?);
    Ok((high << 32) | low)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_jpip_read_u16(input@, position),
))]
pub(super) fn read_u16_be(input: &[u8], position: usize) -> Result<u16, DecodeError> {
    let bytes = input
        .get(position..position.saturating_add(2))
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if position as nat + 2 <= usize::MAX as nat {
            assert(position.saturating_add(2) as nat == position as nat + 2);
            assert(bytes@.len() == 2);
        } else {
            assert(position.saturating_add(2) == usize::MAX);
            assert(bytes@.len() < 2);
        }
        assert(bytes@.len() == 2 <==>
            position as nat + 2 <= input@.len() && position as nat + 2 <= usize::MAX as nat);
        assert(bytes@ == input@.subrange(position as int, position as int + bytes@.len()));
    }
    let high = *bytes
        .first()
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    let low = *bytes
        .get(1)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    Ok((u16::from(high) << 8) | u16::from(low))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_jpip_read_u32(input@, position),
))]
pub(super) fn read_u32_be(input: &[u8], position: usize) -> Result<u32, DecodeError> {
    let bytes = input
        .get(position..position.saturating_add(4))
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    #[cfg(verus_keep_ghost)]
    proof! {
        if position as nat + 4 <= usize::MAX as nat {
            assert(position.saturating_add(4) as nat == position as nat + 4);
            assert(bytes@.len() == 4);
        } else {
            assert(position.saturating_add(4) == usize::MAX);
            assert(bytes@.len() < 4);
        }
        assert(bytes@.len() == 4 <==>
            position as nat + 4 <= input@.len() && position as nat + 4 <= usize::MAX as nat);
        assert(bytes@ == input@.subrange(position as int, position as int + bytes@.len()));
    }
    let first = *bytes
        .first()
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    let second = *bytes
        .get(1)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    let third = *bytes
        .get(2)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    let fourth = *bytes
        .get(3)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(position as u64, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(position as u64, MalformedKind::Truncated),
        )?;
    Ok((u32::from(first) << 24)
        | (u32::from(second) << 16)
        | (u32::from(third) << 8)
        | u32::from(fourth))
}

pub(super) fn write_u32_be(
    output: &mut [u8],
    position: usize,
    value: u32,
) -> Result<(), DecodeError> {
    let bytes = output
        .get_mut(position..position.saturating_add(4))
        .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
    let source = [
        u8::try_from((value >> 24) & 0xff)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        u8::try_from((value >> 16) & 0xff)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        u8::try_from((value >> 8) & 0xff)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        u8::try_from(value & 0xff)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
    ];
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= source.len(),
            decreases source.len() - index,
        )
    )]
    while index < source.len() {
        *bytes
            .get_mut(index)
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))? =
            source[index];
        index += 1;
    }
    Ok(())
}
