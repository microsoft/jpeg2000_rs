use super::arithmetic::{
    arithmetic_overflow, checked_area, invalid_transform, transform_dimension,
};
use super::{WaveletBand, WaveletLevel};
#[cfg(verus_keep_ghost)]
use super::{row_outcome, sequence_outcome, wavelet_band_view, wavelet_level_view};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_validate_level(wavelet_level_view(level)),
))]
pub(super) fn validate_level(level: WaveletLevel<'_>) -> Result<(), DecodeError> {
    if level.output_width == 0 || level.output_height == 0 {
        return Err(invalid_transform());
    }
    let low_width = low_count(level.output_width, level.low_pass_first_x);
    let high_width = level
        .output_width
        .checked_sub(low_width)
        .ok_or_else(arithmetic_overflow)?;
    let low_height = low_count(level.output_height, level.low_pass_first_y);
    let high_height = level
        .output_height
        .checked_sub(low_height)
        .ok_or_else(arithmetic_overflow)?;
    validate_band(level.ll, low_width, low_height)?;
    validate_band(level.hl, high_width, low_height)?;
    validate_band(level.lh, low_width, high_height)?;
    validate_band(level.hh, high_width, high_height)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_validate_band(wavelet_band_view(band), width, height),
))]
fn validate_band(band: WaveletBand<'_>, width: u32, height: u32) -> Result<(), DecodeError> {
    if band.width != width
        || band.height != height
        || band.samples.len() != checked_area(width, height)?
    {
        return Err(invalid_transform());
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_low_count(length, low_pass_first),
))]
pub(super) fn low_count(length: u32, low_pass_first: bool) -> u32 {
    if low_pass_first {
        length / 2 + length % 2
    } else {
        length / 2
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures row_outcome(result) == crate::specs::part1_band_row(wavelet_band_view(band), y),
))]
pub(super) fn band_row(band: WaveletBand<'_>, y: u32) -> Result<&[i64], DecodeError> {
    if y >= band.height {
        return Err(invalid_transform());
    }
    let start = transform_dimension(y)?
        .checked_mul(transform_dimension(band.width)?)
        .ok_or_else(arithmetic_overflow)?;
    let end = start
        .checked_add(transform_dimension(band.width)?)
        .ok_or_else(arithmetic_overflow)?;
    band.samples.get(start..end).ok_or_else(invalid_transform)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_gather_result((width,height,samples@),x,sequence_outcome(result)),
        sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_collect_column((width, height, samples@), x),
))]
pub(super) fn collect_column(
    samples: &[i64],
    width: u32,
    height: u32,
    x: u32,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_gather_normal((width,height,samples@),x);}
    if x >= width {
        return Err(invalid_transform());
    }
    let count = transform_dimension(height)?;
    let allocated = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_wavelet_line_capacity_observed(crate::specs::Part2WaveletLineContext::Gather {width,height,column:x},unit);
        if let Err(error)=allocated{crate::specs::part2_wavelet_gather_refused((width,height,samples@),x,error);}
    }
    let mut column = allocated?;
    let mut y = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant y <= height,
            x < width,
            height <= usize::MAX,
            crate::specs::part2_wavelet_gather_result((width,height,samples@),x,crate::specs::part1_collect_column((width,height,samples@),x)),
            crate::specs::part1_column_prefix(samples@, width, x, y as nat) == Ok(column@),
            decreases height - y,
        )
    )]
    while y < height {
        let value = match column_sample(samples, width, x, y) {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_column_error_persists(
                        samples@, width, x, y as nat + 1, height as nat, error,
                    );
                }
                return Err(error);
            }
        };
        column.push(value);
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(column)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_transform_offset(y, width, x),
))]
pub(crate) fn transform_offset(y: u32, width: u32, x: u32) -> Result<usize, DecodeError> {
    let row = transform_dimension(y)?
        .checked_mul(transform_dimension(width)?)
        .ok_or_else(arithmetic_overflow)?;
    row.checked_add(transform_dimension(x)?)
        .ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_column_sample(samples@, width, x, y),
))]
fn column_sample(samples: &[i64], width: u32, x: u32, y: u32) -> Result<i64, DecodeError> {
    let index = transform_offset(y, width, x)?;
    if index >= samples.len() {
        return Err(invalid_transform());
    }
    Ok(samples[index])
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part1_store_column_sample(
        old(output)@, width, x, column@, y,
    ),
))]
fn store_column_sample(
    output: &mut [i64],
    width: u32,
    x: u32,
    column: &[i64],
    y: u32,
) -> Result<(), DecodeError> {
    let destination = transform_offset(y, width, x)?;
    let column_index = transform_dimension(y)?;
    let value = *column.get(column_index).ok_or_else(invalid_transform)?;
    if destination >= output.len() {
        return Err(invalid_transform());
    }
    output[destination] = value;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part1_store_column_prefix(
        old(output)@, width, x, column@, height as nat,
    ),
))]
pub(super) fn store_column(
    output: &mut [i64],
    width: u32,
    height: u32,
    x: u32,
    column: &[i64],
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = output@; }
    let mut y = 0_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant y <= height,
        original == old(output)@,
        crate::specs::part1_store_column_prefix(original, width, x, column@, y as nat) == (Ok(()), output@),
        decreases height - y,
    ))]
    while y < height {
        match store_column_sample(output, width, x, column, y) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_store_column_error_persists(
                        original, width, x, column@, y as nat + 1, height as nat,
                    );
                }
                return Err(error);
            }
        }
        y += 1;
    }
    Ok(())
}
