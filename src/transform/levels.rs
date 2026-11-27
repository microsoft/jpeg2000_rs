use super::arbitrary::inverse_arbitrary;
use super::arithmetic::{
    arithmetic_overflow, checked_area, invalid_transform, validate_output_size,
};
use super::geometry::{
    band_row, collect_column, low_count, store_column, validate_level, validate_level_bands,
};
use super::wavelets::{inverse_5_3, inverse_9_7};
use super::{FIXED_BITS, ReconstructedPlane, WaveletBand, WaveletLevel};
#[cfg(verus_keep_ghost)]
use super::{
    arbitrary_kernel_option, arbitrary_kernel_supplied, reconstruction_outcome, sequence_outcome,
    wavelet_band_view, wavelet_level_view,
};
use crate::codestream::ArbitraryKernel;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures reconstruction_outcome(result) == crate::specs::part1_inverse_empty_level(
        wavelet_level_view(level), irreversible, crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub(crate) fn inverse_empty_level(
    level: WaveletLevel<'_>,
    irreversible: bool,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    if level.output_width != 0 && level.output_height != 0 {
        return Err(invalid_transform());
    }
    validate_level_bands(level)?;
    let length = checked_area(level.output_width, level.output_height)?;
    validate_output_size(length, limits)?;
    Ok(ReconstructedPlane {
        width: level.output_width,
        height: level.output_height,
        fraction_bits: if irreversible { FIXED_BITS } else { 0 },
        samples: Vec::new(),
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_level_result(wavelet_level_view(level),false,None,crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_level(
        wavelet_level_view(level), false, crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_level_5_3(
    level: WaveletLevel<'_>,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_level(level, limits, false, None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_level_result(wavelet_level_view(level),true,None,crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_level(
        wavelet_level_view(level), true, crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_level_9_7(
    level: WaveletLevel<'_>,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_level(level, limits, true, None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_level_result(wavelet_level_view(level),!crate::codestream::raw_kernel_view(*kernel).0,Some(crate::codestream::raw_kernel_view(*kernel)),crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result)
        == crate::specs::part2_atk_inverse_level(wavelet_level_view(level), !crate::codestream::raw_kernel_view(*kernel).0,
            crate::codestream::raw_kernel_view(*kernel), crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn inverse_level_arbitrary(
    level: WaveletLevel<'_>,
    kernel: &ArbitraryKernel,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_level(level, limits, !kernel.reversible(), Some(kernel))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_horizontal_result(wavelet_band_view(low),wavelet_band_view(high),output_width,low_pass_first,false,None,crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_horizontal(
        wavelet_band_view(low), wavelet_band_view(high), output_width, low_pass_first, false,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_horizontal_5_3(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_width: u32,
    low_pass_first: bool,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_horizontal(low, high, output_width, low_pass_first, limits, false, None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_horizontal_result(wavelet_band_view(low),wavelet_band_view(high),output_width,low_pass_first,true,None,crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_horizontal(
        wavelet_band_view(low), wavelet_band_view(high), output_width, low_pass_first, true,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_horizontal_9_7(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_width: u32,
    low_pass_first: bool,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_horizontal(low, high, output_width, low_pass_first, limits, true, None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_horizontal_result(wavelet_band_view(low),wavelet_band_view(high),output_width,low_pass_first,!crate::codestream::raw_kernel_view(*kernel).0,Some(crate::codestream::raw_kernel_view(*kernel)),crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result)
        == crate::specs::part2_atk_inverse_horizontal(wavelet_band_view(low), wavelet_band_view(high),
            output_width, low_pass_first, !crate::codestream::raw_kernel_view(*kernel).0, crate::codestream::raw_kernel_view(*kernel),
            crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn inverse_horizontal_arbitrary(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_width: u32,
    low_pass_first: bool,
    kernel: &ArbitraryKernel,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_horizontal(
        low,
        high,
        output_width,
        low_pass_first,
        limits,
        !kernel.reversible(),
        Some(kernel),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_horizontal_result(wavelet_band_view(low),wavelet_band_view(high),output_width,low_pass_first,irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        kernel.is_none() && reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_horizontal(
        wavelet_band_view(low), wavelet_band_view(high), output_width, low_pass_first, irreversible,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
    arbitrary_kernel_supplied(kernel) && reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part2_atk_inverse_horizontal(
        wavelet_band_view(low), wavelet_band_view(high), output_width, low_pass_first, irreversible,
        arbitrary_kernel_option(kernel).unwrap(), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
fn inverse_horizontal(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_width: u32,
    low_pass_first: bool,
    limits: &ResourceLimits,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
) -> Result<ReconstructedPlane, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_horizontal_normal(wavelet_band_view(low),wavelet_band_view(high),output_width,low_pass_first,irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits));}
    if low.height == 0
        || low.height != high.height
        || low.width != low_count(output_width, low_pass_first)
        || high.width
            != output_width
                .checked_sub(low.width)
                .ok_or_else(arithmetic_overflow)?
    {
        return Err(invalid_transform());
    }
    let output_len = checked_area(output_width, low.height)?;
    validate_output_size(output_len, limits)?;
    let rows = inverse_rows(low, high, low_pass_first, irreversible, kernel, output_len);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_horizontal_observed(wavelet_band_view(low),wavelet_band_view(high),output_width,low_pass_first,irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),output_len,sequence_outcome(rows));}
    let samples = rows?;
    Ok(ReconstructedPlane {
        width: output_width,
        height: low.height,
        fraction_bits: if irreversible { FIXED_BITS } else { 0 },
        samples,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_rows_result(wavelet_band_view(low),wavelet_band_view(high),low_pass_first,irreversible,arbitrary_kernel_option(kernel),capacity,sequence_outcome(result)),
        kernel.is_none() && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_horizontal_prefix(
        wavelet_band_view(low), wavelet_band_view(high), low_pass_first, irreversible, low.height as nat,
    ),
    arbitrary_kernel_supplied(kernel) && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part2_atk_horizontal_prefix(
        wavelet_band_view(low), wavelet_band_view(high), low_pass_first, arbitrary_kernel_option(kernel).unwrap(), low.height as nat,
    ),
))]
fn inverse_rows(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    low_pass_first: bool,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
    capacity: usize,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_rows_normal(wavelet_band_view(low),wavelet_band_view(high),low_pass_first,irreversible,arbitrary_kernel_option(kernel),capacity);}
    let allocated = if capacity == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(capacity)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Rows,capacity as nat,unit);
        if let Err(error)=allocated{crate::specs::part2_wavelet_rows_refused(wavelet_band_view(low),wavelet_band_view(high),low_pass_first,irreversible,arbitrary_kernel_option(kernel),capacity,error);}
    }
    let mut samples = allocated?;
    let mut y = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant y <= low.height,
            crate::specs::part2_wavelet_rows_result(wavelet_band_view(low),wavelet_band_view(high),low_pass_first,irreversible,arbitrary_kernel_option(kernel),capacity,
                crate::specs::part2_wavelet_rows_value(wavelet_band_view(low),wavelet_band_view(high),low_pass_first,irreversible,arbitrary_kernel_option(kernel))),
            kernel.is_none() ==> crate::specs::part1_horizontal_prefix(
                wavelet_band_view(low), wavelet_band_view(high), low_pass_first, irreversible, y as nat,
            ) == Ok(samples@),
            arbitrary_kernel_supplied(kernel) ==> crate::specs::part2_atk_horizontal_prefix(
                wavelet_band_view(low), wavelet_band_view(high), low_pass_first, arbitrary_kernel_option(kernel).unwrap(), y as nat,
            ) == Ok(samples@),
            decreases low.height - y,
        )
    )]
    while y < low.height {
        let row = match inverse_row_pair(low, high, y, low_pass_first, irreversible, kernel) {
            Ok(row) => row,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_wavelet_rows_child_error(wavelet_band_view(low),wavelet_band_view(high),low_pass_first,irreversible,arbitrary_kernel_option(kernel),capacity,y as nat,samples@,error);
                    if error!=DecodeError::AllocationFailed{
                    if kernel.is_none() {
                        crate::proofs::production_impl::production_horizontal_error_persists(
                            wavelet_band_view(low), wavelet_band_view(high), low_pass_first, irreversible,
                            y as nat + 1, low.height as nat, error,
                        );
                    } else if arbitrary_kernel_supplied(kernel) {
                        crate::proofs::production_impl::production_atk_horizontal_error_persists(
                            wavelet_band_view(low), wavelet_band_view(high), low_pass_first, arbitrary_kernel_option(kernel).unwrap(),
                            y as nat + 1, low.height as nat, error,
                        );
                    }
                    }
                }
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost appended = samples@ + row@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            if kernel.is_none() {
                assert(crate::specs::part1_horizontal_prefix(
                    wavelet_band_view(low), wavelet_band_view(high), low_pass_first, irreversible, y as nat + 1,
                ) == Ok(appended));
            } else if arbitrary_kernel_supplied(kernel) {
                assert(crate::specs::part2_atk_horizontal_prefix(
                    wavelet_band_view(low), wavelet_band_view(high), low_pass_first,
                    arbitrary_kernel_option(kernel).unwrap(), y as nat + 1,
                ) == Ok(appended));
            }
        }
        samples.extend_from_slice(&row);
        #[cfg(verus_keep_ghost)]
        proof! { assert(samples@ == appended); }
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(samples)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_row_result(wavelet_band_view(low),wavelet_band_view(high),y,low_first,irreversible,arbitrary_kernel_option(kernel),sequence_outcome(result)),
        kernel.is_none() && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_horizontal_row(
        wavelet_band_view(low), wavelet_band_view(high), y, low_first, irreversible,
    ),
    arbitrary_kernel_supplied(kernel) && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part2_atk_horizontal_row(
        wavelet_band_view(low), wavelet_band_view(high), y, low_first, arbitrary_kernel_option(kernel).unwrap(),
    ),
))]
fn inverse_row_pair(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    y: u32,
    low_first: bool,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_row_normal(wavelet_band_view(low),wavelet_band_view(high),y,low_first,irreversible,arbitrary_kernel_option(kernel));}
    let low_row = band_row(low, y)?;
    let high_row = band_row(high, y)?;
    let result = if let Some(kernel) = kernel {
        inverse_arbitrary(low_row, high_row, low_first, kernel)
    } else if irreversible {
        inverse_9_7(low_row, high_row, low_first)
    } else {
        inverse_5_3(low_row, high_row, low_first)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(kernel)=kernel{crate::specs::part2_wavelet_sequence_kernel_observed(low_row@,high_row@,low_first,irreversible,crate::codestream::raw_kernel_view(*kernel),sequence_outcome(result));}
        crate::specs::part2_wavelet_row_child_observed(wavelet_band_view(low),wavelet_band_view(high),y,low_first,irreversible,arbitrary_kernel_option(kernel),low_row@,high_row@,sequence_outcome(result));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_vertical_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,false,None,crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_vertical(
        wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, false,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_vertical_5_3(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_height: u32,
    low_pass_first: bool,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_vertical(
        low,
        high,
        output_height,
        low_pass_first,
        limits,
        false,
        None,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_vertical_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,true,None,crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_vertical(
        wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, true,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_vertical_9_7(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_height: u32,
    low_pass_first: bool,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_vertical(low, high, output_height, low_pass_first, limits, true, None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_vertical_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,!crate::codestream::raw_kernel_view(*kernel).0,Some(crate::codestream::raw_kernel_view(*kernel)),crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result)
        == crate::specs::part2_atk_inverse_vertical(wavelet_band_view(low), wavelet_band_view(high),
            output_height, low_pass_first, !crate::codestream::raw_kernel_view(*kernel).0, crate::codestream::raw_kernel_view(*kernel),
            crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn inverse_vertical_arbitrary(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_height: u32,
    low_pass_first: bool,
    kernel: &ArbitraryKernel,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_vertical(
        low,
        high,
        output_height,
        low_pass_first,
        limits,
        !kernel.reversible(),
        Some(kernel),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_vertical_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        kernel.is_none() && reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_vertical(
        wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, irreversible,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
    arbitrary_kernel_supplied(kernel) && reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part2_atk_inverse_vertical(
        wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, irreversible,
        arbitrary_kernel_option(kernel).unwrap(), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
fn inverse_vertical(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_height: u32,
    low_pass_first: bool,
    limits: &ResourceLimits,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
) -> Result<ReconstructedPlane, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_vertical_normal(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits));}
    if low.width == 0
        || low.width != high.width
        || low.height != low_count(output_height, low_pass_first)
        || high.height
            != output_height
                .checked_sub(low.height)
                .ok_or_else(arithmetic_overflow)?
    {
        return Err(invalid_transform());
    }
    let output_len = checked_area(low.width, output_height)?;
    validate_output_size(output_len, limits)?;
    let columns = inverse_columns(
        low,
        high,
        output_height,
        low_pass_first,
        irreversible,
        kernel,
        output_len,
    );
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_vertical_observed(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),output_len,sequence_outcome(columns));}
    let samples = columns?;
    Ok(ReconstructedPlane {
        width: low.width,
        height: output_height,
        fraction_bits: if irreversible { FIXED_BITS } else { 0 },
        samples,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_columns_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,sequence_outcome(result)),
        kernel.is_none() && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_vertical_prefix(
        wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, irreversible,
        output_len, low.width as nat,
    ),
    arbitrary_kernel_supplied(kernel) && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part2_atk_vertical_prefix(
        wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
        arbitrary_kernel_option(kernel).unwrap(), output_len, low.width as nat,
    ),
))]
fn inverse_columns(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_height: u32,
    low_pass_first: bool,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
    output_len: usize,
) -> Result<Vec<i64>, DecodeError> {
    if !irreversible
        && kernel.is_none()
        && super::rowwise::eligible(low, high, output_height, low_pass_first, output_len)?
    {
        let result = super::rowwise::inverse(low, high, output_height, low_pass_first, output_len);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_wavelet_columns_observed(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,sequence_outcome(result));}
        return result;
    }
    if irreversible
        && kernel.is_none()
        && output_height > 1
        && super::rowwise::eligible(low, high, output_height, low_pass_first, output_len)?
    {
        let result =
            super::rowwise::inverse_fixed(low, high, output_height, low_pass_first, output_len);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_wavelet_columns_observed(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,sequence_outcome(result));}
        return result;
    }
    let result = inverse_columns_scalar(
        low,
        high,
        output_height,
        low_pass_first,
        irreversible,
        kernel,
        output_len,
    );
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_columns_observed(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,sequence_outcome(result));}
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_scalar_columns_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,sequence_outcome(result)),
        kernel.is_none() && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_vertical_prefix(
            wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,output_len,low.width as nat),
        arbitrary_kernel_supplied(kernel) && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part2_atk_vertical_prefix(
            wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,arbitrary_kernel_option(kernel).unwrap(),output_len,low.width as nat),
))]
fn inverse_columns_scalar(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    output_height: u32,
    low_pass_first: bool,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
    output_len: usize,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_scalar_columns_normal(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len);}
    let allocated = crate::allocation::zero_i64_values(output_len);
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_wavelet_capacity_observed(crate::specs::Part2WaveletPlaneOwner::Columns,output_len as nat,unit);
        if let Err(error)=allocated{crate::specs::part2_wavelet_scalar_columns_refused(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,error);}
    }
    let mut samples = allocated?;
    #[cfg(verus_keep_ghost)]
    proof! { assert(samples@ =~= Seq::new(output_len as nat, |i: int| 0i64)); }
    let mut x = 0_u32;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant x <= low.width,
            crate::specs::part2_wavelet_scalar_columns_result(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,
                crate::specs::part2_wavelet_columns_value(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len)),
            kernel.is_none() ==> crate::specs::part1_vertical_prefix(
                wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, irreversible,
                output_len, x as nat,
            ) == Ok(samples@),
            arbitrary_kernel_supplied(kernel) ==> crate::specs::part2_atk_vertical_prefix(
                wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
                arbitrary_kernel_option(kernel).unwrap(), output_len, x as nat,
            ) == Ok(samples@),
            decreases low.width - x,
        )
    )]
    while x < low.width {
        let column = match inverse_column_pair(low, high, x, low_pass_first, irreversible, kernel) {
            Ok(column) => column,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_wavelet_columns_child_error(wavelet_band_view(low),wavelet_band_view(high),output_height,low_pass_first,irreversible,arbitrary_kernel_option(kernel),output_len,x as nat,samples@,error);
                    if error!=DecodeError::AllocationFailed{
                    if kernel.is_none() {
                        crate::proofs::production_impl::production_vertical_error_persists(
                            wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
                            irreversible, output_len, x as nat + 1, low.width as nat, error,
                        );
                    } else if arbitrary_kernel_supplied(kernel) {
                        crate::proofs::production_impl::production_atk_vertical_error_persists(
                            wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
                            arbitrary_kernel_option(kernel).unwrap(), output_len, x as nat + 1, low.width as nat, error,
                        );
                    }
                    }
                }
                return Err(error);
            }
        };
        match store_column(&mut samples, low.width, output_height, x, &column) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    if kernel.is_none() {
                        crate::proofs::production_impl::production_vertical_error_persists(
                            wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
                            irreversible, output_len, x as nat + 1, low.width as nat, error,
                        );
                    } else if arbitrary_kernel_supplied(kernel) {
                        crate::proofs::production_impl::production_atk_vertical_error_persists(
                            wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
                            arbitrary_kernel_option(kernel).unwrap(), output_len, x as nat + 1, low.width as nat, error,
                        );
                    }
                }
                return Err(error);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if kernel.is_none() {
                assert(crate::specs::part1_vertical_prefix(
                    wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first, irreversible,
                    output_len, x as nat + 1,
                ) == Ok(samples@));
            } else if arbitrary_kernel_supplied(kernel) {
                assert(crate::specs::part2_atk_vertical_prefix(
                    wavelet_band_view(low), wavelet_band_view(high), output_height, low_pass_first,
                    arbitrary_kernel_option(kernel).unwrap(), output_len, x as nat + 1,
                ) == Ok(samples@));
            }
        }
        x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(samples)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_column_result(wavelet_band_view(low),wavelet_band_view(high),x,low_pass_first,irreversible,arbitrary_kernel_option(kernel),sequence_outcome(result)),
        kernel.is_none() && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_vertical_column(
        wavelet_band_view(low), wavelet_band_view(high), x, low_pass_first, irreversible,
    ),
    arbitrary_kernel_supplied(kernel) && sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part2_atk_vertical_column(
        wavelet_band_view(low), wavelet_band_view(high), x, low_pass_first, arbitrary_kernel_option(kernel).unwrap(),
    ),
))]
fn inverse_column_pair(
    low: WaveletBand<'_>,
    high: WaveletBand<'_>,
    x: u32,
    low_pass_first: bool,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_column_normal(wavelet_band_view(low),wavelet_band_view(high),x,low_pass_first,irreversible,arbitrary_kernel_option(kernel));}
    let low_result = collect_column(low.samples, low.width, low.height, x);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=low_result{crate::specs::part2_wavelet_column_low_error(wavelet_band_view(low),wavelet_band_view(high),x,low_pass_first,irreversible,arbitrary_kernel_option(kernel),error);}}
    let low_column = low_result?;
    let high_result = collect_column(high.samples, high.width, high.height, x);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=high_result{crate::specs::part2_wavelet_column_high_error(wavelet_band_view(low),wavelet_band_view(high),x,low_pass_first,irreversible,arbitrary_kernel_option(kernel),low_column@,error);}}
    let high_column = high_result?;
    let result = if let Some(kernel) = kernel {
        inverse_arbitrary(&low_column, &high_column, low_pass_first, kernel)
    } else if irreversible {
        inverse_9_7(&low_column, &high_column, low_pass_first)
    } else {
        inverse_5_3(&low_column, &high_column, low_pass_first)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some(kernel)=kernel{crate::specs::part2_wavelet_sequence_kernel_observed(low_column@,high_column@,low_pass_first,irreversible,crate::codestream::raw_kernel_view(*kernel),sequence_outcome(result));}
        crate::specs::part2_wavelet_column_sequence_observed(wavelet_band_view(low),wavelet_band_view(high),x,low_pass_first,irreversible,arbitrary_kernel_option(kernel),low_column@,high_column@,sequence_outcome(result));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod zero_level {
    use super::super::WaveletLevel;
    #[cfg(verus_keep_ghost)]
    use super::super::wavelet_level_view;
    #[cfg(verus_keep_ghost)]
    use crate::DecodeError;
    #[cfg(verus_keep_ghost)]
    use vstd::prelude::*;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == forall |i: int| 0 <= i < samples.len() ==> #[trigger] samples@[i] == 0i64,
    ))]
    #[inline]
    pub(super) fn slice_is_all_zero(samples: &[i64]) -> bool {
        let mut i = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= samples.len(),
                forall |k: int| 0 <= k < i ==> #[trigger] samples@[k] == 0i64,
            decreases samples.len() - i,
        ))]
        while i < samples.len() {
            if samples[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == forall |i: int| 0 <= i < samples.len() ==> -1_073_741_824i64 <= #[trigger] samples@[i] <= 1_073_741_824i64,
    ))]
    #[inline]
    fn slice_within_bound(samples: &[i64]) -> bool {
        let mut i = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= samples.len(),
                forall |k: int| 0 <= k < i ==> -1_073_741_824i64 <= #[trigger] samples@[k] <= 1_073_741_824i64,
            decreases samples.len() - i,
        ))]
        while i < samples.len() {
            let v = samples[i];
            #[allow(
                clippy::manual_range_contains,
                reason = "Direct comparisons keep Verus loop invariants simple."
            )]
            if v < -1_073_741_824 || v > 1_073_741_824 {
                return false;
            }
            i += 1;
        }
        true
    }

    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn zeros(n: nat) -> Seq<i64> {
            Seq::new(n, |_: int| 0i64)
        }

        proof fn zero_interleave(low: Seq<i64>, high: Seq<i64>, first: bool)
            requires
                low.len() + high.len() <= usize::MAX,
                low.len() == if first { (low.len() + high.len()) / 2 + (low.len() + high.len()) % 2 } else { (low.len() + high.len()) / 2 },
                forall |i: int| 0 <= i < low.len() ==> #[trigger] low[i] == 0i64,
                forall |i: int| 0 <= i < high.len() ==> #[trigger] high[i] == 0i64,
            ensures
                crate::specs::part1_interleaved(low, high, first) == Ok::<Seq<i64>, DecodeError>(zeros(low.len() + high.len())),
        {
            let expected = crate::specs::part1_interleaved(low, high, first).get_Ok_0();
            assert(expected =~= zeros(low.len() + high.len()));
        }

        proof fn zero_scale_prefix(n: nat, low_parity: bool, factor: i64, k: nat)
            requires k <= n,
            ensures crate::specs::part1_scaling_prefix(zeros(n), low_parity, factor, k) == (Ok::<(), DecodeError>(()), zeros(n)),
            decreases k,
        {
            reveal_with_fuel(crate::specs::part1_scaling_prefix, 2);
            if k > 0 {
                zero_scale_prefix(n, low_parity, factor, (k - 1) as nat);
                assert(((0i64 as int) * (factor as int) + 32768) == 32768int);
                assert(((32768i64) >> 16i64) == 0i64) by(bit_vector);
                assert(zeros(n).update((k - 1) as int, 0i64) =~= zeros(n));
            }
        }

        proof fn zero_lifting_prefix(n: nat, target_even: bool, kind: u8, factor: i64, k: nat)
            requires k <= n,
            ensures crate::specs::part1_lifting_prefix(zeros(n), target_even, kind, factor, k) == (Ok::<(), DecodeError>(()), zeros(n)),
            decreases k,
        {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            if k > 0 {
                zero_lifting_prefix(n, target_even, kind, factor, (k - 1) as nat);
                assert((2i64 >> 2i64) == 0i64 && (0i64 >> 1i64) == 0i64 && (32768i64 >> 16i64) == 0i64) by(bit_vector);
                assert(((0i64 as int) * (factor as int) + 32768) == 32768int);
                assert(zeros(n).update((k - 1) as int, 0i64) =~= zeros(n));
            }
        }

        #[verifier::spinoff_prover]
        proof fn zero_1d_wavelet(low: Seq<i64>, high: Seq<i64>, first: bool, irreversible: bool)
            requires
                low.len() + high.len() <= usize::MAX,
                low.len() == if first { (low.len() + high.len()) / 2 + (low.len() + high.len()) % 2 } else { (low.len() + high.len()) / 2 },
                forall |i: int| 0 <= i < low.len() ==> #[trigger] low[i] == 0i64,
                forall |i: int| 0 <= i < high.len() ==> #[trigger] high[i] == 0i64,
            ensures
                (if irreversible {
                    crate::specs::part1_inverse_nine_seven(low, high, first)
                } else {
                    crate::specs::part1_inverse_five_three(low, high, first)
                }) == Ok::<Seq<i64>, DecodeError>(zeros(low.len() + high.len())),
        {
            let n = low.len() + high.len();
            zero_interleave(low, high, first);
            if n == 1 && !first {
                assert((0i64 >> 1i64) == 0i64) by(bit_vector);
                assert(zeros(1).update(0, 0i64) =~= zeros(1));
            } else if irreversible {
                if n > 1 {
                    zero_scale_prefix(n, first, crate::specs::part1_nine_seven_scale(true), n);
                    zero_scale_prefix(n, !first, crate::specs::part1_nine_seven_scale(false), n);
                    reveal_with_fuel(crate::specs::part1_nine_seven_lifting_prefix, 5);
                    zero_lifting_prefix(n, first, 2u8, crate::specs::part1_nine_seven_lift(0), n);
                    zero_lifting_prefix(n, !first, 2u8, crate::specs::part1_nine_seven_lift(1), n);
                    zero_lifting_prefix(n, first, 2u8, crate::specs::part1_nine_seven_lift(2), n);
                    zero_lifting_prefix(n, !first, 2u8, crate::specs::part1_nine_seven_lift(3), n);
                }
            } else {
                zero_lifting_prefix(n, first, 0u8, 0, n);
                zero_lifting_prefix(n, !first, 1u8, 0, n);
            }
        }

        proof fn zero_horizontal_prefix(
            low: crate::specs::Part1WaveletBand,
            high: crate::specs::Part1WaveletBand,
            first: bool,
            irreversible: bool,
            y: nat,
        )
            requires
                y <= low.1,
                low.1 == high.1,
                low.1 <= usize::MAX,
                low.0 as nat + high.0 as nat <= usize::MAX,
                low.0 as nat == if first { (low.0 as nat + high.0 as nat) / 2 + (low.0 as nat + high.0 as nat) % 2 } else { (low.0 as nat + high.0 as nat) / 2 },
                low.2.len() == (low.0 as nat) * (low.1 as nat),
                high.2.len() == (high.0 as nat) * (high.1 as nat),
                (low.0 as nat + high.0 as nat) * (low.1 as nat) <= usize::MAX,
                forall |i: int| 0 <= i < low.2.len() ==> #[trigger] low.2[i] == 0i64,
                forall |i: int| 0 <= i < high.2.len() ==> #[trigger] high.2[i] == 0i64,
            ensures
                crate::specs::part1_horizontal_prefix(low, high, first, irreversible, y)
                    == Ok::<Seq<i64>, DecodeError>(zeros(y * (low.0 as nat + high.0 as nat))),
            decreases y,
        {
            if y == 0 {
                assert(Seq::<i64>::empty() =~= zeros(0));
            } else {
                let prev = (y - 1) as nat;
                zero_horizontal_prefix(low, high, first, irreversible, prev);
                let lw = low.0 as nat;
                let hw = high.0 as nat;
                let w = lw + hw;
                assert(prev * lw + lw <= low.2.len() && prev * hw + hw <= high.2.len()
                    && low.2.len() <= w * (low.1 as nat) && high.2.len() <= w * (low.1 as nat)) by(nonlinear_arith)
                    requires prev < low.1, w == lw + hw,
                        low.2.len() == lw * (low.1 as nat), high.2.len() == hw * (low.1 as nat);
                let lr = low.2.subrange((prev * lw) as int, (prev * lw + lw) as int);
                let hr = high.2.subrange((prev * hw) as int, (prev * hw + hw) as int);
                assert(crate::specs::part1_band_row(low, prev as u32) == Ok::<Seq<i64>, DecodeError>(lr));
                assert(crate::specs::part1_band_row(high, prev as u32) == Ok::<Seq<i64>, DecodeError>(hr));
                zero_1d_wavelet(lr, hr, first, irreversible);
                assert(zeros(prev * w) + zeros(w) =~= zeros(y * w)) by {
                    assert(prev * w + w == y * w) by(nonlinear_arith) requires y == prev + 1;
                }
            }
        }

        proof fn zero_column_prefix(
            samples: Seq<i64>,
            width: u32,
            height: u32,
            x: u32,
            r: nat,
        )
            requires
                x < width,
                r <= height,
                width <= usize::MAX,
                height <= usize::MAX,
                samples.len() == (width as nat) * (height as nat),
                samples.len() <= usize::MAX,
                forall |i: int| 0 <= i < samples.len() ==> #[trigger] samples[i] == 0i64,
            ensures
                crate::specs::part1_column_prefix(samples, width, x, r)
                    == Ok::<Seq<i64>, DecodeError>(zeros(r)),
            decreases r,
        {
            if r == 0 {
                assert(Seq::<i64>::empty() =~= zeros(0));
            } else {
                let prev = (r - 1) as nat;
                zero_column_prefix(samples, width, height, x, prev);
                assert(prev * (width as nat) + (x as nat) < samples.len()) by(nonlinear_arith)
                    requires prev < height, x < width, samples.len() == (width as nat) * (height as nat);
                assert(crate::specs::part1_column_sample(samples, width, x, prev as u32) == Ok::<i64, DecodeError>(0i64));
                assert(zeros(prev).push(0i64) =~= zeros(r));
            }
        }

        proof fn zero_store_column_prefix(
            output_len: nat,
            width: u32,
            height: u32,
            x: u32,
            r: nat,
        )
            requires
                x < width,
                r <= height,
                width <= usize::MAX,
                height <= usize::MAX,
                output_len <= usize::MAX,
                output_len == (width as nat) * (height as nat),
            ensures
                crate::specs::part1_store_column_prefix(zeros(output_len), width, x, zeros(height as nat), r)
                    == (Ok::<(), DecodeError>(()), zeros(output_len)),
            decreases r,
        {
            if r > 0 {
                let prev = (r - 1) as nat;
                zero_store_column_prefix(output_len, width, height, x, prev);
                assert(prev * (width as nat) + (x as nat) < output_len) by(nonlinear_arith)
                    requires prev < height, x < width, output_len == (width as nat) * (height as nat);
                assert(crate::specs::part1_transform_offset(prev as u32, width, x)
                    == Ok::<usize, DecodeError>((prev * (width as nat) + (x as nat)) as usize));
                assert(zeros(output_len).update((prev * (width as nat) + (x as nat)) as int, 0i64) =~= zeros(output_len));
            }
        }

        proof fn zero_vertical_prefix(
            low: crate::specs::Part1WaveletBand,
            high: crate::specs::Part1WaveletBand,
            output_height: u32,
            first: bool,
            irreversible: bool,
            output_len: usize,
            x: nat,
        )
            requires
                x <= low.0,
                low.0 == high.0,
                low.0 <= usize::MAX,
                low.1 as nat + high.1 as nat == output_height as nat,
                output_height <= usize::MAX,
                low.1 as nat == if first { output_height as nat / 2 + output_height as nat % 2 } else { output_height as nat / 2 },
                low.2.len() == (low.0 as nat) * (low.1 as nat),
                high.2.len() == (high.0 as nat) * (high.1 as nat),
                output_len as nat == (low.0 as nat) * (output_height as nat),
                forall |i: int| 0 <= i < low.2.len() ==> #[trigger] low.2[i] == 0i64,
                forall |i: int| 0 <= i < high.2.len() ==> #[trigger] high.2[i] == 0i64,
            ensures
                crate::specs::part1_vertical_prefix(low, high, output_height, first, irreversible, output_len, x)
                    == Ok::<Seq<i64>, DecodeError>(zeros(output_len as nat)),
            decreases x,
        {
            if x == 0 {
                assert(Seq::new(output_len as nat, |_: int| 0i64) =~= zeros(output_len as nat));
            } else {
                let prev = (x - 1) as nat;
                zero_vertical_prefix(low, high, output_height, first, irreversible, output_len, prev);
                assert(low.2.len() <= output_len as nat && high.2.len() <= output_len as nat) by(nonlinear_arith)
                    requires low.1 <= output_height, high.1 <= output_height, low.0 == high.0,
                        low.2.len() == (low.0 as nat) * (low.1 as nat),
                        high.2.len() == (high.0 as nat) * (high.1 as nat),
                        output_len as nat == (low.0 as nat) * (output_height as nat);
                zero_column_prefix(low.2, low.0, low.1, prev as u32, low.1 as nat);
                zero_column_prefix(high.2, high.0, high.1, prev as u32, high.1 as nat);
                assert(crate::specs::part1_collect_column(low, prev as u32) == Ok::<Seq<i64>, DecodeError>(zeros(low.1 as nat)));
                assert(crate::specs::part1_collect_column(high, prev as u32) == Ok::<Seq<i64>, DecodeError>(zeros(high.1 as nat)));
                zero_1d_wavelet(zeros(low.1 as nat), zeros(high.1 as nat), first, irreversible);
                zero_store_column_prefix(output_len as nat, low.0, output_height, prev as u32, output_height as nat);
            }
        }

        spec fn upsample_1d(low: Seq<i64>, out_len: nat) -> Seq<i64> {
            Seq::new(out_len, |i: int| {
                if i % 2 == 0 {
                    low[i / 2]
                } else {
                    let left = low[i / 2];
                    let right = if i / 2 + 1 < low.len() { low[i / 2 + 1] } else { low[i / 2] };
                    ((left as int + right as int) as i64) >> 1
                }
            })
        }

        proof fn avg_bounded(a: i64, b: i64)
            requires
                -1_073_741_824i64 <= a && a <= 1_073_741_824i64,
                -1_073_741_824i64 <= b && b <= 1_073_741_824i64,
            ensures
                -1_073_741_824i64 <= (((a as int + b as int) as i64) >> 1i64),
                (((a as int + b as int) as i64) >> 1i64) <= 1_073_741_824i64,
        {
            let s: i64 = (a as int + b as int) as i64;
            assert(-2_147_483_648i64 <= s && s <= 2_147_483_648i64);
            assert(-1_073_741_824i64 <= (s >> 1i64) && (s >> 1i64) <= 1_073_741_824i64) by(bit_vector)
                requires -2_147_483_648i64 <= s && s <= 2_147_483_648i64;
        }

        proof fn avg_self(a: i64)
            requires -1_073_741_824i64 <= a && a <= 1_073_741_824i64,
            ensures (((a as int + a as int) as i64) >> 1i64) == a,
        {
            let s: i64 = (a as int + a as int) as i64;
            assert(s == add(a, a));
            assert((add(a, a) >> 1i64) == a) by(bit_vector)
                requires -1_073_741_824i64 <= a && a <= 1_073_741_824i64;
        }

        proof fn zero_high_5_3_update_prefix(inter: Seq<i64>, k: nat)
            requires
                inter.len() > 1,
                k <= inter.len(),
                forall |i: int| 0 <= i < inter.len() && i % 2 == 1 ==> #[trigger] inter[i] == 0i64,
            ensures
                crate::specs::part1_lifting_prefix(inter, true, 0u8, 0, k) == (Ok::<(), DecodeError>(()), inter),
            decreases k,
        {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            if k > 0 {
                let idx = (k - 1) as nat;
                zero_high_5_3_update_prefix(inter, idx);
                if idx % 2 == 0 {
                    let left_i = if idx == 0 { 1int } else { idx as int - 1 };
                    let right_i = if idx + 1 < inter.len() { idx as int + 1 } else { idx as int - 1 };
                    assert(inter[left_i] == 0i64 && inter[right_i] == 0i64);
                    assert((2i64 >> 2i64) == 0i64) by(bit_vector);
                    assert(inter.update(idx as int, inter[idx as int]) =~= inter);
                } else {
                    assert(inter.update(idx as int, inter[idx as int]) =~= inter);
                }
            }
        }

        proof fn zero_high_5_3_predict_prefix(low: Seq<i64>, inter: Seq<i64>, k: nat)
            requires
                inter.len() > 1,
                k <= inter.len(),
                low.len() == inter.len() / 2 + inter.len() % 2,
                forall |i: int| 0 <= i < low.len() ==> -1_073_741_824i64 <= #[trigger] low[i] <= 1_073_741_824i64,
                forall |i: int| 0 <= i < inter.len() ==>
                    #[trigger] inter[i] == if i % 2 == 0 { low[i / 2] } else { 0i64 },
            ensures
                crate::specs::part1_lifting_prefix(inter, false, 1u8, 0, k)
                    == (Ok::<(), DecodeError>(()), Seq::new(inter.len(), |i: int| if i < k { upsample_1d(low, inter.len())[i] } else { inter[i] })),
            decreases k,
        {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            if k == 0 {
                assert(inter =~= Seq::new(inter.len(), |i: int| if i < 0 { upsample_1d(low, inter.len())[i] } else { inter[i] }));
            } else {
                let idx = (k - 1) as nat;
                zero_high_5_3_predict_prefix(low, inter, idx);
                let prev = Seq::new(inter.len(), |i: int| if i < idx { upsample_1d(low, inter.len())[i] } else { inter[i] });
                let target = Seq::new(inter.len(), |i: int| if i < k { upsample_1d(low, inter.len())[i] } else { inter[i] });
                if idx % 2 == 1 {
                    let left = low[(idx as int) / 2];
                    let right = if (idx as int) / 2 + 1 < low.len() { low[(idx as int) / 2 + 1] } else { low[(idx as int) / 2] };
                    assert(-2_147_483_648 <= (left as int) + (right as int) <= 2_147_483_648);
                    assert(prev.update(idx as int, upsample_1d(low, inter.len())[idx as int]) =~= target);
                } else {
                    assert(prev.update(idx as int, inter[idx as int]) =~= target);
                }
            }
        }

        #[verifier::spinoff_prover]
        proof fn zero_high_5_3_row(low: Seq<i64>, high: Seq<i64>)
            requires
                low.len() + high.len() > 1,
                low.len() + high.len() <= usize::MAX,
                low.len() == (low.len() + high.len()) / 2 + (low.len() + high.len()) % 2,
                forall |i: int| 0 <= i < low.len() ==> -1_073_741_824i64 <= #[trigger] low[i] <= 1_073_741_824i64,
                forall |i: int| 0 <= i < high.len() ==> #[trigger] high[i] == 0i64,
            ensures
                crate::specs::part1_inverse_five_three(low, high, true)
                    == Ok::<Seq<i64>, DecodeError>(upsample_1d(low, low.len() + high.len())),
        {
            let n = low.len() + high.len();
            let inter = crate::specs::part1_interleaved(low, high, true).get_Ok_0();
            zero_high_5_3_update_prefix(inter, n);
            zero_high_5_3_predict_prefix(low, inter, n);
            assert(Seq::new(n, |i: int| if i < n { upsample_1d(low, n)[i] } else { inter[i] }) =~= upsample_1d(low, n));
        }

        proof fn zero_high_5_3_horizontal_prefix(
            ll: crate::specs::Part1WaveletBand,
            hl: crate::specs::Part1WaveletBand,
            output_width: u32,
            y: nat,
        )
            requires
                y <= ll.1,
                ll.1 == hl.1,
                ll.1 <= usize::MAX,
                output_width >= 4,
                output_width <= usize::MAX,
                ll.0 as nat + hl.0 as nat == output_width as nat,
                ll.0 as nat == output_width as nat / 2 + output_width as nat % 2,
                ll.2.len() == (ll.0 as nat) * (ll.1 as nat),
                hl.2.len() == (hl.0 as nat) * (hl.1 as nat),
                (output_width as nat) * (ll.1 as nat) <= usize::MAX,
                forall |i: int| 0 <= i < ll.2.len() ==> -1_073_741_824i64 <= #[trigger] ll.2[i] <= 1_073_741_824i64,
                forall |i: int| 0 <= i < hl.2.len() ==> #[trigger] hl.2[i] == 0i64,
            ensures
                crate::specs::part1_horizontal_prefix(ll, hl, true, false, y)
                    == Ok::<Seq<i64>, DecodeError>(Seq::new(y * (output_width as nat), |idx: int| {
                        let r = idx / (output_width as int);
                        let c = idx % (output_width as int);
                        let lr = ll.2.subrange(r * (ll.0 as int), (r + 1) * (ll.0 as int));
                        upsample_1d(lr, output_width as nat)[c]
                    })),
            decreases y,
        {
            let w = output_width as nat;
            if y == 0 {
                assert(Seq::<i64>::empty() =~= Seq::new(0nat, |idx: int| {
                    let r = idx / (output_width as int);
                    let c = idx % (output_width as int);
                    let lr = ll.2.subrange(r * (ll.0 as int), (r + 1) * (ll.0 as int));
                    upsample_1d(lr, w)[c]
                }));
            } else {
                let prev = (y - 1) as nat;
                zero_high_5_3_horizontal_prefix(ll, hl, output_width, prev);
                let lw = ll.0 as nat;
                let hw = hl.0 as nat;
                assert(prev * lw + lw <= ll.2.len() && prev * hw + hw <= hl.2.len()
                    && ll.2.len() <= w * (ll.1 as nat) && hl.2.len() <= w * (ll.1 as nat)) by(nonlinear_arith)
                    requires prev < ll.1, w == lw + hw,
                        ll.2.len() == lw * (ll.1 as nat), hl.2.len() == hw * (ll.1 as nat);
                let lr = ll.2.subrange((prev * lw) as int, (prev * lw + lw) as int);
                let hr = hl.2.subrange((prev * hw) as int, (prev * hw + hw) as int);
                assert(crate::specs::part1_band_row(ll, prev as u32) == Ok::<Seq<i64>, DecodeError>(lr));
                assert(crate::specs::part1_band_row(hl, prev as u32) == Ok::<Seq<i64>, DecodeError>(hr));
                assert forall |i: int| 0 <= i < lr.len() implies -1_073_741_824i64 <= #[trigger] lr[i] <= 1_073_741_824i64 by {
                    assert(lr[i] == ll.2[(prev * lw) as int + i]);
                }
                assert forall |i: int| 0 <= i < hr.len() implies #[trigger] hr[i] == 0i64 by {
                    assert(hr[i] == hl.2[(prev * hw) as int + i]);
                }
                zero_high_5_3_row(lr, hr);
                let left = crate::specs::part1_horizontal_prefix(ll, hl, true, false, prev).get_Ok_0();
                let combined = left + upsample_1d(lr, w);
                let target = Seq::new(y * w, |idx: int| {
                    let r = idx / (output_width as int);
                    let c = idx % (output_width as int);
                    let row_s = ll.2.subrange(r * (ll.0 as int), (r + 1) * (ll.0 as int));
                    upsample_1d(row_s, w)[c]
                });
                assert(prev * w + w == y * w) by(nonlinear_arith) requires y == prev + 1;
                assert forall |idx: int| 0 <= idx < (y * w) as int implies combined[idx] == target[idx] by {
                    if idx < (prev * w) as int {
                    } else {
                        let c = idx - (prev * w) as int;
                        crate::specs::rowwise_index(prev as int, c, output_width as int);
                        assert((prev as int) * (ll.0 as int) + (ll.0 as int) == (prev as int + 1) * (ll.0 as int)) by(nonlinear_arith);
                    }
                }
                assert(combined =~= target);
            }
        }

        #[verifier::spinoff_prover]
        proof fn prove_all_zero_level(
            lv: crate::specs::Part1WaveletLevel,
            output: Seq<i64>,
            output_len: usize,
            irreversible: bool,
            maximum: u64,
        )
            requires
                crate::specs::part1_validate_level(lv) == Ok(()),
                crate::specs::part1_transform_area(lv.4, lv.5) == Ok(output_len),
                crate::specs::part1_wavelet_sample_count(lv.4, lv.5, output_len),
                crate::specs::part1_quantization_budget(output_len as nat, maximum) == Ok(()),
                lv.4 >= 4 && lv.5 >= 4,
                output =~= zeros(output_len as nat),
                forall |i: int| 0 <= i < lv.0.2.len() ==> #[trigger] lv.0.2[i] == 0i64,
                forall |i: int| 0 <= i < lv.1.2.len() ==> #[trigger] lv.1.2[i] == 0i64,
                forall |i: int| 0 <= i < lv.2.2.len() ==> #[trigger] lv.2.2[i] == 0i64,
                forall |i: int| 0 <= i < lv.3.2.len() ==> #[trigger] lv.3.2[i] == 0i64,
            ensures
                Ok::<(u32, u32, u8, Seq<i64>), DecodeError>((lv.4, lv.5, if irreversible { 16u8 } else { 0u8 }, output))
                    == crate::specs::part1_inverse_level(lv, irreversible, maximum),
        {
            assert(lv.0.0 as nat + lv.1.0 as nat == lv.4 as nat);
            assert(lv.2.0 as nat + lv.3.0 as nat == lv.4 as nat);
            assert(lv.0.1 as nat + lv.2.1 as nat == lv.5 as nat);
            assert((lv.4 as nat) * (lv.0.1 as nat) <= output_len as nat
                && (lv.4 as nat) * (lv.2.1 as nat) <= output_len as nat) by(nonlinear_arith)
                requires lv.0.1 <= lv.5, lv.2.1 <= lv.5, (lv.4 as nat) * (lv.5 as nat) == output_len as nat;
            assert(crate::specs::part1_transform_area(lv.4, lv.0.1).is_ok());
            assert(crate::specs::part1_transform_area(lv.4, lv.2.1).is_ok());
            zero_horizontal_prefix(lv.0, lv.1, lv.6, irreversible, lv.0.1 as nat);
            zero_horizontal_prefix(lv.2, lv.3, lv.6, irreversible, lv.2.1 as nat);
            let low_rows = crate::specs::part1_horizontal_prefix(lv.0, lv.1, lv.6, irreversible, lv.0.1 as nat).get_Ok_0();
            let high_rows = crate::specs::part1_horizontal_prefix(lv.2, lv.3, lv.6, irreversible, lv.2.1 as nat).get_Ok_0();
            assert(low_rows == zeros((lv.0.1 as nat) * (lv.4 as nat)));
            assert(high_rows == zeros((lv.2.1 as nat) * (lv.4 as nat)));
            assert((lv.0.1 as nat) * (lv.4 as nat) == (lv.4 as nat) * (lv.0.1 as nat)) by(nonlinear_arith);
            assert((lv.2.1 as nat) * (lv.4 as nat) == (lv.4 as nat) * (lv.2.1 as nat)) by(nonlinear_arith);
            zero_vertical_prefix((lv.4, lv.0.1, low_rows), (lv.4, lv.2.1, high_rows), lv.5, lv.7, irreversible, output_len, lv.4 as nat);
            assert(crate::specs::part1_level_rows_and_columns(lv, irreversible, output_len)
                == Ok::<(u32, u32, u8, Seq<i64>), DecodeError>((lv.4, lv.5, if irreversible { 16u8 } else { 0u8 }, output)));
        }

        #[verifier::spinoff_prover]
        proof fn prove_5_3_zero_detail_match_output(
            ll_samples: Seq<i64>,
            lw_u32: u32,
            lh_u32: u32,
            hh_u32: u32,
            w_u32: u32,
            h_u32: u32,
            low_rows: Seq<i64>,
            high_rows: Seq<i64>,
            output: Seq<i64>,
            output_len: usize,
        )
            requires
                w_u32 >= 4 && h_u32 >= 4,
                lw_u32 as nat == w_u32 as nat / 2 + w_u32 as nat % 2,
                lh_u32 as nat == h_u32 as nat / 2 + h_u32 as nat % 2,
                lh_u32 as nat + hh_u32 as nat == h_u32 as nat,
                (w_u32 as nat) * (h_u32 as nat) == output_len as nat,
                ll_samples.len() == (lw_u32 as nat) * (lh_u32 as nat),
                output.len() == output_len as nat,
                low_rows == Seq::new((lh_u32 as nat) * (w_u32 as nat), |idx: int| {
                    let r = idx / (w_u32 as int);
                    let c = idx % (w_u32 as int);
                    let lr = ll_samples.subrange(r * (lw_u32 as int), (r + 1) * (lw_u32 as int));
                    upsample_1d(lr, w_u32 as nat)[c]
                }),
                high_rows == zeros((hh_u32 as nat) * (w_u32 as nat)),
                crate::specs::rowwise_bounded(low_rows),
                crate::specs::rowwise_bounded(high_rows),
                forall |r: int, c: int| 0 <= r < lh_u32 && 0 <= c < w_u32 ==>
                    #[trigger] output[(2 * r) * (w_u32 as int) + c]
                        == upsample_1d(ll_samples.subrange(r * (lw_u32 as int), (r + 1) * (lw_u32 as int)), w_u32 as nat)[c],
                forall |r: int, c: int| 0 <= r < (h_u32 as int) / 2 && 0 <= c < w_u32 ==> {
                    let a = output[(2 * r) * (w_u32 as int) + c];
                    let b = if 2 * r + 2 < h_u32 { output[(2 * r + 2) * (w_u32 as int) + c] } else { a };
                    #[trigger] output[(2 * r + 1) * (w_u32 as int) + c] == (((a as int) + (b as int)) as i64) >> 1
                },
            ensures
                output == crate::specs::rowwise_output((w_u32, lh_u32, low_rows), (w_u32, hh_u32, high_rows), h_u32, true),
        {
            let w = w_u32 as int;
            let h = h_u32 as int;
            let lh = lh_u32 as int;
            let hh = hh_u32 as int;
            let low_band = (w_u32, lh_u32, low_rows);
            let high_band = (w_u32, hh_u32, high_rows);
            assert((lh_u32 as int) * (w_u32 as int) == w * lh
                && (hh_u32 as int) * (w_u32 as int) == w * hh) by(nonlinear_arith)
                requires w == w_u32 as int, lh == lh_u32 as int, hh == hh_u32 as int;
            let inter = crate::specs::rowwise_interleaved(low_band, high_band, h_u32, true);
            let upd = crate::specs::rowwise_stage(inter, w_u32 as nat, h_u32 as nat, true, false);
            assert(upd =~= inter) by {
                assert forall |i: int| 0 <= i < inter.len() implies upd[i] == inter[i] by {
                    crate::specs::rowwise_coordinates(i, w, h);
                    let r = i / w;
                    let c = i % w;
                    if r % 2 == 0 {
                        let left_r = if r == 0 { 1int } else { r - 1 };
                        let right_r = if r + 1 < h { r + 1 } else { r - 1 };
                        crate::specs::rowwise_cell(left_r, c, w, h);
                        crate::specs::rowwise_cell(right_r, c, w, h);
                        crate::specs::rowwise_index(left_r, c, w);
                        crate::specs::rowwise_index(right_r, c, w);
                        crate::specs::rowwise_cell(left_r / 2, c, w, hh);
                        crate::specs::rowwise_cell(right_r / 2, c, w, hh);
                        assert(inter[left_r * w + c] == high_rows[(left_r / 2) * w + c]);
                        assert(inter[right_r * w + c] == high_rows[(right_r / 2) * w + c]);
                        assert(inter[left_r * w + c] == 0i64 && inter[right_r * w + c] == 0i64);
                        assert(inter[i] == low_rows[(r / 2) * w + c]) by {
                            crate::specs::rowwise_cell(r / 2, c, w, lh);
                        }
                        assert((2i64 >> 2i64) == 0i64) by(bit_vector);
                    }
                }
            }
            let final_spec = crate::specs::rowwise_output(low_band, high_band, h_u32, true);
            assert(output =~= final_spec) by {
                assert forall |i: int| 0 <= i < output_len as int implies output[i] == final_spec[i] by {
                    crate::specs::rowwise_coordinates(i, w, h);
                    let r = i / w;
                    let c = i % w;
                    if r % 2 == 0 {
                        let hr = r / 2;
                        assert(2 * hr == r);
                        crate::specs::rowwise_cell(hr, c, w, lh);
                        crate::specs::rowwise_index(hr, c, w);
                        assert(inter[i] == low_rows[hr * w + c]);
                        assert(output[i] == output[(2 * hr) * w + c]);
                    } else {
                        let hr = r / 2;
                        assert(2 * hr + 1 == r);
                        let left_r = r - 1;
                        let right_r = if r + 1 < h { r + 1 } else { r - 1 };
                        crate::specs::rowwise_cell(left_r, c, w, h);
                        crate::specs::rowwise_cell(right_r, c, w, h);
                        crate::specs::rowwise_index(left_r, c, w);
                        crate::specs::rowwise_index(right_r, c, w);
                        crate::specs::rowwise_cell(hr, c, w, hh);
                        assert(inter[i] == high_rows[hr * w + c]);
                        assert(inter[i] == 0i64);
                        assert(inter[left_r * w + c] == output[left_r * w + c]) by {
                            crate::specs::rowwise_cell(left_r / 2, c, w, lh);
                            crate::specs::rowwise_index(left_r / 2, c, w);
                            assert(2 * (left_r / 2) == left_r);
                        }
                        assert(inter[right_r * w + c] == output[right_r * w + c]) by {
                            crate::specs::rowwise_cell(right_r / 2, c, w, lh);
                            crate::specs::rowwise_index(right_r / 2, c, w);
                            assert(2 * (right_r / 2) == right_r);
                        }
                        assert(output[i] == output[(2 * hr + 1) * w + c]);
                        assert(left_r == 2 * hr);
                        assert(right_r == if 2 * hr + 2 < h { 2 * hr + 2 } else { 2 * hr });
                    }
                }
            }
        }

        #[verifier::spinoff_prover]
        proof fn prove_5_3_zero_detail_rowwise(
            ll_samples: Seq<i64>,
            lw_u32: u32,
            lh_u32: u32,
            hh_u32: u32,
            w_u32: u32,
            h_u32: u32,
            low_rows: Seq<i64>,
            high_rows: Seq<i64>,
            output: Seq<i64>,
            output_len: usize,
        )
            requires
                w_u32 >= 4 && h_u32 >= 4,
                w_u32 <= usize::MAX && h_u32 <= usize::MAX,
                lw_u32 as nat == w_u32 as nat / 2 + w_u32 as nat % 2,
                lh_u32 as nat == h_u32 as nat / 2 + h_u32 as nat % 2,
                lh_u32 as nat + hh_u32 as nat == h_u32 as nat,
                (w_u32 as nat) * (h_u32 as nat) == output_len as nat,
                ll_samples.len() == (lw_u32 as nat) * (lh_u32 as nat),
                output.len() == output_len as nat,
                low_rows == Seq::new((lh_u32 as nat) * (w_u32 as nat), |idx: int| {
                    let r = idx / (w_u32 as int);
                    let c = idx % (w_u32 as int);
                    let lr = ll_samples.subrange(r * (lw_u32 as int), (r + 1) * (lw_u32 as int));
                    upsample_1d(lr, w_u32 as nat)[c]
                }),
                high_rows == zeros((hh_u32 as nat) * (w_u32 as nat)),
                forall |i: int| 0 <= i < ll_samples.len() ==> -1_073_741_824i64 <= #[trigger] ll_samples[i] <= 1_073_741_824i64,
                forall |r: int, c: int| 0 <= r < lh_u32 && 0 <= c < w_u32 ==>
                    #[trigger] output[(2 * r) * (w_u32 as int) + c]
                        == upsample_1d(ll_samples.subrange(r * (lw_u32 as int), (r + 1) * (lw_u32 as int)), w_u32 as nat)[c],
                forall |r: int, c: int| 0 <= r < (h_u32 as int) / 2 && 0 <= c < w_u32 ==> {
                    let a = output[(2 * r) * (w_u32 as int) + c];
                    let b = if 2 * r + 2 < h_u32 { output[(2 * r + 2) * (w_u32 as int) + c] } else { a };
                    #[trigger] output[(2 * r + 1) * (w_u32 as int) + c] == (((a as int) + (b as int)) as i64) >> 1
                },
            ensures
                crate::specs::part1_vertical_prefix(
                    (w_u32, lh_u32, low_rows),
                    (w_u32, hh_u32, high_rows),
                    h_u32,
                    true,
                    false,
                    output_len,
                    w_u32 as nat,
                ) == Ok::<Seq<i64>, DecodeError>(output),
        {
            let w = w_u32 as int;
            let lw = lw_u32 as int;
            let lh = lh_u32 as int;
            let low_band = (w_u32, lh_u32, low_rows);
            let high_band = (w_u32, hh_u32, high_rows);
            assert((lh_u32 as int) * (w_u32 as int) == w * lh
                && (hh_u32 as int) * (w_u32 as int) == (w_u32 as int) * (hh_u32 as int)) by(nonlinear_arith)
                requires w == w_u32 as int, lh == lh_u32 as int;
            assert(crate::specs::rowwise_bounded(low_rows)) by {
                assert forall |i: int| 0 <= i < low_rows.len() implies -1_073_741_824 <= #[trigger] low_rows[i] <= 1_073_741_824 by {
                    crate::specs::rowwise_coordinates(i, w, lh);
                    let r = i / w;
                    let c = i % w;
                    let xa = c / 2;
                    assert(0 <= xa && xa < lw);
                    assert(0 <= r * lw && (r + 1) * lw == r * lw + lw && (r + 1) * lw <= ll_samples.len()
                        && 0 <= r * lw + xa && r * lw + xa < ll_samples.len()
                        && (xa + 1 < lw ==> 0 <= r * lw + xa + 1 && r * lw + xa + 1 < ll_samples.len())) by(nonlinear_arith)
                        requires 0 <= r < lh, 0 <= xa < lw, ll_samples.len() == lw * lh;
                    let row_s = ll_samples.subrange(r * lw, (r + 1) * lw);
                    let la = row_s[xa];
                    assert(la == ll_samples[r * lw + xa]);
                    let ra = if xa + 1 < lw { row_s[xa + 1] } else { la };
                    if xa + 1 < lw {
                        assert(ra == ll_samples[r * lw + xa + 1]);
                    }
                    avg_bounded(la, ra);
                }
            }
            assert(crate::specs::rowwise_bounded(high_rows));
            assert(crate::specs::rowwise_eligible(low_band, high_band, h_u32, true, output_len)) by {
                assert((w_u32 as int) * (lh_u32 as int) + (w_u32 as int) * (hh_u32 as int) == output_len as int) by(nonlinear_arith)
                    requires (w_u32 as int) * (h_u32 as int) == output_len as int,
                        (lh_u32 as int) + (hh_u32 as int) == h_u32 as int;
            }
            crate::specs::rowwise_equivalent(low_band, high_band, h_u32, true, output_len);
            prove_5_3_zero_detail_match_output(
                ll_samples, lw_u32, lh_u32, hh_u32, w_u32, h_u32, low_rows, high_rows, output, output_len,
            );
        }

        #[verifier::spinoff_prover]
        proof fn prove_5_3_zero_detail_level(
            lv: crate::specs::Part1WaveletLevel,
            output: Seq<i64>,
            output_len: usize,
            maximum: u64,
        )
            requires
                crate::specs::part1_validate_level(lv) == Ok(()),
                crate::specs::part1_transform_area(lv.4, lv.5) == Ok(output_len),
                crate::specs::part1_wavelet_sample_count(lv.4, lv.5, output_len),
                crate::specs::part1_quantization_budget(output_len as nat, maximum) == Ok(()),
                lv.4 >= 4 && lv.5 >= 4,
                lv.6 && lv.7,
                output.len() == output_len as nat,
                forall |i: int| 0 <= i < lv.0.2.len() ==> -1_073_741_824i64 <= #[trigger] lv.0.2[i] <= 1_073_741_824i64,
                forall |i: int| 0 <= i < lv.1.2.len() ==> #[trigger] lv.1.2[i] == 0i64,
                forall |i: int| 0 <= i < lv.2.2.len() ==> #[trigger] lv.2.2[i] == 0i64,
                forall |i: int| 0 <= i < lv.3.2.len() ==> #[trigger] lv.3.2[i] == 0i64,
                forall |r: int, c: int| 0 <= r < lv.0.1 && 0 <= c < lv.4 ==>
                    #[trigger] output[(2 * r) * (lv.4 as int) + c]
                        == upsample_1d(lv.0.2.subrange(r * (lv.0.0 as int), (r + 1) * (lv.0.0 as int)), lv.4 as nat)[c],
                forall |r: int, c: int| 0 <= r < (lv.5 as int) / 2 && 0 <= c < lv.4 ==> {
                    let a = output[(2 * r) * (lv.4 as int) + c];
                    let b = if 2 * r + 2 < lv.5 { output[(2 * r + 2) * (lv.4 as int) + c] } else { a };
                    #[trigger] output[(2 * r + 1) * (lv.4 as int) + c] == (((a as int) + (b as int)) as i64) >> 1
                },
            ensures
                Ok::<(u32, u32, u8, Seq<i64>), DecodeError>((lv.4, lv.5, 0u8, output))
                    == crate::specs::part1_inverse_level(lv, false, maximum),
        {
            assert(lv.0.0 as nat + lv.1.0 as nat == lv.4 as nat);
            assert(lv.2.0 as nat + lv.3.0 as nat == lv.4 as nat);
            assert(lv.0.1 as nat + lv.2.1 as nat == lv.5 as nat);
            assert((lv.4 as nat) * (lv.0.1 as nat) <= output_len as nat
                && (lv.4 as nat) * (lv.2.1 as nat) <= output_len as nat) by(nonlinear_arith)
                requires lv.0.1 <= lv.5, lv.2.1 <= lv.5, (lv.4 as nat) * (lv.5 as nat) == output_len as nat;
            assert(crate::specs::part1_transform_area(lv.4, lv.0.1).is_ok());
            assert(crate::specs::part1_transform_area(lv.4, lv.2.1).is_ok());
            zero_high_5_3_horizontal_prefix(lv.0, lv.1, lv.4, lv.0.1 as nat);
            zero_horizontal_prefix(lv.2, lv.3, true, false, lv.2.1 as nat);
            let low_rows = crate::specs::part1_horizontal_prefix(lv.0, lv.1, true, false, lv.0.1 as nat).get_Ok_0();
            let high_rows = crate::specs::part1_horizontal_prefix(lv.2, lv.3, true, false, lv.2.1 as nat).get_Ok_0();
            assert(high_rows == zeros((lv.2.1 as nat) * (lv.4 as nat)));
            prove_5_3_zero_detail_rowwise(
                lv.0.2, lv.0.0, lv.0.1, lv.2.1, lv.4, lv.5, low_rows, high_rows, output, output_len,
            );
            assert(crate::specs::part1_level_rows_and_columns(lv, false, output_len)
                == Ok::<(u32, u32, u8, Seq<i64>), DecodeError>((lv.4, lv.5, 0u8, output)));
        }
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires
            crate::specs::part1_validate_level(wavelet_level_view(level)) == Ok(()),
            crate::specs::part1_transform_area(level.output_width, level.output_height) == Ok(output_len),
            crate::specs::part1_wavelet_sample_count(level.output_width, level.output_height, output_len),
            crate::specs::part1_quantization_budget(output_len as nat, maximum) == Ok(()),
            level.output_width >= 4 && level.output_height >= 4,
            forall |i: int| 0 <= i < level.ll.samples.len() ==> #[trigger] level.ll.samples@[i] == 0i64,
            forall |i: int| 0 <= i < level.hl.samples.len() ==> #[trigger] level.hl.samples@[i] == 0i64,
            forall |i: int| 0 <= i < level.lh.samples.len() ==> #[trigger] level.lh.samples@[i] == 0i64,
            forall |i: int| 0 <= i < level.hh.samples.len() ==> #[trigger] level.hh.samples@[i] == 0i64,
        ensures
            match result {
                Some(output) => Ok((level.output_width, level.output_height, if irreversible { 16u8 } else { 0u8 }, output@))
                    == crate::specs::part1_inverse_level(wavelet_level_view(level), irreversible, maximum),
                None => true,
            },
    ))]
    pub(super) fn try_all_zero(
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] level: WaveletLevel<'_>,
        output_len: usize,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] irreversible: bool,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] maximum: u64,
    ) -> Option<Vec<i64>> {
        let Ok(output) = crate::allocation::zero_i64_values(output_len) else {
            return None;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(output@ =~= zeros(output_len as nat));
            prove_all_zero_level(wavelet_level_view(level), output@, output_len, irreversible, maximum);
        }
        Some(output)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            w >= 4 && h >= 4,
            lw == w / 2 + w % 2 && lh == h / 2 + h % 2,
            w * h == old(output).len(),
            lw * lh == ll.len(),
            forall |i: int| 0 <= i < ll.len() ==> -1_073_741_824i64 <= #[trigger] ll@[i] <= 1_073_741_824i64,
        ensures
            final(output).len() == old(output).len(),
            forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                #[trigger] final(output)@[(2 * r) * w + c]
                    == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
    ))]
    fn fill_5_3_even_rows(
        ll: &[i64],
        output: &mut [i64],
        w: usize,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] h: usize,
        lw: usize,
        lh: usize,
    ) {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(lw >= 2 && lh >= 2) by(nonlinear_arith)
                requires w >= 4, h >= 4, lw == w / 2 + w % 2, lh == h / 2 + h % 2;
        }
        let mut y = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant y <= lh,
                w >= 4, h >= 4, lw >= 2, lh >= 2,
                lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                w * h == output.len(),
                lw * lh == ll.len(),
                forall |i: int| 0 <= i < ll.len() ==> -1_073_741_824i64 <= #[trigger] ll@[i] <= 1_073_741_824i64,
                forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==>
                    #[trigger] output@[(2 * r) * w + c]
                        == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
            decreases lh - y,
        ))]
        while y < lh {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(2 * (y as int) < h as int
                    && (y as int) * (lw as int) + (lw as int) <= ll.len()
                    && (2 * (y as int)) * (w as int) + (w as int) <= output.len()) by(nonlinear_arith)
                    requires y < lh, lw * lh == ll.len(), w * h == output.len(), lh == h / 2 + h % 2;
            }
            let src_start = y * lw;
            let dst_start = (2 * y) * w;
            let mut x = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x < lw, y < lh,
                    src_start == y * lw, dst_start == (2 * y) * w,
                    src_start + lw <= ll.len(), dst_start + w <= output.len(),
                    w >= 4, h >= 4, lw >= 2, lh >= 2,
                    lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                    w * h == output.len(),
                    forall |i: int| 0 <= i < ll.len() ==> -1_073_741_824i64 <= #[trigger] ll@[i] <= 1_073_741_824i64,
                    forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==>
                        #[trigger] output@[(2 * r) * w + c]
                            == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
                    forall |c: int| 0 <= c < 2 * x ==>
                        #[trigger] output@[dst_start as int + c]
                            == upsample_1d(ll@.subrange(src_start as int, (src_start + lw) as int), w as nat)[c],
                decreases lw - 1 - x,
            ))]
            while x + 1 < lw {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(2 * (x as int) + 1 < w as int) by(nonlinear_arith)
                        requires (x as int) + 1 < lw as int, lw == w / 2 + w % 2;
                }
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost before_step = output@; }
                let a = ll[src_start + x];
                let b = ll[src_start + x + 1];
                output[dst_start + 2 * x] = a;
                output[dst_start + 2 * x + 1] = (a + b) >> 1;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall |r: int, c: int| 0 <= r < y && 0 <= c < w implies #[trigger] output@[(2 * r) * (w as int) + c]
                        == upsample_1d(ll@.subrange(r * (lw as int), (r + 1) * (lw as int)), w as nat)[c] by {
                        assert((2 * r) * (w as int) + c < dst_start as int) by(nonlinear_arith)
                            requires 0 <= r < y, 0 <= c < w, dst_start == (2 * y) * w;
                        assert(output@[(2 * r) * (w as int) + c] == before_step[(2 * r) * (w as int) + c]);
                    }
                }
                x += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(2 * ((lw - 1) as int) < w as int) by(nonlinear_arith)
                    requires lw >= 2, lw == w / 2 + w % 2;
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before_tail = output@; }
            let last = ll[src_start + lw - 1];
            output[dst_start + 2 * (lw - 1)] = last;
            if 2 * (lw - 1) + 1 < w {
                output[dst_start + 2 * (lw - 1) + 1] = last;
                #[cfg(verus_keep_ghost)]
                proof! {
                    avg_self(last);
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((y as int) * (lw as int) + (lw as int) == (y as int + 1) * (lw as int)) by(nonlinear_arith);
                assert(2 * ((lw - 1) as int) + 2 >= w as int);
                assert forall |r: int, c: int| 0 <= r < y && 0 <= c < w implies #[trigger] output@[(2 * r) * (w as int) + c]
                    == upsample_1d(ll@.subrange(r * (lw as int), (r + 1) * (lw as int)), w as nat)[c] by {
                    assert((2 * r) * (w as int) + c < dst_start as int) by(nonlinear_arith)
                        requires 0 <= r < y, 0 <= c < w, dst_start == (2 * y) * w;
                    assert(output@[(2 * r) * (w as int) + c] == before_tail[(2 * r) * (w as int) + c]);
                }
                assert forall |c: int| 0 <= c < w as int implies #[trigger] output@[dst_start as int + c]
                    == upsample_1d(ll@.subrange((y as int) * (lw as int), (y as int + 1) * (lw as int)), w as nat)[c] by {
                    if c < 2 * ((lw - 1) as int) {
                        assert(output@[dst_start as int + c] == before_tail[dst_start as int + c]);
                    } else if c == 2 * ((lw - 1) as int) {
                    } else {
                        assert(c == 2 * ((lw - 1) as int) + 1);
                    }
                }
            }
            y += 1;
        }
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires
            w >= 4 && h >= 4,
            lw == w / 2 + w % 2 && lh == h / 2 + h % 2,
            w * h == old(output).len(),
            lw * lh == ll.len(),
            forall |i: int| 0 <= i < ll.len() ==> -1_073_741_824i64 <= #[trigger] ll@[i] <= 1_073_741_824i64,
            forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                #[trigger] old(output)@[(2 * r) * w + c]
                    == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
        ensures
            final(output).len() == old(output).len(),
            forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                #[trigger] final(output)@[(2 * r) * w + c]
                    == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
            forall |r: int, c: int| 0 <= r < h / 2 && 0 <= c < w ==> {
                let a = final(output)@[(2 * r) * w + c];
                let b = if 2 * r + 2 < h { final(output)@[(2 * r + 2) * w + c] } else { a };
                #[trigger] final(output)@[(2 * r + 1) * w + c] == (((a as int) + (b as int)) as i64) >> 1
            },
    ))]
    fn fill_5_3_odd_rows(
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] ll: &[i64],
        output: &mut [i64],
        w: usize,
        h: usize,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] lw: usize,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] lh: usize,
    ) {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(lw >= 2 && lh >= 2) by(nonlinear_arith)
                requires w >= 4, h >= 4, lw == w / 2 + w % 2, lh == h / 2 + h % 2;
        }
        let mut y = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant y <= h / 2,
                w >= 4, h >= 4, lw >= 2, lh >= 2,
                lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                w * h == output.len(),
                lw * lh == ll.len(),
                forall |i: int| 0 <= i < ll.len() ==> -1_073_741_824i64 <= #[trigger] ll@[i] <= 1_073_741_824i64,
                forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                    #[trigger] output@[(2 * r) * w + c]
                        == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
                forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==> {
                    let a = output@[(2 * r) * w + c];
                    let b = if 2 * r + 2 < h { output@[(2 * r + 2) * w + c] } else { a };
                    #[trigger] output@[(2 * r + 1) * w + c] == (((a as int) + (b as int)) as i64) >> 1
                },
            decreases h / 2 - y,
        ))]
        while 2 * y + 1 < h {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((2 * (y as int)) * (w as int) + (w as int) <= output.len()
                    && (2 * (y as int) + 1) * (w as int) + (w as int) <= output.len()
                    && (2 * (y as int) + 2 < h as int ==> (2 * (y as int) + 2) * (w as int) + (w as int) <= output.len())) by(nonlinear_arith)
                    requires 2 * (y as int) + 1 < h as int, w * h == output.len();
            }
            let above_start = (2 * y) * w;
            let odd_start = (2 * y + 1) * w;
            let below_start = if 2 * y + 2 < h {
                (2 * y + 2) * w
            } else {
                above_start
            };
            let mut x = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x <= w, 2 * y + 1 < h,
                    above_start == (2 * y) * w, odd_start == (2 * y + 1) * w,
                    below_start == if 2 * y + 2 < h { (2 * y + 2) * w } else { above_start as int },
                    above_start + w <= output.len(), odd_start + w <= output.len(), below_start + w <= output.len(),
                    w >= 4, h >= 4, lw >= 2, lh >= 2,
                    lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                    w * h == output.len(), lw * lh == ll.len(),
                    forall |i: int| 0 <= i < ll.len() ==> -1_073_741_824i64 <= #[trigger] ll@[i] <= 1_073_741_824i64,
                    forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                        #[trigger] output@[(2 * r) * w + c]
                            == upsample_1d(ll@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
                    forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==> {
                        let a = output@[(2 * r) * w + c];
                        let b = if 2 * r + 2 < h { output@[(2 * r + 2) * w + c] } else { a };
                        #[trigger] output@[(2 * r + 1) * w + c] == (((a as int) + (b as int)) as i64) >> 1
                    },
                    forall |c: int| 0 <= c < x ==> {
                        let a = output@[above_start as int + c];
                        let b = output@[below_start as int + c];
                        #[trigger] output@[odd_start as int + c] == (((a as int) + (b as int)) as i64) >> 1
                    },
                decreases w - x,
            ))]
            while x < w {
                let a = output[above_start + x];
                let b = output[below_start + x];
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(y < lh);
                    let xa = (x as int) / 2;
                    assert(0 <= xa && xa < lw as int);
                    assert(0 <= (y as int) * (lw as int)
                        && (y as int + 1) * (lw as int) == (y as int) * (lw as int) + (lw as int)
                        && (y as int + 1) * (lw as int) <= ll.len()
                        && 0 <= (y as int) * (lw as int) + xa && (y as int) * (lw as int) + xa < ll.len()
                        && (xa + 1 < lw as int ==> 0 <= (y as int) * (lw as int) + xa + 1 && (y as int) * (lw as int) + xa + 1 < ll.len())) by(nonlinear_arith)
                        requires y < lh, 0 <= xa < lw, lw * lh == ll.len();
                    assert(-1_073_741_824i64 <= a <= 1_073_741_824i64 && -1_073_741_824i64 <= b <= 1_073_741_824i64) by {
                        assert(a == output@[(2 * (y as int)) * (w as int) + (x as int)]);
                        let row_a = ll@.subrange((y as int) * (lw as int), (y as int + 1) * (lw as int));
                        let la = row_a[xa];
                        assert(la == ll@[(y as int) * (lw as int) + xa]);
                        let ra = if xa + 1 < lw { row_a[xa + 1] } else { la };
                        if xa + 1 < lw {
                            assert(ra == ll@[(y as int) * (lw as int) + xa + 1]);
                        }
                        avg_bounded(la, ra);
                        if 2 * y + 2 < h {
                            assert(y + 1 < lh);
                            assert(b == output@[(2 * (y as int + 1)) * (w as int) + (x as int)]);
                            assert(0 <= (y as int + 1) * (lw as int)
                                && (y as int + 2) * (lw as int) == (y as int + 1) * (lw as int) + (lw as int)
                                && (y as int + 2) * (lw as int) <= ll.len()
                                && 0 <= (y as int + 1) * (lw as int) + xa && (y as int + 1) * (lw as int) + xa < ll.len()
                                && (xa + 1 < lw as int ==> 0 <= (y as int + 1) * (lw as int) + xa + 1 && (y as int + 1) * (lw as int) + xa + 1 < ll.len())) by(nonlinear_arith)
                                requires y + 1 < lh, 0 <= xa < lw, lw * lh == ll.len();
                            let row_b = ll@.subrange((y as int + 1) * (lw as int), (y as int + 2) * (lw as int));
                            let lb = row_b[xa];
                            assert(lb == ll@[(y as int + 1) * (lw as int) + xa]);
                            let rb = if xa + 1 < lw { row_b[xa + 1] } else { lb };
                            if xa + 1 < lw {
                                assert(rb == ll@[(y as int + 1) * (lw as int) + xa + 1]);
                            }
                            avg_bounded(lb, rb);
                        }
                    }
                }
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost before_odd = output@; }
                output[odd_start + x] = (a + b) >> 1;
                #[cfg(verus_keep_ghost)]
                proof! {
                    let target_idx = odd_start as int + x as int;
                    crate::specs::rowwise_index(2 * (y as int) + 1, x as int, w as int);
                    assert forall |r: int, c: int| 0 <= r < lh && 0 <= c < w implies #[trigger] output@[(2 * r) * (w as int) + c]
                        == upsample_1d(ll@.subrange(r * (lw as int), (r + 1) * (lw as int)), w as nat)[c] by {
                        crate::specs::rowwise_index(2 * r, c, w as int);
                        assert((2 * r) * (w as int) + c != target_idx);
                        assert(output@[(2 * r) * (w as int) + c] == before_odd[(2 * r) * (w as int) + c]);
                    }
                    assert forall |r: int, c: int| 0 <= r < y && 0 <= c < w implies {
                        let ea = output@[(2 * r) * (w as int) + c];
                        let eb = if 2 * r + 2 < h { output@[(2 * r + 2) * (w as int) + c] } else { ea };
                        #[trigger] output@[(2 * r + 1) * (w as int) + c] == (((ea as int) + (eb as int)) as i64) >> 1
                    } by {
                        crate::specs::rowwise_index(2 * r, c, w as int);
                        crate::specs::rowwise_index(2 * r + 1, c, w as int);
                        if 2 * r + 2 < h {
                            crate::specs::rowwise_index(2 * r + 2, c, w as int);
                        }
                        assert((2 * r + 1) * (w as int) + c != target_idx);
                        assert(output@[(2 * r + 1) * (w as int) + c] == before_odd[(2 * r + 1) * (w as int) + c]);
                    }
                    assert forall |c: int| 0 <= c <= x as int implies {
                        let ea = output@[above_start as int + c];
                        let eb = output@[below_start as int + c];
                        #[trigger] output@[odd_start as int + c] == (((ea as int) + (eb as int)) as i64) >> 1
                    } by {
                        crate::specs::rowwise_index(2 * (y as int), c, w as int);
                        assert(above_start as int + c != target_idx);
                        assert(output@[above_start as int + c] == before_odd[above_start as int + c]);
                        if 2 * y + 2 < h {
                            crate::specs::rowwise_index(2 * (y as int) + 2, c, w as int);
                            assert(below_start as int + c != target_idx);
                            assert(output@[below_start as int + c] == before_odd[below_start as int + c]);
                        }
                        if c < x as int {
                            assert(output@[odd_start as int + c] == before_odd[odd_start as int + c]);
                        }
                    }
                }
                x += 1;
            }
            y += 1;
        }
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires
            crate::specs::part1_validate_level(wavelet_level_view(level)) == Ok(()),
            crate::specs::part1_transform_area(level.output_width, level.output_height) == Ok(output_len),
            crate::specs::part1_wavelet_sample_count(level.output_width, level.output_height, output_len),
            crate::specs::part1_quantization_budget(output_len as nat, maximum) == Ok(()),
            level.output_width >= 4 && level.output_height >= 4,
            level.low_pass_first_x && level.low_pass_first_y,
            forall |i: int| 0 <= i < level.hl.samples.len() ==> #[trigger] level.hl.samples@[i] == 0i64,
            forall |i: int| 0 <= i < level.lh.samples.len() ==> #[trigger] level.lh.samples@[i] == 0i64,
            forall |i: int| 0 <= i < level.hh.samples.len() ==> #[trigger] level.hh.samples@[i] == 0i64,
        ensures
            match result {
                Some(output) => Ok((level.output_width, level.output_height, 0u8, output@))
                    == crate::specs::part1_inverse_level(wavelet_level_view(level), false, maximum),
                None => true,
            },
    ))]
    pub(super) fn try_5_3_zero_detail(
        level: WaveletLevel<'_>,
        output_len: usize,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] maximum: u64,
    ) -> Option<Vec<i64>> {
        if !slice_within_bound(level.ll.samples) {
            return None;
        }
        let Ok(mut output) = crate::allocation::zero_i64_values(output_len) else {
            return None;
        };
        let w = level.output_width as usize;
        let h = level.output_height as usize;
        let lw = level.ll.width as usize;
        let lh = level.ll.height as usize;
        fill_5_3_even_rows(level.ll.samples, output.as_mut_slice(), w, h, lw, lh);
        fill_5_3_odd_rows(level.ll.samples, output.as_mut_slice(), w, h, lw, lh);
        #[cfg(verus_keep_ghost)]
        proof! {
            prove_5_3_zero_detail_level(wavelet_level_view(level), output@, output_len, maximum);
        }
        Some(output)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_level_result(wavelet_level_view(level),irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        kernel.is_none() && reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_level(
        wavelet_level_view(level), irreversible, crate::limits::resource_decoded_bytes_limit(limits),
    ),
    arbitrary_kernel_supplied(kernel) && reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part2_atk_inverse_level(
        wavelet_level_view(level), irreversible, arbitrary_kernel_option(kernel).unwrap(), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
fn inverse_level(
    level: WaveletLevel<'_>,
    limits: &ResourceLimits,
    irreversible: bool,
    kernel: Option<&ArbitraryKernel>,
) -> Result<ReconstructedPlane, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_level_normal(wavelet_level_view(level),irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits));}
    validate_level(level)?;
    let output_len = checked_area(level.output_width, level.output_height)?;
    if !crate::refinement::wavelet_sample_count(level.output_width, level.output_height, output_len)
    {
        return Err(invalid_transform());
    }
    validate_output_size(output_len, limits)?;
    if kernel.is_none()
        && level.output_width >= 4
        && level.output_height >= 4
        && zero_level::slice_is_all_zero(level.hl.samples)
        && zero_level::slice_is_all_zero(level.lh.samples)
        && zero_level::slice_is_all_zero(level.hh.samples)
    {
        if zero_level::slice_is_all_zero(level.ll.samples) {
            if let Some(samples) = zero_level::try_all_zero(
                level,
                output_len,
                irreversible,
                limits.maximum_decoded_bytes(),
            ) {
                return Ok(ReconstructedPlane {
                    width: level.output_width,
                    height: level.output_height,
                    fraction_bits: if irreversible { FIXED_BITS } else { 0 },
                    samples,
                });
            }
        } else if !irreversible && level.low_pass_first_x && level.low_pass_first_y {
            #[allow(
                clippy::collapsible_if,
                reason = "Avoid let-chains for MSRV 1.88 and Verus compatibility."
            )]
            if let Some(samples) =
                zero_level::try_5_3_zero_detail(level, output_len, limits.maximum_decoded_bytes())
            {
                return Ok(ReconstructedPlane {
                    width: level.output_width,
                    height: level.output_height,
                    fraction_bits: 0,
                    samples,
                });
            }
        }
    }
    let low_height = level.ll.height;
    let high_height = level.lh.height;
    let low_capacity = checked_area(level.output_width, low_height)?;
    let low_result = inverse_rows(
        level.ll,
        level.hl,
        level.low_pass_first_x,
        irreversible,
        kernel,
        low_capacity,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=low_result{crate::specs::part2_wavelet_level_low_error(wavelet_level_view(level),irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),output_len,low_capacity,error);}}
    let low_rows = low_result?;
    let high_capacity = checked_area(level.output_width, high_height)?;
    let high_result = inverse_rows(
        level.lh,
        level.hh,
        level.low_pass_first_x,
        irreversible,
        kernel,
        high_capacity,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=high_result{crate::specs::part2_wavelet_level_high_error(wavelet_level_view(level),irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),output_len,low_rows@,low_capacity,high_capacity,error);}}
    let high_rows = high_result?;
    let columns = inverse_columns(
        WaveletBand {
            width: level.output_width,
            height: low_height,
            samples: &low_rows,
        },
        WaveletBand {
            width: level.output_width,
            height: high_height,
            samples: &high_rows,
        },
        level.output_height,
        level.low_pass_first_y,
        irreversible,
        kernel,
        output_len,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=columns{crate::specs::part2_wavelet_level_columns_error(wavelet_level_view(level),irreversible,arbitrary_kernel_option(kernel),crate::limits::resource_decoded_bytes_limit(limits),output_len,low_rows@,high_rows@,low_capacity,high_capacity,error);}}
    let output = columns?;
    Ok(ReconstructedPlane {
        width: level.output_width,
        height: level.output_height,
        fraction_bits: if irreversible { FIXED_BITS } else { 0 },
        samples: output,
    })
}
