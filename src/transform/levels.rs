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
                assert(prev * lw + lw <= low.2.len() && prev * hw + hw <= high.2.len()) by(nonlinear_arith)
                    requires prev < low.1, low.2.len() == lw * (low.1 as nat), high.2.len() == hw * (low.1 as nat);
                let lr = low.2.subrange((prev * lw) as int, (prev * lw + lw) as int);
                let hr = high.2.subrange((prev * hw) as int, (prev * hw + hw) as int);
                zero_1d_wavelet(lr, hr, first, irreversible);
                assert(zeros(prev * w) + zeros(w) =~= zeros(y * w)) by {
                    assert(prev * w + w == y * w) by(nonlinear_arith) requires y == prev + 1;
                }
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
                let lc = Seq::new(low.1 as nat, |row: int| low.2[row * (low.0 as int) + prev as int]);
                let hc = Seq::new(high.1 as nat, |row: int| high.2[row * (high.0 as int) + prev as int]);
                assert forall |r: int| 0 <= r < lc.len() implies #[trigger] lc[r] == 0i64 by {
                    assert(0 <= r * (low.0 as int) + (prev as int) && r * (low.0 as int) + (prev as int) < low.2.len()) by(nonlinear_arith)
                        requires 0 <= r < low.1, prev < low.0, low.2.len() == (low.0 as int) * (low.1 as int);
                }
                assert forall |r: int| 0 <= r < hc.len() implies #[trigger] hc[r] == 0i64 by {
                    assert(0 <= r * (high.0 as int) + (prev as int) && r * (high.0 as int) + (prev as int) < high.2.len()) by(nonlinear_arith)
                        requires 0 <= r < high.1, prev < high.0, high.2.len() == (high.0 as int) * (high.1 as int);
                }
                zero_1d_wavelet(lc, hc, first, irreversible);
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
                output_width >= 4,
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
                assert(prev * lw + lw <= ll.2.len() && prev * hw + hw <= hl.2.len()) by(nonlinear_arith)
                    requires prev < ll.1, ll.2.len() == lw * (ll.1 as nat), hl.2.len() == hw * (ll.1 as nat);
                let lr = ll.2.subrange((prev * lw) as int, (prev * lw + lw) as int);
                let hr = hl.2.subrange((prev * hw) as int, (prev * hw + hw) as int);
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
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires
            crate::specs::part1_validate_level(wavelet_level_view(level)) == Ok(()),
            level.output_width as nat * level.output_height as nat == output_len as nat,
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
            let lv = wavelet_level_view(level);
            assert(lv.0.0 as nat * lv.0.1 as nat == lv.0.2.len());
            assert((lv.4 as nat) * (lv.0.1 as nat) <= output_len as nat) by(nonlinear_arith)
                requires lv.0.1 <= lv.5, (lv.4 as nat) * (lv.5 as nat) == output_len as nat;
            assert((lv.4 as nat) * (lv.2.1 as nat) <= output_len as nat) by(nonlinear_arith)
                requires lv.2.1 <= lv.5, (lv.4 as nat) * (lv.5 as nat) == output_len as nat;
            zero_horizontal_prefix(lv.0, lv.1, lv.6, irreversible, lv.0.1 as nat);
            zero_horizontal_prefix(lv.2, lv.3, lv.6, irreversible, lv.2.1 as nat);
            let low_band = (lv.4, lv.0.1, zeros((lv.0.1 as nat) * (lv.4 as nat)));
            let high_band = (lv.4, lv.2.1, zeros((lv.2.1 as nat) * (lv.4 as nat)));
            assert((lv.0.1 as nat) * (lv.4 as nat) == (lv.4 as nat) * (lv.0.1 as nat)) by(nonlinear_arith);
            assert((lv.2.1 as nat) * (lv.4 as nat) == (lv.4 as nat) * (lv.2.1 as nat)) by(nonlinear_arith);
            zero_vertical_prefix(low_band, high_band, lv.5, lv.7, irreversible, output_len, lv.4 as nat);
            assert(output@ =~= zeros(output_len as nat));
        }
        Some(output)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires
            crate::specs::part1_validate_level(wavelet_level_view(level)) == Ok(()),
            level.output_width as nat * level.output_height as nat == output_len as nat,
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
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(lw >= 2 && lh >= 2) by(nonlinear_arith)
                requires w >= 4, h >= 4, lw == w / 2 + w % 2, lh == h / 2 + h % 2;
            assert(w * h == output_len && lw * lh == level.ll.samples.len());
            assert((2 * (lh - 1) + 1) * w <= output_len) by(nonlinear_arith)
                requires h >= 4, lh == h / 2 + h % 2, w * h == output_len;
        }
        let mut y = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant y <= lh,
                w == level.output_width, h == level.output_height,
                lw == level.ll.width, lh == level.ll.height,
                w >= 4, h >= 4, lw >= 2, lh >= 2,
                lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                w * h == output_len, output.len() == output_len,
                lw * lh == level.ll.samples.len(),
                forall |i: int| 0 <= i < level.ll.samples.len() ==> -1_073_741_824i64 <= #[trigger] level.ll.samples@[i] <= 1_073_741_824i64,
                forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==>
                    #[trigger] output@[(2 * r) * w + c]
                        == upsample_1d(level.ll.samples@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
            decreases lh - y,
        ))]
        while y < lh {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(y * lw + lw <= level.ll.samples.len() && (2 * y + 1) * w <= output_len) by(nonlinear_arith)
                    requires y < lh, lw * lh == level.ll.samples.len(), w * h == output_len, lh == h / 2 + h % 2;
            }
            let src_start = y * lw;
            let dst_start = (2 * y) * w;
            let mut x = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x < lw, y < lh,
                    src_start == y * lw, dst_start == (2 * y) * w,
                    src_start + lw <= level.ll.samples.len(), dst_start + w <= output_len,
                    w == level.output_width, h == level.output_height,
                    lw == level.ll.width, lh == level.ll.height,
                    lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                    w * h == output_len, output.len() == output_len,
                    forall |i: int| 0 <= i < level.ll.samples.len() ==> -1_073_741_824i64 <= #[trigger] level.ll.samples@[i] <= 1_073_741_824i64,
                    forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==>
                        #[trigger] output@[(2 * r) * w + c]
                            == upsample_1d(level.ll.samples@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
                    forall |c: int| 0 <= c < 2 * x ==>
                        #[trigger] output@[dst_start as int + c]
                            == upsample_1d(level.ll.samples@.subrange(src_start as int, (src_start + lw) as int), w as nat)[c],
                decreases lw - 1 - x,
            ))]
            while x + 1 < lw {
                let a = level.ll.samples[src_start + x];
                let b = level.ll.samples[src_start + x + 1];
                output[dst_start + 2 * x] = a;
                output[dst_start + 2 * x + 1] = (a + b) >> 1;
                x += 1;
            }
            let last = level.ll.samples[src_start + lw - 1];
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
            }
            y += 1;
        }
        let mut y = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant y <= h / 2,
                w == level.output_width, h == level.output_height,
                lw == level.ll.width, lh == level.ll.height,
                w >= 4, h >= 4, lw >= 2, lh >= 2,
                lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                w * h == output_len, output.len() == output_len,
                lw * lh == level.ll.samples.len(),
                forall |i: int| 0 <= i < level.ll.samples.len() ==> -1_073_741_824i64 <= #[trigger] level.ll.samples@[i] <= 1_073_741_824i64,
                forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                    #[trigger] output@[(2 * r) * w + c]
                        == upsample_1d(level.ll.samples@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
                forall |r: int, c: int| 0 <= r < y && 0 <= c < w ==> {
                    let a = output@[(2 * r) * w + c];
                    let b = if 2 * r + 2 < h { output@[(2 * r + 2) * w + c] } else { a };
                    #[trigger] output@[(2 * r + 1) * w + c] == (((a as int) + (b as int)) as i64) >> 1
                },
            decreases h / 2 - y,
        ))]
        while 2 * y + 1 < h {
            let above_start = (2 * y) * w;
            let odd_start = (2 * y + 1) * w;
            let below_start = if 2 * y + 2 < h {
                (2 * y + 2) * w
            } else {
                above_start
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(above_start + w <= output_len && odd_start + w <= output_len && below_start + w <= output_len) by(nonlinear_arith)
                    requires 2 * y + 1 < h, w * h == output_len,
                        above_start == (2 * y) * w, odd_start == (2 * y + 1) * w,
                        below_start == if 2 * y + 2 < h { (2 * y + 2) * w } else { above_start as int };
            }
            let mut x = 0_usize;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x <= w, 2 * y + 1 < h,
                    above_start == (2 * y) * w, odd_start == (2 * y + 1) * w,
                    below_start == if 2 * y + 2 < h { (2 * y + 2) * w } else { above_start as int },
                    above_start + w <= output_len, odd_start + w <= output_len, below_start + w <= output_len,
                    w == level.output_width, h == level.output_height,
                    lw == level.ll.width, lh == level.ll.height,
                    lw == w / 2 + w % 2, lh == h / 2 + h % 2,
                    w * h == output_len, output.len() == output_len,
                    forall |i: int| 0 <= i < level.ll.samples.len() ==> -1_073_741_824i64 <= #[trigger] level.ll.samples@[i] <= 1_073_741_824i64,
                    forall |r: int, c: int| 0 <= r < lh && 0 <= c < w ==>
                        #[trigger] output@[(2 * r) * w + c]
                            == upsample_1d(level.ll.samples@.subrange(r * lw, (r + 1) * lw), w as nat)[c],
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
                    assert(-1_073_741_824i64 <= a <= 1_073_741_824i64 && -1_073_741_824i64 <= b <= 1_073_741_824i64) by {
                        let row_a = level.ll.samples@.subrange((y as int) * (lw as int), (y as int + 1) * (lw as int));
                        let xa = (x as int) / 2;
                        let la = row_a[xa];
                        let ra = if xa + 1 < lw { row_a[xa + 1] } else { la };
                        avg_bounded(la, ra);
                        if 2 * y + 2 < h {
                            let row_b = level.ll.samples@.subrange((y as int + 1) * (lw as int), (y as int + 2) * (lw as int));
                            let lb = row_b[xa];
                            let rb = if xa + 1 < lw { row_b[xa + 1] } else { lb };
                            avg_bounded(lb, rb);
                        }
                    }
                }
                output[odd_start + x] = (a + b) >> 1;
                x += 1;
            }
            y += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let lv = wavelet_level_view(level);
            assert((lv.4 as nat) * (lv.0.1 as nat) <= output_len as nat) by(nonlinear_arith)
                requires lv.0.1 <= lv.5, (lv.4 as nat) * (lv.5 as nat) == output_len as nat;
            assert((lv.4 as nat) * (lv.2.1 as nat) <= output_len as nat) by(nonlinear_arith)
                requires lv.2.1 <= lv.5, (lv.4 as nat) * (lv.5 as nat) == output_len as nat;
            zero_high_5_3_horizontal_prefix(lv.0, lv.1, lv.4, lv.0.1 as nat);
            zero_horizontal_prefix(lv.2, lv.3, true, false, lv.2.1 as nat);
            let low_rows = crate::specs::part1_horizontal_prefix(lv.0, lv.1, true, false, lv.0.1 as nat).get_Ok_0();
            let high_rows = zeros((lv.2.1 as nat) * (lv.4 as nat));
            assert((lv.2.1 as nat) * (lv.4 as nat) == (lv.4 as nat) * (lv.2.1 as nat)) by(nonlinear_arith);
            let low_band = (lv.4, lv.0.1, low_rows);
            let high_band = (lv.4, lv.2.1, high_rows);
            assert(crate::specs::rowwise_bounded(low_rows)) by {
                assert forall |i: int| 0 <= i < low_rows.len() implies -1_073_741_824 <= #[trigger] low_rows[i] <= 1_073_741_824 by {
                    crate::specs::rowwise_coordinates(i, w as int, lh as int);
                    let r = i / (w as int);
                    let c = i % (w as int);
                    let row_s = level.ll.samples@.subrange(r * (lw as int), (r + 1) * (lw as int));
                    let xa = c / 2;
                    let la = row_s[xa];
                    let ra = if xa + 1 < lw { row_s[xa + 1] } else { la };
                    avg_bounded(la, ra);
                }
            }
            assert(crate::specs::rowwise_bounded(high_rows));
            assert(crate::specs::rowwise_eligible(low_band, high_band, lv.5, true, output_len)) by {
                assert((lv.4 as int) * (lv.0.1 as int) + (lv.4 as int) * (lv.2.1 as int) == output_len as int) by(nonlinear_arith)
                    requires (lv.4 as int) * (lv.5 as int) == output_len as int,
                        (lv.0.1 as int) + (lv.2.1 as int) == lv.5 as int;
            }
            crate::specs::rowwise_equivalent(low_band, high_band, lv.5, true, output_len);
            let inter = crate::specs::rowwise_interleaved(low_band, high_band, lv.5, true);
            let upd = crate::specs::rowwise_stage(inter, w as nat, h as nat, true, false);
            assert(upd =~= inter) by {
                assert forall |i: int| 0 <= i < inter.len() implies upd[i] == inter[i] by {
                    crate::specs::rowwise_coordinates(i, w as int, h as int);
                    let r = i / (w as int);
                    let c = i % (w as int);
                    if r % 2 == 0 {
                        let left_r = if r == 0 { 1int } else { r - 1 };
                        let right_r = if r + 1 < h { r + 1 } else { r - 1 };
                        crate::specs::rowwise_index(left_r, c, w as int);
                        crate::specs::rowwise_index(right_r, c, w as int);
                        assert(inter[left_r * (w as int) + c] == 0i64 && inter[right_r * (w as int) + c] == 0i64);
                        assert((2i64 >> 2i64) == 0i64) by(bit_vector);
                    }
                }
            }
            let final_spec = crate::specs::rowwise_output(low_band, high_band, lv.5, true);
            assert(output@ =~= final_spec) by {
                assert forall |i: int| 0 <= i < output_len as int implies output@[i] == final_spec[i] by {
                    crate::specs::rowwise_coordinates(i, w as int, h as int);
                    let r = i / (w as int);
                    let c = i % (w as int);
                    if r % 2 == 0 {
                        let hr = r / 2;
                        assert(2 * hr == r);
                        crate::specs::rowwise_index(hr, c, w as int);
                    } else {
                        let hr = r / 2;
                        assert(2 * hr + 1 == r);
                        let left_r = r - 1;
                        let right_r = if r + 1 < h { r + 1 } else { r - 1 };
                        crate::specs::rowwise_index(left_r, c, w as int);
                        crate::specs::rowwise_index(right_r, c, w as int);
                        assert(inter[i] == 0i64);
                        assert(inter[left_r * (w as int) + c] == output@[left_r * (w as int) + c]) by {
                            crate::specs::rowwise_index(left_r / 2, c, w as int);
                        }
                        assert(inter[right_r * (w as int) + c] == output@[right_r * (w as int) + c]) by {
                            crate::specs::rowwise_index(right_r / 2, c, w as int);
                        }
                    }
                }
            }
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
