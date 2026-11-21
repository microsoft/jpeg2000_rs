use super::arithmetic::{arithmetic_overflow, invalid_transform, validate_quantization_size};
use super::{FIXED_BITS, FIXED_ONE, QuantizationStep, ReconstructedPlane, SignedMagnitude};
#[cfg(verus_keep_ghost)]
use super::{quantized_coefficients_view, reconstruction_outcome};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_integer_quantization_result(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,
        crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_integer_quantization(
        coefficients@, step.exponent, step.mantissa, dynamic_range, reversible, roi_shift,
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub fn inverse_quantize(
    coefficients: &[i64],
    step: QuantizationStep,
    dynamic_range: u8,
    reversible: bool,
    roi_shift: u8,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_quantize_values(
        coefficients,
        step,
        dynamic_range,
        reversible,
        roi_shift,
        limits.maximum_decoded_bytes(),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_integer_quantization_result(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_integer_quantization(
        coefficients@, step.exponent, step.mantissa, dynamic_range, reversible, roi_shift, maximum_decoded_bytes,
    ),
))]
fn inverse_quantize_values(
    coefficients: &[i64],
    step: QuantizationStep,
    dynamic_range: u8,
    reversible: bool,
    roi_shift: u8,
    maximum_decoded_bytes: u64,
) -> Result<ReconstructedPlane, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_integer_quantization_normal(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes);}
    let count = coefficients.len();
    let allocated = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_quantization_capacity_observed(crate::specs::Part2QuantizationOwner::Wide,count as nat,unit);
        if let Err(error)=allocated{crate::specs::part2_integer_quantization_refused(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,error);}
    }
    let mut wide = allocated?;
    let mut index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= coefficients.len(),
            wide.len() == index,
            forall |i: int| 0 <= i < index ==> coefficients[i] != i64::MIN,
            forall |i: int| 0 <= i < index ==>
                quantized_coefficients_view(wide@)[i] == crate::specs::part1_integer_coefficients(coefficients@)[i],
            crate::specs::part2_integer_quantization_result(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,
                crate::specs::part1_inverse_integer_quantization(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes)),
            decreases coefficients.len() - index,
        )
    )]
    while index < coefficients.len() {
        let value = coefficients[index];
        if value == i64::MIN {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(exists |i: int| 0 <= i < coefficients.len() && coefficients[i] == i64::MIN);
            }
            return Err(arithmetic_overflow());
        }
        let magnitude = checked_magnitude(value)? as u64;
        wide.push(SignedMagnitude {
            magnitude: crate::magnitude::magnitude_from_u64(magnitude),
            negative: value < 0,
        });
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(quantized_coefficients_view(wide@) =~= crate::specs::part1_integer_coefficients(coefficients@));
    }
    let quantized = inverse_quantize_plane(
        &wide,
        step,
        dynamic_range,
        reversible,
        roi_shift,
        maximum_decoded_bytes,
    );
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_integer_quantization_child_observed(coefficients@,step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,reconstruction_outcome(quantized));}
    quantized
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_quantization_plane_result(quantized_coefficients_view(coefficients@),step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,
        crate::limits::resource_decoded_bytes_limit(limits),reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_quantization(
        quantized_coefficients_view(coefficients@), step.exponent, step.mantissa,
        dynamic_range, reversible, roi_shift, crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(crate) fn inverse_quantize_magnitudes(
    coefficients: &[SignedMagnitude],
    step: QuantizationStep,
    dynamic_range: u8,
    reversible: bool,
    roi_shift: u8,
    limits: &ResourceLimits,
) -> Result<ReconstructedPlane, DecodeError> {
    inverse_quantize_plane(
        coefficients,
        step,
        dynamic_range,
        reversible,
        roi_shift,
        limits.maximum_decoded_bytes(),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_quantization_plane_result(quantized_coefficients_view(coefficients@),step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,reconstruction_outcome(result)),
        reconstruction_outcome(result)!=Err(DecodeError::AllocationFailed) ==> reconstruction_outcome(result) == crate::specs::part1_inverse_quantization(
        quantized_coefficients_view(coefficients@), step.exponent, step.mantissa,
        dynamic_range, reversible, roi_shift, maximum_decoded_bytes,
    ),
))]
pub(super) fn inverse_quantize_plane(
    coefficients: &[SignedMagnitude],
    step: QuantizationStep,
    dynamic_range: u8,
    reversible: bool,
    roi_shift: u8,
    maximum_decoded_bytes: u64,
) -> Result<ReconstructedPlane, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_quantization_plane_normal(quantized_coefficients_view(coefficients@),step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes);}
    if dynamic_range == 0 || dynamic_range > 38 || step.mantissa > 0x07ff {
        return Err(invalid_transform());
    }
    if step.exponent > 31 {
        return Err(invalid_transform());
    }
    validate_quantization_size(coefficients.len(), maximum_decoded_bytes)?;
    let step_size = if reversible {
        1
    } else {
        quantization_step_q16(step, dynamic_range)?
    };
    let count = coefficients.len();
    let allocated = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_quantization_capacity_observed(crate::specs::Part2QuantizationOwner::Samples,count as nat,unit);
        if let Err(error)=allocated{crate::specs::part2_quantization_plane_refused(quantized_coefficients_view(coefficients@),step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,error);}
    }
    let mut samples = allocated?;
    let mut index = 0;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= coefficients.len(),
            samples.len() == index,
            0 < dynamic_range <= 38,
            step.mantissa <= 2047,
            step.exponent <= 31,
            crate::specs::part1_quantization_budget(coefficients.len() as nat, maximum_decoded_bytes) == Ok(()),
            if reversible { step_size == 1 } else {
                crate::specs::part1_quantization_step(step.exponent, step.mantissa, dynamic_range) == Ok(step_size)
            },
            crate::specs::part1_quantized_prefix(
                quantized_coefficients_view(coefficients@), roi_shift, step_size, reversible, index as nat,
            ) == Ok(samples@),
            crate::specs::part2_quantization_plane_result(quantized_coefficients_view(coefficients@),step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes,
                crate::specs::part1_inverse_quantization(quantized_coefficients_view(coefficients@),step.exponent,step.mantissa,dynamic_range,reversible,roi_shift,maximum_decoded_bytes)),
            decreases coefficients.len() - index,
        )
    )]
    while index < coefficients.len() {
        let sample = match quantize_magnitude_sample(
            coefficients[index],
            roi_shift,
            step_size,
            reversible,
        ) {
            Ok(sample) => sample,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_quantization_error_persists(
                        quantized_coefficients_view(coefficients@), roi_shift, step_size, reversible,
                        index as nat + 1, coefficients.len() as nat, error,
                    );
                }
                return Err(error);
            }
        };
        samples.push(sample);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    if coefficients.len() > u32::MAX as usize {
        return Err(arithmetic_overflow());
    }
    Ok(ReconstructedPlane {
        width: coefficients.len() as u32,
        height: 1,
        fraction_bits: if reversible { 0 } else { FIXED_BITS },
        samples,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_quantized_sample(
        (crate::magnitude::magnitude_limbs(value.magnitude), value.negative), shift, step_size, reversible,
    ),
))]
fn quantize_magnitude_sample(
    value: SignedMagnitude,
    shift: u8,
    step_size: i64,
    reversible: bool,
) -> Result<i64, DecodeError> {
    let coefficient = undo_maxshift_magnitude(value, shift)?;
    if reversible || coefficient == 0 {
        return Ok(crate::refinement::reversible_inverse_quantize(coefficient));
    }
    let magnitude = checked_magnitude(coefficient)?;
    if magnitude < 0 || step_size < 0 {
        return Err(arithmetic_overflow());
    }
    if magnitude <= i32::MAX as i64 && step_size <= i32::MAX as i64 {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((2*(magnitude as int)+1)*(step_size as int)<=i64::MAX) by(nonlinear_arith)
                requires 0<=magnitude<=i32::MAX,0<=step_size<=i32::MAX;
        }
        return Ok(quantize_bounded_magnitude(
            magnitude as u64,
            coefficient < 0,
            step_size,
            false,
        ));
    }
    let centered = crate::refinement::irreversible_centered(magnitude);
    let product = centered
        .checked_mul(step_size as i128)
        .ok_or_else(arithmetic_overflow)?;
    if product < 0 {
        return Err(arithmetic_overflow());
    }
    let scaled = crate::refinement::irreversible_scale(product);
    if scaled > i64::MAX as i128 {
        return Err(arithmetic_overflow());
    }
    let scaled = scaled as i64;
    if coefficient < 0 {
        0_i64.checked_sub(scaled).ok_or_else(arithmetic_overflow)
    } else {
        Ok(scaled)
    }
}

pub fn undo_maxshift(value: i64, shift: u8) -> Result<i64, DecodeError> {
    let magnitude = u64::try_from(checked_magnitude(value)?).map_err(|_| arithmetic_overflow())?;
    let restored = crate::refinement::maxshift_restore(magnitude, shift);
    let restored = i64::try_from(restored).map_err(|_| arithmetic_overflow())?;
    if value < 0 {
        0_i64.checked_sub(restored).ok_or_else(arithmetic_overflow)
    } else {
        Ok(restored)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_roi_coefficient(
        crate::magnitude::magnitude_limbs(value.magnitude), value.negative, shift,
    ),
))]
pub(crate) fn undo_maxshift_magnitude(
    value: SignedMagnitude,
    shift: u8,
) -> Result<i64, DecodeError> {
    if value.magnitude.is_zero() {
        return Ok(0);
    }
    let threshold = crate::magnitude::magnitude_single_bit(shift as u16)?;
    let restored = if shift == 0 || value.magnitude.less_than(threshold) {
        value.magnitude
    } else {
        value.magnitude.shift_right(shift as u16)
    };
    let magnitude = restored.to_u64().ok_or_else(arithmetic_overflow)?;
    if magnitude > i64::MAX as u64 {
        return Err(arithmetic_overflow());
    }
    let magnitude = magnitude as i64;
    if value.negative {
        0_i64.checked_sub(magnitude).ok_or_else(arithmetic_overflow)
    } else {
        Ok(magnitude)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == if value == i64::MIN {
        Err(crate::specs::part1_transform_error(true))
    } else {
        Ok((if value < 0 { -(value as int) } else { value as int }) as i64)
    },
))]
fn checked_magnitude(value: i64) -> Result<i64, DecodeError> {
    if value == i64::MIN {
        return Err(arithmetic_overflow());
    }
    if value < 0 { Ok(-value) } else { Ok(value) }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires magnitude<=i64::MAX,step_size>=0,
        !reversible && magnitude>0 && step_size>0 ==> (2*(magnitude as int)+1)*(step_size as int)<=i64::MAX,
    ensures crate::specs::part1_quantized_sample(
        (Seq::new(6,|i:int|if i==0{magnitude}else{0u64}),negative),0,step_size,reversible)==Ok(result),
        crate::specs::part1_dequantized_sample(
            (if negative{-(magnitude as int)}else{magnitude as int}) as i64,step_size,reversible)==Ok(result),
))]
#[inline]
pub(crate) fn quantize_bounded_magnitude(
    magnitude: u64,
    negative: bool,
    step_size: i64,
    reversible: bool,
) -> i64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(magnitude>>0u8==magnitude) by(bit_vector);
        crate::specs::part2_fused_sparse_roi(magnitude,negative,0);
    }
    let magnitude = magnitude as i64;
    let value = if reversible || magnitude == 0 {
        magnitude
    } else if step_size == 0 {
        0
    } else {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(0<=2*(magnitude as int)+1<=i64::MAX) by(nonlinear_arith)
                requires magnitude>0,step_size>0,(2*(magnitude as int)+1)*(step_size as int)<=i64::MAX;
            assert(0<=(2*(magnitude as int)+1)*(step_size as int)<=i64::MAX) by(nonlinear_arith)
                requires magnitude>0,step_size>0,(2*(magnitude as int)+1)*(step_size as int)<=i64::MAX;
        }
        let centered = crate::refinement::irreversible_centered(magnitude) as i64;
        crate::refinement::irreversible_scale((centered * step_size) as i128) as i64
    };
    if negative { -value } else { value }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_quantization_step(step.exponent, step.mantissa, dynamic_range),
))]
pub(crate) fn quantization_step_q16(
    step: QuantizationStep,
    dynamic_range: u8,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { assert(FIXED_ONE == 65536) by(compute); }
    let base_value = 2048_u32
        .checked_add(step.mantissa as u32)
        .ok_or_else(arithmetic_overflow)?;
    let base = (base_value as i64)
        .checked_mul(FIXED_ONE)
        .ok_or_else(arithmetic_overflow)?
        / 2048;
    if dynamic_range >= step.exponent {
        let shift = dynamic_range - step.exponent;
        if shift > 38 {
            return Err(invalid_transform());
        }

        base.checked_mul(1_i64 << (shift as u32))
            .ok_or_else(arithmetic_overflow)
    } else {
        let shift = step.exponent - dynamic_range;
        if shift > 62 {
            return Err(invalid_transform());
        }
        let divisor = 1_i64 << (shift as u32);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(divisor > 0) by(bit_vector)
                requires shift <= 62, divisor == 1i64 << (shift as u32);
        }
        if divisor == 0 {
            return Err(arithmetic_overflow());
        }
        Ok(base / divisor)
    }
}
