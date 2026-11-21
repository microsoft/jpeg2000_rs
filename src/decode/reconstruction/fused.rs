#[cfg(verus_keep_ghost)]
use super::working_subband_view;
use super::{
    CodeBlockPlane, DecodeError, ResourceLimits, SubbandGeometry, WorkingSubband,
    arithmetic_overflow, collect_prepare_coefficients, invalid_decode, inverse_quantize_magnitudes,
    write_quantized_block,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
struct Quantizer {
    step: i64,
    roi_shift: u8,
    reversible: bool,
}

fn preflight(
    plane: &CodeBlockPlane,
    destination: &WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<Option<Quantizer>, DecodeError> {
    let width = usize::from(plane.width());
    let height = usize::from(plane.height());
    let Some(count) = width.checked_mul(height) else {
        return Ok(None);
    };
    let budget_ok = match (count as u64).checked_mul(8) {
        Some(bytes) => bytes <= limits.maximum_decoded_bytes(),
        None => false,
    };
    if count == 0
        || plane.coefficients().len() != count
        || destination.width != geometry.width
        || destination.height != geometry.height
        || geometry.dynamic_range == 0
        || geometry.dynamic_range > 38
        || geometry.quantization_step.exponent > 31
        || geometry.quantization_step.mantissa > 2047
        || !budget_ok
    {
        return Ok(None);
    }
    let Some(area) = (destination.width as usize).checked_mul(destination.height as usize) else {
        return Ok(None);
    };
    if destination.samples.len() != area || destination.visited.len() != area {
        return Ok(None);
    }
    let step = if reversible {
        1
    } else {
        let Ok(value) = crate::transform::quantization_step_q16(
            geometry.quantization_step,
            geometry.dynamic_range,
        ) else {
            return Ok(None);
        };
        value
    };
    let maximum = if reversible || step == 0 {
        i64::MAX as u64
    } else {
        ((i64::MAX / step) as u64 - 1) / 2
    };
    let mut row = 0;
    while row < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source = &plane.coefficients()[row * width..(row + 1) * width];
        let visited = &destination.visited[start..start + width];
        let mut column = 0;
        while column < width {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(column)?;
            let Some(magnitude) = source[column].narrow_reconstructed_magnitude() else {
                return Ok(None);
            };
            // Maxshift is discontinuous at its threshold: bound each restored value.
            let restored = crate::refinement::maxshift_restore(magnitude, geometry.roi_shift);
            if restored > maximum || visited[column] {
                return Ok(None);
            }
            column += 1;
        }
        row += 1;
    }
    Ok(Some(Quantizer {
        step,
        roi_shift: geometry.roi_shift,
        reversible,
    }))
}

fn write(
    plane: &CodeBlockPlane,
    destination: &mut WorkingSubband,
    x: u32,
    y: u32,
    quantizer: Quantizer,
) -> Result<(), DecodeError> {
    let width = usize::from(plane.width());
    let height = usize::from(plane.height());
    let mut row = 0;
    while row < height {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let start = (y as usize + row) * destination.width as usize + x as usize;
        let source = &plane.coefficients()[row * width..(row + 1) * width];
        let samples = &mut destination.samples[start..start + width];
        let visited = &mut destination.visited[start..start + width];
        let mut column = 0;
        while column < width {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(column)?;
            let coefficient = &source[column];
            let magnitude = crate::refinement::maxshift_restore(
                coefficient.reconstructed_magnitude_bounded(),
                quantizer.roi_shift,
            );
            samples[column] = crate::transform::quantize_bounded_magnitude(
                magnitude,
                coefficient.reconstructed_negative(),
                quantizer.step,
                quantizer.reversible,
            );
            visited[column] = true;
            column += 1;
        }
        row += 1;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result!=Err(DecodeError::AllocationFailed) ==>
        (result,working_subband_view(*final(destination)))==crate::specs::part2_fused_band_value(
            working_subband_view(*old(destination)),crate::tier1::code_block_plane_view(plane),geometry,x,y,reversible,crate::limits::resource_decoded_bytes_limit(limits)),
        result==Err(DecodeError::AllocationFailed) ==> working_subband_view(*final(destination))==working_subband_view(*old(destination)),
))]
pub(in crate::decode) fn place(
    plane: &CodeBlockPlane,
    destination: &mut WorkingSubband,
    geometry: SubbandGeometry,
    x: u32,
    y: u32,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let width = u32::from(plane.width());
    let height = u32::from(plane.height());
    if x.checked_add(width).ok_or_else(arithmetic_overflow)? > geometry.width
        || y.checked_add(height).ok_or_else(arithmetic_overflow)? > geometry.height
    {
        return Err(invalid_decode());
    }
    if let Some(quantizer) = preflight(plane, destination, geometry, x, y, reversible, limits)? {
        return write(plane, destination, x, y, quantizer);
    }
    let coefficients = collect_prepare_coefficients(plane)?;
    let quantized = inverse_quantize_magnitudes(
        &coefficients,
        geometry.quantization_step,
        geometry.dynamic_range,
        reversible,
        geometry.roi_shift,
        limits,
    )?;
    if quantized.fraction_bits() != if reversible { 0 } else { 16 } {
        return Err(invalid_decode());
    }
    write_quantized_block(destination, quantized.samples(), width, height, x, y)
}

#[cfg(test)]
#[path = "fused_tests.rs"]
mod tests;
