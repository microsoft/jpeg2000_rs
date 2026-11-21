#[cfg(any(test, verus_keep_ghost))]
use crate::DecodeError;
#[cfg(test)]
use crate::MalformedKind;
#[cfg(test)]
use crate::Resource;
#[cfg(test)]
use crate::ResourceLimits;
#[cfg(any(test, verus_keep_ghost))]
use crate::codestream::ArbitraryKernel;
#[cfg(test)]
use crate::codestream::KernelCoefficient;
#[cfg(test)]
use crate::codestream::KernelLiftingStep;
use crate::magnitude::Magnitude;
#[cfg(test)]
use arbitrary::apply_arbitrary_steps;
#[cfg(test)]
use arithmetic::arithmetic_overflow;
#[cfg(test)]
use arithmetic::invalid_transform;
#[cfg(test)]
use arithmetic::validate_quantization_size;
#[cfg(test)]
use coefficients::binary_to_fixed;
#[cfg(test)]
use coefficients::fixed_div_q32;
#[cfg(test)]
use coefficients::fixed_from_binary_q32;
#[cfg(test)]
use coefficients::fixed_mul_q32;
#[cfg(test)]
use coefficients::round_shift_i128;
#[cfg(test)]
use geometry::store_column;
#[cfg(test)]
use quantization::inverse_quantize_plane;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(test)]
use wavelets::inverse_lift;
#[cfg(test)]
use wavelets::inverse_nine_seven_lifts;
#[cfg(test)]
use wavelets::scale_parity;

const FIXED_BITS: u8 = 16;
const FIXED_ONE: i64 = 1 << FIXED_BITS;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct QuantizationStep {
    pub exponent: u8,
    pub mantissa: u16,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct WaveletBand<'a> {
    pub width: u32,
    pub height: u32,
    pub samples: &'a [i64],
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct WaveletLevel<'a> {
    pub ll: WaveletBand<'a>,
    pub hl: WaveletBand<'a>,
    pub lh: WaveletBand<'a>,
    pub hh: WaveletBand<'a>,
    pub output_width: u32,
    pub output_height: u32,
    pub low_pass_first_x: bool,
    pub low_pass_first_y: bool,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) struct SignedMagnitude {
    pub magnitude: Magnitude,
    pub negative: bool,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ReconstructedPlane {
    width: u32,
    height: u32,
    fraction_bits: u8,
    samples: Vec<i64>,
}

#[derive(Clone, Copy)]
enum InverseLiftingStep {
    ReversibleUpdate,
    ReversiblePredict,
    Fixed(i64),
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod arbitrary;
pub use arbitrary::inverse_arbitrary;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod arithmetic;
pub(crate) use arithmetic::checked_area;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod coefficients;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod geometry;
pub(crate) use geometry::transform_offset;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod levels;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod rowwise;
pub(crate) use levels::inverse_empty_level;
pub use levels::{
    inverse_horizontal_5_3, inverse_horizontal_9_7, inverse_horizontal_arbitrary,
    inverse_level_5_3, inverse_level_9_7, inverse_level_arbitrary, inverse_vertical_5_3,
    inverse_vertical_9_7, inverse_vertical_arbitrary,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod output;
pub use output::convert_samples;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod quantization;
pub(crate) use quantization::inverse_quantize_magnitudes;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use quantization::undo_maxshift_magnitude;
pub use quantization::{inverse_quantize, undo_maxshift};
pub(crate) use quantization::{quantization_step_q16, quantize_bounded_magnitude};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod wavelets;
pub use wavelets::{inverse_5_3, inverse_9_7};

#[cfg(verus_keep_ghost)]
include!("transform/proof_support.rs");

#[cfg(test)]
pub(crate) mod tests;
