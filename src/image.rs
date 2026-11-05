use crate::codestream::{ComponentInfo, MctWavelet, NonlinearPointTransform};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const FIXED_BITS: u8 = 16;

pub(crate) struct TransformComponentMut<'a> {
    pub component: u16,
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
    pub x_subsampling: u8,
    pub y_subsampling: u8,
    pub fraction_bits: &'a mut u8,
    pub samples: &'a mut [i64],
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TileComponent<'a> {
    pub component: u16,
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
    pub fraction_bits: u8,
    pub samples: &'a [i64],
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecodedComponent {
    width: u32,
    height: u32,
    info: ComponentInfo,
    fraction_bits: u8,
    samples: Vec<i64>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecodedImage {
    width: u32,
    height: u32,
    x_origin: u32,
    y_origin: u32,
    components: Vec<DecodedComponent>,
}

struct AssemblyPlane {
    width: u32,
    height: u32,
    fraction_bits: Option<u8>,
    samples: Vec<i64>,
    visited: Vec<bool>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum TypedSamples {
    Signed(Vec<i64>),
    Unsigned(Vec<u64>),
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ChannelType {
    Color,
    Opacity,
    PremultipliedOpacity,
    Unspecified,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ChannelAssociation {
    WholeImage,
    Color(u16),
    Unassociated,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ChannelDefinition {
    channel_type: ChannelType,
    association: ChannelAssociation,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TypedComponent {
    width: u32,
    height: u32,
    info: ComponentInfo,
    samples: TypedSamples,
    channel_definitions: Vec<ChannelDefinition>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TypedImage {
    width: u32,
    height: u32,
    x_origin: u32,
    y_origin: u32,
    components: Vec<TypedComponent>,
}

pub(crate) struct NonlinearRegion<'a> {
    pub component: u16,
    pub x0: u32,
    pub y0: u32,
    pub x1: u32,
    pub y1: u32,
    pub transform: &'a NonlinearPointTransform,
}

type NonlinearLutCoordinates = (usize, i128, i128);

type AssemblyDimensions = (ComponentInfo, u32, u32, u32, u32, u32, u32);
type AssemblySelection = Option<([u32; 4], u32)>;

struct MctDecorrelationPreparation {
    source_indexes: Vec<usize>,
    destination_indexes: Vec<usize>,
    source_fraction_bits: Vec<u8>,
    sample_count: usize,
    rows: usize,
    columns: usize,
}

struct MctDependencyPreparation {
    source_indexes: Vec<usize>,
    destination_indexes: Vec<usize>,
    sample_count: usize,
    count: usize,
}

struct MctWaveletPreparation {
    source_indexes: Vec<usize>,
    destination_indexes: Vec<usize>,
    low_first: Vec<bool>,
    high_lengths: Vec<usize>,
    low_length: usize,
    sample_count: usize,
    count: usize,
    wavelet: MctWavelet,
    source_fraction_bits: Vec<u8>,
}

#[cfg(verus_keep_ghost)]
include!("image/proof_support.rs");
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod arithmetic;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod assembly;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod component_transform;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod layout;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct_decorrelation;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct_dependency;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct_wavelet;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod nonlinear;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod nonlinear_math;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod samples;
#[cfg(any(test, verus_keep_ghost))]
use crate::DecodeError;
#[cfg(any(test, verus_keep_ghost))]
use crate::codestream::ImageSize;
#[cfg(test)]
use crate::codestream::{MCT_FIXED_BITS, MctArray, MultipleComponentTransform, Part2Extensions};
#[cfg(test)]
use crate::transform::inverse_9_7;
#[cfg(test)]
use crate::{MalformedKind, Resource, ResourceLimits};
#[cfg(test)]
use arithmetic::{arithmetic_overflow, invalid_image, invalid_transform, validate_bytes};
pub use assembly::assemble_image;
pub(crate) use assembly::assemble_selected_image;
#[cfg(test)]
use assembly::charge_assembly_bytes;
#[cfg(test)]
use component_transform::apply_component_pixel;
pub(crate) use component_transform::inverse_component_values;
pub use component_transform::{
    apply_irreversible_component_transform, apply_reversible_component_transform,
};
pub(crate) use layout::{
    channel_definition_new, typed_component_from_parts, typed_image_from_components_with_origin,
};
pub use mct::apply_multiple_component_transform;
pub(crate) use mct::apply_multiple_component_transform_components;
#[cfg(test)]
use mct::{
    admit_mct_decorrelation, apply_mct_destination_precisions, ceil_divide_by_two, charge_mct_work,
    check_mct_scratch, find_transform_component, fixed_mct_row_scaled, offset_value,
    offset_value_scaled, rescale_i128, reversible_mct_row, rounded_shift_i128,
    store_transform_component_sample, store_transform_sample, validate_mct_components_layout,
};
#[cfg(test)]
use mct_decorrelation::{
    append_mct_decorrelation_rows, apply_mct_decorrelation, apply_mct_decorrelation_pixel,
    decorrelation_mct_row, prepare_mct_decorrelation,
};
#[cfg(test)]
use mct_dependency::{
    admit_mct_dependency, apply_mct_dependency, apply_mct_dependency_pixel,
    irreversible_dependency_row, mct_dependency_coefficient_count, prepare_mct_dependency,
    reversible_dependency_row,
};
#[cfg(test)]
use mct_wavelet::{apply_mct_wavelet, begin_mct_wavelet_pixel, prepare_mct_wavelet_partition};
#[cfg(test)]
use nonlinear_math::{
    inverse_nlt_gamma_sample, inverse_nlt_lut_sample, inverse_nlt_sample, nlt_checked_rem,
    nlt_exp_series, nlt_fixed_div_q32, nlt_fixed_exp_q32, nlt_fixed_ln_q32, nlt_fixed_mul_q32,
    nlt_fixed_pow_reciprocal_q32, nlt_gamma_curve, nlt_gamma_parameter, nlt_ln_normalize,
    nlt_ln_series, nlt_lut_coordinates, nlt_lut_interpolate_values, nlt_lut_position,
    nlt_power_of_two, nlt_round_ratio,
};
#[cfg(test)]
mod tests;
