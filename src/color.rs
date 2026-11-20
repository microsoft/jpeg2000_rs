#[cfg(any(test, verus_keep_ghost))]
use crate::DecodeError;
#[cfg(test)]
use crate::MalformedKind;
#[cfg(test)]
use crate::Resource;
#[cfg(test)]
use crate::ResourceLimits;
#[cfg(test)]
use crate::UnsupportedColorConversion;
use crate::image::ChannelAssociation;
#[cfg(test)]
use crate::jp2::ColorMethod;
#[cfg(test)]
use crate::jp2::ColorSpecification;
#[cfg(test)]
use crate::jp2::ENUMERATED_GRAYSCALE;
#[cfg(test)]
use crate::jp2::ENUMERATED_SRGB;
#[cfg(test)]
use crate::jp2::ENUMERATED_SYCC;
#[cfg(test)]
use admission::channel_layout;
#[cfg(test)]
use admission::validate_output_size;
#[cfg(test)]
use conversion::rounded_fixed;
#[cfg(test)]
use conversion::sycc_to_srgb;
#[cfg(test)]
use geometry::invalid_color_input;
#[cfg(test)]
use geometry::registered_ceil_div;
#[cfg(test)]
use geometry::registered_floor_div;
#[cfg(test)]
use normalization::nominal_component_at;
#[cfg(test)]
use normalization::normalized_at;
#[cfg(test)]
use normalization::normalized_difference_at;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const OUTPUT_MAXIMUM: u64 = u16::MAX as u64;
const FIXED_ONE: i128 = 65_536;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ConvertedColorSpace {
    Srgb,
    Grayscale,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ConvertedChannelType {
    Red,
    Green,
    Blue,
    Gray,
    Alpha {
        premultiplied: bool,
        association: ChannelAssociation,
    },
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ConvertedChannel {
    channel_type: ConvertedChannelType,
    samples: Vec<u16>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ConvertedImage {
    width: u32,
    height: u32,
    color_space: ConvertedColorSpace,
    precision: u8,
    channels: Vec<ConvertedChannel>,
}

struct ChannelLayout {
    colors: Vec<usize>,
    alphas: Vec<(usize, bool, ChannelAssociation)>,
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod admission;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod conversion;
pub use conversion::convert_jp2_color;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod compatible;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod crop;
#[cfg(verus_keep_ghost)]
pub use compatible::compatible_color_outcome;
pub(crate) use compatible::esrgb8_compatible;
pub use compatible::{ColorRecovery, CompatibleColorImage, convert_jp2_color_compatible};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod esrgb;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod esrgb_image;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod geometry;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod normalization;
pub(crate) use normalization::{normalize_component, normalize_unsigned};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod output;
pub(crate) use output::{from_composited, from_layer};

#[cfg(verus_keep_ghost)]
include!("color/proof_support.rs");

#[cfg(test)]
mod tests;
