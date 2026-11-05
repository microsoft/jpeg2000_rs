use crate::{
    DecodeError, DecodeOptions, MalformedKind, Resource, ResourceLimits,
    codestream::ComponentInfo,
    color::{ConvertedChannelType, ConvertedColorSpace, ConvertedImage},
    image::{ChannelAssociation, ChannelDefinition, ChannelType, TypedComponent, TypedSamples},
    jp2::{
        self, ComponentBitDepth, CompositingLayer, CompositionInstruction, Jp2File, LayerOpacity,
    },
};

#[cfg(verus_keep_ghost)]
use crate::image::TypedImage;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpxLayerInfo {
    index: usize,
    codestream_indices: Vec<u16>,
    horizontal_grid_size: u16,
    vertical_grid_size: u16,
    horizontal_offset: u32,
    vertical_offset: u32,
    width: u32,
    height: u32,
    has_color_group: bool,
    has_opacity_box: bool,
    nested_metadata_boxes: u32,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpxCompositionInfo {
    width: u32,
    height: u32,
    loop_count: u8,
    instruction_sets: u32,
    frames: Vec<JpxFrameInfo>,
    total_duration_milliseconds: u64,
    has_unknown_boxes: bool,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpxFrameInfo {
    index: usize,
    start_milliseconds: u64,
    duration_milliseconds: u32,
    persistent: bool,
    instructions: Vec<JpxInstructionInfo>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpxInstructionInfo {
    layer_index: usize,
    target_x: u32,
    target_y: u32,
    target_width: u32,
    target_height: u32,
    source_x: u32,
    source_y: u32,
    source_width: u32,
    source_height: u32,
    persistent: bool,
    next_reuse: u32,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpxInspection {
    layers: Vec<JpxLayerInfo>,
    composition: Option<JpxCompositionInfo>,
    metadata_boxes: u32,
    metadata_depth: u32,
}

struct TimelineState {
    frames: Vec<JpxFrameInfo>,
    assignments: Vec<Option<usize>>,
    next_layer: usize,
    instruction_index: usize,
    milliseconds: u64,
}

struct OwnedLayer {
    width: u32,
    height: u32,
    color_space: ConvertedColorSpace,
    colors: Vec<Vec<u16>>,
    alpha: Option<(Vec<u16>, bool)>,
}

type SuppliedLayer = (usize, Option<Result<OwnedLayer, DecodeError>>);

struct LayerChannels<'a> {
    width: u32,
    height: u32,
    colors: Vec<&'a [u16]>,
    alpha: Option<(Vec<u16>, bool)>,
}

#[cfg(verus_keep_ghost)]
include!("jpx/proof_support.rs");

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod channels;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod chroma;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod compositing;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod inspection;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod layer_decode;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod opacity;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod registration;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod render;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod resources;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod timeline;

#[cfg(test)]
use channels::layer_channels;
#[cfg(test)]
use chroma::{
    append_component_chroma_key, apply_chroma_key, apply_chroma_key_with_policy,
    normalized_chroma_keys, normalized_chroma_keys_for_components,
};
#[cfg(test)]
use compositing::{composite_layer, composite_placed_layer};
pub use inspection::inspect_jpx_layers;
#[cfg(test)]
use layer_decode::owned_layer_from_image;
#[cfg(test)]
use opacity::{
    copy_opacity_pixel, copy_opacity_row, copy_registered_layer_opacity, set_layer_alpha_mode,
};
#[cfg(test)]
use registration::{
    copy_registered_pixel, copy_registered_row, register_layer, registered_layer_geometry,
};
#[cfg(test)]
use render::{render_decoded_layers, render_normalized_frame};
pub use render::{render_jpx_composition, render_jpx_frame, render_jpx_layer};
#[cfg(test)]
use resources::{arithmetic_overflow, index_of, invalid_layer, registered_extent};
#[cfg(test)]
use timeline::{
    append_timeline_frame, apply_timeline_instruction, build_timeline, select_frame_instructions,
};

// Retain the private test module's original scope and oracle body tokens.
#[cfg(test)]
include!("jpx/tests.rs");
