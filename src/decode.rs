use crate::{
    DecodeError, DecodeOptions, DecodeSelection, MalformedKind, Resource, ResourceLimits,
    SelectionError, TileSelection,
    codestream::{
        self, ArbitraryKernel, CodestreamLayout, CodingStyle, ComponentCodingStyles,
        ComponentQuantizations, ImageSize, Quantization, QuantizationStyle, RoiShifts,
        TilePartPayload, WaveletTransform,
    },
    image::{
        DecodedImage, NonlinearRegion, TileComponent, TransformComponentMut, TypedComponent,
        TypedImage, TypedSamples, apply_irreversible_component_transform,
        apply_multiple_component_transform_components, apply_reversible_component_transform,
        assemble_image, assemble_selected_image,
    },
    jp2,
    packet::{
        CodeBlockContribution, PacketGrid, PacketPrecinctDecoder, PacketSubbandExecution,
        decode_code_block_contribution_body,
    },
    tier1::{CodeBlockPlane, SubbandOrientation, Tier1CodeBlockDecoder, Tier1CodingStyle},
    transform::{
        QuantizationStep, SignedMagnitude, WaveletBand, WaveletLevel, inverse_horizontal_5_3,
        inverse_horizontal_9_7, inverse_horizontal_arbitrary, inverse_level_5_3, inverse_level_9_7,
        inverse_level_arbitrary, inverse_quantize_magnitudes, inverse_vertical_5_3,
        inverse_vertical_9_7, inverse_vertical_arbitrary,
    },
};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockLayer<'a> {
    pub contribution: &'a CodeBlockContribution,
    pub body: &'a [u8],
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockDecodeRequest<'a> {
    pub width: u16,
    pub height: u16,
    pub significant_bitplanes: u16,
    pub orientation: SubbandOrientation,
    pub style: Tier1CodingStyle,
    pub layers: &'a [CodeBlockLayer<'a>],
    pub quantization_step: QuantizationStep,
    pub dynamic_range: u8,
    pub reversible: bool,
    pub roi_shift: u8,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecodedCodeBlock {
    width: u16,
    height: u16,
    fraction_bits: u8,
    samples: Vec<i64>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PlacedCodeBlock<'a> {
    pub x: u32,
    pub y: u32,
    pub request: CodeBlockDecodeRequest<'a>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecodedSubband {
    width: u32,
    height: u32,
    fraction_bits: u8,
    samples: Vec<i64>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ComponentTransform {
    None,
    Reversible,
    Irreversible,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ComponentResolutionGeometry {
    pub component: u16,
    pub resolution: u8,
    pub width: u32,
    pub height: u32,
    pub subbands: u8,
    pub code_blocks_across: u32,
    pub code_blocks_down: u32,
    pub code_blocks: u64,
    pub precincts_across: u32,
    pub precincts_down: u32,
    pub precincts: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct SubbandGeometry {
    pub resolution: u8,
    pub orientation: SubbandOrientation,
    pub x0: u32,
    pub y0: u32,
    pub width: u32,
    pub height: u32,
    pub resolution_width: u32,
    pub resolution_height: u32,
    pub quantization_index: u16,
    pub quantization_step: QuantizationStep,
    pub dynamic_range: u8,
    pub significant_bitplanes: u16,
    pub roi_shift: u8,
    pub low_pass_first_x: bool,
    pub low_pass_first_y: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ProgressionCodeBlockPlacement {
    pub precinct_index: usize,
    pub decoder_index: usize,
    pub subband_index: usize,
    pub x: u32,
    pub y: u32,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PlannedTileComponent {
    pub component: u16,
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
    output_resolution: u8,
    subbands: Vec<SubbandGeometry>,
    placements: Vec<ProgressionCodeBlockPlacement>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) struct PlannedComponentMetadata {
    pub(crate) component_coding_style: CodingStyle,
    pub(crate) output_resolution: u8,
    pub(crate) tier1_style: Tier1CodingStyle,
    pub(crate) bounds: crate::codestream::TileComponentBounds,
    pub(crate) component_width: u32,
    pub(crate) component_height: u32,
    pub(crate) component_x: u32,
    pub(crate) component_y: u32,
    pub(crate) subbands: Vec<SubbandGeometry>,
}

pub(crate) struct PlannedCodeBlocks {
    pub(crate) decoders: Vec<Tier1CodeBlockDecoder>,
    pub(crate) placements: Vec<ProgressionCodeBlockPlacement>,
    pub(crate) decoder_index: usize,
    pub(crate) planned_code_blocks: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) struct PlannedSubbandLattice {
    pub(crate) grid: [u32; 4],
    pub(crate) clip: [u32; 4],
    pub(crate) blocks: [u32; 2],
}

pub(crate) struct PlannedSubbandExecution {
    pub(crate) execution: Option<PacketSubbandExecution>,
    pub(crate) placements: Vec<ProgressionCodeBlockPlacement>,
    pub(crate) decoder_index: usize,
    pub(crate) planned_code_blocks: u64,
}

pub(crate) struct PlannedPrecinct {
    pub(crate) precinct: PacketPrecinctDecoder,
    pub(crate) placements: Vec<ProgressionCodeBlockPlacement>,
    pub(crate) planned_code_blocks: u64,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) struct ResolutionPlanMetadata {
    pub(crate) geometry: ComponentResolutionGeometry,
    pub(crate) first_subband: usize,
    pub(crate) subband_count: usize,
    pub(crate) precincts_in_resolution: u32,
    pub(crate) first_precinct: [u32; 2],
    pub(crate) band_size: [u32; 2],
    pub(crate) block_size: [u32; 2],
}

pub(crate) struct PlannedComponent {
    pub(crate) component: PlannedTileComponent,
    pub(crate) precincts: Vec<PacketPrecinctDecoder>,
    pub(crate) planned_code_blocks: u64,
}

struct ComponentPlanBuilder {
    precincts: Vec<PacketPrecinctDecoder>,
    placements: Vec<ProgressionCodeBlockPlacement>,
    planned_code_blocks: u64,
}

struct PrecinctPlanBuilder {
    executions: Vec<PacketSubbandExecution>,
    placements: Vec<ProgressionCodeBlockPlacement>,
    decoder_index: usize,
    planned_code_blocks: u64,
}

pub struct ProgressionTilePlan {
    tile_index: u16,
    coding_style: CodingStyle,
    component_coding_styles: ComponentCodingStyles,
    grid: PacketGrid,
    precincts: Vec<PacketPrecinctDecoder>,
    components: Vec<PlannedTileComponent>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PreparedTileComponent {
    component: u16,
    x: u32,
    y: u32,
    width: u32,
    height: u32,
    fraction_bits: u8,
    samples: Vec<i64>,
}

pub(crate) struct DecodedTileComponents {
    pub(crate) prepared: Vec<PreparedTileComponent>,
    pub(crate) mct_work: u64,
}

pub(crate) struct DecodedLayoutTile {
    pub(crate) prepared: Vec<PreparedTileComponent>,
    pub(crate) counters: (u64, u64, u64),
    pub(crate) mct_work: u64,
}

pub(crate) struct TileDecodeMetadata<'a, 'data> {
    pub(crate) first: &'a TilePartPayload<'data>,
    pub(crate) standard: (bool, bool),
    pub(crate) resolution_counts: Vec<u8>,
}

struct WorkingSubband {
    width: u32,
    height: u32,
    fraction_bits: u8,
    samples: Vec<i64>,
    visited: Vec<bool>,
}

struct PrepareWorking {
    bands: Vec<WorkingSubband>,
    bytes: u64,
}

struct PrepareFold {
    width: u32,
    height: u32,
    samples: Vec<i64>,
    first_detail: usize,
}

#[cfg(verus_keep_ghost)]
include!("decode/proof_support.rs");

type NonlinearComponentExtent = ((u32, u32, u32, u32), u64);

struct ValidatedSelection {
    tiles: Vec<u16>,
    region: [u32; 4],
    discard_levels: u8,
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod api;
use api::typed_layout;
pub use api::{
    decode_codestream, decode_codestream_reconstructed, decode_codestream_selected, decode_jp2,
    decode_jp2_color, decode_jp2_color_selected, decode_jp2_selected, decode_jph, decode_jph_color,
    decode_jph_color_selected, decode_jph_selected, decode_jpx_codestream,
    decode_jpx_codestream_color, decode_jpx_codestream_color_selected,
    decode_jpx_codestream_selected,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod arithmetic;
pub(crate) use arithmetic::registered_ceil_div_u32;
use arithmetic::{
    arithmetic_overflow, ceil_div_u32, checked_area_u32, checked_index, floor_div_u32,
    invalid_decode, wavelet_transforms_equal,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod code_blocks;
pub use code_blocks::{decode_code_block, decode_prepared_image, decode_subband};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod execution;
use execution::{decode_layout, decode_layout_selected};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod geometry;
pub use geometry::{
    derive_component_resolution_geometry, derive_component_subbands, derive_packet_grid,
    quantization_step_for_subband,
};
pub(crate) use geometry::{
    derive_component_resolution_geometry_for, derive_component_subbands_for,
    derive_packet_grid_for_components,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod output;
pub(crate) use output::decode_jpx_file;
use output::{
    apply_jp2_output, color_selection, convert_associated_color, convert_associated_selected_color,
    decode_jpx_file_selected, finish_associated_selected_output,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod planning;
use planning::plan_progression_tile_at_selected;
pub use planning::{
    plan_progression_tile, plan_progression_tile_at,
    plan_progression_tile_at_with_component_overrides, plan_progression_tile_at_with_roi,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod reconstruction;
use reconstruction::{
    apply_tile_multiple_component_transform, assemble_prepared_components,
    prepare_tile_component_with_kernel,
};
pub use reconstruction::{decode_progression_prepared_image, prepare_tile_component};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod selection;
use selection::validate_selection;

#[cfg(verus_keep_ghost)]
pub(crate) use execution::{
    account_planned_tile, count_selected_component_blocks, decode_planned_tile_components,
    decode_tile_parts_at,
};
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use execution::{
    collect_tile_parts, optional_multiple_component_transforms_equal,
    prepare_tile_component_resolutions, prepare_tile_decode_metadata, validate_part2_coding_style,
    validate_part2_execution,
};
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use geometry::{
    component_coordinate_bounds, derive_subband_resolution, make_subband_geometry,
    prepare_component_resolution_counts, quantization_step_at_index,
};
#[cfg(verus_keep_ghost)]
pub(crate) use planning::{
    append_planned_codeblock, derive_planned_codeblock_geometry, derive_planned_precinct_origin,
    derive_planned_subband_lattice, plan_codeblock_decoders, plan_packet_precinct,
    plan_subband_execution, plan_tile_component,
};
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use planning::{prepare_component_plan_metadata, prepare_resolution_plan_metadata};

#[cfg(test)]
mod tests;
