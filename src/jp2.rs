use crate::{
    DecodeError, MalformedKind, Resource, ResourceLimits,
    codestream::{self, CodestreamInfo},
    image::{ChannelAssociation, ChannelDefinition, ChannelType},
};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const SIGNATURE_MAGIC: [u8; 4] = [0x0d, 0x0a, 0x87, 0x0a];
pub const ENUMERATED_SRGB: u32 = 16;
pub const ENUMERATED_GRAYSCALE: u32 = 17;
pub const ENUMERATED_SYCC: u32 = 18;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct BoxType(u32);

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct BoxHeader {
    box_type: BoxType,
    offset: u64,
    header_length: u64,
    total_length: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct BoxRef<'a> {
    pub header: BoxHeader,
    pub payload: &'a [u8],
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct BoxReader<'a> {
    input: &'a [u8],
    limits: ResourceLimits,
    position: usize,
    metadata_bytes: u64,
    work_units: u64,
    failed: bool,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct FileType {
    pub brand: BoxType,
    pub minor_version: u32,
    compatible_brands: Vec<BoxType>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ComponentBitDepth {
    Uniform { bits: u8, signed: bool },
    Variable,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ImageHeader {
    pub width: u32,
    pub height: u32,
    pub components: u16,
    pub bit_depth: ComponentBitDepth,
    pub unknown_color_space: bool,
    pub intellectual_property: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ColorMethod {
    Enumerated { color_space: u32 },
    RestrictedIcc { profile_bytes: u64 },
    AnyIcc { profile_bytes: u64 },
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ColorSpecification {
    pub method: ColorMethod,
    pub precedence: u8,
    pub approximation: u8,
    icc_profile: Option<Vec<u8>>,
}

impl Clone for ColorSpecification {
    fn clone(&self) -> Self {
        clone_support::color_specification_clone(self)
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Resolution {
    pub vertical_numerator: u16,
    pub vertical_denominator: u16,
    pub horizontal_numerator: u16,
    pub horizontal_denominator: u16,
    pub vertical_exponent: i8,
    pub horizontal_exponent: i8,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Jp2Header {
    pub image: ImageHeader,
    pub color: ColorSpecification,
    pub nested_box_count: u32,
    pub palette_entries: u16,
    pub palette_columns: u8,
    pub component_mapping_entries: u16,
    pub channel_definitions: u16,
    pub palette: Option<Palette>,
    pub component_mappings: Vec<ComponentMapping>,
    pub channel_definition_records: Vec<ChannelDefinitionRecord>,
    pub capture_resolution: Option<Resolution>,
    pub display_resolution: Option<Resolution>,
}

impl Clone for Jp2Header {
    fn clone(&self) -> Self {
        clone_support::jp2_header_clone(self)
    }
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Jp2File<'a> {
    pub file_type: FileType,
    pub header: Jp2Header,
    codestreams: Vec<CodestreamBox<'a>>,
    compositing_layers: Vec<CompositingLayer<'a>>,
    composition: Option<Composition>,
    metadata_boxes: u32,
    metadata_depth: u32,
    pub box_count: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodestreamRegistration {
    pub codestream_index: u16,
    pub horizontal_subsampling: u8,
    pub vertical_subsampling: u8,
    pub horizontal_offset: u32,
    pub vertical_offset: u32,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CompositingLayer<'a> {
    header: BoxHeader,
    payload: &'a [u8],
    horizontal_grid_size: u16,
    vertical_grid_size: u16,
    registrations: Vec<CodestreamRegistration>,
    color_group: Vec<ColorSpecification>,
    channel_definition_records: Vec<ChannelDefinitionRecord>,
    opacity: Option<LayerOpacity>,
    nested_metadata_boxes: u32,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum LayerOpacity {
    Straight,
    Premultiplied,
    ChromaKey { channels: u8, values: Vec<u8> },
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CompositionInstruction {
    pub target_x: u32,
    pub target_y: u32,
    pub target_width: u32,
    pub target_height: u32,
    pub life: u32,
    pub persistent: bool,
    pub next_reuse: u32,
    pub source_x: u32,
    pub source_y: u32,
    pub source_width: u32,
    pub source_height: u32,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CompositionInstructionSet {
    pub flags: u16,
    pub repeat: u16,
    pub tick: u32,
    pub instructions: Vec<CompositionInstruction>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Composition {
    pub width: u32,
    pub height: u32,
    pub loop_count: u8,
    pub instruction_sets: Vec<CompositionInstructionSet>,
    pub has_unknown_boxes: bool,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct InspectedJp2<'a> {
    pub file: Jp2File<'a>,
    codestreams: Vec<CodestreamInfo>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodestreamHeaderAssociation<'a> {
    pub header: BoxHeader,
    pub payload: &'a [u8],
    parsed: Option<Jp2Header>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodestreamBox<'a> {
    pub header: BoxHeader,
    pub data: &'a [u8],
    codestream_header: Option<CodestreamHeaderAssociation<'a>>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PaletteColumn {
    pub precision: u8,
    pub signed: bool,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Palette {
    entries: u16,
    columns: Vec<PaletteColumn>,
    values: Vec<i64>,
}

impl Clone for Palette {
    fn clone(&self) -> Self {
        clone_support::palette_clone(self)
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum MappingType {
    Direct,
    Palette { column: u8 },
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ComponentMapping {
    pub component: u16,
    pub mapping_type: MappingType,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ChannelDefinitionRecord {
    pub channel: u16,
    pub definition: ChannelDefinition,
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod box_reader;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod clone_support;
use box_reader::{
    add_offset, box_reader_from_input, box_type_from_bytes, byte_at_checked, read_box_type_at,
    read_u16, read_u32, rebase_error, required_box,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod color;
use color::{
    parse_channel_definition, parse_color_specification, parse_component_mapping, parse_palette,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod composition;
use composition::{parse_compositing_layer, parse_composition, validate_layer_references};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod container;
pub(crate) use container::{associated_header_for_codestream, validate_selected_header};
pub use container::{inspect_jph, parse, parse_and_inspect};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod headers;
use headers::{parse_bit_depth, parse_codestream_header, parse_jp2_header};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod metadata;
use metadata::{copy_bytes, inspect_metadata_box, parse_resolution_superbox};
#[cfg(verus_keep_ghost)]
include!("jp2/proof_support.rs");
#[cfg(test)]
mod tests;
