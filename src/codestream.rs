use crate::{
    DecodeError, MalformedKind, Resource, ResourceLimits, tier1::Tier1BlockCoding,
    tier1::Tier1CodingStyle, transform::QuantizationStep,
};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const MAX_QUANTIZATION_STEPS: usize = 97;
pub(crate) const MAX_COMPONENTS: usize = 64;

const SOC: u16 = 0xff4f;
const SIZ: u16 = 0xff51;
const CAP: u16 = 0xff50;
const COD: u16 = 0xff52;
const COC: u16 = 0xff53;
const TLM: u16 = 0xff55;
const PRF: u16 = 0xff56;
const PLM: u16 = 0xff57;
const PLT: u16 = 0xff58;
const PPM: u16 = 0xff60;
const PPT: u16 = 0xff61;
const POC: u16 = 0xff5f;
const CRG: u16 = 0xff63;
const COM: u16 = 0xff64;
const QCD: u16 = 0xff5c;
const QCC: u16 = 0xff5d;
const RGN: u16 = 0xff5e;
const MCT: u16 = 0xff74;
const MCC: u16 = 0xff75;
const DFS: u16 = 0xff72;
const ADS: u16 = 0xff73;
const NLT: u16 = 0xff76;
const MCO: u16 = 0xff77;
const CBD: u16 = 0xff78;
const ATK: u16 = 0xff79;
const SOT: u16 = 0xff90;
const SOD: u16 = 0xff93;
const EOC: u16 = 0xffd9;
const CPF: u16 = 0xff59;
const HT_RSIZ_FLAG: u16 = 0x4000;
const PART_15_CAPABILITY_FLAG: u32 = 0x0002_0000;
pub const MAX_ROI_SHIFT: u8 = u8::MAX;
pub(crate) const MCT_FIXED_BITS: u8 = 32;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ImageSize {
    pub width: u32,
    pub height: u32,
    pub x_origin: u32,
    pub y_origin: u32,
    pub components: u16,
    pub uniform_bit_depth: Option<u8>,
    pub uniform_signed: Option<bool>,
    pub tile_width: u32,
    pub tile_height: u32,
    pub tile_x_origin: u32,
    pub tile_y_origin: u32,
    pub tiles_across: u32,
    pub tiles_down: u32,
    pub(crate) component_info: [ComponentInfo; MAX_COMPONENTS],
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ComponentInfo {
    pub precision: u8,
    pub signed: bool,
    pub x_subsampling: u8,
    pub y_subsampling: u8,
    pub x_registration: u16,
    pub y_registration: u16,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TileBounds {
    pub tile_index: u16,
    pub x0: u32,
    pub y0: u32,
    pub x1: u32,
    pub y1: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TileComponentBounds {
    pub tile_index: u16,
    pub component: u16,
    pub x0: u32,
    pub y0: u32,
    pub x1: u32,
    pub y1: u32,
    pub image_x: u32,
    pub image_y: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum ProgressionOrder {
    Lrcp,
    Rlcp,
    Rpcl,
    Pcrl,
    Cprl,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ProgressionChange {
    pub resolution_start: u8,
    pub component_start: u16,
    pub layer_end: u16,
    pub resolution_end: u8,
    pub component_end: u16,
    pub progression_order: ProgressionOrder,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ProgressionChanges {
    records: Vec<ProgressionChange>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum WaveletTransform {
    Irreversible9x7,
    Reversible5x3,
    Arbitrary(u8),
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodingStyle {
    pub progression_order: ProgressionOrder,
    pub layers: u16,
    pub multiple_component_transform: bool,
    pub decomposition_levels: u8,
    pub decomposition_structure: Option<u8>,
    pub decomposition_directions: [DecompositionDirection; 32],
    pub code_block_width: u16,
    pub code_block_height: u16,
    pub code_block_style: u8,
    pub transform: WaveletTransform,
    pub precincts_defined: bool,
    pub sop_markers: bool,
    pub eph_markers: bool,
    pub precinct_exponents: [(u8, u8); 33],
}

struct ComponentCodingStylePayload {
    component: u16,
    payload: [u8; 43],
    length: usize,
    decomposition_structure: Option<u8>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum QuantizationStyle {
    None,
    ScalarDerived,
    ScalarExpounded,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Quantization {
    pub style: QuantizationStyle,
    pub guard_bits: u8,
    pub step_count: u16,
    steps: [QuantizationStep; MAX_QUANTIZATION_STEPS],
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ComponentCodingStyles {
    components: u16,
    styles: [CodingStyle; MAX_COMPONENTS],
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
/// Bounded per-component quantization snapshots, stored off-stack.
pub struct ComponentQuantizations {
    components: u16,
    quantizations: Vec<Quantization>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct RoiShifts {
    shifts: [u8; MAX_COMPONENTS],
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodestreamInfo {
    pub image_size: ImageSize,
    pub coding_style: CodingStyle,
    pub quantization: Quantization,
    pub component_coding_styles: ComponentCodingStyles,
    pub component_quantizations: ComponentQuantizations,
    pub roi_shifts: RoiShifts,
    pub progression_changes: ProgressionChanges,
    pub multiple_component_transform: Option<MultipleComponentTransform>,
    pub part2_extensions: Part2Extensions,
    pub profile: CodestreamProfile,
    pub main_header_segments: u64,
    pub tile_parts: u32,
    pub consumed_bytes: u64,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum DecompositionDirection {
    #[default]
    None,
    TwoDimensional,
    Horizontal,
    Vertical,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecompositionStructure {
    index: u8,
    directions: Vec<DecompositionDirection>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ArbitraryDecomposition {
    index: u8,
    sublevel_depths: Vec<u8>,
    subband_splits: Vec<DecompositionDirection>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct NonlinearPointTransform {
    component: Option<u16>,
    precision: u8,
    signed: bool,
    transform_type: u8,
    parameters: Vec<u8>,
    d_min: Option<u32>,
    d_max: Option<u32>,
    point_bits: Option<u8>,
    points: Vec<u32>,
    gamma_parameters: Option<[u32; 5]>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ComponentBitDepth {
    pub precision: u8,
    pub signed: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ComponentRegistration {
    pub horizontal: u16,
    pub vertical: u16,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ArbitraryKernel {
    index: u8,
    reversible: bool,
    descriptor: u16,
    coefficient_type: u8,
    whole_sample_filter: bool,
    initial_odd: bool,
    whole_sample_extension: bool,
    scaling: Option<KernelCoefficient>,
    steps: Vec<KernelLiftingStep>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct KernelCoefficient {
    bytes: [u8; 16],
    width: u8,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct KernelLiftingStep {
    offset: i8,
    exponent: u8,
    residue: Option<KernelCoefficient>,
    coefficients: Vec<KernelCoefficient>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TilePartLength {
    pub tile_index: Option<u16>,
    pub length: u32,
}

#[derive(Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Part2Extensions {
    decomposition_structures: Vec<DecompositionStructure>,
    arbitrary_decompositions: Vec<ArbitraryDecomposition>,
    nonlinear_transforms: Vec<NonlinearPointTransform>,
    component_bit_depths: Vec<ComponentBitDepth>,
    arbitrary_kernels: Vec<ArbitraryKernel>,
    component_registrations: Vec<ComponentRegistration>,
    tile_part_lengths: Vec<TilePartLength>,
    metadata_bytes: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum CodestreamBlockCoding {
    Legacy,
    HighThroughput,
    Mixed,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Part15BlockMode {
    HtOnly,
    HtDeclared,
    Mixed,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ExtendedCapabilities {
    p_cap: u32,
    c_capabilities: Vec<u16>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ProfileNumber {
    words: Vec<u16>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodestreamProfile {
    pub r_siz: u16,
    pub block_coding: CodestreamBlockCoding,
    extended_capabilities: Option<ExtendedCapabilities>,
    profile: Option<ProfileNumber>,
    corresponding_profile: Option<ProfileNumber>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum MctArrayKind {
    Dependency,
    Decorrelation,
    Offset,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum MctNumericFormat {
    Int16,
    Int32,
    Float32,
    Float64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum MctCollectionKind {
    Dependency,
    Decorrelation,
    Wavelet,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum MctWaveletType {
    Irreversible9x7,
    Reversible5x3,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MctWavelet {
    transform: MctWaveletType,
    levels: u8,
    component_offset: i32,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MctArray {
    index: u8,
    kind: MctArrayKind,
    numeric_format: MctNumericFormat,
    fraction_bits: u8,
    values: Vec<i64>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MultipleComponentTransform {
    stages: Vec<MctStage>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MctStage {
    index: u8,
    collections: Vec<MctCollection>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct MctCollection {
    reversible: bool,
    input_components: Vec<u16>,
    output_components: Vec<u16>,
    kind: MctCollectionKind,
    matrix: Option<MctArray>,
    offsets: Option<MctArray>,
    wavelet: Option<MctWavelet>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
enum PacketLengthSource<'a> {
    None,
    Plm(&'a [u8]),
    Plt(&'a [u8]),
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
enum PackedPacketHeaderSource<'a> {
    None,
    MarkerSegments {
        header: &'a [u8],
        marker: u16,
        logical_start: usize,
    },
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PackedPacketHeaders<'a> {
    source: PackedPacketHeaderSource<'a>,
    length: usize,
    fragments: u16,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PacketLengths<'a> {
    source: PacketLengthSource<'a>,
    packet_count: u64,
    encoded_bytes: u64,
}

pub(crate) struct PacketLengthIter<'a> {
    source: PacketLengthSource<'a>,
    position: usize,
    segment_end: usize,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct Segment<'a> {
    marker: u16,
    offset: usize,
    payload: &'a [u8],
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct MctParameters {
    arrays: Vec<MctArray>,
    records: Vec<MctRecord>,
    order: Vec<u8>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct MctRecord {
    index: u8,
    collections: Vec<MctCollectionReference>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct MctCollectionReference {
    input_components: Vec<u16>,
    output_components: Vec<u16>,
    transform: MctCollectionReferenceTransform,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
enum MctCollectionReferenceTransform {
    Array {
        kind: MctArrayKind,
        reversible: bool,
        transform_index: u8,
        offset_index: u8,
    },
    Wavelet(MctWavelet),
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct MctFragment {
    descriptor: u16,
    next_index: u16,
    final_index: u16,
    offset: usize,
    data: Vec<u8>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct MccFragment {
    record_index: u8,
    next_index: u16,
    final_index: u16,
    collection_count: u16,
    offset: usize,
    data: Vec<u8>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct TilePart {
    start: usize,
    length: u32,
    tile_index: u16,
    tile_part_index: u8,
    tile_part_count: u8,
}

#[derive(Clone, Copy)]
struct PackedHeaderFrame {
    start: usize,
    length: usize,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodestreamLayout<'a> {
    pub info: CodestreamInfo,
    pub tile_parts: Vec<TilePartPayload<'a>>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TilePartPayload<'a> {
    pub tile_index: u16,
    pub tile_part_index: u8,
    pub tile_part_count: u8,
    pub coding_style: CodingStyle,
    pub quantization: Quantization,
    pub component_coding_styles: ComponentCodingStyles,
    pub component_quantizations: ComponentQuantizations,
    pub roi_shifts: RoiShifts,
    pub progression_changes: ProgressionChanges,
    pub multiple_component_transform: Option<MultipleComponentTransform>,
    pub part2_extensions: Part2Extensions,
    pub packet_lengths: PacketLengths<'a>,
    pub packed_packet_headers: PackedPacketHeaders<'a>,
    pub has_functional_header_marker: bool,
    pub has_roi_marker: bool,
    pub data: &'a [u8],
}

struct Parser<'a> {
    input: &'a [u8],
    limits: &'a ResourceLimits,
    position: usize,
    work_units: u64,
    packet_length_bytes: u64,
    packet_lengths: u64,
}

#[cfg(verus_keep_ghost)]
include!("codestream/proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("codestream/tile_header_traversal_proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("codestream/tile_part_proof_support.rs");

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod coding_markers;
#[cfg(test)]
use coding_markers::progression_owners_complete;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod coding_style;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod decomposition;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod extensions;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod geometry;
#[cfg(test)]
use geometry::{ceil_div, selection_geometry_invalid};
pub(crate) use geometry::{image_component_info, registered_ceil_div};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod image_header;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod layout;
pub use layout::{parse, parse_layout};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct_markers;
#[cfg(test)]
use mct_markers::{
    find_mcc_fragment, find_mct_fragment, fixed_from_binary, float32_to_fixed, float64_to_fixed,
    parse_mcc_component_list, u16_list_contains,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mct_resolution;
#[cfg(test)]
use mct_resolution::{
    component_lists_overlap, find_mct_array_index, find_mct_record_index, referenced_mct_array,
    replace_mct_array, replace_mct_record, u8_list_contains, validate_parallel_collections,
    validate_unique_mct_array_indexes, validate_unique_mct_record_indexes,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod packet_headers;
#[cfg(test)]
use packet_headers::decode_packet_length;
pub(crate) use packet_headers::{packed_packet_headers_none, packet_lengths_none};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod part2_transforms;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod profile;
#[cfg(test)]
use profile::{count_set_bits, maximum_u32_for_bits};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod quantization;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod reader;
#[cfg(test)]
use reader::{
    is_standalone_marker, new_parser, read_u16, read_u32, read_u64, signed_u16, signed_u32,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod tile_header_traversal;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod tiles;

#[cfg(test)]
mod tests;
