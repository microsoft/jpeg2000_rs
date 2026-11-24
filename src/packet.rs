use crate::{
    DecodeError, MalformedKind, Resource, ResourceLimits,
    codestream::{ProgressionChange, ProgressionChanges, ProgressionOrder, TilePartPayload},
    tier1::{SubbandOrientation, Tier1CodeBlockDecoder, Tier1CodingStyle},
};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION: usize = 164;
const SOP_MARKER: [u8; 2] = [0xff, 0x91];
const EPH_MARKER: [u8; 2] = [0xff, 0x92];

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PacketBitReader<'a> {
    input: &'a [u8],
    byte_index: usize,
    current_byte: u8,
    bits_remaining: u8,
    previous_byte_was_ff: bool,
    bits_read: u64,
    maximum_work_units: u64,
    maximum_header_bytes: u64,
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
pub struct PacketGrid {
    layers: u16,
    components: u16,
    resolutions: u8,
    component_resolutions: Vec<u8>,
    maximum_precincts_per_resolution: u32,
    precinct_counts: Vec<u32>,
    precinct_offsets: Vec<usize>,
    candidate_count: u64,
    packet_count: u64,
    spatial: Option<PacketSpatialGrid>,
    maximum_work_units: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) struct PacketSpatialResolution {
    pub(crate) first_x: u64,
    pub(crate) first_y: u64,
    pub(crate) origin_x: u64,
    pub(crate) origin_y: u64,
    pub(crate) step_x: u64,
    pub(crate) step_y: u64,
    pub(crate) across: u32,
    pub(crate) down: u32,
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
pub(crate) struct PacketSpatialGrid {
    pub(crate) rows: Vec<PacketSpatialResolution>,
    pub(crate) x0: u32,
    pub(crate) y0: u32,
    pub(crate) step_x: u64,
    pub(crate) step_y: u64,
    pub(crate) across: u64,
    pub(crate) positions: u64,
}

struct PacketGridCountState {
    index: usize,
    component: usize,
    resolution: usize,
    total: u64,
    maximum: u32,
    offsets: Vec<usize>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, Hash, PartialEq))]
pub struct PacketCoordinate {
    pub layer: u16,
    pub resolution: u8,
    pub component: u16,
    pub precinct: u32,
}

pub struct PacketIterator<'a> {
    grid: &'a PacketGrid,
    order: ProgressionOrder,
    candidate_index: u64,
    emitted: u64,
}

pub struct ProgressionPacketIterator<'a> {
    grid: &'a PacketGrid,
    changes: &'a ProgressionChanges,
    default: Option<PacketIterator<'a>>,
    window_index: usize,
    window_candidate: u64,
    window_candidates: u64,
    emitted: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockPacketState {
    included: bool,
    zero_bitplanes: Option<u16>,
    lblock: u8,
    total_passes: u32,
    high_throughput: Option<bool>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockContribution {
    pub first_inclusion: bool,
    pub zero_bitplanes: u16,
    pub new_passes: u8,
    pub data_length: u32,
    pub high_throughput: bool,
    segment_count: u8,
    segment_passes: [u8; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
    segment_lengths: [u32; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockSegmentContribution {
    pub passes: u8,
    pub data_length: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockBodyDecode {
    pub segments: u8,
    pub passes: u32,
    pub bytes: u32,
}

#[derive(Clone, Copy)]
pub(crate) struct HtBodyProgress {
    pub segment_index: u8,
    pub offset: usize,
    pub decoded_passes: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PacketBodyDecode {
    pub present: bool,
    pub code_blocks: u32,
    pub contributions: u32,
    pub segments: u32,
    pub passes: u32,
    pub header_bytes: u32,
    pub body_bytes: u32,
    pub bytes_consumed: u32,
}

pub struct PacketCodeBlockExecution<'a> {
    pub states: &'a mut [CodeBlockPacketState],
    pub inclusion_tree: &'a mut TagTree,
    pub zero_bitplane_tree: &'a mut TagTree,
    pub contexts: &'a [CodeBlockPacketContext],
    pub decoders: &'a mut [Tier1CodeBlockDecoder],
}

pub struct PacketPrecinctDecoder {
    component: u16,
    resolution: u8,
    precinct: u32,
    states: Vec<CodeBlockPacketState>,
    contexts: Vec<CodeBlockPacketContext>,
    decoders: Vec<Tier1CodeBlockDecoder>,
    subbands: Vec<PacketSubbandState>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct PacketPrecinctGeometry {
    pub component: u16,
    pub resolution: u8,
    pub precinct: u32,
    pub code_blocks_across: u32,
    pub code_blocks_down: u32,
    pub maximum_zero_bitplanes: u16,
}

pub struct PacketSubbandExecution {
    pub orientation: SubbandOrientation,
    pub code_blocks_across: u32,
    pub code_blocks_down: u32,
    pub maximum_zero_bitplanes: u16,
    pub decoders: Vec<Tier1CodeBlockDecoder>,
}

struct PacketSubbandState {
    orientation: SubbandOrientation,
    first_decoder: usize,
    decoder_count: usize,
    code_blocks_across: u32,
    code_blocks_down: u32,
    inclusion_tree: TagTree,
    zero_bitplane_tree: TagTree,
}

#[derive(Clone, Copy)]
struct PrecinctHeaderParameters {
    layer: u16,
    style: Tier1CodingStyle,
}

#[derive(Clone, Copy)]
struct PrecinctHeaderProgress {
    subband_index: usize,
    local_index: usize,
    contribution_count: u32,
}

#[derive(Clone, Copy)]
struct PrecinctPayloadParameters {
    owned_body: bool,
    error_offset: usize,
    packed_offset: usize,
    expected_packet_length: Option<u32>,
    expected_sop_sequence: u16,
    style: Tier1CodingStyle,
    sop: bool,
    eph: bool,
    packed: bool,
    decode_tier1: bool,
}

struct PrecinctPayloadReader<'a> {
    reader: PacketBitReader<'a>,
    packet_data: &'a [u8],
    present: bool,
    sop_bytes: usize,
}

struct PrecinctPayloadHeader<'a> {
    prefix: PrecinctPayloadReader<'a>,
    contributions: Vec<Option<CodeBlockContribution>>,
    contribution_count: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TilePacketDecode {
    pub tile_index: u16,
    pub tile_parts: u32,
    pub packets: u64,
    pub present_packets: u64,
    pub contributions: u64,
    pub segments: u64,
    pub passes: u64,
    pub packet_header_bytes: u64,
    pub packet_body_bytes: u64,
    pub payload_bytes: u64,
}

struct ProgressionTilePreparation {
    tile_index: u16,
    index: usize,
    payload_bytes: u64,
    packed_payload_bytes: u64,
    declared_packets: u64,
    all_lengths: bool,
    packed: Vec<Vec<u8>>,
}

struct ProgressionTileParameters<'a, 'data> {
    owned_body: bool,
    tile_parts: &'a [TilePartPayload<'data>],
    grid: &'a PacketGrid,
    input: &'a ProgressionTilePreparation,
    selection: Option<&'a [u8]>,
    limits: &'a ResourceLimits,
}

struct ProgressionTileProgress<'a> {
    iterator: ProgressionPacketIterator<'a>,
    length_iterator: crate::codestream::PacketLengthIter<'a>,
    current_tile_part: usize,
    length_tile_part: usize,
    offset: usize,
    packed_offset: usize,
    packets: u64,
    present_packets: u64,
    contributions: u64,
    segments: u64,
    passes: u64,
    packet_header_bytes: u64,
    packet_body_bytes: u64,
    seen: Vec<bool>,
    remaining_packets: u64,
}

#[derive(Clone, Copy)]
struct PacketBodyPreflight {
    index: usize,
    end: usize,
}

#[derive(Clone, Copy)]
struct PacketBodyExecutionProgress {
    index: usize,
    offset: usize,
    segments: u32,
    passes: u32,
}

struct MultiPacketParameters<'a, 'data> {
    part: &'a TilePartPayload<'data>,
    offset: usize,
    limits: &'a ResourceLimits,
}

#[derive(Clone, Copy)]
struct MultiHeaderProgress {
    index: usize,
    count: u32,
}

#[derive(Clone, Copy)]
struct MultiHeaderParameters<'a> {
    contexts: &'a [CodeBlockPacketContext],
    offset: usize,
}

#[derive(Clone, Copy)]
struct MultiPacketLayout {
    blocks: u64,
    present: bool,
    count: u32,
    header: usize,
    start: usize,
}

#[cfg(test)]
pub(crate) mod ht_route_test_support {
    use super::*;

    pub(crate) fn segment_body(
        decoder: &mut Tier1CodeBlockDecoder,
        passes: u8,
        data_length: u32,
        body: &[u8],
        offset: &mut usize,
        decoded_passes: &mut u32,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        decode_ht_segment_body(
            decoder,
            CodeBlockSegmentContribution {
                passes,
                data_length,
            },
            body,
            offset,
            decoded_passes,
            limits,
        )
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockPacketContext {
    pub leaf_x: u32,
    pub leaf_y: u32,
    pub layer: u16,
    pub maximum_zero_bitplanes: u16,
    pub tier1_style: Tier1CodingStyle,
}

struct CodeBlockHeaderSegments {
    segment_passes: [u8; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
    segment_lengths: [u32; MAX_CODE_BLOCK_SEGMENTS_PER_CONTRIBUTION],
    segment_count: usize,
    accounted_passes: u32,
    data_length: u32,
    routing: Option<bool>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct TagTreeNode {
    low: u32,
    value: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
struct TagTreeLevel {
    offset: usize,
    width: u32,
    height: u32,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TagTree {
    levels: Vec<TagTreeLevel>,
    nodes: Vec<TagTreeNode>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) struct TagTreeCopyPath {
    pub subband: usize,
    pub zero: bool,
}

#[derive(Clone, Copy)]
struct TagTreePath {
    nodes: [usize; 64],
    length: usize,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct TagTreeValue {
    pub value: Option<u32>,
    pub is_below_threshold: bool,
}

#[cfg(test)]
pub(crate) fn exact_packet_precinct_snapshot(value: &PacketPrecinctDecoder) -> String {
    let subbands = value
        .subbands
        .iter()
        .map(|s| {
            (
                s.orientation,
                s.first_decoder,
                s.decoder_count,
                s.code_blocks_across,
                s.code_blocks_down,
                &s.inclusion_tree,
                &s.zero_bitplane_tree,
            )
        })
        .collect::<Vec<_>>();
    format!(
        "{:?}",
        (
            value.component,
            value.resolution,
            value.precinct,
            &value.states,
            &value.contexts,
            &value.decoders,
            subbands
        )
    )
}

#[cfg(verus_keep_ghost)]
include!("packet/proof_support.rs");

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod bit_reader;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use bit_reader::{
    packet_reader_from_input, packet_reader_new, packet_reader_prefix,
    packet_reader_prefix_from_input,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod body;
pub use body::decode_code_block_contribution_body;
#[cfg(test)]
use body::{
    decode_code_block_contribution_body_staged, decode_ht_segment_body,
    decode_legacy_code_block_contribution_body, decode_legacy_code_block_segment,
    execute_packet_body_contributions, preflight_packet_body_ranges,
    prepare_code_block_contribution_body,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod contributions;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use contributions::code_block_packet_state_new;
pub use contributions::decode_code_block_contribution;
#[cfg(test)]
use contributions::{
    commit_header_contribution, floor_log2, header_segments_new, read_header_segment,
    read_header_segment_length, read_new_passes,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod errors;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use errors::packet_reader_error;
#[cfg(test)]
use errors::{
    invalid_packet_header, packet_arithmetic_overflow, packet_invalid_code_block,
    packet_reader_limit,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod multi_packet;
#[cfg(test)]
use multi_packet::read_multi_packet_header_slot;
pub use multi_packet::{decode_multi_code_block_packet, decode_single_code_block_packet};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod precinct;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use precinct::prepare_precinct_contexts;
pub(crate) use precinct::{decode_jpip_precinct_packet, packet_precinct_from_subbands};
#[cfg(test)]
use precinct::{
    decode_jpip_precinct_packet_inner, decode_precinct_contribution_headers,
    decode_precinct_packet, decode_precinct_packet_payload, decode_precinct_packet_payload_prefix,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod progression;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod spatial;
pub(crate) use progression::packet_grid_new_with_selected_resolutions;
#[cfg(test)]
use progression::{decode_window_candidate, window_candidate_count};
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use progression::{
    packet_grid_new_with_component_resolutions, packet_iterator_new,
    progression_packet_iterator_new,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod tag_tree;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use tag_tree::{tag_tree_from_dimensions, tag_tree_new};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod tile;
pub use tile::decode_progression_tile_packets;
#[cfg(test)]
pub(crate) use tile::decode_progression_tile_packets_selected;
#[cfg(test)]
use tile::{
    account_progression_packet, prepare_progression_tile_input, progression_tile_progress_new,
    run_progression_tile_packets,
};
pub(crate) use tile::{
    decode_progression_tile_packets_owned, decode_progression_tile_packets_recover_trailer_selected,
};

#[cfg(test)]
mod tests;
