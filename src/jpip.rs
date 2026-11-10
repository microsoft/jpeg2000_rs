//! Bounded JPIP message parsing, deterministic data-bin reassembly, and
//! automatic or caller-planned precinct quality reconstruction.
//!
//! This proof-of-concept profile accepts the standard binary message-header
//! forms with inherited, explicit-class, or explicit-class-and-codestream
//! identifiers. It reassembles classes 0 through 8 and can reconstruct a
//! bounded multi-tile packet/codestream views from explicit packet ranges or
//! SIZ/COD/COC-derived precinct mappings across every progression order.
//! It does not implement cache signaling, transport, request generation,
//! authentication, server behavior, or TLS.

use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const MAX_VBAS_BYTES: usize = 10;
const SOC: [u8; 2] = [0xff, 0x4f];
const EOC: [u8; 2] = [0xff, 0xd9];

#[cfg(verus_keep_ghost)]
include!("jpip/proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("jpip/cache_proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("jpip/range_proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("jpip/plan_proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("jpip/progression_proof_support.rs");
#[cfg(verus_keep_ghost)]
include!("jpip/transition_proof_support.rs");

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq, Hash))]
#[non_exhaustive]
pub enum DatabinClass {
    Precinct,
    TileHeader,
    TileData,
    MainHeader,
    Metadata,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq, Hash))]
pub struct DatabinId {
    class_identifier: u64,
    class: DatabinClass,
    codestream: u64,
    in_class: u64,
}

/// Committed message history. Absent inherited fields decode as zero until a
/// complete data message commits them; construction and EOR retain absence.
#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipHeaderContext {
    previous_class: Option<u64>,
    previous_codestream: Option<u64>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipMessageHeader {
    databin: DatabinId,
    offset: u64,
    length: u64,
    last_byte: bool,
    auxiliary: Option<u64>,
    header_length: usize,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipEndOfResponse<'a> {
    reason_code: u8,
    body: &'a [u8],
    header_length: usize,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum JpipMessage<'a> {
    Data {
        header: JpipMessageHeader,
        body: &'a [u8],
    },
    EndOfResponse(JpipEndOfResponse<'a>),
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipMessageParser {
    context: JpipHeaderContext,
    limits: ResourceLimits,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipFragment {
    databin: DatabinId,
    offset: u64,
    bytes: Vec<u8>,
    final_length: Option<u64>,
    auxiliary: Option<u64>,
}

struct StoredFragment {
    offset: u64,
    bytes: Vec<u8>,
}

impl Clone for StoredFragment {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_stored_fragment_view(&result) == jpip_stored_fragment_view(self),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_stored_fragment_view); }
        Self {
            offset: self.offset,
            bytes: self.bytes.clone(),
        }
    }
}

struct Databin {
    id: DatabinId,
    fragments: Vec<StoredFragment>,
    final_length: Option<u64>,
}

impl Clone for Databin {
    // Retain the derived implementation's field-clone calls and their order.
    #[allow(clippy::clone_on_copy)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_databin_view(&result) == jpip_databin_view(self),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_databin_view); }
        Self {
            id: self.id.clone(),
            fragments: self.fragments.clone(),
            final_length: self.final_length.clone(),
        }
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DatabinStatus {
    final_length: Option<u64>,
    contiguous_prefix: u64,
    stored_bytes: u64,
    intervals: u64,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipByteView {
    bytes: Vec<u8>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipDatabinRange {
    databin: DatabinId,
    offset: u64,
    length: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipMissingRange {
    databin: DatabinId,
    offset: u64,
    length: Option<u64>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum JpipAvailability {
    Missing,
    Partial,
    Available,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipAvailabilityReport {
    status: JpipAvailability,
    required_bytes: u64,
    available_bytes: u64,
    missing: Vec<JpipMissingRange>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipPrecinctPacket {
    range: JpipDatabinRange,
    layer: u16,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipPrecinctCodestreamPlan {
    main_header: DatabinId,
    tile_header: DatabinId,
    packets: Vec<JpipPrecinctPacket>,
    layer_ends: Vec<usize>,
}

pub struct JpipPrecinctTranscode {
    layers: u16,
    availability: JpipAvailabilityReport,
    codestream: Option<JpipByteView>,
}

pub struct JpipPrecinctPackets {
    layers: u16,
    availability: JpipAvailabilityReport,
    packets: Option<JpipByteView>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum JpipProgressiveStatus {
    WaitingForData,
    QualityAdvanced,
    Complete,
}

pub struct JpipProgressiveUpdate {
    status: JpipProgressiveStatus,
    previous_layers: u16,
    available_layers: u16,
    missing: Vec<JpipMissingRange>,
    image: Option<crate::image::TypedImage>,
}

pub struct JpipProgressiveDecoder {
    plan: JpipPrecinctCodestreamPlan,
    decoded_layers: u16,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipPrecinctCoordinate {
    pub tile: u16,
    pub component: u16,
    pub resolution: u8,
    pub precinct: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipPrecinctMapping {
    databin: DatabinId,
    coordinate: JpipPrecinctCoordinate,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipPrecinctMap {
    codestream: u64,
    mappings: Vec<JpipPrecinctMapping>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum JpipSemanticNeedKind {
    MetadataBin,
    Codestream,
    TilePartTransition,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipSemanticNeed {
    kind: JpipSemanticNeedKind,
    identifier: u64,
}

pub struct JpipContainerAssembly {
    status: JpipAvailability,
    missing: Vec<JpipMissingRange>,
    needs: Vec<JpipSemanticNeed>,
    container: Option<JpipByteView>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipTilePartTransition {
    tile: u16,
    tile_part: u8,
    packet_count: Option<u64>,
    data_length: Option<u64>,
    functional: bool,
    header: Vec<u8>,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipTilePartTransitionReport {
    status: JpipAvailability,
    transitions: Vec<JpipTilePartTransition>,
    needs: Vec<JpipSemanticNeed>,
    missing: Vec<JpipMissingRange>,
}

#[derive(Clone, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipPacketSelection {
    components: Vec<u16>,
}

pub struct JpipAutomaticProgressiveDecoder {
    codestream: u64,
    decoded_layers: u16,
}

struct AutomaticSnapshotResult {
    ready: Option<AutomaticSnapshot>,
    missing: Vec<JpipMissingRange>,
}

struct AutomaticSnapshot {
    codestream: JpipByteView,
    available_layers: u16,
    layers: u16,
    missing: Vec<JpipMissingRange>,
}

struct AutomaticPacket {
    databin: DatabinId,
    bytes: Option<Vec<u8>>,
    next_offset: u64,
    required: bool,
    ordinal: u16,
    layer: u16,
}

struct AutomaticTile {
    parts: Vec<AutomaticTilePart>,
}

struct AutomaticTilePart {
    header: Vec<u8>,
    packets: Vec<AutomaticPacket>,
    sop: bool,
    eph: bool,
}

struct AutomaticHeaders {
    main: Vec<u8>,
    tiles: Vec<Vec<u8>>,
    tile_count: u64,
    components: u16,
}

pub struct DatabinCache {
    limits: ResourceLimits,
    databins: Vec<Databin>,
    stored_bytes: u64,
    accepted_fragments: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct JpipResponseSummary {
    messages: u64,
    end_of_response_reason: Option<u8>,
}

struct JpipPlaceholder {
    flags: u32,
    bin: u64,
    original_header: Vec<u8>,
    original_type: crate::jp2::BoxType,
    equivalent_bin: Option<u64>,
    equivalent_header: Option<Vec<u8>>,
    equivalent_type: Option<crate::jp2::BoxType>,
    stream: Option<u64>,
    stream_count: u32,
}

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod automatic_headers;
use automatic_headers::{
    append_empty_packet, automatic_tile_part, build_automatic_template,
    build_automatic_transition_template, ceil_div_jpip, marker_segment,
    normalize_automatic_tile_headers, normalize_main_header, partition_automatic_tile_parts,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod byte_io;
use byte_io::{read_u16_be, read_u32_be, read_u64_be, write_u32_be, write_u64_be};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod cache;
use cache::copy_bytes;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod mapping;
use mapping::{
    automatic_precinct_in_class, jpip_resolution_selected, jpip_tile_selected,
    parse_tile_part_transitions, siz_cardinality, validate_packet_component_selection,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod message;
pub use message::{ingest_jpip_response, parse_jpip_message};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod precinct;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod progression;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ranges;
use ranges::append_missing_ranges;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod reconstruction;
#[cfg(test)]
use reconstruction::parse_jpip_placeholder;
#[cfg(test)]
mod cache_layout_result_tests;
#[cfg(test)]
mod range_result_tests;
#[cfg(test)]
mod response_result_tests;
#[cfg(test)]
mod tests;
