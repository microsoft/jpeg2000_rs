use crate::{
    DecodeError,
    mq::{MqContextState, MqDecoder},
};

#[cfg(any(test, verus_keep_ghost))]
use crate::{MalformedKind, Resource, ResourceLimits, magnitude::Magnitude};

#[cfg(verus_keep_ghost)]
use crate::transform::SignedMagnitude;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[path = "tier1_ht_tables.rs"]
mod ht_vlc_tables;

#[cfg(verus_keep_ghost)]
use ht_vlc_tables::{HT_VLC_INITIAL, HT_VLC_NON_INITIAL};

const RUN_LENGTH_CONTEXT: usize = 17;
const UNIFORM_CONTEXT: usize = 18;
pub const MAX_TIER1_BITPLANES: u16 = 292;
pub const MAX_TIER1_PASSES: u32 = 874;
const MAX_HT_SCUP: usize = 4_079;
const MAX_HT_CLEANUP_BYTES: usize = 65_534;
const MAX_HT_REFINEMENT_BYTES: usize = 2_046;
const MAX_HT_MAGNITUDE_BITS: u8 = 74;
const MAX_HT_MAGSGN_BITS: u8 = MAX_HT_MAGNITUDE_BITS + 1;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct RawBitReader<'a> {
    input: &'a [u8],
    next_index: usize,
    current_byte: u8,
    bits_remaining: u8,
    marker_padding_count: u64,
    work_units: u64,
    maximum_work_units: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Tier1PassKind {
    SignificancePropagation,
    MagnitudeRefinement,
    Cleanup,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtPassGroup {
    pub cleanup_passes: u8,
    pub refinement_passes: u8,
    pub placeholder_passes: u8,
    pub skipped_bitplanes: u8,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum HtStreamDirection {
    Forward,
    Reverse,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtSubstreamView<'a> {
    bytes: &'a [u8],
    offset: u32,
    direction: HtStreamDirection,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtCleanupSegment<'a> {
    encoded: &'a [u8],
    scup: u16,
    mag_sgn: HtSubstreamView<'a>,
    mel_vlc: HtSubstreamView<'a>,
    mel: HtSubstreamView<'a>,
    vlc: HtSubstreamView<'a>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtBitPosition {
    pub byte: u16,
    pub bit: u8,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtForwardMagSgnReader<'a> {
    input: &'a [u8],
    next_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    current_is_physical: bool,
    previous_was_ff: bool,
    physical_bits_read: u64,
    fill_bits_read: u64,
    work_units: u64,
    maximum_work_units: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtMelBitReader<'a> {
    input: &'a [u8],
    next_byte: usize,
    current_byte: usize,
    value: u8,
    next_bit: i8,
    previous_was_ff: bool,
    bits_read: u64,
    maximum_work_units: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtReverseVlcReader<'a> {
    input: &'a [u8],
    current_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    later_byte_requires_unstuffing: bool,
    bits_read: u64,
    maximum_work_units: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtQuadMetadata {
    pub x: u16,
    pub y: u16,
    pub context: u8,
    pub initial_row: bool,
    pub significance: u8,
    /// Values of the embedded leading bits (e_1), one flag per sample.
    pub embedded_magnitude: u8,
    /// Flags selecting omitted leading bits (e_k), one flag per sample.
    pub embedded_bit_mask: u8,
    pub u_offset: bool,
    pub u_base: u8,
    pub codeword_bits: u8,
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
pub struct HtCleanupMetadata {
    pub width: u16,
    pub height: u16,
    pub quads: Vec<HtQuadMetadata>,
    pub significant_samples: u16,
    pub mel_bits: u32,
    pub vlc_bits: u32,
    pub mel_events: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtRefinementSegment<'a> {
    encoded: &'a [u8],
    significance_propagation: HtSubstreamView<'a>,
    magnitude_refinement: HtSubstreamView<'a>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtForwardRefinementReader<'a> {
    input: &'a [u8],
    next_byte: usize,
    current_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    previous_was_ff: bool,
    physical_bits_read: u64,
    fill_bits_read: u64,
    maximum_work_units: u64,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtReverseRefinementReader<'a> {
    input: &'a [u8],
    current_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    later_requires_unstuffing: bool,
    physical_bits_read: u64,
    fill_bits_read: u64,
    maximum_work_units: u64,
}

struct HtRefinementReaders<'a> {
    forward: HtForwardRefinementReader<'a>,
    reverse: Option<HtReverseRefinementReader<'a>>,
    claimed: Vec<u8>,
    stuffed: Vec<u8>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtBlockSegments<'a> {
    cleanup: HtCleanupSegment<'a>,
    refinement: Option<HtRefinementSegment<'a>>,
    bytes: u32,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1CodingStyle {
    pub block_coding: Tier1BlockCoding,
    pub force_high_throughput: bool,
    pub selective_arithmetic_coding_bypass: bool,
    pub reset_contexts: bool,
    pub terminate_all_passes: bool,
    pub vertical_causal_context: bool,
    pub predictable_termination: bool,
    pub segmentation_symbols: bool,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Tier1BlockCoding {
    #[default]
    Legacy,
    HighThroughput,
    Mixed,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Tier1CodingMode {
    Mq,
    Raw,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1PassPlan {
    pub kind: Tier1PassKind,
    pub coding_mode: Tier1CodingMode,
    pub terminates_segment: bool,
    pub reset_contexts_after_pass: bool,
    pub validate_predictable_termination: bool,
    pub expect_segmentation_symbol: bool,
}

struct HtCleanupReaders<'a> {
    mel: HtMelBitReader<'a>,
    vlc: HtReverseVlcReader<'a>,
    mel_last_byte: Option<u16>,
    vlc_last_byte: Option<u16>,
    terminal_byte: u16,
    mel_state: u8,
    mel_zero_events: u8,
    mel_terminating_one: bool,
    mel_events: u32,
    work_units: u64,
    maximum_work_units: u64,
}

struct HtCleanupPlaneReconstruction<'a> {
    output: CodeBlockPlane,
    reader: HtForwardMagSgnReader<'a>,
    previous_exponents: Vec<u8>,
    current_exponents: Vec<u8>,
    statistics: Tier1PassStatistics,
}

struct HtRefinementPlaneState<'a> {
    output: CodeBlockPlane,
    readers: HtRefinementReaders<'a>,
    cleanup_significant: Vec<bool>,
    statistics: Tier1PassStatistics,
}

struct HtSignificancePatchState<'a> {
    core: HtRefinementPlaneState<'a>,
    discovery: CodeBlockPlane,
    pending: Vec<(u16, u16)>,
}

struct HtSigpropPlaneState<'a> {
    core: HtRefinementPlaneState<'a>,
    discovery: CodeBlockPlane,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockSegmentAccounting {
    maximum_passes: u32,
    maximum_bytes: u64,
    total_passes: u32,
    total_bytes: u64,
    segments: u32,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CoefficientState {
    /// Decoded magnitude bits; unfinished legacy passes retain a bit prefix.
    pub magnitude: u64,
    magnitude_high: [u64; 5],
    legacy_bitplane: Option<u16>,
    pub negative: bool,
    pub significant: bool,
    pub refined: bool,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct NeighborSummary {
    pub horizontal_significant: u8,
    pub vertical_significant: u8,
    pub diagonal_significant: u8,
    pub horizontal_sign_balance: i8,
    pub vertical_sign_balance: i8,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum SubbandOrientation {
    Ll,
    Lh,
    Hl,
    Hh,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct SignContext {
    pub context: u8,
    pub predicted_negative: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct SignificanceStep {
    pub zero_coding_context: u8,
    pub sign_context: Option<u8>,
    pub became_significant: bool,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1BitplaneState {
    width: u16,
    height: u16,
    bitplane: u16,
    significant_before: Vec<bool>,
    significance_visited: Vec<bool>,
    significance_propagation_complete: bool,
    magnitude_refinement_complete: bool,
    cleanup_complete: bool,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1PassStatistics {
    pub coefficients_scanned: u32,
    pub coding_symbols: u32,
    pub newly_significant: u32,
    pub refined_coefficients: u32,
    pub run_mode_columns: u32,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1SegmentDecode {
    pub passes: u32,
    pub bytes: u32,
    pub statistics: Tier1PassStatistics,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
struct LegacySegmentState {
    plane: CodeBlockPlane,
    next_pass: u32,
    bitplane: u16,
    bitplane_state: Option<Tier1BitplaneState>,
    mq_context_state: Option<MqContextState>,
    reset_contexts_before_mq: bool,
    decoded_segments: u32,
    decoded_bytes: u64,
    input: Vec<u8>,
    passes: u32,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct Tier1CodeBlockDecoder {
    plane: CodeBlockPlane,
    private_plan: bool,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
    maximum_passes: u32,
    next_pass: u32,
    bitplane: u16,
    zero_bitplanes: Option<u16>,
    bitplane_state: Option<Tier1BitplaneState>,
    mq_context_state: Option<MqContextState>,
    reset_contexts_before_mq: bool,
    decoded_segments: u32,
    decoded_bytes: u64,
    legacy_segment: Option<LegacySegmentState>,
    legacy_decode_work: u64,
    ht_cleanup_plane: Option<ht_checkpoint::HtCleanupCheckpoint>,
    ht_refinement_data: Vec<u8>,
    ht_refinement_passes: u8,
    ht_decoded_bitplanes: u16,
    ht_current_set_has_cleanup: bool,
    ht_sets_seen: u16,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
}

trait Tier1SymbolDecoder {
    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn symbols_view(&self) -> crate::specs::Part1LegacySymbols;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, final(self).symbols_view()) == crate::specs::part1_legacy_symbol(
            old(self).symbols_view(), context),
    ))]
    fn decode(&mut self, context: usize) -> Result<bool, DecodeError>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == (self.symbols_view() is Raw),
    ))]
    fn is_raw(&self) -> bool;
}

impl Tier1SymbolDecoder for MqDecoder<'_> {
    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn symbols_view(&self) -> crate::specs::Part1LegacySymbols {
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(self))
        }
    }

    fn decode(&mut self, context: usize) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_symbol); }
        MqDecoder::decode(self, context)
    }

    fn is_raw(&self) -> bool {
        false
    }
}

impl Tier1SymbolDecoder for RawBitReader<'_> {
    #[cfg(verus_keep_ghost)]
    verus! {
        spec fn symbols_view(&self) -> crate::specs::Part1LegacySymbols {
            crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(self))
        }
    }

    fn decode(&mut self, _context: usize) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_symbol); }
        self.read_bit()
    }

    fn is_raw(&self) -> bool {
        true
    }
}

#[derive(Clone, Copy)]
enum NeighborKind {
    Horizontal,
    Vertical,
    Diagonal,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockPlane {
    width: u16,
    height: u16,
    coefficients: Vec<CoefficientState>,
}

#[cfg(test)]
pub(crate) type ExtractionTestCoefficient = (u64, [u64; 5], bool, bool, Option<u16>);

#[cfg(test)]
pub(crate) fn extraction_test_plane(
    width: u16,
    height: u16,
    input: &[ExtractionTestCoefficient],
) -> CodeBlockPlane {
    CodeBlockPlane {
        width,
        height,
        coefficients: input
            .iter()
            .map(
                |(magnitude, high, negative, significant, bitplane)| CoefficientState {
                    magnitude: *magnitude,
                    magnitude_high: *high,
                    legacy_bitplane: *bitplane,
                    negative: *negative,
                    significant: *significant,
                    refined: false,
                },
            )
            .collect(),
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) enum CoefficientStorageRole {
    InitialDecoder,
    Standalone,
    #[cfg(test)]
    Duplicate,
    CleanupOutput,
    CleanupCopy,
    RefinementOutput,
    RefinementDiscovery,
    PrivatePrimaryOutput,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) enum HtRefinementCopyRole {
    HtStaging,
    PacketStaging,
    RetainedReplay,
    CleanupRetention,
    LegacySnapshot,
    LegacyRestore,
}

#[cfg(verus_keep_ghost)]
include!("tier1/proof_support.rs");

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod coding;
pub use coding::pass_kind;
pub(crate) use coding::tier1_block_coding_from_code_block_style;
pub(crate) use coding::tier1_coding_style_from_code_block_style;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod contributions;
#[cfg(test)]
pub(crate) use contributions::tier1_configured_decoder;
pub(crate) use contributions::tier1_configured_decoder_with_checkpoint;
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use contributions::tier1_decoder_from_dimensions;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_cleanup;
pub use ht_cleanup::complete_ht_kappa;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_checkpoint;
pub(crate) use ht_checkpoint::PrivatePrimarySlices;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod private_ht;
#[cfg(test)]
pub(crate) use private_ht::extraction_test_private_decoder;
#[cfg(verus_keep_ghost)]
pub(crate) use private_ht::private_decoder_outcome;
pub(crate) use private_ht::{PrivateHtDecoder, new_private_ht_decoder};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_cleanup_readers;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_contributions;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_metadata;
pub use ht_metadata::decode_ht_cleanup_metadata;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_refinement;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_refinement_readers;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod ht_segments;
pub use ht_segments::parse_ht_block_segments;
mod compact_legacy;
pub(crate) use compact_legacy::{
    compact_word_reconstructed_magnitude, compact_word_reconstructed_negative,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod legacy_passes;
pub use legacy_passes::decode_cleanup_pass;
pub use legacy_passes::decode_cleanup_pass_with_style;
pub use legacy_passes::decode_magnitude_refinement_pass;
pub use legacy_passes::decode_magnitude_refinement_pass_with_style;
pub use legacy_passes::decode_raw_magnitude_refinement_pass;
pub use legacy_passes::decode_raw_significance_propagation_pass;
pub use legacy_passes::decode_significance_propagation_pass;
pub use legacy_passes::decode_significance_propagation_pass_with_style;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod legacy_segments;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod raw;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod state;
#[cfg(test)]
use coding::legacy_maximum_passes;
#[cfg(test)]
use contributions::legacy_contribution_work;
#[cfg(test)]
use ht_cleanup::{
    center_ht_numeric_magnitude, reconstruct_ht_cleanup_plane, reconstruct_ht_magnitude,
};
#[cfg(test)]
use ht_cleanup_readers::{ht_cleanup_readers_from_inputs, ht_uvlc_byte};
#[cfg(test)]
use ht_metadata::{
    append_ht_metadata_quad, decode_ht_cleanup_segment_metadata, decode_ht_metadata_row,
    decode_ht_metadata_words,
};
#[cfg(test)]
use ht_refinement::{ht_collect_cleanup_significance, run_ht_significance_pass};
#[cfg(test)]
use ht_refinement_readers::ht_refinement_readers_from_inputs;
#[cfg(test)]
use legacy_passes::{decode_cleanup, legacy_bitplane_from_plane};
#[cfg(test)]
use raw::raw_reader_from_input;
pub use state::apply_significance_decision;
pub use state::initialize_tier1_contexts;
pub use state::magnitude_refinement_context;
pub use state::reset_tier1_contexts_after_pass;
pub use state::sign_context;
pub use state::zero_coding_context;
#[cfg(test)]
use state::{arithmetic_overflow, invalid_code_block};

#[cfg(test)]
mod tests;
