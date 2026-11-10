use vstd::prelude::*;

use crate::proofs::shared::{CursorView, DatabinView};
use crate::specs::{
    ads_payload_bytes, atk_reconstruction_step, atk_update_parity, bounded_jpip_transcode,
    bounded_loop_frame, clipped_composition_extent, codestream_count_within_limit,
    complete_jpip_range, component_index_width, composition_instruction_work,
    composition_output_bytes, consistent_jpip_final_length, consistent_part15_signaling,
    decomposition_graph_cardinality, decomposition_stage_subbands, disjoint_ht_refinement_claims,
    effective_component_override, effective_jpx_layer_count, ht_cleanup_byte_claims_valid,
    ht_completed_u, ht_kappa_extension, ht_placeholder_passes, ht_quad_count,
    ht_substantive_passes, jpip_packet_boundary_exact, jpip_packet_boundary_step,
    jpip_precinct_in_class, jpip_quality_prefix_available, jpip_ranges_overlap,
    jpip_reconstructed_box_length, jpip_tile_transition_sufficient, magnitude_addition,
    magnitude_less, magnitude_limb_index, magnitude_limb_offset, magnitude_shift_fits,
    maxshift_restored_magnitude, nested_metadata_work, packed_header_index_continuous,
    packed_packet_length_matches, packet_length_index_continuous, packet_length_step,
    packet_lengths_cover_payload, palette_linear_index, poc_contains, ppm_frame_fits, region_fits,
    registered_channel_count, registered_sample_numerator, resampled_component_coordinate,
    signed_color_to_nominal, tile_transform_scope, valid_cbd_scope, valid_channel_association,
    valid_codestream_header_associations, valid_color_sample, valid_component_mapping,
    valid_component_override_index, valid_decomposition_direction, valid_ht_cleanup_partition,
    valid_ht_pass_group, valid_ht_quad_origin, valid_ht_refinement_segment, valid_ht_style_prefix,
    valid_jp2_primary_brand, valid_jph_branding, valid_jpip_codestream_layout, valid_jpip_fragment,
    valid_jpip_precinct_coordinate, valid_jpip_progressive_update,
    valid_layer_codestream_reference, valid_magnitude_bit, valid_maxshift_roi,
    valid_mct_array_reference, valid_mct_collection_count, valid_mct_dimensions,
    valid_mct_matrix_bounds, valid_mct_stage_edge, valid_palette_lookup, valid_part15_block_mode,
    valid_poc_record, valid_selected_codestream_index, valid_selection_region,
    valid_signed_color_sample, work_within_limit,
};

verus! {

#[verifier::spinoff_prover]
pub proof fn ht_staged_group_every_failure_preserves_complete_original_decoder(
    state: crate::specs::Tier1DecoderState, input: Seq<u8>, passes: u8,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
)
    ensures crate::specs::ht_decode_staged_group(state, input, passes, pass_limit, byte_limit, work_limit).0.is_err()
        ==> crate::specs::ht_decode_staged_group(state, input, passes, pass_limit, byte_limit, work_limit).1 == state,
{
}

#[verifier::spinoff_prover]
pub proof fn ht_staged_group_success_reports_original_packet_pass_count(
    state: crate::specs::Tier1DecoderState, input: Seq<u8>, passes: u8,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
)
    ensures match crate::specs::ht_decode_staged_group(state, input, passes, pass_limit, byte_limit, work_limit).0 {
        Err(_) => true, Ok(result) => result.passes == passes as u32,
    },
{
}

pub proof fn ht_group_route_uses_retained_option_not_current_cleanup_flag(state: crate::specs::Tier1DecoderState)
    requires matches!(state.style.block_coding, crate::tier1::Tier1BlockCoding::Mixed),
        state.ht_cleanup_plane.is_some(),
    ensures crate::specs::ht_group_route(state),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_continuation_first_accounting_overflow_preserves_already_prepared_state(
    state: crate::specs::Tier1DecoderState, passes: u8, bytes: nat, next_bytes: u64,
    statistics: crate::tier1::Tier1PassStatistics, replayed: bool,
)
    requires state.next_pass as nat + passes as nat > u32::MAX,
    ensures crate::specs::ht_finish_refinement_contribution(state, passes, bytes, next_bytes, statistics, replayed)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_continuation_segment_overflow_keeps_pass_but_not_byte_update(
    state: crate::specs::Tier1DecoderState, passes: u8, bytes: nat, next_bytes: u64,
    statistics: crate::tier1::Tier1PassStatistics, replayed: bool,
)
    requires state.next_pass as nat + passes as nat <= u32::MAX, state.decoded_segments == u32::MAX,
    ensures crate::specs::ht_finish_refinement_contribution(state, passes, bytes, next_bytes, statistics, replayed)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
            crate::specs::Tier1DecoderState { next_pass: (state.next_pass + passes) as u32, ..state }),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_placeholder_preserves_output_and_retained_cleanup_on_every_return(
    state: crate::specs::Tier1DecoderState, passes: u8, maximum_passes: u32,
)
    ensures crate::specs::ht_skip_segment(state, passes, maximum_passes).1.plane == state.plane,
        crate::specs::ht_skip_segment(state, passes, maximum_passes).1.ht_cleanup_plane == state.ht_cleanup_plane,
        crate::specs::ht_skip_segment(state, passes, maximum_passes).1.decoded_bytes == state.decoded_bytes,
{
}

#[verifier::spinoff_prover]
pub proof fn ht_refinement_reset_frames_all_unrelated_decoder_fields(state: crate::specs::Tier1DecoderState)
    ensures crate::specs::ht_clear_refinement_state(state) == (crate::specs::Tier1DecoderState {
        ht_refinement_data: Seq::empty(), ht_refinement_passes: 0, ..state
    }),
{
}

pub proof fn standard_prepare_preserves_complete_plan_metadata(
    plan: crate::specs::Part1PreparePlan, precincts: Seq<Seq<crate::specs::Tier1RawPlane>>,
    style: crate::specs::Part1PrepareStyle, maximum: u64,
)
    ensures match crate::specs::part1_prepare_standard_component(plan, precincts, style, maximum) {
        Err(_) => true,
        Ok(prepared) => prepared.0 == plan.component && prepared.1 == plan.x && prepared.2 == plan.y
            && prepared.3 == plan.width && prepared.4 == plan.height
            && prepared.5 == if matches!(style.0, crate::codestream::WaveletTransform::Reversible5x3) { 0u8 } else { 16u8 },
    },
{
    reveal(crate::specs::part1_prepare_standard_component);
    reveal(crate::specs::part2_prepare_component);
}

pub proof fn decoded_signed_prefix_has_complete_length(samples: Seq<i64>, fraction: u8, precision: u8, count: nat)
    ensures match crate::specs::part1_decoded_signed_prefix(samples, fraction, precision, count) {
        Ok(values) => values.len() == count, Err(_) => true,
    },
    decreases count,
{
    reveal_with_fuel(crate::specs::part1_decoded_signed_prefix, 1);
    if count > 0 { decoded_signed_prefix_has_complete_length(samples, fraction, precision, (count - 1) as nat); }
}

pub proof fn decoded_unsigned_prefix_has_complete_length(samples: Seq<i64>, fraction: u8, precision: u8, count: nat)
    ensures match crate::specs::part1_decoded_unsigned_prefix(samples, fraction, precision, count) {
        Ok(values) => values.len() == count, Err(_) => true,
    },
    decreases count,
{
    reveal_with_fuel(crate::specs::part1_decoded_unsigned_prefix, 1);
    if count > 0 { decoded_unsigned_prefix_has_complete_length(samples, fraction, precision, (count - 1) as nat); }
}

pub proof fn decoded_typed_component_preserves_kind_and_complete_length(component: crate::specs::Part1DecodedComponentModel, maximum: u64)
    ensures match crate::specs::part1_decoded_component_typed_samples(component, maximum) {
        Ok(crate::specs::Part1TypedSampleSequence::Signed(values)) => component.2.signed && values.len() == component.4.len(),
        Ok(crate::specs::Part1TypedSampleSequence::Unsigned(values)) => !component.2.signed && values.len() == component.4.len(),
        Err(_) => true,
    },
{
    decoded_signed_prefix_has_complete_length(component.4, component.3, component.2.precision, component.4.len());
    decoded_unsigned_prefix_has_complete_length(component.4, component.3, component.2.precision, component.4.len());
}

#[verifier::spinoff_prover]
pub proof fn ht_full_refinement_rejects_front_parameters_before_any_plane_or_stream(
    plane: crate::specs::Tier1RawPlane, segment: crate::specs::HtRefinementSegmentState,
    passes: u8, planes: u16, causal: bool, work: u64,
)
    requires segment.encoded.len() <= usize::MAX, passes == 0 || passes > 2 || planes < 2,
    ensures crate::specs::ht_refinement_plane(plane, segment, passes, planes, causal, work)
        == Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_delayed_signs_preserve_discovery_and_pending_on_every_return(
    state: crate::specs::HtSignificancePatchState, index: nat, magnitude: (Seq<u64>, nat),
)
    ensures crate::specs::ht_patch_sign_sample(state, index, magnitude).1.discovery == state.discovery,
        crate::specs::ht_patch_sign_sample(state, index, magnitude).1.pending == state.pending,
{
}

#[verifier::spinoff_prover]
pub proof fn ht_neighbor_balance_overflow_keeps_the_prior_count_increment(state: crate::tier1::NeighborSummary)
    requires state.horizontal_significant < u8::MAX, state.horizontal_sign_balance == i8::MAX,
    ensures crate::specs::ht_neighbor_update(state, 0, false)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
            crate::tier1::NeighborSummary { horizontal_significant: (state.horizontal_significant + 1) as u8, ..state }),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_complete_symbol_model_preserves_the_frozen_cleanup_only_profile(
    state: crate::specs::Tier1DecoderState, segments: crate::specs::HtBlockSegmentsState,
    passes: u32, maximum_u: u8, skipped: u16, work: u64,
)
    requires segments.refinement.is_none(),
    ensures crate::specs::ht_coefficient_symbols(state, segments, passes, maximum_u, skipped, work)
        == crate::specs::ht_cleanup_symbols_only(state, segments, passes, maximum_u, skipped, work),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_cleanup_caller_preparation_error_preserves_complete_decoder(
    state: crate::specs::Tier1DecoderState, segments: crate::specs::HtBlockSegmentsState,
    passes: u32, maximum_u: u8, skipped: u16, work: u64,
)
    requires crate::specs::ht_cleanup_prepare(state.plane, segments.cleanup, state.maximum_passes, maximum_u, skipped, work).is_err(),
    ensures crate::specs::ht_cleanup_symbols_only(state, segments, passes, maximum_u, skipped, work).1 == state,
        crate::specs::ht_cleanup_symbols_only(state, segments, passes, maximum_u, skipped, work).0.is_err(),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_cleanup_store_first_counter_overflow_retains_new_planes_and_all_other_fields(
    state: crate::specs::Tier1DecoderState, output: crate::specs::Tier1RawPlane,
    cleanup: crate::specs::Tier1RawPlane, statistics: crate::tier1::Tier1PassStatistics,
    bitplanes: u16, passes: u32, bytes: u32, refinement: bool,
)
    requires state.ht_sets_seen == u16::MAX,
    ensures crate::specs::ht_store_coefficient_symbols(state, output, cleanup, statistics, bitplanes, passes, bytes, refinement)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
            crate::specs::Tier1DecoderState { plane: output, ht_cleanup_plane: Some(cleanup),
                ht_current_set_has_cleanup: true, ht_decoded_bitplanes: bitplanes, ..state }),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_cleanup_store_final_byte_overflow_keeps_earlier_counter_updates(
    state: crate::specs::Tier1DecoderState, output: crate::specs::Tier1RawPlane,
    cleanup: crate::specs::Tier1RawPlane, statistics: crate::tier1::Tier1PassStatistics,
    bitplanes: u16, passes: u32, bytes: u32, refinement: bool,
)
    requires state.ht_sets_seen < u16::MAX, state.next_pass as nat + passes as nat <= u32::MAX,
        state.decoded_segments as nat + (if refinement { 2nat } else { 1nat }) <= u32::MAX,
        state.decoded_bytes as nat + bytes as nat > u64::MAX,
    ensures crate::specs::ht_store_coefficient_symbols(state, output, cleanup, statistics, bitplanes, passes, bytes, refinement)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
            crate::specs::Tier1DecoderState { plane: output, ht_cleanup_plane: Some(cleanup),
                ht_current_set_has_cleanup: true, ht_decoded_bitplanes: bitplanes,
                ht_sets_seen: (state.ht_sets_seen + 1) as u16,
                next_pass: (state.next_pass + passes) as u32,
                decoded_segments: (state.decoded_segments + if refinement { 2int } else { 1int }) as u32, ..state }),
{
}

pub(crate) proof fn tier1_raw_result_interfaces_expose_consumed_fields(
    coefficient: Result<crate::tier1::CoefficientState, crate::DecodeError>,
    signed: Result<crate::transform::SignedMagnitude, crate::DecodeError>,
)
    ensures match coefficient {
        Ok(value) => crate::tier1::coefficient_raw_outcome(coefficient) == Ok(crate::tier1::coefficient_raw_view(value)),
        Err(error) => crate::tier1::coefficient_raw_outcome(coefficient) == Err(error),
    },
    match signed {
        Ok(value) => crate::tier1::coefficient_signed_outcome(signed)
            == Ok((crate::magnitude::magnitude_limbs(value.magnitude),
                crate::magnitude::magnitude_value(value.magnitude), value.negative)),
        Err(error) => crate::tier1::coefficient_signed_outcome(signed) == Err(error),
    },
{
}

#[verifier::spinoff_prover]
pub proof fn ht_plane_zero_metadata_width_precedes_all_other_rejections(
    plane: crate::specs::Tier1RawPlane, cleanup: crate::specs::HtCleanupSegmentState,
    metadata: crate::specs::HtMetadataOutput, maximum_u: u8, bitplanes: u16, work: u64,
)
    requires metadata.width == 0,
    ensures crate::specs::ht_cleanup_plane(plane, cleanup, metadata, maximum_u, bitplanes, work)
        == Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_plane_coordinate_overflow_precedes_scanning_and_reader_errors(
    state: crate::specs::HtPlaneState, quad: crate::tier1::HtQuadMetadata,
    width: u16, height: u16, column: nat, completed_u: u8, bitplanes: u16, sample: u8,
)
    requires sample < 4, column + 1 < state.current.len(),
        quad.x as nat + (sample >> 1) as nat > u16::MAX
            || quad.y as nat + (sample & 1u8) as nat > u16::MAX,
    ensures crate::specs::ht_plane_sample(state, quad, width, height, column, completed_u, bitplanes, sample)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_plane_clipping_does_not_validate_numeric_inputs(
    state: crate::specs::HtPlaneState, quad: crate::tier1::HtQuadMetadata,
    width: u16, height: u16, column: nat, completed_u: u8, bitplanes: u16, sample: u8,
)
    requires sample < 4, column + 1 < state.current.len(),
        quad.x as nat + (sample >> 1) as nat <= u16::MAX,
        quad.y as nat + (sample & 1u8) as nat <= u16::MAX,
        quad.x as nat + (sample >> 1) as nat >= width
            || quad.y as nat + (sample & 1u8) as nat >= height,
    ensures crate::specs::ht_plane_sample(state, quad, width, height, column, completed_u, bitplanes, sample)
        == (Ok(()), state),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_kappa_conservative_overflow_applies_without_gamma(
    base: u8, significance: u8, north_west: u8, north_east: u8, maximum: u8,
)
    requires base > 0, significance & 0xf0u8 == 0, 1 <= maximum <= 75,
        base as nat + (if north_west > north_east { north_west } else { north_east }) as nat > 255,
    ensures crate::specs::ht_complete_kappa(base, significance, north_west, north_east, maximum)
        == Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
{
}

#[verifier::spinoff_prover]
pub proof fn tier1_raw_index_rejects_missing_storage_without_a_rectangular_premise(
    plane: crate::specs::Tier1RawPlane, x: u16, y: u16,
)
    requires x < plane.width, y < plane.height,
        y as nat * plane.width as nat + x as nat <= usize::MAX,
        y as nat * plane.width as nat + x as nat >= plane.coefficients.len(),
    ensures crate::specs::tier1_raw_plane_index(plane, x, y)
        == Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
{
}

#[verifier::spinoff_prover]
pub proof fn tier1_raw_insignificance_ignores_stale_full_words_and_legacy_tags(coefficient: crate::specs::Tier1RawCoefficient)
    requires coefficient.limbs.len() == 6, !coefficient.significant,
    ensures crate::specs::tier1_raw_signed_coefficient(coefficient) == Ok((Seq::new(6, |i: int| 0u64), 0nat, false)),
{
}

pub proof fn ht_numeric_invalid_parameters_preserve_complete_reader(
    reader: crate::specs::HtMagSgnState, completed_u: u8,
    embedded_bit: bool, embedded_value: bool, decoded_bitplanes: u16,
)
    requires completed_u == 0 || completed_u > 75 || decoded_bitplanes == 0 || decoded_bitplanes > 292,
    ensures crate::specs::ht_reconstruct_numeric_magnitude(reader, completed_u, embedded_bit, embedded_value, decoded_bitplanes)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), reader),
{
}

pub proof fn ht_numeric_zero_payload_needs_no_reader_budget(reader: crate::specs::HtMagSgnState)
    ensures crate::specs::ht_reconstruct_numeric_magnitude(reader, 1, true, false, 1)
        == (Ok((1nat, false, 1u8)), reader),
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2_strictly_increases(2, 384);
    crate::proofs::production_impl::production_ht_numeric_payload_unfold(reader, 0, 0, 0, false, 0);
}

#[verifier::spinoff_prover]
pub proof fn ht_metadata_invalid_header_precedes_stream_construction(
    cleanup: crate::specs::HtCleanupSegmentState, width: u16, height: u16, maximum_u: u8, maximum_work: u64,
)
    requires width == 0 || height == 0 || maximum_u == 0 || maximum_u > 75,
    ensures crate::specs::ht_cleanup_segment_metadata(cleanup, width, height, maximum_u, maximum_work)
        == Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_public_metadata_byte_limit_precedes_invalid_dimensions(
    cleanup: Seq<u8>, width: u16, height: u16, maximum_u: u8, maximum_bytes: u64, maximum_work: u64,
)
    requires 2 <= cleanup.len() <= 65534, cleanup.len() > maximum_bytes,
    ensures crate::specs::ht_decode_cleanup_metadata(cleanup, width, height, maximum_u, maximum_bytes, maximum_work)
        == Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::CodeBlockBytes, limit: maximum_bytes, actual: cleanup.len() as u64,
        }),
{
}

#[verifier::spinoff_prover]
pub proof fn ht_metadata_zero_samples_preserve_counter(
    significant: u16, x: u16, y: u16, width: u16, height: u16, sample: u8,
)
    requires sample <= 4, x <= 65534, y <= 65534,
    ensures crate::specs::ht_metadata_samples(significant, 0, x, y, width, height, sample) == (Ok(()), significant),
    decreases 4 - sample,
{
    crate::proofs::production_impl::production_ht_metadata_samples_unfold(significant, 0, x, y, width, height, sample);
    if sample < 4 {
        assert(0u8 & (1u8 << sample) == 0) by(bit_vector) requires sample < 4;
        ht_metadata_zero_samples_preserve_counter(significant, x, y, width, height, (sample + 1) as u8);
    }
}

#[verifier::spinoff_prover]
pub proof fn ht_metadata_quad_tick_overflow_preserves_the_store(
    readers: crate::specs::HtCleanupReaderState, quads: Seq<crate::tier1::HtQuadMetadata>,
    significant: u16, input: crate::specs::HtMetadataQuadInput,
)
    requires input.index < 32768, input.row < 32768, input.significance == 0,
        input.u_value <= input.maximum_u,
        crate::specs::ht_quad_origin_valid(input.index as nat * 2, input.row as nat * 2, input.width as nat, input.height as nat),
        readers.work_units == u64::MAX,
    ensures crate::specs::ht_metadata_emit(readers, quads, significant, input).0
            == Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        crate::specs::ht_metadata_emit(readers, quads, significant, input).1 == readers,
        crate::specs::ht_metadata_emit(readers, quads, significant, input).2.len() == quads.len() + 1,
        crate::specs::ht_metadata_emit(readers, quads, significant, input).3 == significant,
{
    let x = (input.index * 2) as u16;
    let y = (input.row * 2) as u16;
    assert(x as nat == input.index as nat * 2);
    assert(y as nat == input.row as nat * 2);
    ht_metadata_zero_samples_preserve_counter(significant, x, y, input.width, input.height, 0);
}

pub proof fn magnitude_limb_interface_covers_native_indices(value: crate::magnitude::Magnitude, index: usize)
    ensures crate::magnitude::magnitude_limbs(value).len() == 6,
        crate::specs::part1_magnitude_limb(crate::magnitude::magnitude_limbs(value), index).is_some() == (index < 6),
{
    crate::magnitude::representation_proofs::magnitude_limbs_shape(value);
}

pub proof fn ht_partition_budget_failure_precedes_any_scup_validation(
    cleanup: Seq<u8>, refinement: Option<Seq<u8>>, maximum: u64,
)
    requires 2 <= cleanup.len() <= 65534,
        (match refinement { None => 0nat, Some(bytes) => bytes.len() }) <= 2046,
        cleanup.len() + (match refinement { None => 0nat, Some(bytes) => bytes.len() }) > maximum,
    ensures crate::specs::ht_parse_block_segments(cleanup, refinement, maximum)
        == Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::CodeBlockBytes, limit: maximum,
            actual: (cleanup.len() + (match refinement { None => 0nat, Some(bytes) => bytes.len() })) as u64,
        }),
{
}

pub proof fn ht_successful_partition_preserves_optional_refinement_presence(
    cleanup: Seq<u8>, refinement: Option<Seq<u8>>, maximum: u64, result: crate::specs::HtBlockSegmentsState,
)
    requires crate::specs::ht_parse_block_segments(cleanup, refinement, maximum) == Ok(result),
    ensures result.refinement.is_some() == refinement.is_some(),
{
}

pub proof fn ht_packet_group_rejects_the_complete_invalid_native_domain(passes: u8)
    requires passes == 0 || passes > 164,
    ensures crate::specs::ht_packet_pass_group(passes)
        == Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
{
}

pub proof fn color_precision_binary_bounds(precision: u8)
    requires 1 <= precision <= 38,
    ensures
        2 <= (1u64 << precision) <= 274877906944,
        1 <= (1i64 << ((precision - 1) as u8)) <= 137438953472,
{
    assert(2 <= (1u64 << precision) <= 274877906944)
        by(bit_vector) requires 1 <= precision && precision <= 38;
    assert(1 <= (1i64 << ((precision - 1) as u8)) <= 137438953472)
        by(bit_vector) requires 1 <= precision && precision <= 38;
}

pub proof fn ht_uvlc_invalid_modes_leave_complete_state(state: crate::specs::HtCleanupReaderState, mode: u8)
    requires mode >= 5,
    ensures crate::specs::ht_uvlc_initial(state, mode)
            == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
        crate::specs::ht_uvlc_non_initial(state, mode)
            == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
{
}

pub proof fn ht_uvlc_wide_set_bit_is_rejected_after_consumption(
    state: crate::specs::HtCleanupReaderState, changed: crate::specs::HtCleanupReaderState,
    remaining: nat, index: nat, value: u8,
)
    requires remaining > 0, index >= 8, index + remaining <= 255,
        crate::specs::ht_cleanup_reader_read_vlc(state) == (Ok(true), changed),
    ensures crate::specs::ht_uvlc_suffix_run(state, remaining, index, value)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), changed),
{
    crate::proofs::production_impl::production_ht_uvlc_suffix_unfold(state, remaining, index, value);
}

pub proof fn ht_quad_invalid_context_precedes_all_stream_work(
    state: crate::specs::HtCleanupReaderState, table: Seq<u16>, context: u8,
)
    requires context > 7,
    ensures crate::specs::ht_cleanup_quad_word(state, table, context)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
{
}

pub proof fn ht_cleanup_cached_zero_event_precedes_invalid_state_and_counter_overflow(
    state: crate::specs::HtCleanupReaderState,
)
    requires state.mel_zero_events > 0, state.mel_events == u32::MAX,
    ensures crate::specs::ht_cleanup_mel_event(state) == (
        Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        crate::specs::HtCleanupReaderState { mel_zero_events: (state.mel_zero_events - 1) as u8, ..state },
    ),
{
}

pub proof fn ht_cleanup_invalid_uncached_mel_state_does_not_consume(state: crate::specs::HtCleanupReaderState)
    requires state.mel_zero_events == 0, !state.mel_terminating_one, state.mel_state > 12,
    ensures crate::specs::ht_cleanup_mel_event(state)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
{
}

pub proof fn ht_refinement_absent_reverse_preserves_all_state(state: crate::specs::HtRefinementReadersState)
    requires state.reverse.is_none(),
    ensures crate::specs::ht_refinement_read_reverse(state)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
{
}

pub proof fn ht_refinement_duplicate_claim_preserves_both_vectors_and_readers(
    state: crate::specs::HtRefinementReadersState, position: crate::tier1::HtBitPosition,
)
    requires position.bit < 8, position.byte < state.claimed.len(),
        state.claimed[position.byte as int] & (1u8 << position.bit) != 0,
    ensures crate::specs::ht_refinement_claim(state, Some(position))
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
{
}

pub proof fn ht_forward_refinement_sum_overflow_retains_physical_consumption(
    state: crate::specs::HtForwardRefinementState,
)
    requires state.has_byte, state.next_bit <= state.last_bit, state.next_bit < 8,
        state.current_byte < state.input.len(), state.physical_bits_read < u64::MAX,
        state.physical_bits_read + state.fill_bits_read >= u64::MAX,
    ensures crate::specs::ht_forward_refinement_positioned(state) == (
        Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        crate::specs::HtForwardRefinementState {
            next_bit: (state.next_bit + 1) as u8, physical_bits_read: (state.physical_bits_read + 1) as u64, ..state
        },
    ),
{
}

pub proof fn ht_magsgn_selected_counter_overflow_precedes_work(state: crate::specs::HtMagSgnState)
    requires state.has_byte, state.next_bit <= state.last_bit, state.next_bit < 8,
        (if state.current_is_physical { state.physical_bits_read } else { state.fill_bits_read }) == u64::MAX,
    ensures crate::specs::ht_magsgn_read(state) == (
        Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        crate::specs::HtMagSgnState { next_bit: (state.next_bit + 1) as u8, ..state },
    ),
{
}

pub proof fn ht_magsgn_work_overflow_retains_consumed_physical_bit(state: crate::specs::HtMagSgnState)
    requires state.has_byte, state.next_bit <= state.last_bit, state.next_bit < 8,
        state.current_is_physical, state.physical_bits_read < u64::MAX, state.work_units == u64::MAX,
    ensures crate::specs::ht_magsgn_read(state) == (
        Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        crate::specs::HtMagSgnState {
            next_bit: (state.next_bit + 1) as u8, physical_bits_read: (state.physical_bits_read + 1) as u64, ..state
        },
    ),
{
}

pub proof fn ht_reverse_vlc_budget_failure_precedes_eager_load(state: crate::specs::HtReverseVlcState)
    requires state.has_byte, state.next_bit < 8, state.bits_read < u64::MAX,
        state.bits_read >= state.maximum_work_units,
    ensures crate::specs::ht_reverse_vlc_read(state) == (
        Err(crate::specs::ht_reader_work_error(state.maximum_work_units, (state.bits_read + 1) as u64)),
        crate::specs::HtReverseVlcState {
            next_bit: (state.next_bit + 1) as u8, bits_read: (state.bits_read + 1) as u64, ..state
        },
    ),
{
}

pub proof fn ht_cleanup_vlc_collision_does_not_consume(state: crate::specs::HtCleanupReaderState, position: (u16, u8))
    requires crate::specs::ht_reverse_vlc_position(state.vlc) == Some(position),
        !crate::specs::ht_cleanup_reader_can_claim(state, false, position.0),
    ensures crate::specs::ht_cleanup_reader_read_vlc(state)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
{
}

pub proof fn ht_cleanup_outer_budget_failure_retains_inner_bit_and_claim(
    state: crate::specs::HtCleanupReaderState, position: (u16, u8), bit: bool,
    consumed: crate::specs::HtReverseVlcState,
)
    requires crate::specs::ht_reverse_vlc_position(state.vlc) == Some(position),
        crate::specs::ht_cleanup_reader_can_claim(state, false, position.0),
        crate::specs::ht_reverse_vlc_read(state.vlc) == (Ok(bit), consumed),
        state.work_units < u64::MAX, state.work_units >= state.maximum_work_units,
    ensures crate::specs::ht_cleanup_reader_read_vlc(state) == (
        Err(crate::specs::ht_reader_work_error(state.maximum_work_units, (state.work_units + 1) as u64)),
        crate::specs::HtCleanupReaderState {
            vlc: consumed, vlc_last_byte: Some(position.0),
            work_units: (state.work_units + 1) as u64, ..state
        },
    ),
{
}

pub proof fn ht_reverse_vlc_counter_overflow_preserves_advanced_cursor(state: crate::specs::HtReverseVlcState)
    requires state.has_byte, state.next_bit < 8, state.bits_read == u64::MAX,
    ensures crate::specs::ht_reverse_vlc_read(state) == (
        Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        crate::specs::HtReverseVlcState { next_bit: (state.next_bit + 1) as u8, ..state },
    ),
{
}

pub proof fn ht_mel_stuffing_failure_is_atomic(state: crate::specs::HtMelState)
    requires state.next_bit < 0, state.next_byte < state.input.len(),
        state.previous_was_ff, state.input[state.next_byte as int] > 0x8f,
    ensures crate::specs::ht_mel_read(state) == (
        Err(crate::DecodeError::MalformedInput {
            offset: state.next_byte as u64, kind: crate::MalformedKind::InvalidBitStuffing,
        }), state,
    ),
{
    let value = state.input[state.next_byte as int];
    assert((value | 0x0fu8) > 0x8f) by (bit_vector)
        requires value > 0x8f;
}

pub proof fn ht_mel_prefix_first_error_is_absorbing(
    state: crate::specs::HtMelState, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end, crate::specs::ht_mel_prefix(state, count).0 == Err(error),
    ensures crate::specs::ht_mel_prefix(state, end) == crate::specs::ht_mel_prefix(state, count),
    decreases end - count,
{
    if end > count {
        ht_mel_prefix_first_error_is_absorbing(state, count, (end - 1) as nat, error);
        crate::proofs::production_impl::production_ht_mel_prefix_step(state, (end - 1) as nat);
    }
}

pub proof fn ht_reverse_vlc_prefix_first_error_is_absorbing(
    state: crate::specs::HtReverseVlcState, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end, crate::specs::ht_reverse_vlc_prefix(state, count).0 == Err(error),
    ensures crate::specs::ht_reverse_vlc_prefix(state, end) == crate::specs::ht_reverse_vlc_prefix(state, count),
    decreases end - count,
{
    if end > count {
        ht_reverse_vlc_prefix_first_error_is_absorbing(state, count, (end - 1) as nat, error);
        crate::proofs::production_impl::production_ht_reverse_vlc_prefix_step(state, (end - 1) as nat);
    }
}

pub proof fn normalized_composition_domain_matches_binary_width()
    ensures
        crate::specs::PART2_NORMALIZED_SAMPLE_MAX as nat + 1
            == vstd::arithmetic::power2::pow2(crate::specs::PART2_NORMALIZED_SAMPLE_BITS as nat),
        crate::specs::PART2_NORMALIZED_SAMPLE_HALF as nat
            == (crate::specs::PART2_NORMALIZED_SAMPLE_MAX as nat) / 2,
{
    vstd::arithmetic::power2::lemma2_to64();
}

pub proof fn symbolic_source_over_matches_word_normalization(
    source: u16, destination: u16, source_alpha: u16, destination_alpha: u16, premultiplied: bool,
)
    ensures
        crate::specs::part2_source_over_alpha_numerator(source_alpha, destination_alpha)
            == (source_alpha as nat) * 65535
                + (destination_alpha as nat) * ((65535 - source_alpha as int) as nat),
        crate::specs::part2_source_over_color_numerator(source, destination, source_alpha, destination_alpha, premultiplied)
            == (if premultiplied { (source as nat) * 65535 * 65535 }
                else { (source as nat) * (source_alpha as nat) * 65535 })
                + (destination as nat) * (destination_alpha as nat) * ((65535 - source_alpha as int) as nat),
        crate::specs::part2_source_over_alpha_sample(source_alpha, destination_alpha)
            == (crate::specs::part2_source_over_alpha_numerator(source_alpha, destination_alpha) + 32767) / 65535,
{
}

pub proof fn region_end_is_bounded(parent_length: nat, offset: nat, length: nat)
    requires
        region_fits(parent_length, offset, length),
    ensures
        offset + length <= parent_length,
{
}

pub proof fn selected_region_is_nonempty_and_image_bounded(
    image_x0: nat,
    image_y0: nat,
    image_x1: nat,
    image_y1: nat,
    region_x0: nat,
    region_y0: nat,
    region_x1: nat,
    region_y1: nat,
)
    requires
        valid_selection_region(
            image_x0,
            image_y0,
            image_x1,
            image_y1,
            region_x0,
            region_y0,
            region_x1,
            region_y1,
        ),
    ensures
        region_x0 < region_x1,
        region_y0 < region_y1,
        image_x0 <= region_x0,
        region_x1 <= image_x1,
        image_y0 <= region_y0,
        region_y1 <= image_y1,
{
    reveal(valid_selection_region);
}

pub proof fn cursor_remaining_reconstructs_length(view: CursorView)
    requires
        view.invariant(),
    ensures
        view.position + view.remaining() == view.length,
{
}

pub proof fn bounded_work_increment(consumed: nat, amount: nat, limit: nat)
    requires
        work_within_limit(consumed + amount, limit),
    ensures
        work_within_limit(consumed, limit),
        consumed + amount <= limit,
{
}

pub proof fn decomposition_stage_has_bounded_band_count(direction: nat)
    requires
        valid_decomposition_direction(direction),
    ensures
        decomposition_stage_subbands(direction) <= 3,
{
    reveal(valid_decomposition_direction);
    reveal(decomposition_stage_subbands);
}

pub proof fn ads_independent_padding_has_bounded_overhead(depths: nat, splits: nat)
    ensures
        ads_payload_bytes(depths, splits)
            == 3 + (depths + 3) / 4 + (splits + 3) / 4,
{
    reveal(ads_payload_bytes);
    reveal(crate::specs::packed_two_bit_bytes);
}

pub proof fn atk_steps_execute_in_reverse_order(step: nat, steps: nat)
    requires
        step < steps,
    ensures
        atk_reconstruction_step(step, steps) < steps,
{
    reveal(atk_reconstruction_step);
}

pub proof fn atk_update_parity_alternates(initial_odd: bool, reverse_step: nat)
    ensures
        atk_update_parity(initial_odd, reverse_step + 1)
            != atk_update_parity(initial_odd, reverse_step),
{
    reveal(atk_update_parity);
}

pub proof fn cbd_is_main_header_only()
    ensures
        valid_cbd_scope(true),
        !valid_cbd_scope(false),
{
    reveal(valid_cbd_scope);
}

pub proof fn decomposition_graph_count_is_monotonic(
    no_dwt: nat,
    one_axis: nat,
    bidirectional: nat,
)
    ensures
        decomposition_graph_cardinality(no_dwt, one_axis, bidirectional) >= 1,
        decomposition_graph_cardinality(no_dwt, one_axis, bidirectional)
            == 1 + one_axis + 3 * bidirectional,
{
    reveal(decomposition_graph_cardinality);
}

pub proof fn jpip_fragment_end_is_bounded(offset: nat, length: nat, limit: nat)
    requires
        valid_jpip_fragment(offset, length, limit),
    ensures
        offset + length <= limit,
{
    reveal(valid_jpip_fragment);
}

pub proof fn repeated_jpip_final_length_is_unique(existing: nat, announced: nat)
    requires
        consistent_jpip_final_length(existing, announced),
    ensures
        existing == announced,
{
    reveal(consistent_jpip_final_length);
}

pub proof fn jpip_overlap_is_symmetric(
    first_offset: nat,
    first_length: nat,
    second_offset: nat,
    second_length: nat,
)
    ensures
        jpip_ranges_overlap(first_offset, first_length, second_offset, second_length)
            == jpip_ranges_overlap(second_offset, second_length, first_offset, first_length),
{
    reveal(jpip_ranges_overlap);
}

pub proof fn jpip_complete_view_reaches_final_length(view: DatabinView)
    requires
        view.invariant(),
        view.complete(),
    ensures
        view.contiguous_prefix == view.final_length,
{
}

pub proof fn jpip_complete_packet_range_has_no_missing_bytes(available: nat, required: nat)
    requires
        complete_jpip_range(available, required),
    ensures
        available == required,
{
    reveal(complete_jpip_range);
}

pub proof fn jpip_progressive_layer_count_is_bounded(
    previous_layers: nat,
    available_layers: nat,
    planned_layers: nat,
)
    requires
        valid_jpip_progressive_update(previous_layers, available_layers, planned_layers),
    ensures
        previous_layers <= planned_layers,
        available_layers <= planned_layers,
{
    reveal(valid_jpip_progressive_update);
}

pub proof fn jpip_transcode_length_includes_eoc(
    main_header: nat,
    tile_header: nat,
    packet_bytes: nat,
    limit: nat,
)
    requires
        bounded_jpip_transcode(main_header, tile_header, packet_bytes, limit),
    ensures
        main_header + tile_header + packet_bytes + 2 <= limit,
{
    reveal(bounded_jpip_transcode);
}

pub proof fn jpip_precinct_identifier_is_deterministic(
    tile: nat,
    tile_count: nat,
    component: nat,
    components: nat,
    precinct_index: nat,
)
    requires
        valid_jpip_precinct_coordinate(tile, tile_count, component, components),
    ensures
        jpip_precinct_in_class(tile, tile_count, component, components, precinct_index)
            == tile + tile_count * (component + components * precinct_index),
{
    reveal(jpip_precinct_in_class);
}

pub proof fn jpip_quality_prefix_is_monotonic(available: nat, requested: nat)
    requires
        jpip_quality_prefix_available(available, requested),
    ensures
        requested <= available,
{
    reveal(jpip_quality_prefix_available);
}

pub proof fn jpip_metadata_replacement_length_is_deterministic(header: nat, payload: nat)
    ensures
        jpip_reconstructed_box_length(header, payload) == header + payload,
{
    reveal(jpip_reconstructed_box_length);
}

pub proof fn jpip_transition_status_is_precise(
    later_functional: bool,
    preceding_packet_count_known: bool,
    preceding_exact_consumption_known: bool,
)
    ensures
        jpip_tile_transition_sufficient(
            later_functional,
            preceding_packet_count_known,
            preceding_exact_consumption_known,
        ) == (
            !later_functional
            || preceding_packet_count_known
            || preceding_exact_consumption_known
        ),
{
    reveal(jpip_tile_transition_sufficient);
}

pub proof fn jpip_packet_boundary_advance_is_bounded(
    consumed: nat,
    packet_length: nat,
    tile_part_length: nat,
)
    requires
        jpip_packet_boundary_step(consumed, packet_length, tile_part_length),
    ensures
        consumed + packet_length <= tile_part_length,
        jpip_packet_boundary_exact(consumed + packet_length, tile_part_length)
            == (consumed + packet_length == tile_part_length),
{
    reveal(jpip_packet_boundary_step);
    reveal(jpip_packet_boundary_exact);
}

pub proof fn selected_codestream_index_is_bounded(index: nat, codestreams: nat)
    requires
        valid_selected_codestream_index(index, codestreams),
    ensures
        codestreams > 0,
        index < codestreams,
{
}

pub proof fn codestream_header_ordinal_target_is_bounded(
    index: nat,
    headers: nat,
    codestreams: nat,
)
    requires
        index < headers,
        valid_codestream_header_associations(headers, codestreams),
    ensures
        index < codestreams,
{
}

pub proof fn canonical_jph_brand_has_one_zero_version_compatibility()
    ensures
        valid_jph_branding(true, 0, 1, true),
{
}

pub proof fn consistent_part15_profile_binds_all_three_signals(
    rsiz_announces_ht: bool,
    cap_announces_ht: bool,
    style_uses_ht: bool,
    has_corresponding_profile: bool,
)
    requires
        consistent_part15_signaling(
            rsiz_announces_ht,
            cap_announces_ht,
            style_uses_ht,
            has_corresponding_profile,
        ),
    ensures
        rsiz_announces_ht == cap_announces_ht,
        style_uses_ht ==> cap_announces_ht,
        has_corresponding_profile ==> cap_announces_ht,
{
}

pub proof fn part15_rejects_reserved_style_prefix()
    ensures
        !valid_ht_style_prefix(2),
        valid_ht_style_prefix(0),
        valid_ht_style_prefix(1),
        valid_ht_style_prefix(3),
{
}

pub proof fn part15_rejects_reserved_capability_mode()
    ensures
        valid_part15_block_mode(0),
        !valid_part15_block_mode(1),
        valid_part15_block_mode(2),
        valid_part15_block_mode(3),
{
}

pub proof fn valid_ht_cleanup_has_bounded_disjoint_physical_partition(
    cleanup_length: nat,
    scup: nat,
)
    requires
        valid_ht_cleanup_partition(cleanup_length, scup),
    ensures
        scup >= 2,
        scup <= 4079,
        cleanup_length - scup <= cleanup_length,
        cleanup_length - scup + scup == cleanup_length,
{
    reveal(valid_ht_cleanup_partition);
}

pub proof fn ht_cleanup_shared_byte_is_unique(
    mel_byte: nat,
    vlc_byte: nat,
    terminal_byte: nat,
    value: u8,
    shared_a: nat,
    shared_b: nat,
)
    requires
        ht_cleanup_byte_claims_valid(mel_byte, vlc_byte, terminal_byte, value),
        vlc_byte <= shared_a <= mel_byte,
        vlc_byte <= shared_b <= mel_byte,
    ensures
        shared_a == shared_b,
        shared_a < terminal_byte,
        value != 0xff,
{
    reveal(ht_cleanup_byte_claims_valid);
}

pub proof fn valid_ht_quad_origin_is_sample_bounded(
    x: nat,
    y: nat,
    width: nat,
    height: nat,
)
    requires
        valid_ht_quad_origin(x, y, width, height),
    ensures
        x < width,
        y < height,
        x % 2 == 0,
        y % 2 == 0,
{
    reveal(valid_ht_quad_origin);
}

pub proof fn ht_quad_count_is_bounded_by_samples(width: nat, height: nat)
    requires
        width > 0,
        height > 0,
    ensures
        ht_quad_count(width, height) <= width * height,
{
    reveal(ht_quad_count);
    assert((width + 1) / 2 <= width) by (nonlinear_arith);
    assert((height + 1) / 2 <= height) by (nonlinear_arith);
    assert(((width + 1) / 2) * ((height + 1) / 2) <= width * height) by (nonlinear_arith);
}

pub proof fn source_over_numerators_are_bounded(
    source: u16, destination: u16, source_alpha: u16, destination_alpha: u16, premultiplied: bool,
)
    requires
        !premultiplied || source <= source_alpha,
    ensures
        crate::specs::part2_source_over_alpha_numerator(source_alpha, destination_alpha)
            <= 4294836225,
        crate::specs::part2_source_over_color_numerator(
            source, destination, source_alpha, destination_alpha, premultiplied,
        ) <= 65535 * crate::specs::part2_source_over_alpha_numerator(source_alpha, destination_alpha),
{
    let s = source as int;
    let c = destination as int;
    let a = source_alpha as int;
    let d = destination_alpha as int;
    assert(a * 65535 + d * (65535 - a) <= 4294836225) by (nonlinear_arith)
        requires 0 <= a <= 65535, 0 <= d <= 65535,
    {}
    if premultiplied {
        assert(s * 65535 * 65535 + c * d * (65535 - a)
            <= 65535 * (a * 65535 + d * (65535 - a))) by (nonlinear_arith)
            requires 0 <= s <= a <= 65535, 0 <= c <= 65535, 0 <= d <= 65535,
        {}
    } else {
        assert(s * a * 65535 + c * d * (65535 - a)
            <= 65535 * (a * 65535 + d * (65535 - a))) by (nonlinear_arith)
            requires 0 <= s <= 65535, 0 <= a <= 65535, 0 <= c <= 65535, 0 <= d <= 65535,
        {}
    }
}

pub proof fn source_over_rounding_is_nearest(numerator: u64, denominator: u64)
    ensures
        denominator == 0 ==> crate::specs::part2_source_over_rounded_ratio(numerator, denominator) == 0,
        denominator > 0 ==> 2 * ((denominator as nat)
            * crate::specs::part2_source_over_rounded_ratio(numerator, denominator))
            <= 2 * (numerator as nat) + denominator as nat,
        denominator > 0 ==> 2 * (numerator as nat) < 2 * ((denominator as nat)
            * crate::specs::part2_source_over_rounded_ratio(numerator, denominator))
            + denominator as nat,
{
    if denominator > 0 {
        let d = denominator as int;
        let biased = numerator as int + d / 2;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(d, 2);
        vstd::arithmetic::div_mod::lemma_mod_bound(d, 2);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(biased, d);
        vstd::arithmetic::div_mod::lemma_mod_bound(biased, d);
    }
}

pub proof fn source_over_rounding_preserves_sample_bound(numerator: u64, denominator: u64)
    requires
        numerator as nat <= 65535 * (denominator as nat),
    ensures
        crate::specs::part2_source_over_rounded_ratio(numerator, denominator) <= 65535,
{
    source_over_rounding_is_nearest(numerator, denominator);
    if denominator > 0 {
        let output = crate::specs::part2_source_over_rounded_ratio(numerator, denominator) as int;
        if output > 65535 {
            vstd::arithmetic::mul::lemma_mul_inequality(65536, output, denominator as int);
            vstd::arithmetic::mul::lemma_mul_is_commutative(output, denominator as int);
            assert(false);
        }
    }
}

pub proof fn ht_kappa_completion_never_reduces_base_u(
    u_base: nat,
    gamma: bool,
    exponent: nat,
)
    ensures
        ht_completed_u(u_base, gamma, exponent) >= u_base,
        !gamma ==> ht_completed_u(u_base, gamma, exponent) == u_base,
        exponent <= 2 ==> ht_completed_u(u_base, gamma, exponent) == u_base,
{
    reveal(ht_completed_u);
    reveal(ht_kappa_extension);
}

pub proof fn ht_pass_group_bounds_placeholders_and_substantive_set(packet_passes: nat)
    requires
        valid_ht_pass_group(packet_passes),
    ensures
        ht_placeholder_passes(packet_passes) % 3 == 0,
        ht_substantive_passes(packet_passes) >= 1,
        ht_substantive_passes(packet_passes) <= 3,
{
    reveal(valid_ht_pass_group);
    reveal(ht_placeholder_passes);
    reveal(ht_substantive_passes);
}

pub proof fn ht_refinement_bounds_bytes_and_passes(bytes: nat, passes: nat)
    requires
        valid_ht_refinement_segment(bytes, passes),
    ensures
        bytes <= 2046,
        passes >= 1,
        passes <= 2,
{
    reveal(valid_ht_refinement_segment);
}

pub proof fn ht_refinement_claims_cannot_alias(
    forward_end: nat,
    reverse_start: nat,
)
    requires
        disjoint_ht_refinement_claims(forward_end, reverse_start),
    ensures
        forward_end <= reverse_start,
{
    reveal(disjoint_ht_refinement_claims);
}

pub proof fn bounded_codestream_count_is_nonzero(codestreams: nat, limit: nat)
    requires
        codestream_count_within_limit(codestreams, limit),
    ensures
        codestreams > 0,
        codestreams <= limit,
{
}

pub proof fn valid_mct_reference_is_nonzero_and_bounded(index: nat, arrays: nat)
    requires
        valid_mct_array_reference(index, arrays),
    ensures
        index > 0,
        index <= arrays,
{
}

pub proof fn valid_mct_dimensions_bound_matrix_and_offsets(
    components: nat,
    matrix_elements: nat,
    offset_elements: nat,
)
    requires
        valid_mct_dimensions(components, matrix_elements, offset_elements),
    ensures
        matrix_elements == components * components,
        offset_elements <= components,
{
}

pub proof fn selected_mct_graph_has_bounded_collections_and_stages(collections: nat, stages: nat)
    requires
        valid_mct_collection_count(collections, stages),
    ensures
        collections > 0,
        collections <= 64,
        stages > 0,
        stages <= 255,
{
}

pub proof fn ordered_mct_stage_edge_is_acyclic(parent: nat, child: nat, stages: nat)
    requires
        valid_mct_stage_edge(parent, child, stages),
    ensures
        parent < child,
        child < stages,
{
}

pub proof fn valid_mct_matrix_is_bounded_and_rectangular(
    rows: nat,
    columns: nat,
    elements: nat,
    component_limit: nat,
)
    requires
        valid_mct_matrix_bounds(rows, columns, elements, component_limit),
    ensures
        rows == columns,
        rows <= component_limit,
        elements == rows * columns,
{
}

pub proof fn valid_maxshift_has_bounded_component_and_shift(
    component: nat,
    components: nat,
    style: nat,
    shift: nat,
)
    requires
        valid_maxshift_roi(component, components, style, shift),
    ensures
        component < components,
        style == 0,
        shift <= 255,
{
}

pub proof fn magnitude_bit_has_bounded_limb_and_offset(bit: nat)
    requires
        valid_magnitude_bit(bit),
    ensures
        magnitude_limb_index(bit) < 6,
        magnitude_limb_offset(bit) < 64,
{
    reveal(valid_magnitude_bit);
    reveal(magnitude_limb_index);
    reveal(magnitude_limb_offset);
}

pub proof fn magnitude_shift_stays_in_fixed_width(highest_bit: nat, shift: nat)
    requires
        magnitude_shift_fits(highest_bit, shift),
    ensures
        highest_bit + shift < 384,
{
    reveal(magnitude_shift_fits);
}

pub proof fn magnitude_comparison_is_transitive(left: nat, middle: nat, right: nat)
    requires
        magnitude_less(left, middle),
        magnitude_less(middle, right),
    ensures
        magnitude_less(left, right),
{
    reveal(magnitude_less);
}

pub proof fn magnitude_addition_contains_both_operands(left: nat, right: nat)
    ensures
        magnitude_addition(left, right) >= left,
        magnitude_addition(left, right) >= right,
{
    reveal(magnitude_addition);
}

pub proof fn maxshift_undo_does_not_increase_magnitude(magnitude: nat, threshold: nat)
    requires
        threshold > 0,
    ensures
        maxshift_restored_magnitude(magnitude, threshold) <= magnitude,
{
    reveal(maxshift_restored_magnitude);
}

pub proof fn component_index_width_is_part_one_width(components: nat)
    requires
        components > 0,
    ensures
        component_index_width(components) == 1 || component_index_width(components) == 2,
        (components < 257 ==> component_index_width(components) == 1),
        (components >= 257 ==> component_index_width(components) == 2),
{
}

pub proof fn valid_component_override_is_in_range(component: nat, components: nat)
    requires
        valid_component_override_index(component, components),
    ensures
        components > 0,
        component < components,
{
}

pub proof fn valid_palette_lookup_has_bounded_linear_index(
    entry: nat,
    entries: nat,
    column: nat,
    columns: nat,
)
    requires
        valid_palette_lookup(entry, entries, column, columns),
    ensures
        palette_linear_index(entry, column, columns) < entries * columns,
{
    reveal(valid_palette_lookup);
    reveal(palette_linear_index);
}

pub proof fn valid_direct_mapping_has_zero_palette_column(
    component: nat,
    components: nat,
    palette_column: nat,
    palette_columns: nat,
)
    requires
        valid_component_mapping(component, components, 0, palette_column, palette_columns),
    ensures
        component < components,
        palette_column == 0,
{
}

pub proof fn valid_palette_mapping_has_bounded_column(
    component: nat,
    components: nat,
    palette_column: nat,
    palette_columns: nat,
)
    requires
        valid_component_mapping(component, components, 1, palette_column, palette_columns),
    ensures
        component < components,
        palette_column < palette_columns,
{
}

pub proof fn unassociated_channel_is_valid(output_channels: nat)
    ensures
        valid_channel_association(0xffff, output_channels),
{
}

pub proof fn valid_color_sample_is_bounded(value: nat, maximum: nat)
    requires
        valid_color_sample(value, maximum),
    ensures
        maximum > 0,
        value <= maximum,
{
}

pub proof fn signed_color_nominalization_is_bounded(value: int, level: nat)
    requires
        valid_signed_color_sample(value, level),
    ensures
        0 <= signed_color_to_nominal(value, level),
        signed_color_to_nominal(value, level) < 2 * level,
{
    reveal(valid_signed_color_sample);
    reveal(signed_color_to_nominal);
}

pub proof fn resampled_color_coordinate_is_component_bounded(
    grid_coordinate: nat,
    sampling_step: nat,
    first_component_coordinate: nat,
    component_count: nat,
)
    requires
        sampling_step > 0,
        component_count > 0,
    ensures
        first_component_coordinate <= resampled_component_coordinate(
            grid_coordinate,
            sampling_step,
            first_component_coordinate,
            component_count,
        ),
        resampled_component_coordinate(
            grid_coordinate,
            sampling_step,
            first_component_coordinate,
            component_count,
        ) < first_component_coordinate + component_count,
{
    reveal(resampled_component_coordinate);
}

pub proof fn packet_length_step_extends_base_128(prefix: nat, group: nat)
    requires
        group < 128,
    ensures
        packet_length_step(prefix, group) == prefix * 128 + group,
        packet_length_step(prefix, group) >= prefix * 128,
{
}

pub proof fn continuous_packet_length_index_is_bounded(expected: nat, actual: nat)
    requires
        packet_length_index_continuous(expected, actual),
    ensures
        actual == expected,
        actual < 256,
{
}

pub proof fn covered_packet_payload_has_exact_boundary(declared: nat, payload: nat)
    requires
        packet_lengths_cover_payload(declared, payload),
    ensures
        declared <= payload,
        payload <= declared,
{
}

pub proof fn continuous_packed_header_index_is_bounded(expected: nat, actual: nat)
    requires
        packed_header_index_continuous(expected, actual),
    ensures
        actual == expected,
        actual < 256,
{
}

pub proof fn bounded_ppm_frame_has_bounded_end(total: nat, position: nat, length: nat)
    requires
        ppm_frame_fits(total, position, length),
    ensures
        position + length <= total,
{
}

pub proof fn packed_packet_partition_is_exact(declared: nat, tile_body: nat, packed_header: nat)
    requires
        packed_packet_length_matches(declared, tile_body, packed_header),
    ensures
        tile_body <= declared,
        packed_header <= declared,
        declared == tile_body + packed_header,
{
}

pub proof fn valid_poc_bounds_contained_coordinates(
    resolution_start: nat,
    resolution_end: nat,
    component_start: nat,
    component_end: nat,
    layer_end: nat,
    components: nat,
    layers: nat,
    resolutions: nat,
    order: nat,
    layer: nat,
    resolution: nat,
    component: nat,
)
    requires
        valid_poc_record(
            resolution_start,
            resolution_end,
            component_start,
            component_end,
            layer_end,
            components,
            layers,
            resolutions,
            order,
        ),
        poc_contains(
            layer,
            resolution,
            component,
            resolution_start,
            resolution_end,
            component_start,
            component_end,
            layer_end,
        ),
    ensures
        layer < layers,
        resolution < resolutions,
        component < components,
        order < 5,
{
}

pub proof fn tile_component_override_has_highest_precedence(
    main_default: int,
    main_component: int,
    has_main_component: bool,
    tile_default: int,
    has_tile_default: bool,
    tile_component: int,
)
    ensures
        effective_component_override(
            main_default,
            main_component,
            has_main_component,
            tile_default,
            has_tile_default,
            tile_component,
            true,
        ) == tile_component,
{
}

pub proof fn tile_default_precedes_main_component(
    main_default: int,
    main_component: int,
    has_main_component: bool,
    tile_default: int,
)
    ensures
        effective_component_override(
            main_default,
            main_component,
            has_main_component,
            tile_default,
            true,
            0,
            false,
        ) == tile_default,
{
}

pub proof fn supported_layer_reference_is_bounded(index: nat, codestreams: nat)
    requires
        valid_layer_codestream_reference(index, codestreams),
    ensures
        index < codestreams,
{
}

pub proof fn implicit_jpx_layers_are_codestream_layers(codestreams: nat)
    ensures
        effective_jpx_layer_count(0, codestreams) == codestreams,
{
}

pub proof fn jp2_primary_excludes_jpx_compatibility()
    ensures
        !valid_jp2_primary_brand(true, true),
{
}

pub proof fn jpip_pair_layout_is_odd(tile_pairs: nat)
    ensures
        valid_jpip_codestream_layout(3 + tile_pairs * 2),
{
}

pub proof fn tile_transform_slice_is_local(start: nat, components: nat, total: nat)
    requires
        tile_transform_scope(start, components, total),
    ensures
        start + components <= total,
{
}

pub proof fn clipped_layer_extent_fits_source_and_canvas(
    offset: nat,
    extent: nat,
    canvas: nat,
)
    ensures
        clipped_composition_extent(offset, extent, canvas) <= extent,
        offset < canvas ==> clipped_composition_extent(offset, extent, canvas) <= canvas - offset,
{
}

pub proof fn composited_storage_includes_alpha(pixels: nat, color_channels: nat)
    ensures
        composition_output_bytes(pixels, color_channels)
            == pixels * (color_channels + 1) * 2,
{
}

pub proof fn registered_extent_numerator_includes_offset(
    samples: nat,
    subsampling: nat,
    offset: nat,
)
    ensures
        registered_sample_numerator(samples, subsampling, offset)
            == samples * subsampling + offset,
{
}

pub proof fn instruction_materialization_is_frame_layer_bounded(frames: nat, layers: nat)
    ensures
        composition_instruction_work(frames, layers)
            == frames * if layers == 0 { 1 } else { layers },
{
}

pub proof fn multi_codestream_channel_assembly_is_additive(
    prior_channels: nat,
    codestream_channels: nat,
)
    ensures
        registered_channel_count(prior_channels, codestream_channels)
            == prior_channels + codestream_channels,
{
}

pub proof fn nested_metadata_accounting_covers_boxes_and_depth(boxes: nat, depth: nat)
    ensures
        nested_metadata_work(boxes, depth) == boxes + depth,
{
}

pub proof fn looped_frame_selection_stays_in_timeline(index: nat, frames: nat)
    requires
        frames > 0,
    ensures
        bounded_loop_frame(index, frames) < frames,
{
}

pub proof fn part15_cap_payload_tracks_ordered_ccap_words(capabilities: u8)
    ensures
        crate::specs::part15_cap_payload_length(capabilities)
            == 4 + 2 * capabilities as usize,
{
}

pub proof fn part15_classification_is_total(
    legacy: bool,
    ht: bool,
    mixed: bool,
)
    ensures
        crate::specs::part15_codestream_class(legacy, ht, mixed) <= 2,
{
    reveal(crate::specs::part15_codestream_class);
}

pub proof fn part15_magnitude_parameter_is_bounded(parameter: nat)
    requires
        parameter < 32,
    ensures
        8 <= crate::specs::part15_magnitude_bound(parameter),
        crate::specs::part15_magnitude_bound(parameter) <= 74,
{
    reveal(crate::specs::part15_magnitude_bound);
}

pub proof fn ht_group_partition_is_exact(passes: nat)
    requires
        1 <= passes,
        passes <= 164,
    ensures
        crate::specs::ht_placeholder_passes(passes)
            + crate::specs::ht_substantive_passes(passes) == passes,
{
    reveal(crate::specs::ht_placeholder_passes);
    reveal(crate::specs::ht_substantive_passes);
}

pub proof fn ht_scup_partitions_cleanup(cleanup: nat, penultimate: u8, last: u8)
    requires
        crate::specs::ht_scup(penultimate, last) as nat <= cleanup,
    ensures
        crate::specs::ht_magsgn_end(
            cleanup,
            crate::specs::ht_scup(penultimate, last) as nat,
        ) + crate::specs::ht_scup(penultimate, last) as nat == cleanup,
{
    reveal(crate::specs::ht_magsgn_end);
}

pub proof fn ht_stuffed_streams_expose_seven_data_bits()
    ensures
        crate::specs::ht_forward_data_bits(true) == 7,
        crate::specs::ht_reverse_data_bits(true, 127) == 7,
{
}

pub proof fn ht_mel_state_and_vlc_index_are_bounded(state: nat, context: nat, lookahead: nat)
    requires
        state <= 12,
        context <= 7,
        lookahead <= 127,
    ensures
        crate::specs::ht_mel_exponent(state) <= 5,
        crate::specs::ht_mel_next_state(state, true) <= 12,
        crate::specs::ht_vlc_table_index(context, lookahead) < 1024,
{
    reveal(crate::specs::ht_mel_exponent);
    reveal(crate::specs::ht_mel_next_state);
    reveal(crate::specs::ht_vlc_table_index);
}

pub proof fn ht_kappa_completion_never_reduces_u(u_base: nat, gamma: bool, exponent: nat)
    ensures
        crate::specs::ht_kappa_completion(u_base, gamma, exponent) >= u_base,
{
    reveal(crate::specs::ht_kappa_completion);
}

pub proof fn ht_bin_center_normalization_is_odd(value: nat)
    ensures
        crate::specs::ht_bin_center_odd(value) % 2 == 1,
        crate::specs::ht_bin_center_odd(value) >= value,
{
    reveal(crate::specs::ht_bin_center_odd);
}

pub proof fn ht_traversal_bounds_stripes_and_patches(height: nat, y: nat, width: nat, x: nat)
    requires
        y <= height,
        x <= width,
    ensures
        crate::specs::ht_stripe_rows(height, y) <= 4,
        crate::specs::ht_patch_end(x, width) <= width,
{
    reveal(crate::specs::ht_stripe_rows);
    reveal(crate::specs::ht_patch_end);
}

pub proof fn ht_refinement_continuation_is_additive(existing: nat, additional: nat)
    ensures
        crate::specs::ht_refinement_pass_total(existing, additional)
            == existing + additional,
{
}

pub proof fn quantized_prefix_has_exact_length(
    coefficients: Seq<crate::specs::Part1QuantizedCoefficient>, shift: u8,
    step: i64, reversible: bool, count: nat,
)
    requires count <= coefficients.len(),
    ensures match crate::specs::part1_quantized_prefix(coefficients, shift, step, reversible, count) {
        Ok(samples) => samples.len() == count,
        Err(_) => true,
    },
    decreases count,
{
    if count > 0 {
        quantized_prefix_has_exact_length(coefficients, shift, step, reversible, (count - 1) as nat);
    }
}

pub proof fn inverse_quantization_has_complete_plane_metadata(
    coefficients: Seq<crate::specs::Part1QuantizedCoefficient>, exponent: u8, mantissa: u16,
    range: u8, reversible: bool, shift: u8, maximum: u64,
)
    ensures match crate::specs::part1_inverse_quantization(
        coefficients, exponent, mantissa, range, reversible, shift, maximum,
    ) {
        Ok(plane) => plane.0 == coefficients.len() && plane.1 == 1
            && plane.2 == (if reversible { 0u8 } else { 16u8 })
            && plane.3.len() == coefficients.len(),
        Err(_) => true,
    },
{
    let step_result = if reversible { Ok(1i64) }
        else { crate::specs::part1_quantization_step(exponent, mantissa, range) };
    if let Ok(step) = step_result {
        quantized_prefix_has_exact_length(coefficients, shift, step, reversible, coefficients.len());
    }
}

pub proof fn lifting_prefix_preserves_length_and_opposite_parity(
    samples: Seq<i64>, target_even: bool, kind: u8, factor: i64, count: nat,
)
    requires count <= samples.len(),
    ensures
        crate::specs::part1_lifting_prefix(samples, target_even, kind, factor, count).1.len() == samples.len(),
        forall |i: int| 0 <= i < samples.len() && (i >= count || (i % 2 == 0) != target_even) ==>
            crate::specs::part1_lifting_prefix(samples, target_even, kind, factor, count).1[i] == samples[i],
    decreases count,
{
    if count > 0 {
        lifting_prefix_preserves_length_and_opposite_parity(samples, target_even, kind, factor, (count - 1) as nat);
    }
}

pub proof fn inverse_five_three_preserves_complete_sequence_length(
    low: Seq<i64>, high: Seq<i64>, low_first: bool,
)
    ensures match crate::specs::part1_inverse_five_three(low, high, low_first) {
        Ok(samples) => samples.len() == low.len() + high.len(),
        Err(_) => true,
    },
{
    if let Ok(samples) = crate::specs::part1_interleaved(low, high, low_first) {
        lifting_prefix_preserves_length_and_opposite_parity(samples, low_first, 0, 0, samples.len());
        let updated = crate::specs::part1_lifting_prefix(samples, low_first, 0, 0, samples.len());
        lifting_prefix_preserves_length_and_opposite_parity(updated.1, !low_first, 1, 0, updated.1.len());
    }
}

pub proof fn scaling_prefix_preserves_complete_length(
    samples: Seq<i64>, target_even: bool, factor: i64, count: nat,
)
    requires count <= samples.len(),
    ensures crate::specs::part1_scaling_prefix(samples, target_even, factor, count).1.len() == samples.len(),
    decreases count,
{
    if count > 0 {
        scaling_prefix_preserves_complete_length(samples, target_even, factor, (count - 1) as nat);
    }
}

pub proof fn nine_seven_lifting_preserves_complete_length(samples: Seq<i64>, low_first: bool, count: nat)
    ensures crate::specs::part1_nine_seven_lifting_prefix(samples, low_first, count).1.len() == samples.len(),
    decreases count,
{
    if count > 0 {
        nine_seven_lifting_preserves_complete_length(samples, low_first, (count - 1) as nat);
        let previous = crate::specs::part1_nine_seven_lifting_prefix(samples, low_first, (count - 1) as nat);
        lifting_prefix_preserves_length_and_opposite_parity(
            previous.1, if count % 2 == 1 { low_first } else { !low_first },
            2, crate::specs::part1_nine_seven_lift((count - 1) as u8), previous.1.len(),
        );
    }
}

pub proof fn inverse_nine_seven_preserves_complete_sequence_length(
    low: Seq<i64>, high: Seq<i64>, low_first: bool,
)
    ensures match crate::specs::part1_inverse_nine_seven(low, high, low_first) {
        Ok(samples) => samples.len() == low.len() + high.len(),
        Err(_) => true,
    },
{
    if let Ok(samples) = crate::specs::part1_interleaved(low, high, low_first) {
        scaling_prefix_preserves_complete_length(samples, low_first, crate::specs::part1_nine_seven_scale(true), samples.len());
        let low_scaled = crate::specs::part1_scaling_prefix(samples, low_first, crate::specs::part1_nine_seven_scale(true), samples.len());
        scaling_prefix_preserves_complete_length(low_scaled.1, !low_first, crate::specs::part1_nine_seven_scale(false), low_scaled.1.len());
        let high_scaled = crate::specs::part1_scaling_prefix(low_scaled.1, !low_first, crate::specs::part1_nine_seven_scale(false), low_scaled.1.len());
        nine_seven_lifting_preserves_complete_length(high_scaled.1, low_first, 4);
    }
}

pub proof fn inverse_sequence_preserves_complete_length(
    low: Seq<i64>, high: Seq<i64>, low_first: bool, irreversible: bool,
)
    ensures match crate::specs::part1_inverse_sequence(low, high, low_first, irreversible) {
        Ok(samples) => samples.len() == low.len() + high.len(),
        Err(_) => true,
    },
{
    if irreversible {
        inverse_nine_seven_preserves_complete_sequence_length(low, high, low_first);
    } else {
        inverse_five_three_preserves_complete_sequence_length(low, high, low_first);
    }
}

pub proof fn horizontal_row_has_complete_length(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    y: u32, low_first: bool, irreversible: bool,
)
    ensures match crate::specs::part1_horizontal_row(low, high, y, low_first, irreversible) {
        Ok(samples) => samples.len() == (low.0 as nat) + (high.0 as nat),
        Err(_) => true,
    },
{
    if let Ok(low_row) = crate::specs::part1_band_row(low, y) {
        assert(low_row.len() == low.0);
        if let Ok(high_row) = crate::specs::part1_band_row(high, y) {
            assert(high_row.len() == high.0);
            inverse_sequence_preserves_complete_length(low_row, high_row, low_first, irreversible);
        }
    }
}

pub proof fn horizontal_prefix_has_complete_length(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    low_first: bool, irreversible: bool, count: nat,
)
    requires count <= low.1,
    ensures match crate::specs::part1_horizontal_prefix(low, high, low_first, irreversible, count) {
        Ok(samples) => samples.len() == count * ((low.0 as nat) + (high.0 as nat)),
        Err(_) => true,
    },
    decreases count,
{
    if count > 0 {
        horizontal_prefix_has_complete_length(low, high, low_first, irreversible, (count - 1) as nat);
        let y = (count - 1) as u32;
        horizontal_row_has_complete_length(low, high, y, low_first, irreversible);
        assert(((count - 1) as nat) * ((low.0 as nat) + (high.0 as nat))
            + ((low.0 as nat) + (high.0 as nat)) == count * ((low.0 as nat) + (high.0 as nat))) by(nonlinear_arith)
            requires count > 0;
        if let Ok(previous) = crate::specs::part1_horizontal_prefix(low, high, low_first, irreversible, (count - 1) as nat) {
            if let Ok(row) = crate::specs::part1_horizontal_row(low, high, y, low_first, irreversible) {
                assert((previous + row).len() == previous.len() + row.len());
                assert((previous + row).len() == count * ((low.0 as nat) + (high.0 as nat)));
                assert(crate::specs::part1_horizontal_prefix(low, high, low_first, irreversible, count) == Ok(previous + row));
            }
        }
    }
}

pub proof fn store_column_prefix_preserves_complete_length(
    output: Seq<i64>, width: u32, x: u32, column: Seq<i64>, count: nat,
)
    ensures crate::specs::part1_store_column_prefix(output, width, x, column, count).1.len() == output.len(),
    decreases count,
{
    if count > 0 {
        store_column_prefix_preserves_complete_length(output, width, x, column, (count - 1) as nat);
    }
}

pub proof fn vertical_prefix_preserves_complete_length(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    height: u32, low_first: bool, irreversible: bool, length: usize, count: nat,
)
    ensures match crate::specs::part1_vertical_prefix(low, high, height, low_first, irreversible, length, count) {
        Ok(samples) => samples.len() == length,
        Err(_) => true,
    },
    decreases count,
{
    if count > 0 {
        vertical_prefix_preserves_complete_length(low, high, height, low_first, irreversible, length, (count - 1) as nat);
        if let Ok(previous) = crate::specs::part1_vertical_prefix(low, high, height, low_first, irreversible, length, (count - 1) as nat) {
            if let Ok(column) = crate::specs::part1_vertical_column(low, high, (count - 1) as u32, low_first, irreversible) {
                store_column_prefix_preserves_complete_length(previous, low.0, (count - 1) as u32, column, height as nat);
            }
        }
    }
}

pub proof fn standard_horizontal_plane_has_complete_shape(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    width: u32, low_first: bool, irreversible: bool, maximum: u64,
)
    ensures match crate::specs::part1_inverse_horizontal(low, high, width, low_first, irreversible, maximum) {
        Ok(plane) => plane.3.len() == (plane.0 as nat) * (plane.1 as nat),
        Err(_) => true,
    },
{
    horizontal_prefix_has_complete_length(low, high, low_first, irreversible, low.1 as nat);
    assert((low.1 as nat) * (width as nat) == (width as nat) * (low.1 as nat)) by(nonlinear_arith);
}

pub proof fn standard_vertical_plane_has_complete_shape(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    height: u32, low_first: bool, irreversible: bool, maximum: u64,
)
    ensures match crate::specs::part1_inverse_vertical(low, high, height, low_first, irreversible, maximum) {
        Ok(plane) => plane.3.len() == (plane.0 as nat) * (plane.1 as nat),
        Err(_) => true,
    },
{
    if let Ok(length) = crate::specs::part1_transform_area(low.0, height) {
        vertical_prefix_preserves_complete_length(low, high, height, low_first, irreversible, length, low.0 as nat);
    }
}

pub proof fn standard_level_plane_has_complete_shape(
    level: crate::specs::Part1WaveletLevel, irreversible: bool, maximum: u64,
)
    ensures match crate::specs::part1_inverse_level(level, irreversible, maximum) {
        Ok(plane) => plane.3.len() == (plane.0 as nat) * (plane.1 as nat),
        Err(_) => true,
    },
{
    if let Ok(length) = crate::specs::part1_transform_area(level.4, level.5) {
        if let Ok(low_rows) = crate::specs::part1_horizontal_prefix(level.0, level.1, level.6, irreversible, level.0.1 as nat) {
            if let Ok(high_rows) = crate::specs::part1_horizontal_prefix(level.2, level.3, level.6, irreversible, level.2.1 as nat) {
                vertical_prefix_preserves_complete_length(
                    (level.4, level.0.1, low_rows), (level.4, level.2.1, high_rows),
                    level.5, level.7, irreversible, length, level.4 as nat,
                );
            }
        }
    }
}

pub proof fn conversion_prefix_has_complete_length(
    samples: Seq<i64>, fraction_bits: u8, shift: i64, minimum: i64, maximum: i64, count: nat,
)
    requires count <= samples.len(),
    ensures match crate::specs::part1_conversion_prefix(samples, fraction_bits, shift, minimum, maximum, count) {
        Ok(converted) => converted.len() == count,
        Err(_) => true,
    },
    decreases count,
{
    if count > 0 {
        conversion_prefix_has_complete_length(samples, fraction_bits, shift, minimum, maximum, (count - 1) as nat);
    }
}

pub proof fn converted_samples_preserve_complete_length(
    plane: crate::specs::Part1ReconstructedPlane, precision: u8, signed: bool, maximum_bytes: u64,
)
    ensures match crate::specs::part1_convert_samples(plane, precision, signed, maximum_bytes) {
        Ok(samples) => samples.len() == plane.3.len(),
        Err(_) => true,
    },
{
    conversion_prefix_has_complete_length(
        plane.3, plane.2, crate::specs::part1_level_shift(precision, signed),
        crate::specs::part1_output_minimum(precision, signed), crate::specs::part1_output_maximum(precision, signed), plane.3.len(),
    );
}

pub proof fn decoded_sample_store_preserves_component_frame(
    image: crate::specs::Part1DecodedImageModel, component: usize, index: usize, value: i64,
)
    requires component < 3,
    ensures crate::specs::part1_component_transform_frame(
        image, crate::specs::part1_set_decoded_component_sample(image, component, index, value).1,
    ),
{
}

pub proof fn component_transform_frame_is_transitive(
    before: crate::specs::Part1DecodedImageModel,
    middle: crate::specs::Part1DecodedImageModel,
    after: crate::specs::Part1DecodedImageModel,
)
    requires
        crate::specs::part1_component_transform_frame(before, middle),
        crate::specs::part1_component_transform_frame(middle, after),
    ensures crate::specs::part1_component_transform_frame(before, after),
{
}

pub proof fn component_pixel_preserves_complete_metadata_and_extra_planes(
    image: crate::specs::Part1DecodedImageModel, index: usize, irreversible: bool,
)
    ensures crate::specs::part1_component_transform_frame(
        image, crate::specs::part1_component_pixel_state(image, index, irreversible).1,
    ),
{
    if let Ok(y) = crate::specs::part1_decoded_component_sample(image, 0, index) {
        if let Ok(cb) = crate::specs::part1_decoded_component_sample(image, 1, index) {
            if let Ok(cr) = crate::specs::part1_decoded_component_sample(image, 2, index) {
                if let Ok((red, green, blue)) = crate::specs::part1_component_values(y, cb, cr, irreversible) {
                    decoded_sample_store_preserves_component_frame(image, 0, index, red);
                    let red_state = crate::specs::part1_set_decoded_component_sample(image, 0, index, red);
                    decoded_sample_store_preserves_component_frame(red_state.1, 1, index, green);
                    let green_state = crate::specs::part1_set_decoded_component_sample(red_state.1, 1, index, green);
                    component_transform_frame_is_transitive(image, red_state.1, green_state.1);
                    decoded_sample_store_preserves_component_frame(green_state.1, 2, index, blue);
                    let blue_state = crate::specs::part1_set_decoded_component_sample(green_state.1, 2, index, blue);
                    component_transform_frame_is_transitive(image, green_state.1, blue_state.1);
                }
            }
        }
    }
}

pub proof fn component_prefix_preserves_complete_metadata_and_extra_planes(
    image: crate::specs::Part1DecodedImageModel, irreversible: bool, count: nat,
)
    ensures crate::specs::part1_component_transform_frame(
        image, crate::specs::part1_component_transform_prefix(image, irreversible, count).1,
    ),
    decreases count,
{
    if count > 0 {
        component_prefix_preserves_complete_metadata_and_extra_planes(image, irreversible, (count - 1) as nat);
        let previous = crate::specs::part1_component_transform_prefix(image, irreversible, (count - 1) as nat);
        component_pixel_preserves_complete_metadata_and_extra_planes(previous.1, (count - 1) as usize, irreversible);
        component_transform_frame_is_transitive(
            image, previous.1, crate::specs::part1_component_pixel_state(previous.1, (count - 1) as usize, irreversible).1,
        );
    }
}

pub proof fn component_transforms_preserve_complete_metadata_and_extra_planes(
    image: crate::specs::Part1DecodedImageModel, irreversible: bool,
)
    ensures crate::specs::part1_component_transform_frame(
        image, crate::specs::part1_apply_component_transform(image, irreversible).1,
    ),
{
    if image.4.len() >= 3 {
        component_prefix_preserves_complete_metadata_and_extra_planes(image, irreversible, image.4[0].4.len());
    }
}

pub proof fn quantized_pixel_preserves_metadata_and_previsited_samples(
    band: crate::specs::Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, x: u32, y: u32,
)
    ensures crate::specs::part1_working_subband_frame(
        band, crate::specs::part1_quantized_block_pixel(band, source, block_width, placement_x, placement_y, x, y).1,
    ),
{
}

pub proof fn working_subband_frame_is_transitive(
    before: crate::specs::Part1WorkingSubbandModel,
    middle: crate::specs::Part1WorkingSubbandModel,
    after: crate::specs::Part1WorkingSubbandModel,
)
    requires
        crate::specs::part1_working_subband_frame(before, middle),
        crate::specs::part1_working_subband_frame(middle, after),
    ensures crate::specs::part1_working_subband_frame(before, after),
{
}

pub proof fn quantized_row_preserves_metadata_and_previsited_samples(
    band: crate::specs::Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, y: u32, count: nat,
)
    ensures crate::specs::part1_working_subband_frame(
        band, crate::specs::part1_quantized_block_row(band, source, block_width, placement_x, placement_y, y, count).1,
    ),
    decreases count,
{
    if count > 0 {
        quantized_row_preserves_metadata_and_previsited_samples(band, source, block_width, placement_x, placement_y, y, (count - 1) as nat);
        let previous = crate::specs::part1_quantized_block_row(band, source, block_width, placement_x, placement_y, y, (count - 1) as nat);
        quantized_pixel_preserves_metadata_and_previsited_samples(previous.1, source, block_width, placement_x, placement_y, (count - 1) as u32, y);
        working_subband_frame_is_transitive(
            band, previous.1,
            crate::specs::part1_quantized_block_pixel(previous.1, source, block_width, placement_x, placement_y, (count - 1) as u32, y).1,
        );
    }
}

pub proof fn quantized_block_preserves_metadata_and_previsited_samples(
    band: crate::specs::Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, count: nat,
)
    ensures crate::specs::part1_working_subband_frame(
        band, crate::specs::part1_quantized_block_rows(band, source, block_width, placement_x, placement_y, count).1,
    ),
    decreases count,
{
    if count > 0 {
        quantized_block_preserves_metadata_and_previsited_samples(band, source, block_width, placement_x, placement_y, (count - 1) as nat);
        let previous = crate::specs::part1_quantized_block_rows(band, source, block_width, placement_x, placement_y, (count - 1) as nat);
        quantized_row_preserves_metadata_and_previsited_samples(previous.1, source, block_width, placement_x, placement_y, (count - 1) as u32, block_width as nat);
        working_subband_frame_is_transitive(
            band, previous.1,
            crate::specs::part1_quantized_block_row(previous.1, source, block_width, placement_x, placement_y, (count - 1) as u32, block_width as nat).1,
        );
    }
}

pub proof fn ht_packet_segment_pass_error_precedes_range_and_state_effects(
    state: crate::specs::Tier1DecoderState, segment: crate::packet::CodeBlockSegmentContribution,
    body: Seq<u8>, offset: usize, decoded_passes: u32,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
)
    ensures segment.passes == 0 || segment.passes > 2 ==>
        crate::specs::ht_packet_segment_body(state, segment, body, offset, decoded_passes,
            pass_limit, byte_limit, work_limit)
        == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
            state, offset, decoded_passes),
{
}

pub proof fn ht_packet_finished_progress_preserves_complete_state(
    state: crate::specs::Tier1DecoderState, header: crate::specs::Part1CodeBlockContribution,
    body: Seq<u8>, progress: crate::specs::HtPacketBodyProgress,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
)
    ensures progress.segment_index >= header.segment_count ==>
        crate::specs::ht_packet_body_run(state, header, body, progress, pass_limit, byte_limit, work_limit)
        == (Ok(()), state, progress),
{
    reveal(crate::specs::ht_packet_body_run);
}

pub proof fn ht_packet_transaction_errors_restore_complete_decoder(
    state: crate::specs::Tier1DecoderState, header: crate::specs::Part1CodeBlockContribution,
    body: Seq<u8>, pass_limit: u32, byte_limit: u64, work_limit: u64,
)
    ensures crate::specs::ht_packet_body(state, header, body, pass_limit, byte_limit, work_limit).0.is_err()
        ==> crate::specs::ht_packet_body(state, header, body, pass_limit, byte_limit, work_limit).1 == state,
{
}

pub proof fn ht_packet_success_reports_exact_declared_counts(
    state: crate::specs::Tier1DecoderState, header: crate::specs::Part1CodeBlockContribution,
    body: Seq<u8>, pass_limit: u32, byte_limit: u64, work_limit: u64,
)
    ensures match crate::specs::ht_packet_body_segments(state, header, body, pass_limit, byte_limit, work_limit).0 {
        Err(_) => true,
        Ok(result) => result.segments == header.segment_count
            && result.passes == header.new_passes && result.bytes == header.data_length,
    },
{
}

pub proof fn mixed_packet_dispatch_preserves_both_selected_profiles(
    state: crate::specs::Tier1DecoderState, header: crate::specs::Part1CodeBlockContribution,
    body: Seq<u8>, pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures
        header.high_throughput ==> crate::specs::part1_code_block_body_staged(
            state, header, body, pass_limit, byte_limit, input_limit, work_limit)
            == crate::specs::ht_packet_body_staged(state, header, body, pass_limit, byte_limit, work_limit),
        !header.high_throughput ==> crate::specs::part1_code_block_body_staged(
            state, header, body, pass_limit, byte_limit, input_limit, work_limit)
            == crate::specs::part1_legacy_code_block_staged(
                state, header, body, pass_limit, byte_limit, input_limit, work_limit),
{
    reveal(crate::specs::part1_legacy_code_block_staged);
}

pub proof fn mixed_packet_transaction_restores_every_decoder_field_on_error(
    state: crate::specs::Tier1DecoderState, header: crate::specs::Part1CodeBlockContribution,
    body: Seq<u8>, pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures crate::specs::part1_code_block_body_transaction(
        state, header, body, pass_limit, byte_limit, input_limit, work_limit).0.is_err()
        ==> crate::specs::part1_code_block_body_transaction(
            state, header, body, pass_limit, byte_limit, input_limit, work_limit).1 == state,
{
}

pub proof fn mixed_packet_preparation_failure_precedes_both_actual_routes(
    state: crate::specs::Tier1DecoderState, header: crate::specs::Part1CodeBlockContribution,
    body: Seq<u8>, pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures crate::specs::part1_code_block_body_prepare(state, header, body).0.is_err()
        ==> crate::specs::part1_code_block_body_staged(
            state, header, body, pass_limit, byte_limit, input_limit, work_limit).1
            == crate::specs::part1_code_block_body_prepare(state, header, body).1,
{
}

pub proof fn mixed_tier1_dispatch_retains_actual_native_route_order(
    state: crate::specs::Tier1DecoderState, input: Seq<u8>, passes: u8,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures
        passes == 0 ==> crate::specs::part1_tier1_segment(
            state, input, passes, pass_limit, byte_limit, input_limit, work_limit)
            == (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
        passes > 0 && !crate::specs::ht_group_route(state) ==> crate::specs::part1_tier1_segment(
            state, input, passes, pass_limit, byte_limit, input_limit, work_limit)
            == crate::specs::part1_legacy_segment(
                state, input, passes as u32, pass_limit, byte_limit, input_limit, work_limit),
{
}

pub proof fn packet_body_finished_preflight_preserves_raw_cursor(
    state: crate::specs::Part1PacketBodyPreflight,
    contributions: Seq<Option<crate::specs::Part1CodeBlockContribution>>, data: Seq<u8>, error_offset: usize,
)
    ensures state.index >= contributions.len() ==>
        crate::specs::part1_packet_body_preflight(state, contributions, data, error_offset) == (Ok(()), state),
{
    reveal(crate::specs::part1_packet_body_preflight);
    reveal(crate::specs::part1_packet_body_preflight_at);
}

pub proof fn packet_body_preflight_truncation_retains_advanced_end_before_index(
    state: crate::specs::Part1PacketBodyPreflight,
    contributions: Seq<Option<crate::specs::Part1CodeBlockContribution>>, data: Seq<u8>, error_offset: usize,
)
    ensures if state.index < contributions.len() {
        match contributions[state.index as int] {
            None => true,
            Some(contribution) => contribution.data_length as nat <= usize::MAX
                && state.end as nat + contribution.data_length as nat <= usize::MAX
                && state.end as nat + contribution.data_length as nat > data.len()
                ==> crate::specs::part1_packet_body_preflight(state, contributions, data, error_offset)
                    == (Err(crate::DecodeError::MalformedInput {
                        offset: error_offset as u64, kind: crate::MalformedKind::Truncated,
                    }), crate::specs::Part1PacketBodyPreflight {
                        end: (state.end + contribution.data_length) as usize, ..state
                    }),
        }
    } else { true },
{
    reveal(crate::specs::part1_packet_body_preflight);
    reveal(crate::specs::part1_packet_body_preflight_at);
}

pub proof fn packet_body_skipped_execution_preserves_all_decoders_and_counts(
    state: crate::specs::Part1PacketBodyExecution,
    contributions: Seq<Option<crate::specs::Part1CodeBlockContribution>>, data: Seq<u8>, error_offset: usize,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures
        crate::specs::part1_packet_body_execute(state, contributions, data, error_offset, false,
            pass_limit, byte_limit, input_limit, work_limit).1.decoders == state.decoders,
        crate::specs::part1_packet_body_execute(state, contributions, data, error_offset, false,
            pass_limit, byte_limit, input_limit, work_limit).1.segments == state.segments,
        crate::specs::part1_packet_body_execute(state, contributions, data, error_offset, false,
            pass_limit, byte_limit, input_limit, work_limit).1.passes == state.passes,
    decreases contributions.len() - state.index as nat,
{
    reveal(crate::specs::part1_packet_body_execute);
    reveal(crate::specs::part1_packet_body_execute_at);
    if state.index < contributions.len() {
        let step = match contributions[state.index as int] {
            None => (Ok(()), state),
            Some(contribution) => crate::specs::part1_packet_body_execute_slot(
                state, contribution, data, error_offset, false, pass_limit, byte_limit, input_limit, work_limit),
        };
        if step.0.is_ok() && step.1.index != usize::MAX {
            packet_body_skipped_execution_preserves_all_decoders_and_counts(
                crate::specs::Part1PacketBodyExecution { index: (step.1.index + 1) as usize, ..step.1 },
                contributions, data, error_offset, pass_limit, byte_limit, input_limit, work_limit,
            );
        }
    }
}

pub proof fn precinct_finished_raw_header_cursor_preserves_every_owner(
    state: crate::specs::Part1PrecinctHeaderState,
    contexts: Seq<crate::packet::CodeBlockPacketContext>, layer: u16, style: crate::tier1::Tier1CodingStyle,
)
    ensures state.subband_index >= state.subbands.len() ==>
        crate::specs::part1_precinct_headers(state, contexts, layer, style) == (Ok(()), state),
{
    reveal(crate::specs::part1_precinct_headers_run);
}

pub proof fn precinct_header_slot_preserves_all_physical_storage_lengths(
    state: crate::specs::Part1PrecinctHeaderState,
    contexts: Seq<crate::packet::CodeBlockPacketContext>, layer: u16, style: crate::tier1::Tier1CodingStyle,
)
    ensures
        crate::specs::part1_precinct_header_slot(state, contexts, layer, style).1.states.len() == state.states.len(),
        crate::specs::part1_precinct_header_slot(state, contexts, layer, style).1.subbands.len() == state.subbands.len(),
        crate::specs::part1_precinct_header_slot(state, contexts, layer, style).1.contributions.len()
            == state.contributions.len(),
        crate::specs::part1_precinct_header_slot(state, contexts, layer, style).1.subband_index == state.subband_index,
{
    reveal(crate::specs::part1_precinct_header_slot);
}

pub proof fn precinct_style_comparison_retains_native_force_flag_policy(
    style: crate::tier1::Tier1CodingStyle, required: bool,
)
    ensures crate::specs::part1_packet_styles_equal(
        style, crate::tier1::Tier1CodingStyle { force_high_throughput: required, ..style }),
{
}

pub proof fn precinct_sop_truncation_precedes_packed_offsets_and_reader_budgets(
    data: Seq<u8>, packed: Seq<u8>, parameters: crate::specs::Part1PrecinctPayloadParameters,
    header_limit: u64, work_limit: u64,
)
    ensures parameters.sop && 2 <= data.len() < 4 && data[0] == 0xff
        && (data[1] == 0x91 || (!parameters.packed && data[1] >= 0x90)) ==>
        crate::specs::part1_precinct_payload_prefix(data, packed, parameters, header_limit, work_limit)
            == Err(crate::specs::part1_packet_reader_error(parameters.error_offset, crate::MalformedKind::Truncated)),
{
}

pub proof fn precinct_malformed_sop_precedes_missing_sequence_and_reader_budgets(
    data: Seq<u8>, packed: Seq<u8>, parameters: crate::specs::Part1PrecinctPayloadParameters,
    header_limit: u64, work_limit: u64,
)
    ensures parameters.sop && data.len() >= 4 && data[0] == 0xff
        && (data[1] == 0x91 || (!parameters.packed && data[1] >= 0x90))
        && !crate::specs::part1_sop_valid(data[0], data[1], data[2], data[3]) ==>
        crate::specs::part1_precinct_payload_prefix(data, packed, parameters, header_limit, work_limit)
            == Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidPacketHeader)),
{
}

pub proof fn precinct_sop_omission_preserves_disabled_prefix_result(
    data: Seq<u8>, packed: Seq<u8>, parameters: crate::specs::Part1PrecinctPayloadParameters,
    header_limit: u64, work_limit: u64,
)
    ensures (data.len() < 2 || data[0] != 0xff
        || (data[1] != 0x91 && (parameters.packed || data[1] < 0x90))) ==>
        crate::specs::part1_precinct_payload_prefix(data, packed, parameters, header_limit, work_limit)
            == crate::specs::part1_precinct_payload_prefix(data, packed,
                crate::specs::Part1PrecinctPayloadParameters { sop: false, ..parameters }, header_limit, work_limit),
{
}

pub proof fn multi_sop_omission_preserves_disabled_prefix_result(
    data: Seq<u8>, offset: usize, header_limit: u64, work_limit: u64,
)
    ensures (data.len() < 2 || data[0] != 0xff || data[1] < 0x90) ==>
        crate::specs::part1_multi_packet_prefix(data, true, offset, header_limit, work_limit)
            == crate::specs::part1_multi_packet_prefix(data, false, offset, header_limit, work_limit),
{
}

pub proof fn precinct_payload_preserves_readonly_identity_and_every_context(
    state: crate::specs::Part1PacketPrecinctState, data: Seq<u8>, packed: Seq<u8>,
    parameters: crate::specs::Part1PrecinctPayloadParameters,
    header_limit: u64, pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures
        crate::specs::part1_precinct_payload(state, data, packed, parameters, header_limit,
            pass_limit, byte_limit, input_limit, work_limit).1.component == state.component,
        crate::specs::part1_precinct_payload(state, data, packed, parameters, header_limit,
            pass_limit, byte_limit, input_limit, work_limit).1.resolution == state.resolution,
        crate::specs::part1_precinct_payload(state, data, packed, parameters, header_limit,
            pass_limit, byte_limit, input_limit, work_limit).1.precinct == state.precinct,
        crate::specs::part1_precinct_payload(state, data, packed, parameters, header_limit,
            pass_limit, byte_limit, input_limit, work_limit).1.contexts == state.contexts,
{
    reveal(crate::specs::part1_precinct_payload_headers);
    reveal(crate::specs::part1_precinct_payload_after_headers);
    reveal(crate::specs::part1_precinct_payload_body);
}

pub proof fn precinct_payload_preflight_failure_precedes_every_coefficient_execution(
    state: crate::specs::Part1PacketPrecinctState,
    contributions: Seq<Option<crate::specs::Part1CodeBlockContribution>>, data: Seq<u8>,
    parameters: crate::specs::Part1PrecinctPayloadParameters, present: bool, contribution_count: u32,
    header_bytes: usize, body_start: usize, packed_consumed: usize,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
)
    ensures crate::specs::part1_packet_body_preflight(
        crate::specs::Part1PacketBodyPreflight { index: 0, end: body_start },
        contributions, data, parameters.error_offset).0.is_err() ==>
        crate::specs::part1_precinct_payload_body(state, contributions, data, parameters,
            present, contribution_count, header_bytes, body_start, packed_consumed,
            pass_limit, byte_limit, input_limit, work_limit).1 == state,
{
    reveal(crate::specs::part1_precinct_payload_body);
}

pub proof fn precinct_final_accounting_preserves_every_prior_effect_even_on_error(
    state: crate::specs::Part1PacketPrecinctState, parameters: crate::specs::Part1PrecinctPayloadParameters,
    present: bool, contribution_count: u32, segments: u32, passes: u32,
    header_bytes: usize, body_start: usize, tile_offset: usize, packed_consumed: usize,
)
    ensures crate::specs::part1_precinct_payload_finish(state, parameters, present, contribution_count,
        segments, passes, header_bytes, body_start, tile_offset, packed_consumed).1 == state,
{
}

pub proof fn raw_grid_absent_resolution_precedes_missing_count_storage(
    grid:crate::specs::Part1PacketGrid,component:u16,resolution:u8,
)
    ensures component<grid.components && resolution<grid.resolutions
        && (component as nat)<grid.component_resolutions.len()
        && resolution>=grid.component_resolutions[component as int] ==>
        crate::specs::part1_packet_grid_precinct_count(grid,component,resolution)==Ok(0),
{
}

pub proof fn raw_packet_candidate_failure_keeps_advanced_cursor_and_prior_emission(
    state:crate::specs::Part1PacketIterator,
)
    ensures state.candidate_index<state.grid.candidate_count
        && crate::specs::part1_packet_candidate(state.grid,state.order,state.candidate_index).is_err() ==>
        crate::specs::part1_packet_iterator_next(state).1.candidate_index==(state.candidate_index+1) as u64
        && crate::specs::part1_packet_iterator_next(state).1.emitted==state.emitted
        && crate::specs::part1_packet_iterator_next(state).0.is_err(),
{
    reveal(crate::specs::part1_packet_iterator_next);
}

pub proof fn raw_default_failure_does_not_synchronize_outer_emission(
    state:crate::specs::Part1ProgressionPacketIterator,
)
    ensures match state.default {
        None=>true,
        Some(default)=>crate::specs::part1_packet_iterator_next(default).0.is_err() ==>
            crate::specs::part1_progression_iterator_next(state).1.emitted==state.emitted
            && crate::specs::part1_progression_iterator_next(state).1.default
                ==Some(crate::specs::part1_packet_iterator_next(default).1),
    },
{
}

pub proof fn tile_metadata_ignores_owned_allocation_identity(
    left: Seq<crate::codestream::TilePartPayload<'_>>, right: Seq<crate::codestream::TilePartPayload<'_>>,
    components: u16, discard: Option<u8>,
)
    requires crate::codestream::tile_parts_owned_view(left) == crate::codestream::tile_parts_owned_view(right),
    ensures crate::specs::part2_tile_decode_metadata(left, components, discard)
        == crate::specs::part2_tile_decode_metadata(right, components, discard),
{
}

pub proof fn tile_byte_execution_ignores_owned_allocation_identity(
    left: Seq<crate::codestream::TilePartPayload<'_>>, right: Seq<crate::codestream::TilePartPayload<'_>>,
    grid: crate::specs::Part1PacketGrid, precincts: Seq<crate::specs::Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
)
    requires crate::codestream::tile_parts_owned_view(left) == crate::codestream::tile_parts_owned_view(right),
    ensures crate::specs::part1_progression_tile_decode(left, grid, precincts, selection, limits)
        == crate::specs::part1_progression_tile_decode(right, grid, precincts, selection, limits),
{
}

pub proof fn raw_tile_decoder_ignores_owned_allocation_identity(
    size: &crate::codestream::ImageSize, tile: u16,
    left: Seq<crate::codestream::TilePartPayload<'_>>, right: Seq<crate::codestream::TilePartPayload<'_>>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits,
    prepared: Seq<crate::specs::Part1AssemblyTile>, initial: (u64, u64, u64), work: u64,
)
    requires crate::codestream::tile_parts_owned_view(left) == crate::codestream::tile_parts_owned_view(right),
    ensures crate::specs::part2_decode_tile_parts_at(size, tile, left, caps, discard, limits, prepared, initial, work)
        == crate::specs::part2_decode_tile_parts_at(size, tile, right, caps, discard, limits, prepared, initial, work),
{
}

pub proof fn tile_boundary_preserves_real_work_seen_and_accounting_owners(
    params:crate::specs::Part1TilePacketParameters,p:crate::specs::Part1TilePacketProgress,
)
    ensures
        crate::specs::part1_tile_boundary(params,p).1.remaining_packets==p.remaining_packets,
        crate::specs::part1_tile_boundary(params,p).1.seen==p.seen,
        crate::specs::part1_tile_boundary(params,p).1.packets==p.packets,
        crate::specs::part1_tile_boundary(params,p).1.present_packets==p.present_packets,
        crate::specs::part1_tile_boundary(params,p).1.contributions==p.contributions,
        crate::specs::part1_tile_boundary(params,p).1.segments==p.segments,
        crate::specs::part1_tile_boundary(params,p).1.passes==p.passes,
        crate::specs::part1_tile_boundary(params,p).1.packet_header_bytes==p.packet_header_bytes,
        crate::specs::part1_tile_boundary(params,p).1.packet_body_bytes==p.packet_body_bytes,
{
}

pub proof fn late_packed_offset_overflow_reports_new_tile_offset_without_later_commits(
    p:crate::specs::Part1TilePacketProgress,decoded:crate::packet::PacketBodyDecode,
    tile_bytes:usize,packed_bytes:usize,expected:Option<u32>,seen_index:usize,
)
    ensures seen_index<p.seen.len() && decoded.bytes_consumed>0
        && (expected.is_none() || expected.unwrap()==decoded.bytes_consumed)
        && p.offset as nat+tile_bytes as nat<=usize::MAX
        && p.packed_offset as nat+packed_bytes as nat>usize::MAX ==>
        crate::specs::part1_tile_account(p,decoded,tile_bytes,packed_bytes,expected,seen_index)
            ==(Err(crate::specs::part1_packet_reader_error((p.offset+tile_bytes) as usize,
                crate::MalformedKind::ArithmeticOverflow)),
                crate::specs::Part1TilePacketProgress {offset:(p.offset+tile_bytes) as usize,..p}),
{
}

pub proof fn actual_tile_work_guard_follows_the_real_iterator_transition(
    params:crate::specs::Part1TilePacketParameters,state:crate::specs::Part1TilePacketExecution,
)
    ensures match crate::specs::part1_progression_iterator_next(state.progress.iterator).0 {
        Ok(Some(_))=>state.progress.remaining_packets==0 ==>
            crate::specs::part1_tile_run(params,state).0
                ==Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange))
            && crate::specs::part1_tile_run(params,state).1.precincts==state.precincts
            && crate::specs::part1_tile_run(params,state).1.progress.iterator
                ==crate::specs::part1_progression_iterator_next(state.progress.iterator).1,
        _=>true,
    },
{
    reveal(crate::specs::part1_tile_run);
}

pub proof fn actual_missing_packed_storage_rejects_after_complete_layer_writes(
    params:crate::specs::Part1TilePacketParameters,part:crate::codestream::TilePartPayload<'_>,
    p:crate::specs::Part1TilePacketProgress,coordinate:crate::packet::PacketCoordinate,
    expected:Option<u32>,precinct:crate::specs::Part1PacketPrecinctState,
)
    ensures p.current_tile_part>=params.input.packed.len() ==>
        crate::specs::part1_tile_precinct_packet(params,part,p,coordinate,expected,precinct)
            ==(Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidTilePart)),
                crate::specs::part1_precinct_context_layer(precinct,coordinate.layer)),
{
}

pub proof fn single_whole_payload_cap_precedes_all_tree_and_decoder_effects(
    s:crate::specs::Part1SinglePacketState,data:Seq<u8>,context:crate::packet::CodeBlockPacketContext,
    header_limit:u64,pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
)
    ensures data.len() as u64>header_limit ==>
        crate::specs::part1_single_code_block_packet(s,data,context,header_limit,pass_limit,byte_limit,input_limit,work_limit)
            ==(Err(crate::specs::part1_packet_reader_limit(crate::Resource::PacketHeaderBytes,header_limit,data.len() as u64)),s),
{
}

pub proof fn multi_sop_sequence_bytes_are_not_a_sequence_validation_premise(
    first_hi:u8,first_lo:u8,second_hi:u8,second_lo:u8,tail:Seq<u8>,offset:usize,header_limit:u64,work_limit:u64,
)
    ensures crate::specs::part1_multi_packet_prefix(seq![255u8,145u8,0u8,4u8,first_hi,first_lo]+tail,true,offset,header_limit,work_limit)
        ==crate::specs::part1_multi_packet_prefix(seq![255u8,145u8,0u8,4u8,second_hi,second_lo]+tail,true,offset,header_limit,work_limit),
{
    assert((seq![255u8,145u8,0u8,4u8,first_hi,first_lo]+tail).subrange(6,(6+tail.len()) as int) =~= tail);
    assert((seq![255u8,145u8,0u8,4u8,second_hi,second_lo]+tail).subrange(6,(6+tail.len()) as int) =~= tail);
}

pub proof fn common_preflight_overflow_retains_real_progress_and_caller_offset(
    s:crate::specs::Part1PacketBodyPreflight,contributions:Seq<Option<crate::specs::Part1CodeBlockContribution>>,
    data:Seq<u8>,truncated_offset:usize,local_offset:usize,
)
    ensures s.end==usize::MAX && s.index<contributions.len() && contributions[s.index as int].is_some()
        && contributions[s.index as int].unwrap().data_length>0 ==>
        crate::specs::part1_packet_body_preflight_at(s,contributions,data,truncated_offset,local_offset)
            ==(Err(crate::specs::part1_packet_reader_error(local_offset,crate::MalformedKind::ArithmeticOverflow)),s),
{
    reveal(crate::specs::part1_packet_body_preflight_at);
}

pub proof fn multi_complete_preflight_failure_precedes_every_coefficient_effect(
    s:crate::specs::Part1MultiPacketState,data:Seq<u8>,contributions:Seq<Option<crate::specs::Part1CodeBlockContribution>>,
    present:bool,count:u32,header:usize,start:usize,offset:usize,pass_limit:u32,byte_limit:u64,input_limit:u64,work_limit:u64,
)
    ensures crate::specs::part1_packet_body_preflight_at(crate::specs::Part1PacketBodyPreflight {index:0,end:start},
        contributions,data,offset,offset).0.is_err() ==>
        crate::specs::part1_multi_body(s,data,contributions,present,count,header,start,offset,pass_limit,byte_limit,input_limit,work_limit).1==s,
{
    reveal(crate::specs::part1_multi_body);
}

pub proof fn jpip_actual_layer_writes_precede_raw_shape_rejection(
    s:crate::specs::Part1PacketPrecinctState,template:&crate::codestream::TilePartPayload<'_>,
    data:Seq<u8>,sequence:u16,layer:u16,limits:&crate::ResourceLimits,
)
    ensures s.states.len()!=s.contexts.len() ==>
        crate::specs::part1_jpip_precinct_packet_inner(s,template,data,sequence,layer,limits)
            ==(Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidPacketHeader)),
                crate::specs::part1_precinct_context_layer(s,layer)),
{
}

pub proof fn jpip_actual_transaction_preserves_every_owner_on_any_error(
    s:crate::specs::Part1PacketPrecinctState,template:&crate::codestream::TilePartPayload<'_>,
    data:Seq<u8>,sequence:u16,layer:u16,limits:&crate::ResourceLimits,
)
    ensures crate::specs::part1_jpip_precinct_packet(s,template,data,sequence,layer,limits).0.is_err() ==>
        crate::specs::part1_jpip_precinct_packet(s,template,data,sequence,layer,limits).1==s,
{
}

}
