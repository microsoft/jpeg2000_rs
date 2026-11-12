pub(crate) type CompositionPixelInputs = ([u16; 3], [u16; 3], u16, u16, bool);

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod composition;
#[cfg(verus_keep_ghost)]
pub(crate) use composition::inverse_alpha;
pub(crate) use composition::{
    chroma_key_alpha, compose_planar_pixel, composition_clip, composition_mapped_offset,
    composition_pixel_index, effective_layer_count, loop_frame, normalized_sample_product,
};
#[cfg(any(test, verus_keep_ghost))]
pub(crate) use composition::{
    gather_composition_pixel, scatter_composition_pixel, source_over_alpha_numerator,
    source_over_color_numerator, source_over_pixel, source_over_rounded_ratio,
    try_store_composition_sample,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod geometry;
pub(crate) use geometry::{
    ceil_div_u32, component_output_shape_valid, crg_component_predecessor,
    decode_output_shape_valid, registered_extent, registered_source_coordinate, tile_clip_end,
    tile_clip_start,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod headers;
pub(crate) use headers::{
    cbd_precision, cbd_signed, channel_definition_valid, component_mapping_valid,
    crg_payload_bytes, dfs_direction_code, exact_consumption, first_override_allowed,
    main_header_boundary, marker_value, metadata_count, packed_two_bit_bytes,
    palette_coordinates_valid, parser_progress, part15_cap_payload_length,
    part15_capability_fields_valid, part15_cleanup_u_bound, part15_codestream_class,
    part15_component_allowed, part15_headers_allowed, part15_jph_branding, part15_magnitude_bound,
    part15_mode_allows, part15_signaling_valid, tile_header_boundary, tlm_length_bytes,
    tlm_tile_index_bytes,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod jpip;
pub(crate) use jpip::{
    jpip_auxiliary_present, jpip_available_bytes, jpip_box_length, jpip_databin_complete,
    jpip_databin_identity, jpip_eor_extent, jpip_final_length_consistent, jpip_fragment_valid,
    jpip_header_form_valid, jpip_header_has_explicit_class, jpip_header_has_explicit_codestream,
    jpip_merge_end, jpip_merge_start, jpip_metadata_descent_allowed, jpip_missing_length,
    jpip_overlap_consistent, jpip_packet_reframed_length, jpip_precinct_in_class,
    jpip_progression_supported, jpip_progressive_update_valid, jpip_quality_prefix_available,
    jpip_range_complete, jpip_reconstruction_length, jpip_reframed_marker_removed,
    jpip_standard_class_assigned, jpip_tile_transition_sufficient, jpip_transaction_commit,
    jpip_vbas_step,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod packet;
pub(crate) use packet::{
    eph_valid, packet_bit, packet_data_bits, packet_length_matches, packet_logical_bytes,
    packet_next_included, packet_next_lblock, packet_next_passes, progression_advance,
    progression_digit, progression_emit_allowed, sop_sequence, sop_valid, tag_inherited_low,
    tag_step_low, tag_step_value,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod reconstruction;
pub(crate) use reconstruction::{
    atk_next_parity, atk_reconstruction_step, binary_fixed_shift, clip_sample, five_three_predict,
    five_three_update, fixed_round_q16, irreversible_centered, irreversible_scale, level_shift,
    maxshift_restore, mct_fragment_complete, mct_fragment_next, mct_reverse_stage, nine_seven_lift,
    nine_seven_scale, nlt_binary_complement, rct_blue, rct_green, rct_red,
    reversible_inverse_quantize, signed_to_nominal, wavelet_detail_advance,
    wavelet_next_resolution, wavelet_sample_count,
};
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod tier1;
pub(crate) use tier1::{
    ht_bin_center_odd, ht_claim_available, ht_cleanup_byte_claims_valid, ht_forward_data_bits,
    ht_forward_stuffing_valid, ht_kappa_completion, ht_magnitude_payload_bits, ht_magnitude_sign,
    ht_magref_eligible, ht_magsgn_end, ht_magsgn_fill_value, ht_mel_exponent, ht_mel_next_state,
    ht_mel_stuffing_valid, ht_mixed_selects_legacy, ht_multiple_set_allowed,
    ht_noninitial_vlc_context, ht_patch_end, ht_placeholder_passes, ht_quad_origin_valid,
    ht_quad_sample_in_bounds, ht_refinement_pass_total, ht_replacement_allowed,
    ht_reverse_data_bits, ht_scup, ht_segment_passes, ht_sigprop_eligible, ht_stripe_rows,
    ht_substantive_passes, ht_uvlc_value, ht_vlc_table_index, ht_vlc_word_valid, mq_byte_addend,
    mq_byte_advances, mq_byte_class, mq_byte_ct, mq_code_subtract, mq_decision,
    mq_interval_subtract, mq_next_mps, mq_renorm_ct, mq_renorm_double, tier1_cleanup_eligible,
    tier1_decoded_sign, tier1_magref_eligible, tier1_midpoint_delta, tier1_pass_code,
    tier1_pass_complete, tier1_predicted_negative, tier1_refined_magnitude,
    tier1_refinement_context, tier1_sign_offset, tier1_sigprop_eligible, tier1_stripe_rows,
    tier1_zero_context,
};
