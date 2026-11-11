use vstd::prelude::*;

use crate::specs::{
    ads_payload_bytes, atk_reconstruction_step, atk_update_parity, bounded_jpip_transcode,
    bounded_loop_frame, clamp_color_sample, clipped_composition_extent, color_output_bytes,
    complete_jpip_databin, complete_jpip_range, complete_mct_fragment_series,
    composition_instruction_work, composition_output_bytes, consistent_jpip_final_length,
    consistent_part15_signaling, effective_jpx_layer_count, ht_cleanup_byte_claims_valid,
    ht_completed_u, ht_kappa_extension, ht_placeholder_passes, ht_substantive_passes,
    jpip_precinct_in_class, jpip_quality_prefix_available, jpip_reconstructed_box_length,
    jpip_tile_transition_sufficient, magnitude_addition, magnitude_less, magnitude_limb_index,
    magnitude_limb_offset, magnitude_shift_fits, maxshift_restored_magnitude,
    mct_dependency_coefficients, mct_wavelet_work_units, mct_work_units, mixed_block_selects_ht,
    nested_metadata_work, palette_linear_index, part9_auxiliary_present, part9_available_bytes,
    part9_class_identifier_valid, part9_databin_identity, part9_eor_extent,
    part9_header_form_valid, part9_header_has_explicit_class, part9_header_has_explicit_codestream,
    part9_merge_end, part9_merge_start, part9_metadata_descent_allowed, part9_missing_length,
    part9_overlap_consistent, part9_packet_reframed_length, part9_precinct_flat_identity,
    part9_progression_supported, part9_reconstruction_length, part9_reframed_marker_removed,
    part9_transaction_commit, part9_vbas_step, registered_channel_count,
    resampled_component_coordinate, signed_color_to_nominal, tile_transform_scope,
    valid_box_lengths, valid_cbd_scope, valid_codestream_header_associations,
    valid_ht_cleanup_partition, valid_ht_pass_group, valid_ht_quad_origin,
    valid_ht_refinement_segment, valid_ht_style_prefix, valid_jp2_primary_brand,
    valid_jph_branding, valid_jpip_codestream_layout, valid_jpip_fragment,
    valid_jpip_precinct_coordinate, valid_jpip_progressive_update,
    valid_layer_codestream_reference, valid_magnitude_bit, valid_mct_dimensions,
    valid_mct_fragment_index, valid_mct_matrix_bounds, valid_mct_stage_edge,
    valid_mct_wavelet_partition, valid_palette_lookup, valid_selection_region,
    valid_signed_color_sample,
};

verus! {

pub proof fn production_precinct_initialization_step(
    executions: Seq<crate::specs::Part2PacketSubbandExecution>, style: crate::tier1::Tier1CodingStyle,
    limits: &crate::ResourceLimits, index: nat,
    before: crate::specs::Part1PacketPrecinctState, total_before: u64,
    after: crate::specs::Part1PacketPrecinctState, total_after: u64,
)
    requires index < executions.len(),
        crate::specs::part2_precinct_execution(before, total_before, executions[index as int], style, limits)
            == Ok((after, total_after)),
    ensures crate::specs::part2_precinct_initialization_run(executions, style, limits, index, before, total_before)
        == crate::specs::part2_precinct_initialization_run(executions, style, limits, index + 1, after, total_after),
{
    reveal_with_fuel(crate::specs::part2_precinct_initialization_run, 1);
}

pub proof fn production_packet_grid_component_start(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    layers: u16, limits: &crate::ResourceLimits, tile: Option<u16>, discard: u8,
    descriptors: crate::specs::Part2ComponentResolutionCounts, component: u16,
    counts: Seq<u32>, total: u64, style: crate::codestream::CodingStyle, resolutions: u8,
)
    requires component < crate::codestream::image_size_component_count(size),
        crate::codestream::component_coding_style_result(styles, component) == Ok(style),
        style.decomposition_levels < u8::MAX,
        resolutions as int == style.decomposition_levels as int + 1,
    ensures crate::specs::part2_packet_grid_components_run(
        size, styles, layers, limits, tile, discard, descriptors, component, counts, total,
    ) == crate::specs::part2_packet_grid_resolutions_run(
        size, styles, layers, limits, tile, discard, descriptors, component, style, resolutions, 0, counts, total,
    ),
{
    reveal_with_fuel(crate::specs::part2_packet_grid_components_run, 1);
}

pub proof fn production_resolution_scales_empty(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>,
)
    ensures crate::specs::part2_resolution_scale_prefix(levels, directions, 0) == Ok((1, 1)),
{
    reveal_with_fuel(crate::specs::part2_resolution_scale_prefix, 1);
}

pub proof fn production_resolution_scales_step(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, count: nat,
)
    ensures crate::specs::part2_resolution_scale_prefix(levels, directions, count + 1) == {
        match crate::specs::part2_resolution_scale_prefix(levels, directions, count) {
            Err(error) => Err(error),
            Ok(previous) => crate::specs::part2_resolution_scale_step(levels, directions, count as u8, previous),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_resolution_scale_prefix, 1);
}

pub proof fn production_resolution_scales_error(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, count: nat, finish: nat,
)
    requires count <= finish, crate::specs::part2_resolution_scale_prefix(levels, directions, count).is_err(),
    ensures crate::specs::part2_resolution_scale_prefix(levels, directions, finish)
        == crate::specs::part2_resolution_scale_prefix(levels, directions, count),
    decreases finish - count,
{
    if count < finish {
        production_resolution_scales_step(levels, directions, (finish - 1) as nat);
        production_resolution_scales_error(levels, directions, count, (finish - 1) as nat);
    }
}

pub proof fn production_execution_components_empty(header: crate::specs::Part2ExecutionHeader)
    ensures crate::specs::part2_execution_components_prefix(header, 0) == Ok(()),
{
    reveal_with_fuel(crate::specs::part2_execution_components_prefix, 1);
}

pub proof fn production_execution_components_step(header: crate::specs::Part2ExecutionHeader, count: nat)
    ensures crate::specs::part2_execution_components_prefix(header, count + 1) == {
        match crate::specs::part2_execution_components_prefix(header, count) {
            Err(error) => Err(error),
            Ok(()) => crate::specs::part2_validate_execution_component(header, count as u16),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_execution_components_prefix, 1);
}

pub proof fn production_execution_components_error(header: crate::specs::Part2ExecutionHeader, count: nat, finish: nat)
    requires count <= finish, crate::specs::part2_execution_components_prefix(header, count).is_err(),
    ensures crate::specs::part2_execution_components_prefix(header, finish)
        == crate::specs::part2_execution_components_prefix(header, count),
    decreases finish - count,
{
    if count < finish {
        production_execution_components_step(header, (finish - 1) as nat);
        production_execution_components_error(header, count, (finish - 1) as nat);
    }
}

pub proof fn production_execution_tiles_empty(
    headers: Seq<crate::specs::Part2ExecutionHeader>, main: Seq<(u8, bool)>, components: u16,
)
    ensures crate::specs::part2_execution_tiles_prefix(headers, main, components, 0) == Ok(()),
{
    reveal_with_fuel(crate::specs::part2_execution_tiles_prefix, 1);
}

pub proof fn production_execution_tiles_step(
    headers: Seq<crate::specs::Part2ExecutionHeader>, main: Seq<(u8, bool)>, components: u16, count: nat,
)
    requires count < headers.len(),
    ensures crate::specs::part2_execution_tiles_prefix(headers, main, components, count + 1) == {
        match crate::specs::part2_execution_tiles_prefix(headers, main, components, count) {
            Err(error) => Err(error),
            Ok(()) => crate::specs::part2_validate_execution_tile(headers[count as int], main, components),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_execution_tiles_prefix, 1);
}

pub proof fn production_execution_tiles_error(
    headers: Seq<crate::specs::Part2ExecutionHeader>, main: Seq<(u8, bool)>, components: u16, count: nat, finish: nat,
)
    requires count <= finish <= headers.len(),
        crate::specs::part2_execution_tiles_prefix(headers, main, components, count).is_err(),
    ensures crate::specs::part2_execution_tiles_prefix(headers, main, components, finish)
        == crate::specs::part2_execution_tiles_prefix(headers, main, components, count),
    decreases finish - count,
{
    if count < finish {
        production_execution_tiles_step(headers, main, components, (finish - 1) as nat);
        production_execution_tiles_error(headers, main, components, count, (finish - 1) as nat);
    }
}

pub proof fn production_opacity_columns_empty(context: crate::specs::Part2OpacityCopyContext, y: u32, initial: Seq<u16>)
    ensures crate::specs::part2_opacity_columns_prefix(context, y, initial, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part2_opacity_columns_prefix, 1);
}

pub proof fn production_opacity_columns_step(context: crate::specs::Part2OpacityCopyContext, y: u32, initial: Seq<u16>, count: nat)
    ensures crate::specs::part2_opacity_columns_prefix(context, y, initial, count + 1) == {
        let previous = crate::specs::part2_opacity_columns_prefix(context, y, initial, count);
        match previous.0 { Err(_) => previous, Ok(()) => crate::specs::part2_opacity_pixel(context, count as u32, y, previous.1) }
    },
{
    reveal_with_fuel(crate::specs::part2_opacity_columns_prefix, 1);
}

pub proof fn production_opacity_columns_error(
    context: crate::specs::Part2OpacityCopyContext, y: u32, initial: Seq<u16>, count: nat, finish: nat,
)
    requires count <= finish, crate::specs::part2_opacity_columns_prefix(context, y, initial, count).0.is_err(),
    ensures crate::specs::part2_opacity_columns_prefix(context, y, initial, finish)
        == crate::specs::part2_opacity_columns_prefix(context, y, initial, count),
    decreases finish - count,
{
    if count < finish {
        production_opacity_columns_step(context, y, initial, (finish - 1) as nat);
        production_opacity_columns_error(context, y, initial, count, (finish - 1) as nat);
    }
}

pub proof fn production_opacity_rows_empty(context: crate::specs::Part2OpacityCopyContext, width: u32, initial: Seq<u16>)
    ensures crate::specs::part2_opacity_rows_prefix(context, width, initial, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part2_opacity_rows_prefix, 1);
}

pub proof fn production_opacity_rows_step(context: crate::specs::Part2OpacityCopyContext, width: u32, initial: Seq<u16>, count: nat)
    ensures crate::specs::part2_opacity_rows_prefix(context, width, initial, count + 1) == {
        let previous = crate::specs::part2_opacity_rows_prefix(context, width, initial, count);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => crate::specs::part2_opacity_columns_prefix(context, count as u32, previous.1, width as nat),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_opacity_rows_prefix, 1);
}

pub proof fn production_opacity_rows_error(
    context: crate::specs::Part2OpacityCopyContext, width: u32, initial: Seq<u16>, count: nat, finish: nat,
)
    requires count <= finish, crate::specs::part2_opacity_rows_prefix(context, width, initial, count).0.is_err(),
    ensures crate::specs::part2_opacity_rows_prefix(context, width, initial, finish)
        == crate::specs::part2_opacity_rows_prefix(context, width, initial, count),
    decreases finish - count,
{
    if count < finish {
        production_opacity_rows_step(context, width, initial, (finish - 1) as nat);
        production_opacity_rows_error(context, width, initial, count, (finish - 1) as nat);
    }
}

pub proof fn production_chroma_cover_step(colors: Seq<Seq<u16>>, samples: nat, count: nat)
    requires count < colors.len(),
    ensures crate::proofs::internal_specs::part2_chroma_cover_prefix(colors, samples, count + 1)
        == (crate::proofs::internal_specs::part2_chroma_cover_prefix(colors, samples, count)
            && crate::specs::part2_chroma_plane_has_samples(colors[count as int], samples)),
{
    let prefix = crate::proofs::internal_specs::part2_chroma_cover_prefix(colors, samples, count);
    let next = crate::proofs::internal_specs::part2_chroma_cover_prefix(colors, samples, count + 1);
    let current = crate::specs::part2_chroma_plane_has_samples(colors[count as int], samples);
    if prefix && current {
        assert forall|channel: int| 0 <= channel < count + 1 implies
            #[trigger] crate::specs::part2_chroma_plane_has_samples(colors[channel], samples) by {
            if channel < count {
                assert(crate::specs::part2_chroma_plane_has_samples(colors[channel], samples));
            } else { assert(channel == count); }
        }
    } else if next {
        assert forall|channel: int| 0 <= channel < count implies
            #[trigger] crate::specs::part2_chroma_plane_has_samples(colors[channel], samples) by {
            assert(0 <= channel < count + 1);
        }
        assert(prefix);
        assert(current);
        assert(false);
    }
}

pub proof fn production_chroma_cover_complete(colors: Seq<Seq<u16>>, samples: nat)
    ensures crate::proofs::internal_specs::part2_chroma_cover_prefix(colors, samples, colors.len())
        == crate::specs::part2_chroma_sources_cover(colors, samples),
{
}

pub proof fn production_chroma_descriptors_empty(descriptors: Seq<(u8, bool)>)
    ensures crate::specs::part2_chroma_descriptor_bytes(descriptors, 0) == Ok(0),
{
    reveal_with_fuel(crate::specs::part2_chroma_descriptor_bytes, 1);
}

pub proof fn production_chroma_descriptors_step(descriptors: Seq<(u8, bool)>, count: nat)
    requires count < descriptors.len(),
    ensures crate::specs::part2_chroma_descriptor_bytes(descriptors, count + 1) == {
        match crate::specs::part2_chroma_descriptor_bytes(descriptors, count) {
            Err(error) => Err(error),
            Ok(previous) => {
                let bits = descriptors[count as int].0;
                if bits == 0 || bits > 38 { Err(crate::specs::part2_composition_error(false)) }
                else {
                    let bytes = (bits as nat + 7) / 8;
                    if previous as nat + bytes > usize::MAX as nat { Err(crate::specs::part2_composition_error(true)) }
                    else { Ok((previous as nat + bytes) as usize) }
                }
            },
        }
    },
{
    reveal_with_fuel(crate::specs::part2_chroma_descriptor_bytes, 1);
}

pub proof fn production_chroma_descriptors_error(descriptors: Seq<(u8, bool)>, count: nat, finish: nat)
    requires count <= finish <= descriptors.len(),
        crate::specs::part2_chroma_descriptor_bytes(descriptors, count).is_err(),
    ensures crate::specs::part2_chroma_descriptor_bytes(descriptors, finish)
        == crate::specs::part2_chroma_descriptor_bytes(descriptors, count),
    decreases finish - count,
{
    if count < finish {
        production_chroma_descriptors_step(descriptors, (finish - 1) as nat);
        production_chroma_descriptors_error(descriptors, count, (finish - 1) as nat);
    }
}

pub proof fn production_component_keys_empty(values: Seq<u8>, descriptors: Seq<(u8, bool)>)
    ensures crate::specs::part2_component_keys_prefix(values, descriptors, 0) == (Ok(()), Seq::<u16>::empty(), 0usize),
{
    reveal_with_fuel(crate::specs::part2_component_keys_prefix, 1);
}

pub proof fn production_component_keys_step(values: Seq<u8>, descriptors: Seq<(u8, bool)>, count: nat)
    requires count < descriptors.len(),
    ensures crate::specs::part2_component_keys_prefix(values, descriptors, count + 1) == {
        let previous = crate::specs::part2_component_keys_prefix(values, descriptors, count);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => crate::specs::part2_append_component_key(values, descriptors[count as int], previous.1, previous.2),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_component_keys_prefix, 1);
}

pub proof fn production_component_keys_error(values: Seq<u8>, descriptors: Seq<(u8, bool)>, count: nat, finish: nat)
    requires count <= finish <= descriptors.len(),
        crate::specs::part2_component_keys_prefix(values, descriptors, count).0.is_err(),
    ensures crate::specs::part2_component_keys_prefix(values, descriptors, finish)
        == crate::specs::part2_component_keys_prefix(values, descriptors, count),
    decreases finish - count,
{
    if count < finish {
        production_component_keys_step(values, descriptors, (finish - 1) as nat);
        production_component_keys_error(values, descriptors, count, (finish - 1) as nat);
    }
}

pub proof fn production_chroma_bytes_step(values: Seq<u8>, start: nat, count: nat)
    requires start + count < values.len(),
    ensures crate::specs::part2_chroma_key_bytes(values, start, count + 1)
        == crate::specs::part2_chroma_key_bytes(values, start, count) * 256 + values[(start + count) as int] as nat,
        crate::proofs::internal_specs::part2_chroma_byte_bound(count + 1)
            == crate::proofs::internal_specs::part2_chroma_byte_bound(count) * 256 + 255,
{
    reveal_with_fuel(crate::specs::part2_chroma_key_bytes, 1);
    reveal_with_fuel(crate::proofs::internal_specs::part2_chroma_byte_bound, 1);
}

pub proof fn production_chroma_byte_bound(count: nat)
    requires count <= 5,
    ensures crate::proofs::internal_specs::part2_chroma_byte_bound(count) <= 1099511627775,
{
    reveal_with_fuel(crate::proofs::internal_specs::part2_chroma_byte_bound, 6);
}

pub proof fn production_chroma_normalization(raw: u64, bits: u8, signed: bool)
    requires 0 < bits <= 38,
    ensures {
        let maximum = ((1u64 << bits) - 1) as u64;
        let nominal = if signed { (raw & maximum) ^ (((maximum + 1) / 2) as u64) } else { raw & maximum };
        nominal <= maximum
            && crate::specs::color_normalize_unsigned(nominal, bits)
                == Ok(crate::specs::part2_chroma_key_normalize(raw as nat, bits, signed))
    },
{
    crate::proofs::spec_properties::color_precision_binary_bounds(bits);
    assert((if signed { (raw & (((1u64 << bits) - 1) as u64)) ^ (((1u64 << bits) / 2) as u64) }
        else { raw & (((1u64 << bits) - 1) as u64) })
        <= (((1u64 << bits) - 1) as u64)) by(bit_vector) requires 0 < bits <= 38;
}

pub proof fn production_registered_columns_empty(
    context: crate::specs::Part2RegistrationContext, y: u32, source_y: u32,
    colors: Seq<Seq<u16>>, alpha: Seq<u16>,
)
    ensures crate::specs::part2_registered_columns_prefix(context, y, source_y, colors, alpha, 0) == (Ok(()), colors, alpha),
{
    reveal_with_fuel(crate::specs::part2_registered_columns_prefix, 1);
}

pub proof fn production_registered_columns_step(
    context: crate::specs::Part2RegistrationContext, y: u32, source_y: u32,
    colors: Seq<Seq<u16>>, alpha: Seq<u16>, count: nat,
)
    ensures crate::specs::part2_registered_columns_prefix(context, y, source_y, colors, alpha, count + 1) == {
        let previous = crate::specs::part2_registered_columns_prefix(context, y, source_y, colors, alpha, count);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => crate::specs::part2_registered_column(context, y, source_y, count as u32, previous.1, previous.2),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_registered_columns_prefix, 1);
}

pub proof fn production_registered_columns_error(
    context: crate::specs::Part2RegistrationContext, y: u32, source_y: u32,
    colors: Seq<Seq<u16>>, alpha: Seq<u16>, count: nat, finish: nat,
)
    requires count <= finish,
        crate::specs::part2_registered_columns_prefix(context, y, source_y, colors, alpha, count).0.is_err(),
    ensures crate::specs::part2_registered_columns_prefix(context, y, source_y, colors, alpha, finish)
        == crate::specs::part2_registered_columns_prefix(context, y, source_y, colors, alpha, count),
    decreases finish - count,
{
    if count < finish {
        production_registered_columns_step(context, y, source_y, colors, alpha, (finish - 1) as nat);
        production_registered_columns_error(context, y, source_y, colors, alpha, count, (finish - 1) as nat);
    }
}

pub proof fn production_registered_rows_empty(
    context: crate::specs::Part2RegistrationContext, colors: Seq<Seq<u16>>, alpha: Seq<u16>,
)
    ensures crate::specs::part2_registered_rows_prefix(context, colors, alpha, 0) == (Ok(()), colors, alpha),
{
    reveal_with_fuel(crate::specs::part2_registered_rows_prefix, 1);
}

pub proof fn production_registered_rows_step(
    context: crate::specs::Part2RegistrationContext, colors: Seq<Seq<u16>>, alpha: Seq<u16>, count: nat,
)
    ensures crate::specs::part2_registered_rows_prefix(context, colors, alpha, count + 1) == {
        let previous = crate::specs::part2_registered_rows_prefix(context, colors, alpha, count);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => crate::specs::part2_registered_row(context, count as u32, previous.1, previous.2),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_registered_rows_prefix, 1);
}

pub proof fn production_registered_rows_error(
    context: crate::specs::Part2RegistrationContext, colors: Seq<Seq<u16>>, alpha: Seq<u16>, count: nat, finish: nat,
)
    requires count <= finish, crate::specs::part2_registered_rows_prefix(context, colors, alpha, count).0.is_err(),
    ensures crate::specs::part2_registered_rows_prefix(context, colors, alpha, finish)
        == crate::specs::part2_registered_rows_prefix(context, colors, alpha, count),
    decreases finish - count,
{
    if count < finish {
        production_registered_rows_step(context, colors, alpha, (finish - 1) as nat);
        production_registered_rows_error(context, colors, alpha, count, (finish - 1) as nat);
    }
}

pub proof fn production_registered_colors_empty(
    initial: Seq<Seq<u16>>, source: Seq<Seq<u16>>, source_index: usize, destination: usize,
)
    ensures crate::specs::part2_registered_colors_prefix(initial, source, source_index, destination, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part2_registered_colors_prefix, 1);
}

pub proof fn production_registered_colors_step(
    initial: Seq<Seq<u16>>, source: Seq<Seq<u16>>, source_index: usize, destination: usize, count: nat,
)
    ensures crate::specs::part2_registered_colors_prefix(initial, source, source_index, destination, count + 1) == {
        let previous = crate::specs::part2_registered_colors_prefix(initial, source, source_index, destination, count);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => crate::specs::part2_registered_color_store(previous.1, source, count, source_index, destination),
        }
    },
{
    reveal_with_fuel(crate::specs::part2_registered_colors_prefix, 1);
}

pub proof fn production_registered_colors_error(
    initial: Seq<Seq<u16>>, source: Seq<Seq<u16>>, source_index: usize, destination: usize,
    count: nat, finish: nat,
)
    requires count <= finish,
        crate::specs::part2_registered_colors_prefix(initial, source, source_index, destination, count).0.is_err(),
    ensures crate::specs::part2_registered_colors_prefix(initial, source, source_index, destination, finish)
        == crate::specs::part2_registered_colors_prefix(initial, source, source_index, destination, count),
    decreases finish - count,
{
    if count < finish {
        production_registered_colors_step(initial, source, source_index, destination, (finish - 1) as nat);
        production_registered_colors_error(initial, source, source_index, destination, count, (finish - 1) as nat);
    }
}

pub proof fn production_chroma_key_prefix_step(
    colors: Seq<Seq<u16>>, keys: Seq<u16>, pixel: int, count: nat,
)
    requires count < colors.len(),
    ensures crate::proofs::internal_specs::part2_chroma_key_prefix_matches(colors, keys, pixel, count + 1)
        == (crate::proofs::internal_specs::part2_chroma_key_prefix_matches(colors, keys, pixel, count)
            && 0 <= pixel < colors[count as int].len() && count < keys.len()
            && colors[count as int][pixel] == keys[count as int]),
{
    reveal(crate::proofs::internal_specs::part2_chroma_key_prefix_matches);
    let prefix = crate::proofs::internal_specs::part2_chroma_key_prefix_matches(colors, keys, pixel, count);
    let next = crate::proofs::internal_specs::part2_chroma_key_prefix_matches(colors, keys, pixel, count + 1);
    let current = crate::specs::part2_chroma_key_channel_matches(colors, keys, pixel, count as int);
    if prefix && current {
        assert forall|channel: int| 0 <= channel < count + 1 implies
            #[trigger] crate::specs::part2_chroma_key_channel_matches(colors, keys, pixel, channel) by {
            if channel < count {
                assert(crate::specs::part2_chroma_key_channel_matches(colors, keys, pixel, channel));
            } else {
                assert(channel == count);
            }
        }
    } else if next {
        assert forall|channel: int| 0 <= channel < count implies
            #[trigger] crate::specs::part2_chroma_key_channel_matches(colors, keys, pixel, channel) by {
            assert(0 <= channel < count + 1);
        }
        assert(prefix);
        assert(current);
        assert(false);
    }
}

pub proof fn production_chroma_key_prefix_complete(colors: Seq<Seq<u16>>, keys: Seq<u16>, pixel: int)
    ensures crate::specs::part2_chroma_key_pixel(colors, keys, pixel)
        == if crate::proofs::internal_specs::part2_chroma_key_prefix_matches(colors, keys, pixel, colors.len()) {
            0u16
        } else { u16::MAX },
{
    reveal(crate::proofs::internal_specs::part2_chroma_key_prefix_matches);
    reveal(crate::specs::part2_chroma_key_pixel);
}

pub proof fn production_reconstruct_components_empty(
    initial: Seq<crate::specs::Part1AssemblyTile>, plans: Seq<crate::specs::Part1PreparePlan>,
    precincts: Seq<Seq<crate::specs::Tier1RawPlane>>, styles: crate::codestream::ComponentCodingStyles,
    kernels: Seq<(u8, crate::specs::Part2RawKernel)>, maximum: u64,
)
    ensures crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part2_reconstruct_components_prefix, 1);
}

pub proof fn production_reconstruct_components_step(
    initial: Seq<crate::specs::Part1AssemblyTile>, plans: Seq<crate::specs::Part1PreparePlan>,
    precincts: Seq<Seq<crate::specs::Tier1RawPlane>>, styles: crate::codestream::ComponentCodingStyles,
    kernels: Seq<(u8, crate::specs::Part2RawKernel)>, maximum: u64, count: nat,
)
    requires count < plans.len(),
    ensures crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum, count + 1)
        == {
            let previous = crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => match crate::specs::part2_reconstruct_component(plans[count as int], precincts, styles, kernels, maximum) {
                    Err(error) => (Err(error), previous.1), Ok(component) => (Ok(()), previous.1.push(component)),
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_reconstruct_components_prefix, 1);
}

pub proof fn production_reconstruct_components_error(
    initial: Seq<crate::specs::Part1AssemblyTile>, plans: Seq<crate::specs::Part1PreparePlan>,
    precincts: Seq<Seq<crate::specs::Tier1RawPlane>>, styles: crate::codestream::ComponentCodingStyles,
    kernels: Seq<(u8, crate::specs::Part2RawKernel)>, maximum: u64, count: nat, finish: nat,
)
    requires count <= finish <= plans.len(),
    ensures crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum, count).0.is_err()
        ==> crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum, finish)
            == crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum, count),
    decreases finish - count,
{
    if count < finish {
        production_reconstruct_components_error(initial, plans, precincts, styles, kernels, maximum, count, (finish - 1) as nat);
        production_reconstruct_components_step(initial, plans, precincts, styles, kernels, maximum, (finish - 1) as nat);
    }
}

pub proof fn production_kernel_registry_empty(kernels: Seq<(u8, crate::specs::Part2RawKernel)>, index: u8)
    ensures crate::specs::part2_kernel_registry_prefix(kernels, index, 0) == None,
{
    reveal_with_fuel(crate::specs::part2_kernel_registry_prefix, 1);
}

pub proof fn production_kernel_registry_step(kernels: Seq<(u8, crate::specs::Part2RawKernel)>, index: u8, count: nat)
    requires count < kernels.len(),
    ensures crate::specs::part2_kernel_registry_prefix(kernels, index, count + 1)
        == match crate::specs::part2_kernel_registry_prefix(kernels, index, count) {
            Some(value) => Some(value),
            None => if kernels[count as int].0 == index { Some(kernels[count as int].1) } else { None },
        },
{
    reveal_with_fuel(crate::specs::part2_kernel_registry_prefix, 1);
}

pub proof fn production_kernel_registry_found(kernels: Seq<(u8, crate::specs::Part2RawKernel)>, index: u8, count: nat, finish: nat)
    requires count <= finish <= kernels.len(),
    ensures crate::specs::part2_kernel_registry_prefix(kernels, index, count).is_some()
        ==> crate::specs::part2_kernel_registry_prefix(kernels, index, finish)
            == crate::specs::part2_kernel_registry_prefix(kernels, index, count),
    decreases finish - count,
{
    if count < finish {
        production_kernel_registry_found(kernels, index, count, (finish - 1) as nat);
        production_kernel_registry_step(kernels, index, (finish - 1) as nat);
    }
}

pub proof fn production_prepared_standard_empty(before: Seq<crate::specs::Part1AssemblyTile>, irreversible: bool)
    ensures crate::specs::part1_prepared_standard_prefix(before, irreversible, 0) == (Ok(()), before),
{
    reveal_with_fuel(crate::specs::part1_prepared_standard_prefix, 1);
}

pub proof fn production_prepared_standard_step(before: Seq<crate::specs::Part1AssemblyTile>, irreversible: bool, count: nat)
    requires count <= usize::MAX,
    ensures crate::specs::part1_prepared_standard_prefix(before, irreversible, count + 1)
        == {
            let previous = crate::specs::part1_prepared_standard_prefix(before, irreversible, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => crate::specs::part1_prepared_standard_pixel(previous.1, count as usize, irreversible),
            }
        },
{
    reveal_with_fuel(crate::specs::part1_prepared_standard_prefix, 1);
}

pub proof fn production_prepared_standard_error(before: Seq<crate::specs::Part1AssemblyTile>, irreversible: bool, count: nat, finish: nat)
    requires count <= finish <= usize::MAX,
    ensures crate::specs::part1_prepared_standard_prefix(before, irreversible, count).0.is_err()
        ==> crate::specs::part1_prepared_standard_prefix(before, irreversible, finish)
            == crate::specs::part1_prepared_standard_prefix(before, irreversible, count),
    decreases finish - count,
{
    if count < finish {
        production_prepared_standard_error(before, irreversible, count, (finish - 1) as nat);
        production_prepared_standard_step(before, irreversible, (finish - 1) as nat);
    }
}

pub proof fn production_mct_unit_result(result: Result<(), crate::DecodeError>)
    requires result.is_ok(),
    ensures result == Ok(()),
{
    match result { Ok(value) => { assert(value == ()); }, Err(_) => {} }
}

pub proof fn production_mct_prepared_inputs_shape(
    before: Seq<crate::specs::Part1AssemblyTile>, count: u16, infos: Seq<crate::codestream::ComponentInfo>,
)
    ensures
        crate::specs::part2_mct_prepared_inputs(before, count, infos).1.len() <= before.len(),
        crate::specs::part2_mct_prepared_inputs(before, count, infos).0.is_ok()
            ==> crate::specs::part2_mct_prepared_inputs(before, count, infos).1.len() == before.len(),
        forall |index: int| 0 <= index < crate::specs::part2_mct_prepared_inputs(before, count, infos).1.len() ==>
            crate::specs::part2_mct_prepared_inputs(before, count, infos).1[index].2 == before[index].5
                && crate::specs::part2_mct_prepared_inputs(before, count, infos).1[index].3 == before[index].6,
    decreases before.len(),
{
    reveal_with_fuel(crate::specs::part2_mct_prepared_inputs, 1);
    if before.len() > 0 {
        production_mct_prepared_inputs_shape(before.drop_first(), count, infos);
        assert forall |index: int| 0 <= index < crate::specs::part2_mct_prepared_inputs(before, count, infos).1.len() implies
            crate::specs::part2_mct_prepared_inputs(before, count, infos).1[index].2 == before[index].5
                && crate::specs::part2_mct_prepared_inputs(before, count, infos).1[index].3 == before[index].6 by {
            if index > 0 {
                assert(before.drop_first()[index - 1] == before[index]);
            }
        }
    }
}

pub proof fn production_mct_stage_empty(
    before: Seq<crate::specs::Part2MctComponent>, collections: Seq<crate::specs::Part2MctCollection>, work: u64, max_work: u64, max_bytes: u64,
)
    ensures crate::specs::part2_mct_stage_prefix(before, collections, work, max_work, max_bytes, 0) == (Ok(()), before, work),
{
    reveal_with_fuel(crate::specs::part2_mct_stage_prefix, 1);
}

pub proof fn production_mct_stage_step(
    before: Seq<crate::specs::Part2MctComponent>, collections: Seq<crate::specs::Part2MctCollection>, work: u64, max_work: u64, max_bytes: u64, count: nat,
)
    requires count < collections.len(),
    ensures crate::specs::part2_mct_stage_prefix(before, collections, work, max_work, max_bytes, count + 1)
        == {
            let previous = crate::specs::part2_mct_stage_prefix(before, collections, work, max_work, max_bytes, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => crate::specs::part2_mct_collection(previous.1, collections[count as int], previous.2, max_work, max_bytes),
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_stage_prefix, 1);
}

pub proof fn production_mct_stage_error(
    before: Seq<crate::specs::Part2MctComponent>, collections: Seq<crate::specs::Part2MctCollection>, work: u64, max_work: u64, max_bytes: u64, count: nat, finish: nat,
)
    requires count <= finish <= collections.len(),
    ensures crate::specs::part2_mct_stage_prefix(before, collections, work, max_work, max_bytes, count).0.is_err()
        ==> crate::specs::part2_mct_stage_prefix(before, collections, work, max_work, max_bytes, finish)
            == crate::specs::part2_mct_stage_prefix(before, collections, work, max_work, max_bytes, count),
    decreases finish - count,
{
    if count < finish {
        production_mct_stage_error(before, collections, work, max_work, max_bytes, count, (finish - 1) as nat);
        production_mct_stage_step(before, collections, work, max_work, max_bytes, (finish - 1) as nat);
    }
}

pub proof fn production_mct_transform_empty(
    before: Seq<crate::specs::Part2MctComponent>, stages: Seq<crate::specs::Part2MctStage>, work: u64, max_work: u64, max_bytes: u64,
)
    ensures crate::specs::part2_mct_transform_prefix(before, stages, work, max_work, max_bytes, 0) == (Ok(()), before, work),
{
    reveal_with_fuel(crate::specs::part2_mct_transform_prefix, 1);
}

pub proof fn production_mct_transform_step(
    before: Seq<crate::specs::Part2MctComponent>, stages: Seq<crate::specs::Part2MctStage>, work: u64, max_work: u64, max_bytes: u64, count: nat,
)
    requires count < stages.len(),
    ensures crate::specs::part2_mct_transform_prefix(before, stages, work, max_work, max_bytes, count + 1)
        == {
            let previous = crate::specs::part2_mct_transform_prefix(before, stages, work, max_work, max_bytes, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => {
                    let stage = stages[stages.len() - count - 1];
                    crate::specs::part2_mct_stage_prefix(previous.1, stage.1, previous.2, max_work, max_bytes, stage.1.len())
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_transform_prefix, 1);
}

pub proof fn production_mct_transform_error(
    before: Seq<crate::specs::Part2MctComponent>, stages: Seq<crate::specs::Part2MctStage>, work: u64, max_work: u64, max_bytes: u64, count: nat, finish: nat,
)
    requires count <= finish <= stages.len(),
    ensures crate::specs::part2_mct_transform_prefix(before, stages, work, max_work, max_bytes, count).0.is_err()
        ==> crate::specs::part2_mct_transform_prefix(before, stages, work, max_work, max_bytes, finish)
            == crate::specs::part2_mct_transform_prefix(before, stages, work, max_work, max_bytes, count),
    decreases finish - count,
{
    if count < finish {
        production_mct_transform_error(before, stages, work, max_work, max_bytes, count, (finish - 1) as nat);
        production_mct_transform_step(before, stages, work, max_work, max_bytes, (finish - 1) as nat);
    }
}

pub proof fn production_mct_wavelet_intervals_empty(start: i64, end: i64)
    ensures crate::specs::part2_mct_wavelet_intervals(start, end, 0) == Ok((start, end, Seq::empty(), Seq::empty())),
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_intervals, 1);
}

pub proof fn production_mct_wavelet_intervals_step(start: i64, end: i64, count: nat)
    ensures crate::specs::part2_mct_wavelet_intervals(start, end, count + 1)
        == crate::specs::part2_mct_wavelet_interval_step(crate::specs::part2_mct_wavelet_intervals(start, end, count)),
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_intervals, 1);
}

pub proof fn production_mct_wavelet_intervals_error(start: i64, end: i64, count: nat, finish: nat)
    requires count <= finish,
    ensures crate::specs::part2_mct_wavelet_intervals(start, end, count).is_err()
        ==> crate::specs::part2_mct_wavelet_intervals(start, end, finish)
            == crate::specs::part2_mct_wavelet_intervals(start, end, count),
    decreases finish - count,
{
    if count < finish {
        production_mct_wavelet_intervals_error(start, end, count, (finish - 1) as nat);
        production_mct_wavelet_intervals_step(start, end, (finish - 1) as nat);
    }
}

pub proof fn production_mct_wavelet_snapshot_empty(
    before: Seq<crate::specs::Part2MctComponent>, indexes: Seq<usize>, fractions: Seq<u8>, sample: usize, reversible: bool,
)
    ensures crate::specs::part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, 0) == (Ok(()), Seq::empty()),
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_snapshot, 1);
}

pub proof fn production_mct_wavelet_snapshot_step(
    before: Seq<crate::specs::Part2MctComponent>, indexes: Seq<usize>, fractions: Seq<u8>, sample: usize, reversible: bool, count: nat,
)
    ensures crate::specs::part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, count + 1)
        == {
            let previous = crate::specs::part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => match crate::specs::part2_mct_wavelet_source_value(before, indexes, fractions, sample, count, reversible) {
                    Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_snapshot, 1);
}

pub proof fn production_mct_wavelet_snapshot_error(
    before: Seq<crate::specs::Part2MctComponent>, indexes: Seq<usize>, fractions: Seq<u8>, sample: usize, reversible: bool,
    count: nat, finish: nat,
)
    requires count <= finish,
    ensures crate::specs::part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, count).0.is_err()
        ==> crate::specs::part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, finish)
            == crate::specs::part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, count),
    decreases finish - count,
{
    if count < finish {
        production_mct_wavelet_snapshot_error(before, indexes, fractions, sample, reversible, count, (finish - 1) as nat);
        production_mct_wavelet_snapshot_step(before, indexes, fractions, sample, reversible, (finish - 1) as nat);
    }
}

pub proof fn production_mct_wavelet_reconstruction_empty(
    source: Seq<i64>, high: Seq<usize>, first: Seq<bool>, reversible: bool, low: usize,
)
    ensures crate::specs::part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, 0)
        == if low > source.len() { Err(crate::specs::part1_transform_error(false)) }
            else { Ok((low, source.take(low as int))) },
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_reconstruction_steps, 1);
}

pub proof fn production_mct_wavelet_reconstruction_step(
    source: Seq<i64>, high: Seq<usize>, first: Seq<bool>, reversible: bool, low: usize, count: nat,
)
    requires count < high.len(),
    ensures crate::specs::part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, count + 1)
        == crate::specs::part2_mct_wavelet_reconstruction_step(
            crate::specs::part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, count),
            source, high, first, reversible, (high.len() - count - 1) as nat),
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_reconstruction_steps, 1);
}

pub proof fn production_mct_wavelet_reconstruction_error(
    source: Seq<i64>, high: Seq<usize>, first: Seq<bool>, reversible: bool, low: usize, count: nat, finish: nat,
)
    requires count <= finish <= high.len(),
    ensures crate::specs::part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, count).is_err()
        ==> crate::specs::part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, finish)
            == crate::specs::part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, count),
    decreases finish - count,
{
    if count < finish {
        production_mct_wavelet_reconstruction_error(source, high, first, reversible, low, count, (finish - 1) as nat);
        production_mct_wavelet_reconstruction_step(source, high, first, reversible, low, (finish - 1) as nat);
    }
}

pub proof fn production_mct_wavelet_pixels_empty(
    before: Seq<crate::specs::Part2MctComponent>, prepared: crate::specs::Part2MctWaveletPreparation,
)
    ensures crate::specs::part2_mct_wavelet_pixels(before, prepared, 0) == (Ok(()), before),
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_pixels, 1);
}

pub proof fn production_mct_wavelet_pixels_step(
    before: Seq<crate::specs::Part2MctComponent>, prepared: crate::specs::Part2MctWaveletPreparation, count: nat,
)
    requires count <= usize::MAX,
    ensures crate::specs::part2_mct_wavelet_pixels(before, prepared, count + 1)
        == {
            let previous = crate::specs::part2_mct_wavelet_pixels(before, prepared, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => {
                    let pixel = crate::specs::part2_mct_wavelet_pixel(previous.1, prepared, count as usize);
                    (pixel.0, pixel.1)
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_wavelet_pixels, 1);
}

pub proof fn production_mct_wavelet_pixels_error(
    before: Seq<crate::specs::Part2MctComponent>, prepared: crate::specs::Part2MctWaveletPreparation, count: nat, finish: nat,
)
    requires count <= finish <= usize::MAX,
    ensures crate::specs::part2_mct_wavelet_pixels(before, prepared, count).0.is_err()
        ==> crate::specs::part2_mct_wavelet_pixels(before, prepared, finish)
            == crate::specs::part2_mct_wavelet_pixels(before, prepared, count),
    decreases finish - count,
{
    if count < finish {
        production_mct_wavelet_pixels_error(before, prepared, count, (finish - 1) as nat);
        production_mct_wavelet_pixels_step(before, prepared, (finish - 1) as nat);
    }
}

pub proof fn production_mct_dependency_layout_rejects(
    components: Seq<crate::specs::Part2MctComponent>, source: Seq<usize>, destination: Seq<usize>,
    reversible: bool, source_list: bool, position: nat,
)
    requires source.len() > 0, source[0] < components.len(),
        position < (if source_list { source.len() } else { destination.len() }),
        !crate::specs::part2_mct_dependency_layout_index_valid(
            components, source[0], if source_list { source[position as int] } else { destination[position as int] }, reversible),
    ensures crate::specs::part2_mct_validate_dependency_layout(components, source, destination, reversible)
        == Err(crate::specs::part1_transform_error(false)),
{
    if source_list {
        assert(!(forall |index: int| 0 <= index < source.len()
            ==> crate::specs::part2_mct_dependency_layout_index_valid(components, source[0], source[index], reversible)));
    } else {
        assert(!(forall |index: int| 0 <= index < destination.len()
            ==> crate::specs::part2_mct_dependency_layout_index_valid(components, source[0], destination[index], reversible)));
    }
}

pub proof fn production_mct_dependency_layout_bounds(
    components: Seq<crate::specs::Part2MctComponent>, source: Seq<usize>, destination: Seq<usize>,
    reversible: bool, samples: usize,
)
    requires crate::specs::part2_mct_validate_dependency_layout(components, source, destination, reversible) == Ok(samples),
    ensures forall |index: int| 0 <= index < source.len() ==> source[index] < components.len(),
        forall |index: int| 0 <= index < destination.len() ==> destination[index] < components.len(),
{
    assert forall |index: int| 0 <= index < source.len() implies source[index] < components.len() by {
        assert(crate::specs::part2_mct_dependency_layout_index_valid(components, source[0], source[index], reversible));
    }
    assert forall |index: int| 0 <= index < destination.len() implies destination[index] < components.len() by {
        assert(crate::specs::part2_mct_dependency_layout_index_valid(components, source[0], destination[index], reversible));
    }
}

pub proof fn production_mct_pairs_empty(
    components: Seq<crate::specs::Part2MctComponent>, source: Seq<u16>, destination: Seq<u16>,
)
    ensures crate::specs::part2_mct_component_pairs(components, source, destination, 0) == Ok((Seq::empty(), Seq::empty())),
{
    reveal_with_fuel(crate::specs::part2_mct_component_pairs, 1);
}

pub proof fn production_mct_pairs_step(
    components: Seq<crate::specs::Part2MctComponent>, source: Seq<u16>, destination: Seq<u16>, count: nat,
)
    ensures crate::specs::part2_mct_component_pairs(components, source, destination, count + 1)
        == crate::specs::part2_mct_component_pair_step(
            crate::specs::part2_mct_component_pairs(components, source, destination, count),
            components, source, destination, count),
{
    reveal_with_fuel(crate::specs::part2_mct_component_pairs, 1);
}

pub proof fn production_mct_pairs_error(
    components: Seq<crate::specs::Part2MctComponent>, source: Seq<u16>, destination: Seq<u16>, count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part2_mct_component_pairs(components, source, destination, count).is_err()
        ==> crate::specs::part2_mct_component_pairs(components, source, destination, end)
            == crate::specs::part2_mct_component_pairs(components, source, destination, count),
    decreases end - count,
{
    if count < end {
        production_mct_pairs_error(components, source, destination, count, (end - 1) as nat);
        production_mct_pairs_step(components, source, destination, (end - 1) as nat);
    }
}

pub proof fn production_mct_pairs_lengths(
    components: Seq<crate::specs::Part2MctComponent>, source: Seq<u16>, destination: Seq<u16>, count: nat,
    inputs: Seq<usize>, outputs: Seq<usize>,
)
    requires crate::specs::part2_mct_component_pairs(components, source, destination, count) == Ok((inputs, outputs)),
    ensures inputs.len() == count, outputs.len() == count,
    decreases count,
{
    reveal_with_fuel(crate::specs::part2_mct_component_pairs, 1);
    if count > 0 {
        match crate::specs::part2_mct_component_pairs(components, source, destination, (count - 1) as nat) {
            Ok((previous_inputs, previous_outputs)) => {
                production_mct_pairs_lengths(components, source, destination, (count - 1) as nat, previous_inputs, previous_outputs);
            },
            Err(_) => {},
        }
    }
}

pub proof fn production_mct_dependency_rows_empty(
    initial: Seq<i64>, collection: crate::specs::Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>,
)
    ensures crate::specs::part2_mct_dependency_rows(initial, collection, source, fractions, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part2_mct_dependency_rows, 1);
}

pub proof fn production_mct_dependency_rows_step(
    initial: Seq<i64>, collection: crate::specs::Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>, count: nat,
)
    requires count <= usize::MAX,
    ensures crate::specs::part2_mct_dependency_rows(initial, collection, source, fractions, count + 1)
        == {
            let previous = crate::specs::part2_mct_dependency_rows(initial, collection, source, fractions, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => match crate::specs::part2_mct_dependency_row(collection.4, collection.5, source,
                    if collection.0 { None } else { Some(fractions) }, previous.1, count as usize) {
                    Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_dependency_rows, 1);
}

pub proof fn production_mct_dependency_rows_error(
    initial: Seq<i64>, collection: crate::specs::Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>, count: nat, end: nat,
)
    requires count <= end <= usize::MAX,
    ensures crate::specs::part2_mct_dependency_rows(initial, collection, source, fractions, count).0.is_err()
        ==> crate::specs::part2_mct_dependency_rows(initial, collection, source, fractions, end)
            == crate::specs::part2_mct_dependency_rows(initial, collection, source, fractions, count),
    decreases end - count,
{
    if count < end {
        production_mct_dependency_rows_error(initial, collection, source, fractions, count, (end - 1) as nat);
        production_mct_dependency_rows_step(initial, collection, source, fractions, (end - 1) as nat);
    }
}

pub proof fn production_mct_dependency_pixels_empty(
    components: Seq<crate::specs::Part2MctComponent>, collection: crate::specs::Part2MctCollection,
    prepared: crate::specs::Part2MctDependencyPreparation, fractions: Seq<u8>,
)
    ensures crate::specs::part2_mct_dependency_pixels(components, collection, prepared, fractions, 0) == (Ok(()), components),
{
    reveal_with_fuel(crate::specs::part2_mct_dependency_pixels, 1);
}

pub proof fn production_mct_dependency_pixels_step(
    components: Seq<crate::specs::Part2MctComponent>, collection: crate::specs::Part2MctCollection,
    prepared: crate::specs::Part2MctDependencyPreparation, fractions: Seq<u8>, count: nat,
)
    requires count <= usize::MAX,
    ensures crate::specs::part2_mct_dependency_pixels(components, collection, prepared, fractions, count + 1)
        == {
            let previous = crate::specs::part2_mct_dependency_pixels(components, collection, prepared, fractions, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => {
                    let pixel = crate::specs::part2_mct_dependency_pixel(previous.1, collection, prepared, fractions, count as usize);
                    (pixel.0, pixel.1)
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_dependency_pixels, 1);
}

pub proof fn production_mct_dependency_pixels_error(
    components: Seq<crate::specs::Part2MctComponent>, collection: crate::specs::Part2MctCollection,
    prepared: crate::specs::Part2MctDependencyPreparation, fractions: Seq<u8>, count: nat, end: nat,
)
    requires count <= end <= usize::MAX,
    ensures crate::specs::part2_mct_dependency_pixels(components, collection, prepared, fractions, count).0.is_err()
        ==> crate::specs::part2_mct_dependency_pixels(components, collection, prepared, fractions, end)
            == crate::specs::part2_mct_dependency_pixels(components, collection, prepared, fractions, count),
    decreases end - count,
{
    if count < end {
        production_mct_dependency_pixels_error(components, collection, prepared, fractions, count, (end - 1) as nat);
        production_mct_dependency_pixels_step(components, collection, prepared, fractions, (end - 1) as nat);
    }
}

pub proof fn production_mct_pixels_empty(
    components: Seq<crate::specs::Part2MctComponent>, collection: crate::specs::Part2MctCollection,
    prepared: crate::specs::Part2MctDecorrelationPreparation,
)
    ensures crate::specs::part2_mct_decorrelation_pixels(components, collection, prepared, 0) == (Ok(()), components),
{
    reveal_with_fuel(crate::specs::part2_mct_decorrelation_pixels, 1);
}

pub proof fn production_mct_pixels_step(
    components: Seq<crate::specs::Part2MctComponent>, collection: crate::specs::Part2MctCollection,
    prepared: crate::specs::Part2MctDecorrelationPreparation, count: nat,
)
    requires count <= usize::MAX,
    ensures crate::specs::part2_mct_decorrelation_pixels(components, collection, prepared, count + 1)
        == {
            let previous = crate::specs::part2_mct_decorrelation_pixels(components, collection, prepared, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => {
                    let pixel = crate::specs::part2_mct_decorrelation_pixel(previous.1, collection, prepared, count as usize);
                    (pixel.0, pixel.1)
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_decorrelation_pixels, 1);
}

pub proof fn production_mct_pixels_error(
    components: Seq<crate::specs::Part2MctComponent>, collection: crate::specs::Part2MctCollection,
    prepared: crate::specs::Part2MctDecorrelationPreparation, count: nat, end: nat,
)
    requires count <= end <= usize::MAX,
    ensures crate::specs::part2_mct_decorrelation_pixels(components, collection, prepared, count).0.is_err()
        ==> crate::specs::part2_mct_decorrelation_pixels(components, collection, prepared, end)
            == crate::specs::part2_mct_decorrelation_pixels(components, collection, prepared, count),
    decreases end - count,
{
    if count < end {
        production_mct_pixels_error(components, collection, prepared, count, (end - 1) as nat);
        production_mct_pixels_step(components, collection, prepared, (end - 1) as nat);
    }
}

pub proof fn production_mct_precisions_empty(
    components: Seq<crate::specs::Part2MctComponent>, destinations: Seq<usize>, precision: u8,
)
    ensures crate::specs::part2_mct_destination_precisions(components, destinations, precision, 0) == (Ok(()), components),
{
    reveal_with_fuel(crate::specs::part2_mct_destination_precisions, 1);
}

pub proof fn production_mct_precisions_step(
    components: Seq<crate::specs::Part2MctComponent>, destinations: Seq<usize>, precision: u8, count: nat,
)
    requires count < destinations.len(),
    ensures crate::specs::part2_mct_destination_precisions(components, destinations, precision, count + 1)
        == {
            let previous = crate::specs::part2_mct_destination_precisions(components, destinations, precision, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => crate::specs::part2_mct_set_precision(previous.1, destinations[count as int], precision),
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_destination_precisions, 1);
}

pub proof fn production_mct_precisions_error(
    components: Seq<crate::specs::Part2MctComponent>, destinations: Seq<usize>, precision: u8, count: nat, end: nat,
)
    requires count <= end <= destinations.len(),
    ensures crate::specs::part2_mct_destination_precisions(components, destinations, precision, count).0.is_err()
        ==> crate::specs::part2_mct_destination_precisions(components, destinations, precision, end)
            == crate::specs::part2_mct_destination_precisions(components, destinations, precision, count),
    decreases end - count,
{
    if count < end {
        production_mct_precisions_error(components, destinations, precision, count, (end - 1) as nat);
        production_mct_precisions_step(components, destinations, precision, (end - 1) as nat);
    }
}

pub proof fn production_mct_snapshot_empty(
    components: Seq<crate::specs::Part2MctComponent>, indexes: Seq<usize>, sample: usize,
)
    ensures crate::specs::part2_mct_source_snapshot(components, indexes, sample, 0) == (Ok(()), Seq::empty()),
{
    reveal_with_fuel(crate::specs::part2_mct_source_snapshot, 1);
}

pub proof fn production_mct_snapshot_step(
    components: Seq<crate::specs::Part2MctComponent>, indexes: Seq<usize>, sample: usize, count: nat,
)
    ensures crate::specs::part2_mct_source_snapshot(components, indexes, sample, count + 1)
        == crate::specs::part2_mct_snapshot_step(
            crate::specs::part2_mct_source_snapshot(components, indexes, sample, count),
            components, indexes, sample, count),
{
    reveal_with_fuel(crate::specs::part2_mct_source_snapshot, 1);
}

pub proof fn production_mct_snapshot_error(
    components: Seq<crate::specs::Part2MctComponent>, indexes: Seq<usize>, sample: usize, count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part2_mct_source_snapshot(components, indexes, sample, count).0.is_err()
        ==> crate::specs::part2_mct_source_snapshot(components, indexes, sample, end)
            == crate::specs::part2_mct_source_snapshot(components, indexes, sample, count),
    decreases end - count,
{
    if count < end {
        production_mct_snapshot_error(components, indexes, sample, count, (end - 1) as nat);
        production_mct_snapshot_step(components, indexes, sample, (end - 1) as nat);
    }
}

pub proof fn production_mct_store_rows_empty(
    components: Seq<crate::specs::Part2MctComponent>, destinations: Seq<usize>, values: Seq<i64>, sample: usize,
)
    ensures crate::specs::part2_mct_store_output_rows(components, destinations, values, sample, 0) == (Ok(()), components),
{
    reveal_with_fuel(crate::specs::part2_mct_store_output_rows, 1);
}

pub proof fn production_mct_store_rows_step(
    components: Seq<crate::specs::Part2MctComponent>, destinations: Seq<usize>, values: Seq<i64>, sample: usize, count: nat,
)
    ensures crate::specs::part2_mct_store_output_rows(components, destinations, values, sample, count + 1)
        == crate::specs::part2_mct_store_output_row(
            crate::specs::part2_mct_store_output_rows(components, destinations, values, sample, count),
            destinations, values, sample, count),
{
    reveal_with_fuel(crate::specs::part2_mct_store_output_rows, 1);
}

pub proof fn production_mct_store_rows_error(
    components: Seq<crate::specs::Part2MctComponent>, destinations: Seq<usize>, values: Seq<i64>, sample: usize,
    count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part2_mct_store_output_rows(components, destinations, values, sample, count).0.is_err()
        ==> crate::specs::part2_mct_store_output_rows(components, destinations, values, sample, end)
            == crate::specs::part2_mct_store_output_rows(components, destinations, values, sample, count),
    decreases end - count,
{
    if count < end {
        production_mct_store_rows_error(components, destinations, values, sample, count, (end - 1) as nat);
        production_mct_store_rows_step(components, destinations, values, sample, (end - 1) as nat);
    }
}

pub proof fn production_mct_rows_empty(
    initial: Seq<i64>, collection: crate::specs::Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>,
)
    ensures crate::specs::part2_mct_decorrelation_rows(initial, collection, source, fractions, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part2_mct_decorrelation_rows, 1);
}

pub proof fn production_mct_rows_step(
    initial: Seq<i64>, collection: crate::specs::Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>, count: nat,
)
    requires count <= usize::MAX,
    ensures crate::specs::part2_mct_decorrelation_rows(initial, collection, source, fractions, count + 1)
        == {
            let previous = crate::specs::part2_mct_decorrelation_rows(initial, collection, source, fractions, count);
            match previous.0 {
                Err(_) => previous,
                Ok(()) => match crate::specs::part2_mct_decorrelation_row(collection, source, fractions, count as usize) {
                    Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
                },
            }
        },
{
    reveal_with_fuel(crate::specs::part2_mct_decorrelation_rows, 1);
}

pub proof fn production_mct_rows_error(
    initial: Seq<i64>, collection: crate::specs::Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>,
    count: nat, end: nat,
)
    requires count <= end <= usize::MAX,
    ensures crate::specs::part2_mct_decorrelation_rows(initial, collection, source, fractions, count).0.is_err()
        ==> crate::specs::part2_mct_decorrelation_rows(initial, collection, source, fractions, end)
            == crate::specs::part2_mct_decorrelation_rows(initial, collection, source, fractions, count),
    decreases end - count,
{
    if count < end {
        production_mct_rows_error(initial, collection, source, fractions, count, (end - 1) as nat);
        production_mct_rows_step(initial, collection, source, fractions, (end - 1) as nat);
    }
}

pub proof fn production_mct_indices_empty(components: Seq<crate::specs::Part2MctComponent>)
    ensures crate::specs::part2_mct_component_indices(components, Seq::empty()) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::part2_mct_component_indices, 1);
}

pub proof fn production_mct_indices_step(
    components: Seq<crate::specs::Part2MctComponent>, references: Seq<u16>, count: nat,
)
    requires count < references.len(),
    ensures crate::specs::part2_mct_component_indices(components, references.take(count as int + 1))
        == match crate::specs::part2_mct_component_indices(components, references.take(count as int)) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part2_mct_find_component(components, references[count as int]) {
                Err(error) => Err(error), Ok(index) => Ok(previous.push(index)),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_mct_component_indices, 1);
    assert(references.take(count as int + 1).drop_last() =~= references.take(count as int));
}

pub proof fn production_mct_indices_error(
    components: Seq<crate::specs::Part2MctComponent>, references: Seq<u16>, count: nat, end: nat,
)
    requires count <= end <= references.len(),
    ensures crate::specs::part2_mct_component_indices(components, references.take(count as int)).is_err()
        ==> crate::specs::part2_mct_component_indices(components, references.take(end as int))
            == crate::specs::part2_mct_component_indices(components, references.take(count as int)),
    decreases end - count,
{
    if count < end {
        production_mct_indices_error(components, references, count, (end - 1) as nat);
        production_mct_indices_step(components, references, (end - 1) as nat);
    }
}

pub proof fn production_mct_component_found(components: Seq<crate::specs::Part2MctComponent>, reference: u16, index: usize)
    requires index < components.len(), components[index as int].0 == reference,
        forall |earlier: int| 0 <= earlier < index ==> components[earlier].0 != reference,
    ensures crate::specs::part2_mct_find_component(components, reference) == Ok(index),
{
    let tags = crate::specs::part2_mct_component_tags(components);
    assert(tags[index as int] == reference);
    assert(tags.contains(reference));
    tags.index_of_first_ensures(reference);
    match tags.index_of_first(reference) {
        Some(first) => {
            if first < index { assert(components[first].0 != reference); }
            if index < first { assert(tags[index as int] != reference); }
        },
        None => {},
    }
}

pub proof fn production_mct_component_missing(components: Seq<crate::specs::Part2MctComponent>, reference: u16)
    requires forall |index: int| 0 <= index < components.len() ==> components[index].0 != reference,
    ensures crate::specs::part2_mct_find_component(components, reference) == Err(crate::specs::part1_transform_error(false)),
{
    let tags = crate::specs::part2_mct_component_tags(components);
    tags.index_of_first_ensures(reference);
    match tags.index_of_first(reference) {
        Some(index) => { assert(components[index].0 != reference); },
        None => {},
    }
}

pub proof fn production_mct_dot_empty(
    initial: i128, matrix: crate::specs::Part2MctArray, source: Seq<i64>, fractions: Option<Seq<u8>>, start: usize,
)
    ensures crate::specs::part2_mct_dot_prefix(initial, matrix, source, fractions, start, 0) == Ok(initial),
{
    reveal_with_fuel(crate::specs::part2_mct_dot_prefix, 1);
}

pub proof fn production_mct_dot_step(
    initial: i128, matrix: crate::specs::Part2MctArray, source: Seq<i64>, fractions: Option<Seq<u8>>, start: usize, count: nat,
)
    ensures crate::specs::part2_mct_dot_prefix(initial, matrix, source, fractions, start, count + 1)
        == match crate::specs::part2_mct_dot_prefix(initial, matrix, source, fractions, start, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part2_mct_dot_term(matrix, source, fractions, start, count as usize) {
                Err(error) => Err(error),
                Ok(product) => crate::specs::part2_atk_checked_i128(previous as int + product as int),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_mct_dot_prefix, 1);
}

pub proof fn production_mct_dot_error_guard(
    initial: i128, matrix: crate::specs::Part2MctArray, source: Seq<i64>, fractions: Option<Seq<u8>>,
    start: usize, count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part2_mct_dot_prefix(initial, matrix, source, fractions, start, count).is_err()
        ==> crate::specs::part2_mct_dot_prefix(initial, matrix, source, fractions, start, end)
            == crate::specs::part2_mct_dot_prefix(initial, matrix, source, fractions, start, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_mct_dot_prefix, 1);
    if count < end { production_mct_dot_error_guard(initial, matrix, source, fractions, start, count, (end - 1) as nat); }
}

pub proof fn production_prepare_kernel_fold_empty(
    initial: crate::specs::Part1PrepareFold, bands: Seq<crate::specs::Part1WorkingSubbandModel>,
    geometry: Seq<crate::decode::SubbandGeometry>, style: crate::specs::Part1PrepareStyle,
    reversible: bool, kernel: Option<crate::specs::Part2RawKernel>, maximum: u64,
)
    ensures crate::specs::part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, 0) == Ok(initial),
{
    reveal_with_fuel(crate::specs::part2_prepare_fold, 1);
}

pub proof fn production_prepare_kernel_fold_step(
    initial: crate::specs::Part1PrepareFold, bands: Seq<crate::specs::Part1WorkingSubbandModel>,
    geometry: Seq<crate::decode::SubbandGeometry>, style: crate::specs::Part1PrepareStyle,
    reversible: bool, kernel: Option<crate::specs::Part2RawKernel>, maximum: u64, count: nat,
)
    ensures crate::specs::part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, count + 1)
        == match crate::specs::part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part1_direction_for_resolution(style.1, style.2, (count + 1) as u8) {
                Err(error) => Err(error),
                Ok(direction) => {
                    let transformed = if matches!(direction, crate::codestream::DecompositionDirection::None) { Ok(previous) }
                        else { crate::specs::part2_prepare_resolution(previous, bands, geometry, direction, reversible, kernel, maximum) };
                    match transformed {
                        Err(error) => Err(error),
                        Ok(after) => if count + 1 >= 255 { Err(crate::specs::part1_block_placement_error(true)) } else { Ok(after) },
                    }
                },
            },
        },
{
    reveal_with_fuel(crate::specs::part2_prepare_fold, 1);
}

pub proof fn production_prepare_kernel_fold_error_guard(
    initial: crate::specs::Part1PrepareFold, bands: Seq<crate::specs::Part1WorkingSubbandModel>,
    geometry: Seq<crate::decode::SubbandGeometry>, style: crate::specs::Part1PrepareStyle,
    reversible: bool, kernel: Option<crate::specs::Part2RawKernel>, maximum: u64, count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, count).is_err()
        ==> crate::specs::part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, end)
            == crate::specs::part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_prepare_fold, 1);
    if count < end { production_prepare_kernel_fold_error_guard(initial, bands, geometry, style, reversible, kernel, maximum, count, (end - 1) as nat); }
}

pub proof fn production_atk_scale_empty(original: Seq<i64>, factor: i64, low_first: bool)
    ensures crate::specs::part2_atk_scale_prefix(original, factor, low_first, 0) == Ok(original),
{
    reveal_with_fuel(crate::specs::part2_atk_scale_prefix, 1);
}

pub proof fn production_atk_scale_step(original: Seq<i64>, factor: i64, low_first: bool, count: nat)
    ensures crate::specs::part2_atk_scale_prefix(original, factor, low_first, count + 1)
        == match crate::specs::part2_atk_scale_prefix(original, factor, low_first, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part2_atk_scale_sample(previous[count as int], factor, low_first, count as usize) {
                Err(error) => Err(error),
                Ok(value) => Ok(previous.update(count as int, value)),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_atk_scale_prefix, 1);
}

pub proof fn production_atk_scale_error_guard(original: Seq<i64>, factor: i64, low_first: bool, count: nat, end: nat)
    requires count <= end,
    ensures crate::specs::part2_atk_scale_prefix(original, factor, low_first, count).is_err()
        ==> crate::specs::part2_atk_scale_prefix(original, factor, low_first, end)
            == crate::specs::part2_atk_scale_prefix(original, factor, low_first, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_atk_scale_prefix, 1);
    if count < end { production_atk_scale_error_guard(original, factor, low_first, count, (end - 1) as nat); }
}

pub proof fn production_atk_irreversible_sum_empty(
    samples: Seq<i64>, target: usize, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool,
)
    ensures crate::specs::part2_atk_irreversible_sum(samples, target, step, kernel, low_first, 0) == Ok(0),
{
    reveal_with_fuel(crate::specs::part2_atk_irreversible_sum, 1);
}

pub proof fn production_atk_irreversible_sum_step(
    samples: Seq<i64>, target: usize, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, count: nat,
)
    ensures crate::specs::part2_atk_irreversible_sum(samples, target, step, kernel, low_first, count + 1)
        == match crate::specs::part2_atk_irreversible_sum(samples, target, step, kernel, low_first, count) {
            Err(error) => Err(error),
            Ok(previous) => if count >= step.3.len() { Err(crate::specs::part1_transform_error(false)) } else {
                match crate::specs::part2_atk_fixed_coefficient(step.3[count as int], kernel.1) {
                    Err(error) => Err(error),
                    Ok(alpha) => match crate::specs::part2_atk_source_sum(samples, target, count as usize, step.0, kernel.2, kernel.4, low_first) {
                        Err(error) => Err(error),
                        Ok(contribution) => match crate::specs::part2_atk_checked_i128(alpha as int * contribution as int) {
                            Err(error) => Err(error), Ok(product) => crate::specs::part2_atk_checked_i128(previous as int + product as int),
                        },
                    },
                }
            },
        },
{
    reveal_with_fuel(crate::specs::part2_atk_irreversible_sum, 1);
}

pub proof fn production_atk_irreversible_sum_error_guard(
    samples: Seq<i64>, target: usize, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part2_atk_irreversible_sum(samples, target, step, kernel, low_first, count).is_err()
        ==> crate::specs::part2_atk_irreversible_sum(samples, target, step, kernel, low_first, end)
            == crate::specs::part2_atk_irreversible_sum(samples, target, step, kernel, low_first, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_atk_irreversible_sum, 1);
    if count < end { production_atk_irreversible_sum_error_guard(samples, target, step, kernel, low_first, count, (end - 1) as nat); }
}

pub proof fn production_atk_horizontal_error_persists(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand, low_first: bool,
    kernel: crate::specs::Part2RawKernel, start: nat, end: nat, error: crate::DecodeError,
)
    requires start <= end,
        crate::specs::part2_atk_horizontal_prefix(low, high, low_first, kernel, start) == Err(error),
    ensures crate::specs::part2_atk_horizontal_prefix(low, high, low_first, kernel, end) == Err(error),
    decreases end - start,
{
    if end > start {
        production_atk_horizontal_error_persists(low, high, low_first, kernel, start, (end - 1) as nat, error);
    }
}

pub proof fn production_atk_vertical_error_persists(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand, height: u32, low_first: bool,
    kernel: crate::specs::Part2RawKernel, length: usize, start: nat, end: nat, error: crate::DecodeError,
)
    requires start <= end,
        crate::specs::part2_atk_vertical_prefix(low, high, height, low_first, kernel, length, start) == Err(error),
    ensures crate::specs::part2_atk_vertical_prefix(low, high, height, low_first, kernel, length, end) == Err(error),
    decreases end - start,
{
    if end > start {
        production_atk_vertical_error_persists(low, high, height, low_first, kernel, length, start, (end - 1) as nat, error);
    }
}

pub proof fn production_atk_sum_empty(samples: Seq<i64>, target: usize, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool)
    ensures crate::specs::part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, low_first, 0)
        == match step.2 { None => Err(crate::specs::part1_transform_error(false)), Some(value) => crate::specs::part2_atk_integer(value, kernel.1) },
{
    reveal_with_fuel(crate::specs::part2_atk_sum, 1);
}

pub proof fn production_atk_sum_step(samples: Seq<i64>, target: usize, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, count: nat)
    ensures crate::specs::part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, low_first, count + 1)
        == match crate::specs::part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, low_first, count) {
            Err(error) => Err(error),
            Ok(previous) => if count >= step.3.len() { Err(crate::specs::part1_transform_error(false)) } else {
                match crate::specs::part2_atk_integer(step.3[count as int], kernel.1) {
                    Err(error) => Err(error),
                    Ok(alpha) => match crate::specs::part2_atk_source_sum(samples, target, count as usize, step.0, kernel.2, kernel.4, low_first) {
                        Err(error) => Err(error),
                        Ok(contribution) => match crate::specs::part2_atk_checked_i128(alpha as int * contribution as int) {
                            Err(error) => Err(error), Ok(product) => crate::specs::part2_atk_checked_i128(previous as int + product as int),
                        },
                    },
                }
            },
        },
{
    reveal_with_fuel(crate::specs::part2_atk_sum, 1);
}

pub proof fn production_atk_sum_error_guard(samples: Seq<i64>, target: usize, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, count: nat, end: nat)
    requires count <= end,
    ensures crate::specs::part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, low_first, count).is_err()
        ==> crate::specs::part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, low_first, end)
            == crate::specs::part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, low_first, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_atk_sum, 1);
    if count < end { production_atk_sum_error_guard(samples, target, step, kernel, low_first, count, (end - 1) as nat); }
}

pub proof fn production_atk_targets_empty(original: Seq<i64>, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, start: usize)
    ensures crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, 0) == (Ok(()), original),
{
    reveal_with_fuel(crate::specs::part2_atk_target_prefix, 1);
}

pub proof fn production_atk_targets_step(original: Seq<i64>, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, start: usize, count: nat)
    ensures crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, count + 1)
        == match crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, count).0 {
            Err(_) => crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, count),
            Ok(()) => {
                let previous = crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, count).1;
                let target = (start as nat + 2 * count) as usize;
                match crate::specs::part2_atk_target(previous, target, step, kernel, low_first) {
                    Err(error) => (Err(error), previous),
                    Ok(value) => (if target as nat + 2 > usize::MAX { Err(crate::specs::part1_transform_error(true)) } else { Ok(()) }, previous.update(target as int, value)),
                }
            },
        },
{
    reveal_with_fuel(crate::specs::part2_atk_target_prefix, 1);
}

pub proof fn production_atk_targets_error_guard(original: Seq<i64>, step: crate::specs::Part2RawKernelStep, kernel: crate::specs::Part2RawKernel, low_first: bool, start: usize, count: nat, end: nat)
    requires count <= end,
    ensures crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, count).0.is_err()
        ==> crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, end)
            == crate::specs::part2_atk_target_prefix(original, step, kernel, low_first, start, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_atk_target_prefix, 1);
    if count < end { production_atk_targets_error_guard(original, step, kernel, low_first, start, count, (end - 1) as nat); }
}

pub proof fn production_atk_steps_empty(original: Seq<i64>, kernel: crate::specs::Part2RawKernel, low_first: bool)
    ensures crate::specs::part2_atk_steps(original, kernel, low_first, 0) == (Ok(()), original),
{
    reveal_with_fuel(crate::specs::part2_atk_steps, 1);
}

pub proof fn production_atk_steps_step(original: Seq<i64>, kernel: crate::specs::Part2RawKernel, low_first: bool, count: nat)
    ensures crate::specs::part2_atk_steps(original, kernel, low_first, count + 1)
        == match crate::specs::part2_atk_steps(original, kernel, low_first, count).0 {
            Err(_) => crate::specs::part2_atk_steps(original, kernel, low_first, count),
            Ok(()) => crate::specs::part2_atk_step(crate::specs::part2_atk_steps(original, kernel, low_first, count).1,
                kernel.6[kernel.6.len() - count - 1], kernel, low_first, if count % 2 == 0 { kernel.3 } else { !kernel.3 }),
        },
{
    reveal_with_fuel(crate::specs::part2_atk_steps, 1);
}

pub proof fn production_atk_steps_error_guard(original: Seq<i64>, kernel: crate::specs::Part2RawKernel, low_first: bool, count: nat, end: nat)
    requires count <= end,
    ensures crate::specs::part2_atk_steps(original, kernel, low_first, count).0.is_err()
        ==> crate::specs::part2_atk_steps(original, kernel, low_first, end) == crate::specs::part2_atk_steps(original, kernel, low_first, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_atk_steps, 1);
    if count < end { production_atk_steps_error_guard(original, kernel, low_first, count, (end - 1) as nat); }
}

pub proof fn production_selected_region_empty(size: crate::specs::Part2SelectionGeometry, tiles: Seq<u16>, x1: u32, y1: u32)
    ensures crate::specs::part2_selected_region_prefix(size, tiles, x1, y1, 0) == Ok((x1, y1, size.2, size.3)),
{
    reveal_with_fuel(crate::specs::part2_selected_region_prefix, 1);
}

pub proof fn production_selected_region_step(size: crate::specs::Part2SelectionGeometry, tiles: Seq<u16>, x1: u32, y1: u32, count: nat)
    ensures crate::specs::part2_selected_region_prefix(size, tiles, x1, y1, count + 1)
        == match crate::specs::part2_selected_region_prefix(size, tiles, x1, y1, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part2_selection_tile_bounds(size, tiles[count as int]) {
                Err(error) => Err(error),
                Ok(bounds) => Ok((if previous.0 < bounds.x0 { previous.0 } else { bounds.x0 },
                    if previous.1 < bounds.y0 { previous.1 } else { bounds.y0 },
                    if previous.2 > bounds.x1 { previous.2 } else { bounds.x1 },
                    if previous.3 > bounds.y1 { previous.3 } else { bounds.y1 })),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_selected_region_prefix, 1);
}

pub proof fn production_selected_region_error(size: crate::specs::Part2SelectionGeometry, tiles: Seq<u16>, x1: u32, y1: u32, start: nat, end: nat)
    requires start <= end,
    ensures crate::specs::part2_selected_region_prefix(size, tiles, x1, y1, start).is_err()
        ==> crate::specs::part2_selected_region_prefix(size, tiles, x1, y1, end)
            == crate::specs::part2_selected_region_prefix(size, tiles, x1, y1, start),
    decreases end - start,
{
    reveal_with_fuel(crate::specs::part2_selected_region_prefix, 1);
    if start < end { production_selected_region_error(size, tiles, x1, y1, start, (end - 1) as nat); }
}

pub proof fn production_selected_tiles_empty(size: crate::specs::Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>)
    ensures crate::specs::part2_selected_tiles_prefix(size, explicit, region, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::part2_selected_tiles_prefix, 1);
}

pub proof fn production_selected_tiles_step(size: crate::specs::Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: nat)
    ensures crate::specs::part2_selected_tiles_prefix(size, explicit, region, count + 1)
        == match crate::specs::part2_selected_tiles_prefix(size, explicit, region, count) {
            Err(error) => Err(error),
            Ok(previous) => if count > u16::MAX { Err(crate::specs::part1_block_placement_error(true)) } else {
                let index = count as u16;
                match crate::specs::part2_selection_tile_bounds(size, index) {
                    Err(error) => Err(error),
                    Ok(bounds) => if bounds.x0 < region[2] && bounds.x1 > region[0] && bounds.y0 < region[3] && bounds.y1 > region[1] {
                        if explicit.len() > 0 && !explicit.contains(index) {
                            Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::RegionOutsideSelectedTiles })
                        } else { Ok(previous.push(index)) }
                    } else { Ok(previous) },
                }
            },
        },
{
    reveal_with_fuel(crate::specs::part2_selected_tiles_prefix, 1);
}

pub proof fn production_selected_tiles_error(size: crate::specs::Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, start: nat, end: nat)
    requires start <= end,
    ensures crate::specs::part2_selected_tiles_prefix(size, explicit, region, start).is_err()
        ==> crate::specs::part2_selected_tiles_prefix(size, explicit, region, end)
            == crate::specs::part2_selected_tiles_prefix(size, explicit, region, start),
    decreases end - start,
{
    reveal_with_fuel(crate::specs::part2_selected_tiles_prefix, 1);
    if start < end { production_selected_tiles_error(size, explicit, region, start, (end - 1) as nat); }
}

pub proof fn production_unsigned_remainder_bound(value: u32, divisor: u32)
    requires divisor > 0,
    ensures ((value % divisor) as u32) <= value,
{
    if value < divisor {
        vstd::arithmetic::div_mod::lemma_small_mod(value as nat, divisor as nat);
    } else {
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(value as int, divisor as int);
    }
}

pub proof fn production_tile_box_first(tiles: Seq<u16>, across: u32)
    ensures crate::specs::part2_tile_rectangle_prefix(tiles, across, 1)
        == (((tiles[0] as u32) / across) as u32, ((tiles[0] as u32) % across) as u32,
            ((tiles[0] as u32) / across) as u32, ((tiles[0] as u32) % across) as u32),
{
    reveal_with_fuel(crate::specs::part2_tile_rectangle_prefix, 1);
}

pub proof fn production_tile_box_step(tiles: Seq<u16>, across: u32, count: nat)
    requires count >= 1,
    ensures crate::specs::part2_tile_rectangle_prefix(tiles, across, count + 1) == {
        let previous = crate::specs::part2_tile_rectangle_prefix(tiles, across, count);
        let row = ((tiles[count as int] as u32) / across) as u32;
        let column = ((tiles[count as int] as u32) % across) as u32;
        (if row < previous.0 { row } else { previous.0 }, if column < previous.1 { column } else { previous.1 },
            if row > previous.2 { row } else { previous.2 }, if column > previous.3 { column } else { previous.3 })
    },
{
    reveal_with_fuel(crate::specs::part2_tile_rectangle_prefix, 1);
}

pub proof fn production_rectangle_columns_empty(tiles: Seq<u16>, across: u32, bounds: crate::specs::Part2TileRectangle, row: u32)
    ensures crate::specs::part2_rectangle_columns(tiles, across, bounds, row, 0) == Ok(()),
{
    reveal_with_fuel(crate::specs::part2_rectangle_columns, 1);
}

pub proof fn production_rectangle_columns_step(tiles: Seq<u16>, across: u32, bounds: crate::specs::Part2TileRectangle, row: u32, count: nat)
    ensures crate::specs::part2_rectangle_columns(tiles, across, bounds, row, count + 1)
        == match crate::specs::part2_rectangle_columns(tiles, across, bounds, row, count) {
            Err(error) => Err(error),
            Ok(()) => crate::specs::part2_rectangle_cell(tiles, across, row, (bounds.1 as nat + count) as u32),
        },
{
    reveal_with_fuel(crate::specs::part2_rectangle_columns, 1);
}

pub proof fn production_rectangle_columns_error(tiles: Seq<u16>, across: u32, bounds: crate::specs::Part2TileRectangle, row: u32, start: nat, end: nat)
    requires start <= end,
    ensures crate::specs::part2_rectangle_columns(tiles, across, bounds, row, start).is_err()
        ==> crate::specs::part2_rectangle_columns(tiles, across, bounds, row, end)
            == crate::specs::part2_rectangle_columns(tiles, across, bounds, row, start),
    decreases end - start,
{
    reveal_with_fuel(crate::specs::part2_rectangle_columns, 1);
    if start < end { production_rectangle_columns_error(tiles, across, bounds, row, start, (end - 1) as nat); }
}

pub proof fn production_rectangle_rows_empty(tiles: Seq<u16>, across: u32, bounds: crate::specs::Part2TileRectangle)
    ensures crate::specs::part2_rectangle_rows(tiles, across, bounds, 0) == Ok(()),
{
    reveal_with_fuel(crate::specs::part2_rectangle_rows, 1);
}

pub proof fn production_rectangle_rows_step(tiles: Seq<u16>, across: u32, bounds: crate::specs::Part2TileRectangle, count: nat)
    ensures crate::specs::part2_rectangle_rows(tiles, across, bounds, count + 1)
        == match crate::specs::part2_rectangle_rows(tiles, across, bounds, count) {
            Err(error) => Err(error),
            Ok(()) => crate::specs::part2_rectangle_columns(tiles, across, bounds, (bounds.0 as nat + count) as u32,
                (bounds.3 as nat - bounds.1 as nat + 1) as nat),
        },
{
    reveal_with_fuel(crate::specs::part2_rectangle_rows, 1);
}

pub proof fn production_rectangle_rows_error(tiles: Seq<u16>, across: u32, bounds: crate::specs::Part2TileRectangle, start: nat, end: nat)
    requires start <= end,
    ensures crate::specs::part2_rectangle_rows(tiles, across, bounds, start).is_err()
        ==> crate::specs::part2_rectangle_rows(tiles, across, bounds, end)
            == crate::specs::part2_rectangle_rows(tiles, across, bounds, start),
    decreases end - start,
{
    reveal_with_fuel(crate::specs::part2_rectangle_rows, 1);
    if start < end { production_rectangle_rows_error(tiles, across, bounds, start, (end - 1) as nat); }
}

pub proof fn production_explicit_tiles_empty(tiles: Seq<u16>, count: u64)
    ensures crate::specs::part2_explicit_tile_prefix(tiles, count, 0) == Ok(()),
{
    reveal_with_fuel(crate::specs::part2_explicit_tile_prefix, 1);
}

pub proof fn production_explicit_tiles_step(tiles: Seq<u16>, count: u64, prefix: nat)
    ensures crate::specs::part2_explicit_tile_prefix(tiles, count, prefix + 1)
        == match crate::specs::part2_explicit_tile_prefix(tiles, count, prefix) {
            Err(error) => Err(error),
            Ok(()) => if tiles[prefix as int] as u64 >= count {
                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::TileOutOfRange })
            } else if tiles.take(prefix as int).contains(tiles[prefix as int]) {
                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::DuplicateTile })
            } else { Ok(()) },
        },
{
    reveal_with_fuel(crate::specs::part2_explicit_tile_prefix, 1);
}

pub proof fn production_explicit_tiles_error_guard(tiles: Seq<u16>, count: u64, start: nat, end: nat)
    requires start <= end,
    ensures crate::specs::part2_explicit_tile_prefix(tiles, count, start).is_err()
        ==> crate::specs::part2_explicit_tile_prefix(tiles, count, end)
            == crate::specs::part2_explicit_tile_prefix(tiles, count, start),
    decreases end - start,
{
    reveal_with_fuel(crate::specs::part2_explicit_tile_prefix, 1);
    if start < end { production_explicit_tiles_error_guard(tiles, count, start, (end - 1) as nat); }
}

pub proof fn production_color_sampling_empty(components: Seq<crate::codestream::ComponentInfo>, count: u16, target: Seq<u32>)
    ensures crate::specs::part2_color_sampling_prefix(components, count, target, 0) == Ok((0, 0)),
{
    reveal_with_fuel(crate::specs::part2_color_sampling_prefix, 1);
}

pub proof fn production_color_sampling_step(components: Seq<crate::codestream::ComponentInfo>, count: u16, target: Seq<u32>, prefix: nat)
    ensures crate::specs::part2_color_sampling_prefix(components, count, target, prefix + 1)
        == match crate::specs::part2_color_sampling_prefix(components, count, target, prefix) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part1_image_size_component(count, components, prefix as u16) {
                Err(error) => Err(error),
                Ok(info) => crate::specs::part2_color_sampling_step(previous, info, target),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_color_sampling_prefix, 1);
}

pub proof fn production_color_sampling_error_guard(
    components: Seq<crate::codestream::ComponentInfo>, count: u16, target: Seq<u32>, start: nat, end: nat,
)
    requires start <= end,
    ensures crate::specs::part2_color_sampling_prefix(components, count, target, start).is_err()
        ==> crate::specs::part2_color_sampling_prefix(components, count, target, end)
            == crate::specs::part2_color_sampling_prefix(components, count, target, start),
    decreases end - start,
{
    reveal_with_fuel(crate::specs::part2_color_sampling_prefix, 1);
    if start < end { production_color_sampling_error_guard(components, count, target, start, (end - 1) as nat); }
}

pub proof fn production_typed_components_output_push(
    components: Seq<crate::TypedComponent>, component: crate::TypedComponent,
)
    ensures crate::image::typed_components_output_view(components.push(component))
        == crate::image::typed_components_output_view(components).push(crate::image::typed_component_value_view(component)),
{
    assert(crate::image::typed_components_output_view(components.push(component))
        =~= crate::image::typed_components_output_view(components).push(crate::image::typed_component_value_view(component)));
}

pub proof fn production_output_mapping_empty(
    components: Seq<crate::specs::Part2TypedComponentOutput>, header: crate::specs::Part2OutputHeader,
)
    ensures crate::specs::part2_output_mapping_prefix(components, header, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::part2_output_mapping_prefix, 1);
}

pub proof fn production_output_mapping_step(
    components: Seq<crate::specs::Part2TypedComponentOutput>, header: crate::specs::Part2OutputHeader, count: nat,
)
    ensures crate::specs::part2_output_mapping_prefix(components, header, count + 1)
        == match crate::specs::part2_output_mapping_prefix(components, header, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part2_output_mapped_component(components, header.0, header.1[count as int]) {
                Err(error) => Err(error), Ok(component) => Ok(previous.push(component)),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_output_mapping_prefix, 1);
}

pub proof fn production_output_mapping_error(
    components: Seq<crate::specs::Part2TypedComponentOutput>, header: crate::specs::Part2OutputHeader, start: nat, end: nat,
)
    requires start <= end,
    ensures crate::specs::part2_output_mapping_prefix(components, header, start).is_err()
        ==> crate::specs::part2_output_mapping_prefix(components, header, end)
            == crate::specs::part2_output_mapping_prefix(components, header, start),
    decreases end - start,
{
    if end > start {
        production_output_mapping_error(components, header, start, (end - 1) as nat);
        production_output_mapping_step(components, header, (end - 1) as nat);
    }
}

pub proof fn production_output_definition_empty(
    components: Seq<crate::specs::Part2TypedComponentOutput>, definitions: Seq<(u16, crate::specs::ColorDefinition)>,
)
    ensures crate::specs::part2_output_definition_prefix(components, definitions, 0) == Ok(components),
{
    reveal_with_fuel(crate::specs::part2_output_definition_prefix, 1);
}

pub proof fn production_output_definition_step(
    components: Seq<crate::specs::Part2TypedComponentOutput>, definitions: Seq<(u16, crate::specs::ColorDefinition)>, count: nat,
)
    ensures crate::specs::part2_output_definition_prefix(components, definitions, count + 1)
        == match crate::specs::part2_output_definition_prefix(components, definitions, count) {
            Err(error) => Err(error),
            Ok(previous) => crate::specs::part2_output_apply_definition(previous, definitions[count as int]),
        },
{
    reveal_with_fuel(crate::specs::part2_output_definition_prefix, 1);
}

pub proof fn production_output_definition_error(
    components: Seq<crate::specs::Part2TypedComponentOutput>, definitions: Seq<(u16, crate::specs::ColorDefinition)>, start: nat, end: nat,
)
    requires start <= end,
    ensures crate::specs::part2_output_definition_prefix(components, definitions, start).is_err()
        ==> crate::specs::part2_output_definition_prefix(components, definitions, end)
            == crate::specs::part2_output_definition_prefix(components, definitions, start),
    decreases end - start,
{
    if end > start {
        production_output_definition_error(components, definitions, start, (end - 1) as nat);
        production_output_definition_step(components, definitions, (end - 1) as nat);
    }
}

pub proof fn production_typed_image_admission_empty(
    components: Seq<crate::specs::Part2TypedComponentOutput>, maximum: u64,
)
    ensures crate::specs::part2_typed_image_admission_prefix(components, maximum, 0) == Ok(0),
{
    reveal_with_fuel(crate::specs::part2_typed_image_admission_prefix, 1);
}

pub proof fn production_typed_image_admission_step(
    components: Seq<crate::specs::Part2TypedComponentOutput>, maximum: u64, count: nat,
)
    ensures crate::specs::part2_typed_image_admission_prefix(components, maximum, count + 1)
        == match crate::specs::part2_typed_image_admission_prefix(components, maximum, count) {
            Err(error) => Err(error),
            Ok(previous) => crate::specs::part2_typed_image_admit_component(components[count as int], previous, maximum),
        },
{
    reveal_with_fuel(crate::specs::part2_typed_image_admission_prefix, 1);
}

pub proof fn production_typed_image_admission_error(
    components: Seq<crate::specs::Part2TypedComponentOutput>, maximum: u64, start: nat, end: nat,
)
    requires start <= end,
    ensures crate::specs::part2_typed_image_admission_prefix(components, maximum, start).is_err()
        ==> crate::specs::part2_typed_image_admission_prefix(components, maximum, end)
            == crate::specs::part2_typed_image_admission_prefix(components, maximum, start),
    decreases end - start,
{
    if end > start {
        production_typed_image_admission_error(components, maximum, start, (end - 1) as nat);
        production_typed_image_admission_step(components, maximum, (end - 1) as nat);
    }
}

pub proof fn production_legacy_magnitude_u64(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures match crate::specs::part1_magnitude_u64(limbs) {
        Some(value) => crate::specs::part1_magnitude_value(limbs) == value as nat,
        None => true,
    },
{
    if crate::specs::part1_magnitude_u64(limbs).is_some() {
        production_magnitude_value_expansion(limbs);
        assert(limbs[1] == 0 && limbs[2] == 0 && limbs[3] == 0 && limbs[4] == 0 && limbs[5] == 0);
    }
}

pub proof fn production_prepare_fold_empty(
    initial: crate::specs::Part1PrepareFold, bands: Seq<crate::specs::Part1WorkingSubbandModel>,
    geometry: Seq<crate::decode::SubbandGeometry>, style: crate::specs::Part1PrepareStyle, reversible: bool, maximum: u64,
)
    ensures crate::specs::part1_prepare_fold(initial, bands, geometry, style, reversible, maximum, 0) == Ok(initial),
{
    reveal_with_fuel(crate::specs::part1_prepare_fold, 1);
    reveal_with_fuel(crate::specs::part2_prepare_fold, 1);
}

pub proof fn production_prepare_fold_step(
    initial: crate::specs::Part1PrepareFold, bands: Seq<crate::specs::Part1WorkingSubbandModel>,
    geometry: Seq<crate::decode::SubbandGeometry>, style: crate::specs::Part1PrepareStyle, reversible: bool, maximum: u64, count: nat,
)
    ensures crate::specs::part1_prepare_fold(initial, bands, geometry, style, reversible, maximum, count + 1)
        == match crate::specs::part1_prepare_fold(initial, bands, geometry, style, reversible, maximum, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part1_direction_for_resolution(style.1, style.2, (count + 1) as u8) {
                Err(error) => Err(error),
                Ok(direction) => {
                    let transformed = if matches!(direction, crate::codestream::DecompositionDirection::None) { Ok(previous) }
                        else { crate::specs::part1_prepare_resolution(previous, bands, geometry, direction, reversible, maximum) };
                    match transformed {
                        Err(error) => Err(error),
                        Ok(after) => if count + 1 >= 255 { Err(crate::specs::part1_block_placement_error(true)) } else { Ok(after) },
                    }
                },
            },
        },
{
    reveal_with_fuel(crate::specs::part1_prepare_fold, 1);
    reveal_with_fuel(crate::specs::part2_prepare_fold, 1);
}

pub proof fn production_prepare_fold_error_guard(
    initial: crate::specs::Part1PrepareFold, bands: Seq<crate::specs::Part1WorkingSubbandModel>,
    geometry: Seq<crate::decode::SubbandGeometry>, style: crate::specs::Part1PrepareStyle, reversible: bool, maximum: u64, count: nat, end: nat,
)
    requires count <= end,
    ensures crate::specs::part1_prepare_fold(initial, bands, geometry, style, reversible, maximum, count).is_err()
        ==> crate::specs::part1_prepare_fold(initial, bands, geometry, style, reversible, maximum, end)
            == crate::specs::part1_prepare_fold(initial, bands, geometry, style, reversible, maximum, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_prepare_fold, 1);
    reveal_with_fuel(crate::specs::part2_prepare_fold, 1);
    if count < end { production_prepare_fold_error_guard(initial, bands, geometry, style, reversible, maximum, count, (end - 1) as nat); }
}

pub proof fn production_prepare_init_empty(bands: Seq<crate::decode::SubbandGeometry>, fraction: u8, maximum: u64)
    ensures crate::specs::part1_prepare_init_prefix(bands, fraction, maximum, 0) == Ok((Seq::empty(), 0)),
{
    reveal_with_fuel(crate::specs::part1_prepare_init_prefix, 1);
}

pub proof fn production_prepare_init_step(bands: Seq<crate::decode::SubbandGeometry>, fraction: u8, maximum: u64, count: nat)
    requires count < usize::MAX,
    ensures crate::specs::part1_prepare_init_prefix(bands, fraction, maximum, count + 1)
        == match crate::specs::part1_prepare_init_prefix(bands, fraction, maximum, count) {
            Err(error) => Err(error),
            Ok(previous) => {
                let appended = crate::specs::part1_prepare_append_band(previous, bands, count as usize, fraction, maximum);
                match appended.0 { Err(error) => Err(error), Ok(()) => Ok(appended.1) }
            },
        },
{
    reveal_with_fuel(crate::specs::part1_prepare_init_prefix, 1);
}

pub proof fn production_prepare_init_error(bands: Seq<crate::decode::SubbandGeometry>, fraction: u8, maximum: u64, count: nat, end: nat, error: crate::DecodeError)
    requires count <= end, crate::specs::part1_prepare_init_prefix(bands, fraction, maximum, count) == Err(error),
    ensures crate::specs::part1_prepare_init_prefix(bands, fraction, maximum, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_prepare_init_prefix, 1);
    if count < end { production_prepare_init_error(bands, fraction, maximum, count, (end - 1) as nat, error); }
}

pub proof fn production_prepare_row_empty(plane: crate::specs::Tier1RawPlane, y: u16, initial: Seq<crate::specs::Part1QuantizedCoefficient>)
    ensures crate::specs::part1_prepare_coefficient_row(plane, y, initial, 0) == Ok(initial),
{
    reveal_with_fuel(crate::specs::part1_prepare_coefficient_row, 1);
}

pub proof fn production_prepare_row_step(plane: crate::specs::Tier1RawPlane, y: u16, initial: Seq<crate::specs::Part1QuantizedCoefficient>, count: nat)
    ensures crate::specs::part1_prepare_coefficient_row(plane, y, initial, count + 1)
        == match crate::specs::part1_prepare_coefficient_row(plane, y, initial, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part1_prepare_signed_cell(plane, count as u16, y) {
                Err(error) => Err(error), Ok(value) => Ok(previous.push(value)),
            },
        },
{
    reveal_with_fuel(crate::specs::part1_prepare_coefficient_row, 1);
}

pub proof fn production_prepare_row_error(plane: crate::specs::Tier1RawPlane, y: u16, initial: Seq<crate::specs::Part1QuantizedCoefficient>, count: nat, end: nat, error: crate::DecodeError)
    requires count <= end, crate::specs::part1_prepare_coefficient_row(plane, y, initial, count) == Err(error),
    ensures crate::specs::part1_prepare_coefficient_row(plane, y, initial, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_prepare_coefficient_row, 1);
    if count < end { production_prepare_row_error(plane, y, initial, count, (end - 1) as nat, error); }
}

pub proof fn production_prepare_rows_empty(plane: crate::specs::Tier1RawPlane)
    ensures crate::specs::part1_prepare_coefficient_rows(plane, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::part1_prepare_coefficient_rows, 1);
}

pub proof fn production_prepare_rows_step(plane: crate::specs::Tier1RawPlane, count: nat)
    ensures crate::specs::part1_prepare_coefficient_rows(plane, count + 1)
        == match crate::specs::part1_prepare_coefficient_rows(plane, count) {
            Err(error) => Err(error),
            Ok(previous) => crate::specs::part1_prepare_coefficient_row(plane, count as u16, previous, plane.width as nat),
        },
{
    reveal_with_fuel(crate::specs::part1_prepare_coefficient_rows, 1);
}

pub proof fn production_prepare_rows_error(plane: crate::specs::Tier1RawPlane, count: nat, end: nat, error: crate::DecodeError)
    requires count <= end, crate::specs::part1_prepare_coefficient_rows(plane, count) == Err(error),
    ensures crate::specs::part1_prepare_coefficient_rows(plane, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_prepare_coefficient_rows, 1);
    if count < end { production_prepare_rows_error(plane, count, (end - 1) as nat, error); }
}

pub proof fn production_prepare_placements_empty(
    initial: crate::specs::Part1PrepareWorking, plan: crate::specs::Part1PreparePlan,
    precincts: Seq<Seq<crate::specs::Tier1RawPlane>>, reversible: bool, maximum: u64,
)
    ensures crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, 0) == (Ok(()), initial),
{
    reveal_with_fuel(crate::specs::part1_prepare_placements, 1);
}

pub proof fn production_prepare_placements_step(
    initial: crate::specs::Part1PrepareWorking, plan: crate::specs::Part1PreparePlan,
    precincts: Seq<Seq<crate::specs::Tier1RawPlane>>, reversible: bool, maximum: u64, count: nat,
)
    ensures crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, count + 1)
        == match crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, count).0 {
            Err(_) => crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, count),
            Ok(()) => crate::specs::part1_prepare_placement(
                crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, count).1,
                plan.subbands, precincts, plan.placements[count as int], reversible, maximum),
        },
{
    reveal_with_fuel(crate::specs::part1_prepare_placements, 1);
}

pub proof fn production_prepare_placements_error(
    initial: crate::specs::Part1PrepareWorking, plan: crate::specs::Part1PreparePlan,
    precincts: Seq<Seq<crate::specs::Tier1RawPlane>>, reversible: bool, maximum: u64, count: nat, end: nat,
)
    requires count <= end, crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, count).0.is_err(),
    ensures crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, end)
        == crate::specs::part1_prepare_placements(initial, plan, precincts, reversible, maximum, count),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_prepare_placements, 1);
    if count < end { production_prepare_placements_error(initial, plan, precincts, reversible, maximum, count, (end - 1) as nat); }
}

pub proof fn production_palette_samples_empty(
    samples: crate::specs::Part1TypedSampleSequence, palette: crate::specs::Part2PaletteModel, column: u8,
)
    requires column < palette.1.len(), 0 < palette.1[column as int].precision <= 38,
    ensures crate::specs::part2_palette_samples(samples, palette, column, 0)
        == Ok(if palette.1[column as int].signed {
            crate::specs::Part1TypedSampleSequence::Signed(Seq::empty())
        } else { crate::specs::Part1TypedSampleSequence::Unsigned(Seq::empty()) }),
{
    reveal_with_fuel(crate::specs::part2_palette_samples, 1);
}

pub proof fn production_palette_samples_step(
    samples: crate::specs::Part1TypedSampleSequence, palette: crate::specs::Part2PaletteModel,
    column: u8, count: nat,
)
    requires column < palette.1.len(), 0 < palette.1[column as int].precision <= 38,
    ensures crate::specs::part2_palette_samples(samples, palette, column, count + 1)
        == match crate::specs::part2_palette_samples(samples, palette, column, count) {
            Err(error) => Err(error),
            Ok(previous) => match crate::specs::part2_palette_sample(samples, palette, column, count as usize) {
                Err(error) => Err(error),
                Ok(value) => Ok(match previous {
                    crate::specs::Part1TypedSampleSequence::Signed(values) =>
                        crate::specs::Part1TypedSampleSequence::Signed(values.push(value)),
                    crate::specs::Part1TypedSampleSequence::Unsigned(values) =>
                        crate::specs::Part1TypedSampleSequence::Unsigned(values.push(value as u64)),
                }),
            },
        },
{
    reveal_with_fuel(crate::specs::part2_palette_samples, 1);
}

pub proof fn production_palette_samples_error(
    samples: crate::specs::Part1TypedSampleSequence, palette: crate::specs::Part2PaletteModel,
    column: u8, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end, crate::specs::part2_palette_samples(samples, palette, column, count) == Err(error),
    ensures crate::specs::part2_palette_samples(samples, palette, column, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part2_palette_samples, 1);
    if count < end {
        production_palette_samples_error(samples, palette, column, count, (end - 1) as nat, error);
    }
}

pub proof fn production_palette_component_error(
    source: crate::specs::Part1TypedComponentModel, palette: crate::specs::Part2PaletteModel,
    column: u8, count: nat, error: crate::DecodeError,
)
    requires count <= crate::specs::part2_typed_sample_count(source.samples),
        crate::specs::part2_palette_samples(source.samples, palette, column, count) == Err(error),
    ensures crate::specs::part2_palette_component(source, palette, column) == Err(error),
{
    production_palette_samples_error(source.samples, palette, column, count,
        crate::specs::part2_typed_sample_count(source.samples), error);
    reveal_with_fuel(crate::specs::part2_palette_samples, 1);
}

pub proof fn production_palette_sample_error(
    source: crate::specs::Part1TypedComponentModel, palette: crate::specs::Part2PaletteModel,
    column: u8, index: usize, error: crate::DecodeError,
)
    requires column < palette.1.len(), 0 < palette.1[column as int].precision <= 38,
        index < crate::specs::part2_typed_sample_count(source.samples),
        crate::specs::part2_palette_samples(source.samples, palette, column, index as nat).is_ok(),
        crate::specs::part2_palette_sample(source.samples, palette, column, index) == Err(error),
    ensures crate::specs::part2_palette_component(source, palette, column) == Err(error),
{
    production_palette_samples_step(source.samples, palette, column, index as nat);
    production_palette_component_error(source, palette, column, index as nat + 1, error);
}

pub proof fn production_decoded_signed_empty(samples: Seq<i64>, fraction: u8, precision: u8)
    ensures crate::specs::part1_decoded_signed_prefix(samples, fraction, precision, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::part1_decoded_signed_prefix, 1);
}

pub proof fn production_decoded_signed_step(samples: Seq<i64>, fraction: u8, precision: u8, count: nat)
    ensures crate::specs::part1_decoded_signed_prefix(samples, fraction, precision, count + 1)
        == match crate::specs::part1_decoded_signed_prefix(samples, fraction, precision, count) {
            Err(error) => Err(error),
            Ok(output) => match crate::specs::part1_decoded_signed_sample(samples[count as int], fraction, precision) {
                Err(error) => Err(error), Ok(value) => Ok(output.push(value)),
            },
        },
{
    reveal_with_fuel(crate::specs::part1_decoded_signed_prefix, 1);
}

pub proof fn production_decoded_signed_error(samples: Seq<i64>, fraction: u8, precision: u8, count: nat, end: nat, error: crate::DecodeError)
    requires count <= end, crate::specs::part1_decoded_signed_prefix(samples, fraction, precision, count) == Err(error),
    ensures crate::specs::part1_decoded_signed_prefix(samples, fraction, precision, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_decoded_signed_prefix, 1);
    if count < end { production_decoded_signed_error(samples, fraction, precision, count, (end - 1) as nat, error); }
}

pub proof fn production_decoded_unsigned_empty(samples: Seq<i64>, fraction: u8, precision: u8)
    ensures crate::specs::part1_decoded_unsigned_prefix(samples, fraction, precision, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::part1_decoded_unsigned_prefix, 1);
}

pub proof fn production_decoded_unsigned_step(samples: Seq<i64>, fraction: u8, precision: u8, count: nat)
    ensures crate::specs::part1_decoded_unsigned_prefix(samples, fraction, precision, count + 1)
        == match crate::specs::part1_decoded_unsigned_prefix(samples, fraction, precision, count) {
            Err(error) => Err(error),
            Ok(output) => match crate::specs::part1_decoded_unsigned_sample(samples[count as int], fraction, precision) {
                Err(error) => Err(error), Ok(value) => Ok(output.push(value)),
            },
        },
{
    reveal_with_fuel(crate::specs::part1_decoded_unsigned_prefix, 1);
}

pub proof fn production_decoded_unsigned_error(samples: Seq<i64>, fraction: u8, precision: u8, count: nat, end: nat, error: crate::DecodeError)
    requires count <= end, crate::specs::part1_decoded_unsigned_prefix(samples, fraction, precision, count) == Err(error),
    ensures crate::specs::part1_decoded_unsigned_prefix(samples, fraction, precision, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_decoded_unsigned_prefix, 1);
    if count < end { production_decoded_unsigned_error(samples, fraction, precision, count, (end - 1) as nat, error); }
}

pub proof fn production_decoded_typed_components_empty(components: Seq<crate::specs::Part1DecodedComponentModel>, maximum: u64)
    ensures crate::specs::part1_decoded_typed_components(components, maximum, 0) == Ok((Seq::empty(), 0)),
{
    reveal_with_fuel(crate::specs::part1_decoded_typed_components, 1);
}

pub proof fn production_decoded_typed_components_step(components: Seq<crate::specs::Part1DecodedComponentModel>, maximum: u64, count: nat)
    ensures crate::specs::part1_decoded_typed_components(components, maximum, count + 1)
        == match crate::specs::part1_decoded_typed_components(components, maximum, count) {
            Err(error) => Err(error),
            Ok(previous) => {
                let component = components[count as int];
                let charged = crate::specs::part1_accumulate_decoded_bytes(component.4.len(), previous.1, maximum);
                match charged.0 {
                    Err(error) => Err(error),
                    Ok(()) => match crate::specs::part1_decoded_component_typed_samples(component, maximum) {
                        Err(error) => Err(error),
                        Ok(samples) => Ok((previous.0.push(crate::specs::Part1TypedComponentModel {
                            width: component.0, height: component.1, info: component.2, samples,
                        }), charged.1)),
                    },
                }
            },
        },
{
    reveal_with_fuel(crate::specs::part1_decoded_typed_components, 1);
}

pub proof fn production_decoded_typed_components_error(
    components: Seq<crate::specs::Part1DecodedComponentModel>, maximum: u64, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end, crate::specs::part1_decoded_typed_components(components, maximum, count) == Err(error),
    ensures crate::specs::part1_decoded_typed_components(components, maximum, end) == Err(error),
    decreases end - count,
{
    reveal_with_fuel(crate::specs::part1_decoded_typed_components, 1);
    if count < end { production_decoded_typed_components_error(components, maximum, count, (end - 1) as nat, error); }
}

pub proof fn production_tier1_value_limbs(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures limbs == crate::specs::tier1_value_limbs(crate::specs::part1_magnitude_value(limbs)),
{
    vstd::arithmetic::power2::lemma2_to64();
    assert forall |i: int| 0 <= i < 6 implies limbs[i]
        == crate::specs::tier1_value_limbs(crate::specs::part1_magnitude_value(limbs))[i] by {
        let shift = (64 * i) as u16;
        assert(shift / 64 == i && shift % 64 == 0);
        let shifted = crate::specs::part1_magnitude_shift(limbs, shift);
        production_magnitude_right_shift_value(limbs, shift);
        production_magnitude_low_word(shifted);
        assert(shifted[0] == limbs[i]) by {
            let word = limbs[i];
            assert(word >> 0u32 == word) by(bit_vector);
        }
    }
    assert(limbs =~= crate::specs::tier1_value_limbs(crate::specs::part1_magnitude_value(limbs)));
}

pub proof fn production_assembly_row_error_persists(
    plane: crate::specs::Part1AssemblyPlane, tile: crate::specs::Part1AssemblyTile,
    x: u32, y: u32, crop: Option<(u32, u32)>, completed: nat, total: nat,
)
    requires completed <= total,
        crate::specs::part1_assembly_row_prefix(plane, tile, x, y, crop, completed).0.is_err(),
    ensures crate::specs::part1_assembly_row_prefix(plane, tile, x, y, crop, total)
        == crate::specs::part1_assembly_row_prefix(plane, tile, x, y, crop, completed),
    decreases total - completed,
{
    if completed < total {
        production_assembly_row_error_persists(plane, tile, x, y, crop, completed, (total - 1) as nat);
    }
}

pub proof fn production_assembly_rectangle_error_persists(
    plane: crate::specs::Part1AssemblyPlane, tile: crate::specs::Part1AssemblyTile,
    rectangle: (u32, u32, u32, u32), crop: Option<(u32, u32)>, completed: nat, total: nat,
)
    requires completed <= total,
        crate::specs::part1_assembly_rectangle_prefix(plane, tile, rectangle, crop, completed).0.is_err(),
    ensures crate::specs::part1_assembly_rectangle_prefix(plane, tile, rectangle, crop, total)
        == crate::specs::part1_assembly_rectangle_prefix(plane, tile, rectangle, crop, completed),
    decreases total - completed,
{
    if completed < total {
        production_assembly_rectangle_error_persists(plane, tile, rectangle, crop, completed, (total - 1) as nat);
    }
}

pub proof fn production_assembly_tiles_error_persists(
    plane: crate::specs::Part1AssemblyPlane, tiles: Seq<crate::specs::Part1AssemblyTile>,
    component: u16, crop: Option<(u32, u32, u32, u32)>, completed: nat, total: nat,
)
    requires completed <= total,
        crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, completed).0.is_err(),
    ensures crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, total)
        == crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, completed),
    decreases total - completed,
{
    reveal_with_fuel(crate::specs::part1_assembly_tiles_prefix, 1);
    if completed < total {
        production_assembly_tiles_error_persists(plane, tiles, component, crop, completed, (total - 1) as nat);
    }
}

pub proof fn production_assembly_components_error_persists(
    image: crate::specs::Part1DecodedImageModel, bytes: u64,
    size: crate::specs::Part1AssemblySize, tiles: Seq<crate::specs::Part1AssemblyTile>,
    extent: (u32, u32), selection: crate::specs::Part1AssemblySelection, maximum: u64,
    completed: nat, total: nat,
)
    requires completed <= total,
        crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, completed).0.is_err(),
    ensures crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, total)
        == crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, completed),
    decreases total - completed,
{
    reveal_with_fuel(crate::specs::part1_assembly_components_prefix, 1);
    if completed < total {
        production_assembly_components_error_persists(image, bytes, size, tiles, extent, selection, maximum, completed, (total - 1) as nat);
    }
}

pub proof fn production_assembly_tiles_empty(
    plane: crate::specs::Part1AssemblyPlane, tiles: Seq<crate::specs::Part1AssemblyTile>,
    component: u16, crop: Option<(u32, u32, u32, u32)>,
)
    ensures crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, 0) == (Ok(()), plane),
{
    reveal_with_fuel(crate::specs::part1_assembly_tiles_prefix, 1);
}

pub proof fn production_assembly_tiles_step(
    plane: crate::specs::Part1AssemblyPlane, tiles: Seq<crate::specs::Part1AssemblyTile>,
    component: u16, crop: Option<(u32, u32, u32, u32)>, count: nat,
)
    ensures crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, count + 1)
        == match crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, count).0 {
            Err(_) => crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, count),
            Ok(()) => crate::specs::part1_assembly_tile_step(
                crate::specs::part1_assembly_tiles_prefix(plane, tiles, component, crop, count).1,
                tiles[count as int], component, crop,
            ),
        },
{
    reveal_with_fuel(crate::specs::part1_assembly_tiles_prefix, 1);
}

pub proof fn production_assembly_components_empty(
    image: crate::specs::Part1DecodedImageModel, bytes: u64,
    size: crate::specs::Part1AssemblySize, tiles: Seq<crate::specs::Part1AssemblyTile>,
    extent: (u32, u32), selection: crate::specs::Part1AssemblySelection, maximum: u64,
)
    ensures crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, 0)
        == (Ok(()), image, bytes),
{
    reveal_with_fuel(crate::specs::part1_assembly_components_prefix, 1);
}

pub proof fn production_assembly_components_step(
    image: crate::specs::Part1DecodedImageModel, bytes: u64,
    size: crate::specs::Part1AssemblySize, tiles: Seq<crate::specs::Part1AssemblyTile>,
    extent: (u32, u32), selection: crate::specs::Part1AssemblySelection, maximum: u64, count: nat,
)
    ensures crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, count + 1)
        == match crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, count).0 {
            Err(_) => crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, count),
            Ok(()) => crate::specs::part1_assembly_append_plane(
                crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, count).1,
                crate::specs::part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, count).2,
                size, tiles, count as u16, extent, selection, maximum,
            ),
        },
{
    reveal_with_fuel(crate::specs::part1_assembly_components_prefix, 1);
}

pub proof fn production_subband_count_error_persists(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>,
    completed: nat, total: nat, error: crate::DecodeError,
)
    requires completed <= total,
        crate::specs::part1_subband_count_prefix(levels, directions, completed) == Err(error),
    ensures crate::specs::part1_subband_count_prefix(levels, directions, total) == Err(error),
    decreases total - completed,
{
    if completed < total {
        production_subband_count_error_persists(levels, directions, completed, (total - 1) as nat, error);
    }
}

pub proof fn production_ht_low_word_parity(value: nat)
    ensures (value % 18446744073709551616) % 2 == value % 2,
{
    vstd::arithmetic::div_mod::lemma_mod_mod(value as int, 2, 9223372036854775808);
}

pub proof fn production_ht_numeric_payload_unfold(
    reader: crate::specs::HtMagSgnState, remaining: nat, index: nat, value: nat, negative: bool, exponent: u8,
)
    requires index + remaining <= 75, value < crate::specs::part1_magnitude_capacity(),
    ensures crate::specs::ht_numeric_payload(reader, remaining, index, value, negative, exponent)
        == if remaining == 0 { (Ok((value, negative, exponent)), reader) } else {
            let read = crate::specs::ht_magsgn_read(reader);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(bit) => if bit {
                    let changed = value + vstd::arithmetic::power2::pow2(index);
                    if changed >= crate::specs::part1_magnitude_capacity() {
                        (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), read.1)
                    } else {
                        crate::specs::ht_numeric_payload(read.1, (remaining - 1) as nat, index + 1, changed,
                            negative || index == 0, (index + 1) as u8)
                    }
                } else {
                    crate::specs::ht_numeric_payload(read.1, (remaining - 1) as nat, index + 1, value, negative, exponent)
                },
            }
        },
{
    reveal_with_fuel(crate::specs::ht_numeric_payload, 1);
}

pub proof fn production_crop_columns_empty(samples: Seq<u16>, source_width: u32, row: u32, x: u32, initial: Seq<u16>)
    ensures crate::specs::color_crop_columns(samples, source_width, row, x, initial, 0) == Ok(initial),
{
    reveal_with_fuel(crate::specs::color_crop_columns, 1);
}

pub proof fn production_crop_columns_step(samples: Seq<u16>, source_width: u32, row: u32, x: u32, initial: Seq<u16>, count: nat)
    ensures crate::specs::color_crop_columns(samples, source_width, row, x, initial, count + 1)
        == match crate::specs::color_crop_columns(samples, source_width, row, x, initial, count) {
            Err(error) => Err(error),
            Ok(output) => if (x as nat) + count > u32::MAX as nat { Err(crate::specs::part2_composition_error(true)) }
                else {
                    match crate::specs::color_crop_sample(samples, source_width, row, ((x as nat) + count) as u32) {
                        Err(error) => Err(error),
                        Ok(value) => Ok(output.push(value)),
                    }
                },
        },
{
    reveal_with_fuel(crate::specs::color_crop_columns, 1);
}

pub proof fn production_crop_columns_error(
    samples: Seq<u16>, source_width: u32, row: u32, x: u32, initial: Seq<u16>,
    count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end,
        crate::specs::color_crop_columns(samples, source_width, row, x, initial, count) == Err(error),
    ensures crate::specs::color_crop_columns(samples, source_width, row, x, initial, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_crop_columns_step(samples, source_width, row, x, initial, count);
        production_crop_columns_error(samples, source_width, row, x, initial, count + 1, end, error);
    }
}

pub proof fn production_crop_rows_empty(samples: Seq<u16>, source_width: u32, x: u32, y: u32, width: u32)
    ensures crate::specs::color_crop_rows(samples, source_width, x, y, width, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::color_crop_rows, 1);
}

pub proof fn production_crop_rows_step(samples: Seq<u16>, source_width: u32, x: u32, y: u32, width: u32, count: nat)
    ensures crate::specs::color_crop_rows(samples, source_width, x, y, width, count + 1)
        == match crate::specs::color_crop_rows(samples, source_width, x, y, width, count) {
            Err(error) => Err(error),
            Ok(output) => if (y as nat) + count > u32::MAX as nat { Err(crate::specs::part2_composition_error(true)) }
                else {
                    crate::specs::color_crop_columns(samples, source_width, ((y as nat) + count) as u32, x, output, width as nat)
                },
        },
{
    reveal_with_fuel(crate::specs::color_crop_rows, 1);
}

pub proof fn production_crop_rows_error(
    samples: Seq<u16>, source_width: u32, x: u32, y: u32, width: u32,
    count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end,
        crate::specs::color_crop_rows(samples, source_width, x, y, width, count) == Err(error),
    ensures crate::specs::color_crop_rows(samples, source_width, x, y, width, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_crop_rows_step(samples, source_width, x, y, width, count);
        production_crop_rows_error(samples, source_width, x, y, width, count + 1, end, error);
    }
}

pub proof fn production_crop_channels_empty(
    channels: Seq<crate::specs::ColorChannelModel>, source_width: u32, x: u32, y: u32, x1: u32, y1: u32,
)
    ensures crate::specs::color_crop_channels(channels, source_width, x, y, x1, y1, 0) == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::color_crop_channels, 1);
}

pub proof fn production_crop_channels_step(
    channels: Seq<crate::specs::ColorChannelModel>, source_width: u32, x: u32, y: u32, x1: u32, y1: u32, count: nat,
)
    requires count < channels.len(),
    ensures crate::specs::color_crop_channels(channels, source_width, x, y, x1, y1, count + 1)
        == match crate::specs::color_crop_channels(channels, source_width, x, y, x1, y1, count) {
            Err(error) => Err(error),
            Ok(output) => match crate::specs::color_crop_plane(channels[count as int].1, source_width, x, y, x1, y1) {
                Err(error) => Err(error),
                Ok(samples) => Ok(output.push((channels[count as int].0, samples))),
            },
        },
{
    reveal_with_fuel(crate::specs::color_crop_channels, 1);
}

pub proof fn production_crop_channels_error(
    channels: Seq<crate::specs::ColorChannelModel>, source_width: u32, x: u32, y: u32, x1: u32, y1: u32,
    count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end <= channels.len(),
        crate::specs::color_crop_channels(channels, source_width, x, y, x1, y1, count) == Err(error),
    ensures crate::specs::color_crop_channels(channels, source_width, x, y, x1, y1, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_crop_channels_step(channels, source_width, x, y, x1, y1, count);
        production_crop_channels_error(channels, source_width, x, y, x1, y1, count + 1, end, error);
    }
}

pub proof fn production_color_channels_empty(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    colors: Seq<usize>, color_count: usize,
)
    ensures crate::specs::color_convert_channels_prefix(components, geometry, colors, color_count, 0)
        == Ok(Seq::empty()),
{
    reveal_with_fuel(crate::specs::color_convert_channels_prefix, 1);
}

pub proof fn production_color_channels_step(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    colors: Seq<usize>, color_count: usize, count: nat,
)
    ensures crate::specs::color_convert_channels_prefix(components, geometry, colors, color_count, count + 1)
        == match crate::specs::color_convert_channels_prefix(components, geometry, colors, color_count, count) {
            Err(error) => Err(error),
            Ok(channels) => if count > usize::MAX { Err(crate::specs::part2_composition_error(true)) }
                else {
                    match crate::specs::color_convert_channel(components, geometry, colors, color_count, count as usize) {
                        Err(error) => Err(error),
                        Ok(channel) => Ok(channels.push(channel)),
                    }
                },
        },
{
    reveal_with_fuel(crate::specs::color_convert_channels_prefix, 1);
}

pub proof fn production_color_channels_error(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    colors: Seq<usize>, color_count: usize, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end,
        crate::specs::color_convert_channels_prefix(components, geometry, colors, color_count, count) == Err(error),
    ensures crate::specs::color_convert_channels_prefix(components, geometry, colors, color_count, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_color_channels_step(components, geometry, colors, color_count, count);
        production_color_channels_error(components, geometry, colors, color_count, count + 1, end, error);
    }
}

pub proof fn production_color_alphas_empty(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    alphas: Seq<(usize, bool, crate::image::ChannelAssociation)>, initial: Seq<crate::specs::ColorChannelModel>,
)
    ensures crate::specs::color_append_alphas_prefix(components, geometry, alphas, initial, 0) == Ok(initial),
{
    reveal_with_fuel(crate::specs::color_append_alphas_prefix, 1);
}

pub proof fn production_color_alphas_step(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    alphas: Seq<(usize, bool, crate::image::ChannelAssociation)>,
    initial: Seq<crate::specs::ColorChannelModel>, count: nat,
)
    requires count < alphas.len(),
    ensures crate::specs::color_append_alphas_prefix(components, geometry, alphas, initial, count + 1)
        == match crate::specs::color_append_alphas_prefix(components, geometry, alphas, initial, count) {
            Err(error) => Err(error),
            Ok(channels) => match crate::specs::color_convert_alpha(components, geometry, alphas[count as int]) {
                Err(error) => Err(error),
                Ok(channel) => Ok(channels.push(channel)),
            },
        },
{
    reveal_with_fuel(crate::specs::color_append_alphas_prefix, 1);
}

pub proof fn production_color_alphas_error(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    alphas: Seq<(usize, bool, crate::image::ChannelAssociation)>,
    initial: Seq<crate::specs::ColorChannelModel>, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end <= alphas.len(),
        crate::specs::color_append_alphas_prefix(components, geometry, alphas, initial, count) == Err(error),
    ensures crate::specs::color_append_alphas_prefix(components, geometry, alphas, initial, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_color_alphas_step(components, geometry, alphas, initial, count);
        production_color_alphas_error(components, geometry, alphas, initial, count + 1, end, error);
    }
}

pub proof fn production_color_sycc_empty(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    colors: Seq<usize>, width: usize,
)
    ensures crate::specs::color_sycc_planes_prefix(components, geometry, colors, width, 0)
        == Ok((Seq::empty(), Seq::empty(), Seq::empty())),
{
    reveal_with_fuel(crate::specs::color_sycc_planes_prefix, 1);
}

pub proof fn production_color_sycc_step(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    colors: Seq<usize>, width: usize, count: nat,
)
    ensures crate::specs::color_sycc_planes_prefix(components, geometry, colors, width, count + 1)
        == match crate::specs::color_sycc_planes_prefix(components, geometry, colors, width, count) {
            Err(error) => Err(error),
            Ok(planes) => if count > usize::MAX { Err(crate::specs::part2_composition_error(true)) }
                else {
                    match crate::specs::color_sycc_pixel(components, geometry.2, geometry.3, colors, count as usize, width) {
                        Err(error) => Err(error),
                        Ok((r, g, b)) => Ok((planes.0.push(r), planes.1.push(g), planes.2.push(b))),
                    }
                },
        },
{
    reveal_with_fuel(crate::specs::color_sycc_planes_prefix, 1);
}

pub proof fn production_color_sycc_error(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    colors: Seq<usize>, width: usize, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end,
        crate::specs::color_sycc_planes_prefix(components, geometry, colors, width, count) == Err(error),
    ensures crate::specs::color_sycc_planes_prefix(components, geometry, colors, width, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_color_sycc_step(components, geometry, colors, width, count);
        production_color_sycc_error(components, geometry, colors, width, count + 1, end, error);
    }
}

pub proof fn production_color_validation_empty(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    indices: Seq<usize>,
)
    ensures crate::specs::color_validate_indices_prefix(components, geometry, indices, 0) == Ok(()),
{
    reveal_with_fuel(crate::specs::color_validate_indices_prefix, 1);
}

pub proof fn production_color_validation_step(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    indices: Seq<usize>, count: nat,
)
    requires count < indices.len(),
    ensures crate::specs::color_validate_indices_prefix(components, geometry, indices, count + 1)
        == match crate::specs::color_validate_indices_prefix(components, geometry, indices, count) {
            Err(error) => Err(error),
            Ok(()) => crate::specs::color_validate_component_index(components, geometry, indices[count as int]),
        },
{
    reveal_with_fuel(crate::specs::color_validate_indices_prefix, 1);
}

pub proof fn production_color_validation_error(
    components: Seq<crate::specs::Part1TypedComponentModel>, geometry: crate::specs::ColorGeometry,
    indices: Seq<usize>, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end <= indices.len(),
        crate::specs::color_validate_indices_prefix(components, geometry, indices, count) == Err(error),
    ensures crate::specs::color_validate_indices_prefix(components, geometry, indices, end) == Err(error),
    decreases end - count,
{
    if count < end {
        production_color_validation_step(components, geometry, indices, count);
        production_color_validation_error(components, geometry, indices, count + 1, end, error);
    }
}

pub proof fn production_ht_metadata_pairs_step(
    state: crate::specs::HtMetadataPairState, previous: Seq<u8>, row: nat,
    width: u16, height: u16, maximum_u: u8, count: nat,
)
    requires 0 < previous.len() <= 32768, state.current.len() == previous.len(), row < 32768,
        count < (previous.len() + 1) / 2,
    ensures crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, count + 1)
        == match crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, count).0 {
            Err(error) => (Err(error), crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, count).1),
            Ok(()) => crate::specs::ht_metadata_pair(
                crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, count).1,
                previous, count * 2, row, width, height, maximum_u, row == 0),
        },
{
    reveal_with_fuel(crate::specs::ht_metadata_pairs, 1);
}

pub proof fn production_ht_metadata_pairs_error(
    state: crate::specs::HtMetadataPairState, previous: Seq<u8>, row: nat,
    width: u16, height: u16, maximum_u: u8, count: nat, end: nat,
)
    requires 0 < previous.len() <= 32768, state.current.len() == previous.len(), row < 32768,
        count <= end <= (previous.len() + 1) / 2,
        crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, count).0.is_err(),
    ensures crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, end)
        == crate::specs::ht_metadata_pairs(state, previous, row, width, height, maximum_u, count),
    decreases end - count,
{
    if end > count {
        production_ht_metadata_pairs_error(state, previous, row, width, height, maximum_u, count, (end - 1) as nat);
        production_ht_metadata_pairs_step(state, previous, row, width, height, maximum_u, (end - 1) as nat);
    }
}

pub proof fn production_ht_metadata_rows_step(
    state: crate::specs::HtMetadataRowState, width: u16, height: u16, maximum_u: u8, count: nat,
)
    requires 0 < state.previous.len() <= 32768, count < 32768,
    ensures crate::specs::ht_metadata_rows(state, width, height, maximum_u, count + 1)
        == match crate::specs::ht_metadata_rows(state, width, height, maximum_u, count).0 {
            Err(error) => (Err(error), crate::specs::ht_metadata_rows(state, width, height, maximum_u, count).1),
            Ok(()) => crate::specs::ht_metadata_row(
                crate::specs::ht_metadata_rows(state, width, height, maximum_u, count).1,
                count, width, height, maximum_u),
        },
{
    reveal_with_fuel(crate::specs::ht_metadata_rows, 1);
}

pub proof fn production_ht_metadata_rows_error(
    state: crate::specs::HtMetadataRowState, width: u16, height: u16, maximum_u: u8, count: nat, end: nat,
)
    requires 0 < state.previous.len() <= 32768, count <= end <= 32768,
        crate::specs::ht_metadata_rows(state, width, height, maximum_u, count).0.is_err(),
    ensures crate::specs::ht_metadata_rows(state, width, height, maximum_u, end)
        == crate::specs::ht_metadata_rows(state, width, height, maximum_u, count),
    decreases end - count,
{
    if end > count {
        production_ht_metadata_rows_error(state, width, height, maximum_u, count, (end - 1) as nat);
        production_ht_metadata_rows_step(state, width, height, maximum_u, (end - 1) as nat);
    }
}

pub proof fn production_ht_metadata_emits_unfold(
    state: crate::specs::HtMetadataPairState, words: Seq<u16>, contexts: Seq<u8>, values: [u8; 2],
    pair: nat, row: nat, width: u16, height: u16, maximum_u: u8, initial: bool, member: nat,
)
    requires member <= 2, words.len() == 2, contexts.len() == 2, pair < 32768, row < 32768,
        state.current.len() <= 32768,
    ensures crate::specs::ht_metadata_emits_run(state, words, contexts, values, pair, row, width, height, maximum_u, initial, member)
        == if member >= 2 || pair + member >= state.current.len() { (Ok(()), state) } else {
            let index = pair + member;
            let emit = crate::specs::ht_metadata_emit(state.readers, state.quads, state.significant, crate::specs::HtMetadataQuadInput {
                index: index as usize, row: row as usize, width, height, maximum_u,
                word: words[member as int], context: contexts[member as int],
                significance: state.current[index as int], u_value: values[member as int], initial,
            });
            let changed = crate::specs::HtMetadataPairState {
                readers: emit.1, quads: emit.2, significant: emit.3, ..state
            };
            match emit.0 {
                Err(error) => (Err(error), changed),
                Ok(()) => crate::specs::ht_metadata_emits_run(changed, words, contexts, values, pair, row, width, height, maximum_u, initial, member + 1),
            }
        },
{
    reveal_with_fuel(crate::specs::ht_metadata_emits_run, 1);
}

pub proof fn production_ht_metadata_words_unfold(
    state: crate::specs::HtMetadataWordsState, previous: Seq<u8>, pair: nat, initial: bool, member: nat,
)
    requires member <= 2, state.words.len() == 2, state.contexts.len() == 2, state.current.len() == previous.len(),
    ensures crate::specs::ht_metadata_words_run(state, previous, pair, initial, member)
        == if member >= 2 || pair + member >= previous.len() { (Ok(()), state) } else {
            let index = pair + member;
            let context = crate::specs::ht_metadata_context(previous, state.left, index, initial);
            let read = crate::specs::ht_cleanup_quad_word(state.readers, crate::tier1::ht_vlc_table_view(initial), context);
            let consumed = crate::specs::HtMetadataWordsState { readers: read.1, ..state };
            match read.0 {
                Err(error) => (Err(error), consumed),
                Ok(word) => {
                    let significance = ((word >> 4u16) & 0x0fu16) as u8;
                    crate::specs::ht_metadata_words_run(crate::specs::HtMetadataWordsState {
                        current: state.current.update(index as int, significance),
                        left: crate::specs::ht_metadata_left(significance, initial),
                        words: state.words.update(member as int, word),
                        contexts: state.contexts.update(member as int, context), ..consumed
                    }, previous, pair, initial, member + 1)
                },
            }
        },
{
    reveal_with_fuel(crate::specs::ht_metadata_words_run, 1);
}

pub proof fn production_ht_metadata_samples_unfold(
    significant: u16, significance: u8, x: u16, y: u16, width: u16, height: u16, sample: u8,
)
    requires sample <= 4, x <= 65534, y <= 65534,
    ensures crate::specs::ht_metadata_samples(significant, significance, x, y, width, height, sample)
        == if sample >= 4 { (Ok(()), significant) }
        else if significance & (1u8 << sample) == 0 {
            crate::specs::ht_metadata_samples(significant, significance, x, y, width, height, (sample + 1) as u8)
        } else if x as nat + (sample >> 1u8) as nat >= width || y as nat + (sample & 1u8) as nat >= height {
            (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), significant)
        } else if significant == u16::MAX {
            (Err(crate::specs::ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), significant)
        } else {
            crate::specs::ht_metadata_samples((significant + 1) as u16, significance, x, y, width, height, (sample + 1) as u8)
        },
{
    reveal_with_fuel(crate::specs::ht_metadata_samples, 1);
}

pub proof fn production_color_definition_presence_step(
    definitions: Seq<Seq<crate::specs::ColorDefinition>>, count: nat,
)
    requires count < definitions.len(),
    ensures
        (exists|i: int| #![trigger definitions[i]] 0 <= i < count + 1 && definitions[i].len() > 0)
        == ((exists|i: int| #![trigger definitions[i]] 0 <= i < count && definitions[i].len() > 0)
            || definitions[count as int].len() > 0),
{
    if exists|i: int| #![trigger definitions[i]] 0 <= i < count + 1 && definitions[i].len() > 0 {
        let witness = choose|i: int| 0 <= i < count + 1 && definitions[i].len() > 0;
        if witness < count {
            assert(exists|i: int| #![trigger definitions[i]] 0 <= i < count && definitions[i].len() > 0);
        } else {
            assert(witness == count);
        }
    }
    if exists|i: int| #![trigger definitions[i]] 0 <= i < count && definitions[i].len() > 0 {
        let witness = choose|i: int| 0 <= i < count && definitions[i].len() > 0;
        assert(exists|i: int| #![trigger definitions[i]] 0 <= i < count + 1 && definitions[i].len() > 0);
    } else if definitions[count as int].len() > 0 {
        assert(exists|i: int| #![trigger definitions[i]] 0 <= i < count + 1 && definitions[i].len() > 0);
    }
}

pub proof fn production_color_definitions_empty(
    initial: crate::specs::ColorLayoutState, definitions: Seq<crate::specs::ColorDefinition>,
    component: usize, color_count: usize,
)
    ensures crate::specs::color_layout_definitions_prefix(initial, definitions, component, color_count, 0) == Ok(initial),
{
    reveal(crate::specs::color_layout_definitions_prefix);
}

pub proof fn production_color_definitions_step(
    initial: crate::specs::ColorLayoutState, definitions: Seq<crate::specs::ColorDefinition>,
    component: usize, color_count: usize, count: nat,
)
    requires count < definitions.len(),
    ensures crate::specs::color_layout_definitions_prefix(initial, definitions, component, color_count, count + 1)
        == match crate::specs::color_layout_definitions_prefix(initial, definitions, component, color_count, count) {
            Err(error) => Err(error),
            Ok(state) => crate::specs::color_layout_definition_step(state, definitions[count as int], component, color_count),
        },
{
    reveal_with_fuel(crate::specs::color_layout_definitions_prefix, 1);
}

pub proof fn production_color_definitions_error(
    initial: crate::specs::ColorLayoutState, definitions: Seq<crate::specs::ColorDefinition>,
    component: usize, color_count: usize, count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end <= definitions.len(),
        crate::specs::color_layout_definitions_prefix(initial, definitions, component, color_count, count) == Err(error),
    ensures crate::specs::color_layout_definitions_prefix(initial, definitions, component, color_count, end) == Err(error),
    decreases end - count,
{
    if end > count {
        production_color_definitions_error(initial, definitions, component, color_count, count, (end - 1) as nat, error);
        production_color_definitions_step(initial, definitions, component, color_count, (end - 1) as nat);
    }
}

pub proof fn production_color_layout_empty(definitions: Seq<Seq<crate::specs::ColorDefinition>>, color_count: usize)
    ensures crate::specs::color_layout_components_prefix(definitions, color_count, 0)
        == Ok((Seq::new(color_count as nat, |i: int| usize::MAX), Seq::empty())),
{
    reveal(crate::specs::color_layout_components_prefix);
}

pub proof fn production_color_layout_step(
    definitions: Seq<Seq<crate::specs::ColorDefinition>>, color_count: usize, count: nat,
)
    requires count < definitions.len(),
    ensures crate::specs::color_layout_components_prefix(definitions, color_count, count + 1)
        == match crate::specs::color_layout_components_prefix(definitions, color_count, count) {
            Err(error) => Err(error),
            Ok(state) => crate::specs::color_layout_definitions_prefix(state, definitions[count as int],
                count as usize, color_count, definitions[count as int].len()),
        },
{
    reveal_with_fuel(crate::specs::color_layout_components_prefix, 1);
}

pub proof fn production_color_layout_error(
    definitions: Seq<Seq<crate::specs::ColorDefinition>>, color_count: usize,
    count: nat, end: nat, error: crate::DecodeError,
)
    requires count <= end <= definitions.len(),
        crate::specs::color_layout_components_prefix(definitions, color_count, count) == Err(error),
    ensures crate::specs::color_layout_components_prefix(definitions, color_count, end) == Err(error),
    decreases end - count,
{
    if end > count {
        production_color_layout_error(definitions, color_count, count, (end - 1) as nat, error);
        production_color_layout_step(definitions, color_count, (end - 1) as nat);
    }
}

pub proof fn production_color_plane_empty(
    component: crate::specs::Part1TypedComponentModel, width: u32, x_origin: u32, y_origin: u32,
)
    requires width > 0,
    ensures crate::specs::color_normalize_component_prefix(component, width, x_origin, y_origin, 0) == Ok(Seq::empty()),
{
    reveal(crate::specs::color_normalize_component_prefix);
}

pub proof fn production_color_plane_step(
    component: crate::specs::Part1TypedComponentModel, width: u32, x_origin: u32, y_origin: u32, count: nat,
)
    requires width > 0, width as nat <= usize::MAX as nat, count <= usize::MAX as nat,
    ensures crate::specs::color_normalize_component_prefix(component, width, x_origin, y_origin, count + 1)
        == match crate::specs::color_normalize_component_prefix(component, width, x_origin, y_origin, count) {
            Err(error) => Err(error),
            Ok(samples) => match crate::specs::color_pixel_coordinates(count as usize, width as usize) {
                Err(error) => Err(error),
                Ok((x, y)) => match crate::specs::color_component_normalized(component, x_origin, y_origin, x, y) {
                    Err(error) => Err(error),
                    Ok(value) => Ok(samples.push(value)),
                },
            },
        },
{
    reveal_with_fuel(crate::specs::color_normalize_component_prefix, 1);
}

pub proof fn production_color_plane_error(
    component: crate::specs::Part1TypedComponentModel, width: u32, x_origin: u32, y_origin: u32,
    count: nat, end: nat, error: crate::DecodeError,
)
    requires width > 0, count <= end,
        crate::specs::color_normalize_component_prefix(component, width, x_origin, y_origin, count) == Err(error),
    ensures crate::specs::color_normalize_component_prefix(component, width, x_origin, y_origin, end) == Err(error),
    decreases end - count,
{
    if end > count {
        production_color_plane_error(component, width, x_origin, y_origin, count, (end - 1) as nat, error);
        reveal_with_fuel(crate::specs::color_normalize_component_prefix, 1);
    }
}

pub proof fn production_supply_search_step(supplied: Seq<crate::specs::Part2SuppliedLayer>, reference: usize, start: nat)
    requires start <= supplied.len(),
    ensures crate::specs::part2_supply_search(supplied, reference, start)
        == if start == supplied.len() { None }
        else if supplied[start as int].0 == reference && supplied[start as int].1.is_some() { Some(start) }
        else { crate::specs::part2_supply_search(supplied, reference, start + 1) },
{
    reveal_with_fuel(crate::specs::part2_supply_search, 1);
}

pub proof fn production_gather_base(instructions: Seq<crate::specs::Part2Instruction>, supplied: Seq<crate::specs::Part2SuppliedLayer>)
    ensures crate::specs::part2_gather_layers(instructions, supplied, 0) == (Ok::<(), crate::DecodeError>(()), Seq::<crate::specs::Part2Placement>::empty(), supplied),
{
    reveal(crate::specs::part2_gather_layers);
}

pub proof fn production_gather_step(instructions: Seq<crate::specs::Part2Instruction>, supplied: Seq<crate::specs::Part2SuppliedLayer>, count: nat)
    requires count < instructions.len(),
    ensures crate::specs::part2_gather_layers(instructions, supplied, count + 1)
        == crate::specs::part2_gather_layer_step(instructions[count as int], crate::specs::part2_gather_layers(instructions, supplied, count)),
{
    reveal_with_fuel(crate::specs::part2_gather_layers, 1);
}

pub proof fn production_gather_error(instructions: Seq<crate::specs::Part2Instruction>, supplied: Seq<crate::specs::Part2SuppliedLayer>, count: nat)
    requires count <= instructions.len(), crate::specs::part2_gather_layers(instructions, supplied, count).0.is_err(),
    ensures crate::specs::part2_gather_layers(instructions, supplied, instructions.len())
        == crate::specs::part2_gather_layers(instructions, supplied, count),
    decreases instructions.len() - count,
{
    if count < instructions.len() {
        production_gather_step(instructions, supplied, count);
        production_gather_error(instructions, supplied, count + 1);
    }
}

pub proof fn production_timeline_instruction_base(
    instructions: Seq<crate::specs::Part2TimelineInstruction>, initial: crate::specs::Part2TimelineExecution,
    layers: usize, frames: u32, limit: usize,
)
    ensures crate::specs::part2_timeline_instructions(instructions, initial, 0, layers, frames, limit) == initial,
{
    reveal(crate::specs::part2_timeline_instructions);
}

pub proof fn production_timeline_instruction_step(
    instructions: Seq<crate::specs::Part2TimelineInstruction>, initial: crate::specs::Part2TimelineExecution,
    count: nat, layers: usize, frames: u32, limit: usize,
)
    requires count < instructions.len(),
    ensures crate::specs::part2_timeline_instructions(instructions, initial, count + 1, layers, frames, limit)
        == {
            let prior = crate::specs::part2_timeline_instructions(instructions, initial, count, layers, frames, limit);
            if crate::specs::part2_timeline_finished(prior) { prior } else {
                crate::specs::part2_timeline_step(prior.ok().unwrap().1, instructions[count as int], layers, frames, limit)
            }
        },
{
    reveal_with_fuel(crate::specs::part2_timeline_instructions, 1);
}

pub proof fn production_timeline_instruction_halt(
    instructions: Seq<crate::specs::Part2TimelineInstruction>, initial: crate::specs::Part2TimelineExecution,
    start: nat, end: nat, layers: usize, frames: u32, limit: usize,
)
    requires start <= end <= instructions.len(),
        crate::specs::part2_timeline_finished(crate::specs::part2_timeline_instructions(instructions, initial, start, layers, frames, limit)),
    ensures crate::specs::part2_timeline_instructions(instructions, initial, end, layers, frames, limit)
        == crate::specs::part2_timeline_instructions(instructions, initial, start, layers, frames, limit),
    decreases end - start,
{
    if start < end {
        production_timeline_instruction_halt(instructions, initial, start, (end - 1) as nat, layers, frames, limit);
        production_timeline_instruction_step(instructions, initial, (end - 1) as nat, layers, frames, limit);
    }
}

pub proof fn production_timeline_repetition_base(
    instructions: Seq<crate::specs::Part2TimelineInstruction>, initial: crate::specs::Part2TimelineExecution,
    layers: usize, frames: u32, limit: usize,
)
    ensures crate::specs::part2_timeline_repetitions(instructions, initial, 0, layers, frames, limit) == initial,
{
    reveal(crate::specs::part2_timeline_repetitions);
}

pub proof fn production_timeline_repetition_step(
    instructions: Seq<crate::specs::Part2TimelineInstruction>, initial: crate::specs::Part2TimelineExecution,
    count: nat, layers: usize, frames: u32, limit: usize,
)
    ensures crate::specs::part2_timeline_repetitions(instructions, initial, count + 1, layers, frames, limit)
        == crate::specs::part2_timeline_instructions(instructions,
            crate::specs::part2_timeline_repetitions(instructions, initial, count, layers, frames, limit),
            instructions.len(), layers, frames, limit),
{
    reveal_with_fuel(crate::specs::part2_timeline_repetitions, 1);
}

pub proof fn production_timeline_repetition_halt(
    instructions: Seq<crate::specs::Part2TimelineInstruction>, initial: crate::specs::Part2TimelineExecution,
    start: nat, end: nat, layers: usize, frames: u32, limit: usize,
)
    requires start <= end,
        crate::specs::part2_timeline_finished(crate::specs::part2_timeline_repetitions(instructions, initial, start, layers, frames, limit)),
    ensures crate::specs::part2_timeline_repetitions(instructions, initial, end, layers, frames, limit)
        == crate::specs::part2_timeline_repetitions(instructions, initial, start, layers, frames, limit),
    decreases end - start,
{
    if start < end {
        production_timeline_repetition_halt(instructions, initial, start, (end - 1) as nat, layers, frames, limit);
        let prior = crate::specs::part2_timeline_repetitions(instructions, initial, (end - 1) as nat, layers, frames, limit);
        production_timeline_instruction_base(instructions, prior, layers, frames, limit);
        production_timeline_instruction_halt(instructions, prior, 0, instructions.len(), layers, frames, limit);
        production_timeline_repetition_step(instructions, initial, (end - 1) as nat, layers, frames, limit);
    }
}

pub proof fn production_timeline_set_base(
    sets: Seq<crate::specs::Part2TimelineSet>, initial: crate::specs::Part2TimelineExecution,
    layers: usize, frames: u32, limit: usize,
)
    ensures crate::specs::part2_timeline_sets(sets, initial, 0, layers, frames, limit) == initial,
{
    reveal(crate::specs::part2_timeline_sets);
}

pub proof fn production_timeline_set_step(
    sets: Seq<crate::specs::Part2TimelineSet>, initial: crate::specs::Part2TimelineExecution,
    count: nat, layers: usize, frames: u32, limit: usize,
)
    requires count < sets.len(),
    ensures crate::specs::part2_timeline_sets(sets, initial, count + 1, layers, frames, limit)
        == crate::specs::part2_timeline_repetitions(sets[count as int].1,
            crate::specs::part2_timeline_sets(sets, initial, count, layers, frames, limit),
            sets[count as int].0 as nat + 1, layers, frames, limit),
{
    reveal_with_fuel(crate::specs::part2_timeline_sets, 1);
}

pub proof fn production_timeline_set_halt(
    sets: Seq<crate::specs::Part2TimelineSet>, initial: crate::specs::Part2TimelineExecution,
    start: nat, end: nat, layers: usize, frames: u32, limit: usize,
)
    requires start <= end <= sets.len(),
        crate::specs::part2_timeline_finished(crate::specs::part2_timeline_sets(sets, initial, start, layers, frames, limit)),
    ensures crate::specs::part2_timeline_sets(sets, initial, end, layers, frames, limit)
        == crate::specs::part2_timeline_sets(sets, initial, start, layers, frames, limit),
    decreases end - start,
{
    if start < end {
        production_timeline_set_halt(sets, initial, start, (end - 1) as nat, layers, frames, limit);
        let prior = crate::specs::part2_timeline_sets(sets, initial, (end - 1) as nat, layers, frames, limit);
        let set = sets[end as int - 1];
        production_timeline_repetition_base(set.1, prior, layers, frames, limit);
        production_timeline_repetition_halt(set.1, prior, 0, set.0 as nat + 1, layers, frames, limit);
        production_timeline_set_step(sets, initial, (end - 1) as nat, layers, frames, limit);
    }
}

pub proof fn production_frame_sequence_empty(frames: Seq<crate::specs::Part2Frame>, selected: nat)
    requires selected < frames.len(),
    ensures crate::specs::part2_frame_instruction_sequence(frames, selected, 0) == Seq::<crate::specs::Part2Instruction>::empty(),
{
    reveal(crate::specs::part2_frame_instruction_sequence);
}

pub proof fn production_frame_sequence_step(frames: Seq<crate::specs::Part2Frame>, selected: nat, count: nat)
    requires selected < frames.len(), count <= selected,
    ensures crate::specs::part2_frame_instruction_sequence(frames, selected, count + 1)
        == if count == selected || frames[count as int].3 {
            crate::specs::part2_frame_instruction_sequence(frames, selected, count) + frames[count as int].4
        } else { crate::specs::part2_frame_instruction_sequence(frames, selected, count) },
{
    reveal_with_fuel(crate::specs::part2_frame_instruction_sequence, 1);
}

pub proof fn production_render_empty(
    width: u32, height: u32, layers: Seq<crate::specs::Part2Placement>,
    initial: crate::specs::Part2RenderState, byte_limit: u64, work_limit: u64,
)
    ensures crate::specs::part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, 0) == initial,
{
    reveal(crate::specs::part2_render_prefix);
}

pub proof fn production_render_step(
    width: u32, height: u32, layers: Seq<crate::specs::Part2Placement>,
    initial: crate::specs::Part2RenderState, byte_limit: u64, work_limit: u64, count: nat,
)
    requires count < layers.len(),
    ensures crate::specs::part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, count + 1)
        == crate::specs::part2_render_step(width, height, crate::specs::part2_render_space(layers), layers[count as int],
            crate::specs::part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, count),
            byte_limit, work_limit),
{
    reveal_with_fuel(crate::specs::part2_render_prefix, 1);
}

pub proof fn production_render_error(
    width: u32, height: u32, layers: Seq<crate::specs::Part2Placement>,
    initial: crate::specs::Part2RenderState, byte_limit: u64, work_limit: u64, count: nat,
)
    requires count <= layers.len(),
        crate::specs::part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, count).0.is_err(),
    ensures crate::specs::part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, layers.len())
        == crate::specs::part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, count),
    decreases layers.len() - count,
{
    if count < layers.len() {
        production_render_step(width, height, layers, initial, byte_limit, work_limit, count);
        production_render_error(width, height, layers, initial, byte_limit, work_limit, count + 1);
    }
}

pub proof fn production_ht_uvlc_suffix_unfold(
    state: crate::specs::HtCleanupReaderState, remaining: nat, index: nat, value: u8,
)
    requires index + remaining <= 255,
    ensures crate::specs::ht_uvlc_suffix_run(state, remaining, index, value)
        == if remaining == 0 { (Ok(value), state) } else {
            let read = crate::specs::ht_cleanup_reader_read_vlc(state);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(bit) => if bit && index >= 8 {
                    (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), read.1)
                } else {
                    crate::specs::ht_uvlc_suffix_run(read.1, (remaining - 1) as nat, index + 1,
                        if bit { value | (1u8 << index as u8) } else { value })
                },
            }
        },
{
    reveal_with_fuel(crate::specs::ht_uvlc_suffix_run, 1);
}

pub proof fn production_ht_cleanup_peek_unfold(
    owner: crate::specs::HtCleanupReaderState, copy: crate::specs::HtReverseVlcState,
    remaining: nat, index: nat, value: u16,
)
    requires index + remaining <= 255,
    ensures crate::specs::ht_cleanup_peek_run(owner, copy, remaining, index, value)
        == if remaining == 0 { value } else {
            let available = match crate::specs::ht_reverse_vlc_position(copy) {
                None => false, Some(position) => crate::specs::ht_cleanup_reader_can_claim(owner, false, position.0),
            };
            if !available { value } else {
                let read = crate::specs::ht_reverse_vlc_read(copy);
                match read.0 {
                    Err(_) => value,
                    Ok(bit) => if bit && index >= 16 { value } else {
                        crate::specs::ht_cleanup_peek_run(owner, read.1, (remaining - 1) as nat, index + 1,
                            if bit { value | (1u16 << index as u8) } else { value })
                    },
                }
            }
        },
{
    reveal_with_fuel(crate::specs::ht_cleanup_peek_run, 1);
}

pub proof fn production_ht_cleanup_advance_unfold(state: crate::specs::HtCleanupReaderState, count: nat)
    ensures crate::specs::ht_cleanup_advance_vlc(state, count)
        == if count == 0 { (Ok(()), state) } else {
            let read = crate::specs::ht_cleanup_reader_read_vlc(state);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(_) => crate::specs::ht_cleanup_advance_vlc(read.1, (count - 1) as nat),
            }
        },
{
    reveal_with_fuel(crate::specs::ht_cleanup_advance_vlc, 1);
}

pub proof fn production_ht_cleanup_mel_suffix_unfold(state: crate::specs::HtCleanupReaderState, remaining: nat, suffix: u8)
    requires remaining <= 5,
    ensures crate::specs::ht_cleanup_mel_suffix(state, remaining, suffix)
        == if remaining == 0 { (Ok(suffix), state) } else {
            let read = crate::specs::ht_cleanup_reader_read_mel(state);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(bit) => crate::specs::ht_cleanup_mel_suffix(read.1, (remaining - 1) as nat,
                    if bit { (suffix << 1u8) | 1u8 } else { suffix << 1u8 }),
            }
        },
{
    reveal_with_fuel(crate::specs::ht_cleanup_mel_suffix, 1);
}

pub proof fn production_ht_magsgn_word_unfold(
    state: crate::specs::HtMagSgnState, remaining: nat, index: nat, value: u64,
)
    requires index + remaining <= 39,
    ensures crate::specs::ht_magsgn_word_run(state, remaining, index, value)
        == if remaining == 0 { (Ok(value), state) } else {
            let read = crate::specs::ht_magsgn_read(state);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(bit) => crate::specs::ht_magsgn_word_run(read.1, (remaining - 1) as nat, index + 1,
                    if bit { value | (1u64 << index as u8) } else { value }),
            }
        },
{
    reveal_with_fuel(crate::specs::ht_magsgn_word_run, 1);
}

pub proof fn production_ht_magsgn_finish_unfold(state: crate::specs::HtMagSgnState, remaining: nat)
    ensures crate::specs::ht_magsgn_finish_run(state, remaining)
        == if !crate::specs::ht_magsgn_pending(state) { (Ok(()), state) }
        else if remaining == 0 {
            (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
        } else {
            let read = crate::specs::ht_magsgn_read(state);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(false) => (Err(crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), read.1),
                Ok(true) => crate::specs::ht_magsgn_finish_run(read.1, (remaining - 1) as nat),
            }
        },
{
    reveal_with_fuel(crate::specs::ht_magsgn_finish_run, 1);
}

pub proof fn production_ht_reverse_vlc_prefix_step(state: crate::specs::HtReverseVlcState, count: nat)
    ensures crate::specs::ht_reverse_vlc_prefix(state, count + 1) == {
        let prefix = crate::specs::ht_reverse_vlc_prefix(state, count);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(bits) => {
                let step = crate::specs::ht_reverse_vlc_read(prefix.1);
                match step.0 {
                    Err(error) => (Err(error), step.1),
                    Ok(bit) => (Ok(bits.push(bit)), step.1),
                }
            },
        }
    },
{
    reveal_with_fuel(crate::specs::ht_reverse_vlc_prefix, 1);
}

pub proof fn production_ht_mel_prefix_step(state: crate::specs::HtMelState, count: nat)
    ensures crate::specs::ht_mel_prefix(state, count + 1) == {
        let prefix = crate::specs::ht_mel_prefix(state, count);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(bits) => {
                let step = crate::specs::ht_mel_read(prefix.1);
                match step.0 {
                    Err(error) => (Err(error), step.1),
                    Ok(bit) => (Ok(bits.push(bit)), step.1),
                }
            },
        }
    },
{
    reveal_with_fuel(crate::specs::ht_mel_prefix, 1);
}

pub proof fn production_magnitude_radix_powers()
    ensures
        vstd::arithmetic::power2::pow2(0) == 1,
        vstd::arithmetic::power2::pow2(64) == 18446744073709551616,
        vstd::arithmetic::power2::pow2(128) == 340282366920938463463374607431768211456,
        vstd::arithmetic::power2::pow2(192) == 6277101735386680763835789423207666416102355444464034512896,
        vstd::arithmetic::power2::pow2(256) == 115792089237316195423570985008687907853269984665640564039457584007913129639936,
        vstd::arithmetic::power2::pow2(320) == 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576,
        vstd::arithmetic::power2::pow2(384) == 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma_pow2_adds(64, 64);
    vstd::arithmetic::power2::lemma_pow2_adds(128, 64);
    vstd::arithmetic::power2::lemma_pow2_adds(192, 64);
    vstd::arithmetic::power2::lemma_pow2_adds(256, 64);
    vstd::arithmetic::power2::lemma_pow2_adds(320, 64);
}

pub proof fn production_magnitude_prefix_properties(limbs: Seq<u64>, count: nat)
    requires limbs.len() == 6, count <= 6,
    ensures
        crate::specs::part1_magnitude_prefix_value(limbs, count)
            < vstd::arithmetic::power2::pow2(64 * count),
        (crate::specs::part1_magnitude_prefix_value(limbs, count) == 0)
            == (forall |i: int| 0 <= i < count ==> limbs[i] == 0),
    decreases count,
{
    if count == 0 {
        vstd::arithmetic::power2::lemma2_to64();
    } else {
        production_magnitude_prefix_properties(limbs, (count - 1) as nat);
        vstd::arithmetic::power2::lemma_pow2_pos((64 * (count - 1)) as nat);
        vstd::arithmetic::power2::lemma_pow2_adds((64 * (count - 1)) as nat, 64);
        vstd::arithmetic::power2::lemma2_to64();
        let previous = crate::specs::part1_magnitude_prefix_value(limbs, (count - 1) as nat);
        let weight = vstd::arithmetic::power2::pow2((64 * (count - 1)) as nat);
        let digit = limbs[count - 1] as nat;
        assert(previous + digit * weight < weight * 18446744073709551616) by(nonlinear_arith)
            requires previous < weight, weight > 0, digit <= 18446744073709551615;
        assert((digit * weight == 0) == (digit == 0)) by(nonlinear_arith)
            requires weight > 0;
    }
}

pub proof fn production_magnitude_value_expansion(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(limbs)
        == (limbs[0] as nat)
            + (limbs[1] as nat) * 18446744073709551616
            + (limbs[2] as nat) * 340282366920938463463374607431768211456
            + (limbs[3] as nat) * 6277101735386680763835789423207666416102355444464034512896
            + (limbs[4] as nat) * 115792089237316195423570985008687907853269984665640564039457584007913129639936
            + (limbs[5] as nat) * 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576,
{
    production_magnitude_radix_powers();
    vstd::arithmetic::mul::lemma_mul_basics(limbs[0] as int);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 0) == 0);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 1) == limbs[0] as nat);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 2)
        == (limbs[0] as nat) + (limbs[1] as nat) * 18446744073709551616);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 3)
        == crate::specs::part1_magnitude_prefix_value(limbs, 2)
            + (limbs[2] as nat) * 340282366920938463463374607431768211456);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 4)
        == crate::specs::part1_magnitude_prefix_value(limbs, 2)
            + (limbs[2] as nat) * 340282366920938463463374607431768211456
            + (limbs[3] as nat) * 6277101735386680763835789423207666416102355444464034512896);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 5)
        == crate::specs::part1_magnitude_prefix_value(limbs, 4)
            + (limbs[4] as nat) * 115792089237316195423570985008687907853269984665640564039457584007913129639936);
    assert(crate::specs::part1_magnitude_prefix_value(limbs, 6)
        == crate::specs::part1_magnitude_prefix_value(limbs, 4)
            + (limbs[4] as nat) * 115792089237316195423570985008687907853269984665640564039457584007913129639936
            + (limbs[5] as nat) * 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576);
}

pub proof fn production_magnitude_sparse_prefix(limbs: Seq<u64>, index: nat, digit: u64, count: nat)
    requires
        limbs.len() == 6, index < 6, count <= 6,
        forall |i: int| 0 <= i < 6 ==> limbs[i] == if i == index { digit } else { 0 },
    ensures crate::specs::part1_magnitude_prefix_value(limbs, count)
        == if index < count { (digit as nat) * vstd::arithmetic::power2::pow2(64 * index) } else { 0 },
    decreases count,
{
    reveal_with_fuel(crate::specs::part1_magnitude_prefix_value, 1);
    if count > 0 {
        production_magnitude_sparse_prefix(limbs, index, digit, (count - 1) as nat);
        assert(limbs[count - 1] == if count - 1 == index { digit } else { 0 });
    }
}

pub proof fn production_magnitude_right_bit_word(low: u64, high: u64)
    ensures
        low as nat == ((low >> 1) as nat) * 2 + ((low & 1) as nat),
        (low & 1) < 2,
        crate::specs::part1_magnitude_right_word(low, high, 1) as nat
            == ((low >> 1) as nat) + ((high & 1) as nat) * 9223372036854775808,
{
    assert((low as u128) == ((((low >> 1) as u128) * 2 + ((low & 1) as u128)) as u128)) by(bit_vector);
    assert((low & 1) < 2) by(bit_vector);
    assert((((low >> 1) | (high << 63)) as u128)
        == ((((low >> 1) as u128) + ((high & 1) as u128) * 9223372036854775808) as u128)) by(bit_vector);
}

pub proof fn production_magnitude_left_bit_word(current: u64, previous: u64)
    ensures
        (current >> 63) <= 1,
        (crate::specs::part1_magnitude_left_word(current, previous, 1) as nat)
            + ((current >> 63) as nat) * 18446744073709551616
            == (current as nat) * 2 + ((previous >> 63) as nat),
{
    assert((current >> 63) <= 1) by(bit_vector);
    assert((((((current << 1) | (previous >> 63)) as u128)
        + ((current >> 63) as u128) * 18446744073709551616) as u128)
        == (((current as u128) * 2 + ((previous >> 63) as u128)) as u128)) by(bit_vector);
}

pub proof fn production_magnitude_zero_words(partial: u32)
    requires partial < 64,
    ensures
        crate::specs::part1_magnitude_right_word(0, 0, partial) == 0,
        crate::specs::part1_magnitude_left_word(0, 0, partial) == 0,
{
    if partial > 0 {
        assert((0u64 >> partial) | (0u64 << ((64 - partial) as u32)) == 0) by(bit_vector)
            requires 0 < partial < 64;
        assert((0u64 << partial) | (0u64 >> ((64 - partial) as u32)) == 0) by(bit_vector)
            requires 0 < partial < 64;
    }
}

pub proof fn production_magnitude_right_projection(limbs: Seq<u64>, shift: u16, index: int)
    requires limbs.len() == 6, index >= 0,
    ensures crate::specs::part1_magnitude_limb_or_zero(crate::specs::part1_magnitude_shift(limbs, shift), index)
        == crate::specs::part1_magnitude_right_word(
            crate::specs::part1_magnitude_limb_or_zero(limbs, index + shift / 64),
            crate::specs::part1_magnitude_limb_or_zero(limbs, index + shift / 64 + 1),
            (shift % 64) as u32,
        ),
{
    let partial = (shift % 64) as u32;
    production_magnitude_zero_words(partial);
    if index < 6 && shift < 384 && index + shift / 64 < 6 {
        let low = limbs[index + shift / 64];
        if partial == 0 {
            assert(low >> 0 == low) by(bit_vector);
        } else {
            assert((low >> partial) | (0u64 << ((64 - partial) as u32)) == low >> partial) by(bit_vector)
                requires 0 < partial < 64;
        }
    }
}

pub proof fn production_magnitude_left_projection(limbs: Seq<u64>, shift: u16, index: int)
    requires limbs.len() == 6, index < 6,
    ensures crate::specs::part1_magnitude_limb_or_zero(crate::specs::part1_magnitude_left(limbs, shift), index)
        == crate::specs::part1_magnitude_left_word(
            crate::specs::part1_magnitude_limb_or_zero(limbs, index - shift / 64),
            crate::specs::part1_magnitude_limb_or_zero(limbs, index - shift / 64 - 1),
            (shift % 64) as u32,
        ),
{
    production_magnitude_zero_words((shift % 64) as u32);
}

pub proof fn production_magnitude_right_word_step(a: u64, b: u64, c: u64, partial: u32)
    requires 0 < partial < 64,
    ensures crate::specs::part1_magnitude_right_word(
        crate::specs::part1_magnitude_right_word(a, b, (partial - 1) as u32),
        crate::specs::part1_magnitude_right_word(b, c, (partial - 1) as u32), 1,
    ) == crate::specs::part1_magnitude_right_word(a, b, partial),
{
    if partial > 1 {
        assert(((((a >> ((partial - 1) as u32)) | (b << ((65 - partial) as u32))) >> 1)
            | (((b >> ((partial - 1) as u32)) | (c << ((65 - partial) as u32))) << 63))
            == ((a >> partial) | (b << ((64 - partial) as u32)))) by(bit_vector)
            requires 1 < partial < 64;
    }
}

pub proof fn production_magnitude_left_word_step(a: u64, b: u64, c: u64, partial: u32)
    requires 0 < partial < 64,
    ensures crate::specs::part1_magnitude_left_word(
        crate::specs::part1_magnitude_left_word(a, b, (partial - 1) as u32),
        crate::specs::part1_magnitude_left_word(b, c, (partial - 1) as u32), 1,
    ) == crate::specs::part1_magnitude_left_word(a, b, partial),
{
    if partial > 1 {
        assert(((((a << ((partial - 1) as u32)) | (b >> ((65 - partial) as u32))) << 1)
            | (((b << ((partial - 1) as u32)) | (c >> ((65 - partial) as u32))) >> 63))
            == ((a << partial) | (b >> ((64 - partial) as u32)))) by(bit_vector)
            requires 1 < partial < 64;
    }
}

pub proof fn production_magnitude_word_crossing(a: u64, b: u64, c: u64)
    ensures
        crate::specs::part1_magnitude_right_word(
            crate::specs::part1_magnitude_right_word(a, b, 63),
            crate::specs::part1_magnitude_right_word(b, c, 63), 1,
        ) == b,
        crate::specs::part1_magnitude_left_word(
            crate::specs::part1_magnitude_left_word(a, b, 63),
            crate::specs::part1_magnitude_left_word(b, c, 63), 1,
        ) == b,
{
    assert(((((a >> 63) | (b << 1)) >> 1) | (((b >> 63) | (c << 1)) << 63)) == b) by(bit_vector);
    assert(((((a << 63) | (b >> 1)) << 1) | (((b << 63) | (c >> 1)) >> 63)) == b) by(bit_vector);
}

pub proof fn production_magnitude_right_composes_one(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6, 0 < shift < 384,
    ensures crate::specs::part1_magnitude_shift(limbs, shift)
        == crate::specs::part1_magnitude_shift(crate::specs::part1_magnitude_shift(limbs, (shift - 1) as u16), 1),
{
    let previous = crate::specs::part1_magnitude_shift(limbs, (shift - 1) as u16);
    assert forall |i: int| 0 <= i < 6 implies
        crate::specs::part1_magnitude_shift(limbs, shift)[i]
            == crate::specs::part1_magnitude_shift(previous, 1)[i]
    by {
        production_magnitude_right_projection(limbs, shift, i);
        production_magnitude_right_projection(previous, 1, i);
        production_magnitude_right_projection(limbs, (shift - 1) as u16, i);
        production_magnitude_right_projection(limbs, (shift - 1) as u16, i + 1);
        let base = i + shift / 64;
        if shift % 64 == 0 {
            production_magnitude_word_crossing(
                crate::specs::part1_magnitude_limb_or_zero(limbs, base - 1),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base + 1),
            );
        } else {
            production_magnitude_right_word_step(
                crate::specs::part1_magnitude_limb_or_zero(limbs, base),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base + 1),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base + 2), (shift % 64) as u32,
            );
        }
    }
    assert(crate::specs::part1_magnitude_shift(limbs, shift)
        =~= crate::specs::part1_magnitude_shift(previous, 1));
}

pub proof fn production_magnitude_left_composes_one(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6, 0 < shift < 384,
    ensures crate::specs::part1_magnitude_left(limbs, shift)
        == crate::specs::part1_magnitude_left(crate::specs::part1_magnitude_left(limbs, (shift - 1) as u16), 1),
{
    let previous = crate::specs::part1_magnitude_left(limbs, (shift - 1) as u16);
    assert forall |i: int| 0 <= i < 6 implies
        crate::specs::part1_magnitude_left(limbs, shift)[i]
            == crate::specs::part1_magnitude_left(previous, 1)[i]
    by {
        production_magnitude_left_projection(limbs, shift, i);
        production_magnitude_left_projection(previous, 1, i);
        production_magnitude_left_projection(limbs, (shift - 1) as u16, i);
        production_magnitude_left_projection(limbs, (shift - 1) as u16, i - 1);
        let base = i - shift / 64;
        if shift % 64 == 0 {
            production_magnitude_word_crossing(
                crate::specs::part1_magnitude_limb_or_zero(limbs, base + 1),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base - 1),
            );
        } else {
            production_magnitude_left_word_step(
                crate::specs::part1_magnitude_limb_or_zero(limbs, base),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base - 1),
                crate::specs::part1_magnitude_limb_or_zero(limbs, base - 2), (shift % 64) as u32,
            );
        }
    }
    assert(crate::specs::part1_magnitude_left(limbs, shift)
        =~= crate::specs::part1_magnitude_left(previous, 1));
}

pub proof fn production_magnitude_right_bit_value(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(crate::specs::part1_magnitude_shift(limbs, 1))
        == crate::specs::part1_magnitude_value(limbs) / 2,
{
    let shifted = crate::specs::part1_magnitude_shift(limbs, 1);
    production_magnitude_value_expansion(limbs);
    production_magnitude_value_expansion(shifted);
    assert forall |i: int| 0 <= i < 6 implies
        (shifted[i] as nat) == ((limbs[i] >> 1) as nat)
            + ((crate::specs::part1_magnitude_limb_or_zero(limbs, i + 1) & 1) as nat) * 9223372036854775808
        && (limbs[i] as nat) == ((limbs[i] >> 1) as nat) * 2 + ((limbs[i] & 1) as nat)
    by {
        production_magnitude_right_projection(limbs, 1, i);
        production_magnitude_right_bit_word(limbs[i], crate::specs::part1_magnitude_limb_or_zero(limbs, i + 1));
    }
    production_magnitude_right_bit_word(limbs[0], 0);
    assert(crate::specs::part1_magnitude_value(limbs)
        == 2 * crate::specs::part1_magnitude_value(shifted) + ((limbs[0] & 1) as nat));
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(
        crate::specs::part1_magnitude_value(limbs) as int, 2,
        crate::specs::part1_magnitude_value(shifted) as int, (limbs[0] & 1) as int,
    );
}

pub proof fn production_magnitude_value_bound(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(limbs) < crate::specs::part1_magnitude_capacity(),
{
    production_magnitude_prefix_properties(limbs, 6);
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
pub proof fn production_magnitude_double_telescope(limbs: Seq<u64>, shifted: Seq<u64>, high: Seq<u64>)
    requires
        limbs.len() == 6, shifted.len() == 6, high.len() == 6,
        forall |i: int| 0 <= i < 6 ==>
            (shifted[i] as nat) + (high[i] as nat) * 18446744073709551616
                == (limbs[i] as nat) * 2 + if i == 0 { 0nat } else { high[i - 1] as nat },
    ensures
        2 * crate::specs::part1_magnitude_value(limbs)
            == (high[5] as nat) * crate::specs::part1_magnitude_capacity()
                + crate::specs::part1_magnitude_value(shifted),
{
    production_magnitude_value_expansion(limbs);
    production_magnitude_value_expansion(shifted);
    production_magnitude_radix_powers();
    assert(crate::specs::part1_magnitude_capacity()
        == 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816);
    assert((shifted[0] as nat) + (high[0] as nat) * 18446744073709551616 == (limbs[0] as nat) * 2);
    assert((shifted[1] as nat) + (high[1] as nat) * 18446744073709551616 == (limbs[1] as nat) * 2 + high[0] as nat);
    assert((shifted[2] as nat) + (high[2] as nat) * 18446744073709551616 == (limbs[2] as nat) * 2 + high[1] as nat);
    assert((shifted[3] as nat) + (high[3] as nat) * 18446744073709551616 == (limbs[3] as nat) * 2 + high[2] as nat);
    assert((shifted[4] as nat) + (high[4] as nat) * 18446744073709551616 == (limbs[4] as nat) * 2 + high[3] as nat);
    assert((shifted[5] as nat) + (high[5] as nat) * 18446744073709551616 == (limbs[5] as nat) * 2 + high[4] as nat);
    assert(2 * crate::specs::part1_magnitude_value(limbs)
        == (high[5] as nat) * crate::specs::part1_magnitude_capacity()
            + crate::specs::part1_magnitude_value(shifted)) by(nonlinear_arith)
        requires
            crate::specs::part1_magnitude_value(limbs) == (limbs[0] as nat)
                + (limbs[1] as nat) * 18446744073709551616
                + (limbs[2] as nat) * 340282366920938463463374607431768211456
                + (limbs[3] as nat) * 6277101735386680763835789423207666416102355444464034512896
                + (limbs[4] as nat) * 115792089237316195423570985008687907853269984665640564039457584007913129639936
                + (limbs[5] as nat) * 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576,
            crate::specs::part1_magnitude_value(shifted) == (shifted[0] as nat)
                + (shifted[1] as nat) * 18446744073709551616
                + (shifted[2] as nat) * 340282366920938463463374607431768211456
                + (shifted[3] as nat) * 6277101735386680763835789423207666416102355444464034512896
                + (shifted[4] as nat) * 115792089237316195423570985008687907853269984665640564039457584007913129639936
                + (shifted[5] as nat) * 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576,
            crate::specs::part1_magnitude_capacity()
                == 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816,
            (shifted[0] as nat) + (high[0] as nat) * 18446744073709551616 == (limbs[0] as nat) * 2,
            (shifted[1] as nat) + (high[1] as nat) * 18446744073709551616 == (limbs[1] as nat) * 2 + high[0] as nat,
            (shifted[2] as nat) + (high[2] as nat) * 18446744073709551616 == (limbs[2] as nat) * 2 + high[1] as nat,
            (shifted[3] as nat) + (high[3] as nat) * 18446744073709551616 == (limbs[3] as nat) * 2 + high[2] as nat,
            (shifted[4] as nat) + (high[4] as nat) * 18446744073709551616 == (limbs[4] as nat) * 2 + high[3] as nat,
            (shifted[5] as nat) + (high[5] as nat) * 18446744073709551616 == (limbs[5] as nat) * 2 + high[4] as nat;
}

pub proof fn production_magnitude_left_bit_equation(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures
        2 * crate::specs::part1_magnitude_value(limbs)
            == ((limbs[5] >> 63) as nat) * crate::specs::part1_magnitude_capacity()
                + crate::specs::part1_magnitude_value(crate::specs::part1_magnitude_left(limbs, 1)),
{
    let shifted = crate::specs::part1_magnitude_left(limbs, 1);
    let high = Seq::new(6, |i: int| limbs[i] >> 63);
    assert forall |i: int| 0 <= i < 6 implies
        (shifted[i] as nat) + (high[i] as nat) * 18446744073709551616
            == (limbs[i] as nat) * 2 + if i == 0 { 0nat } else { high[i - 1] as nat }
    by {
        production_magnitude_left_projection(limbs, 1, i);
        production_magnitude_left_bit_word(limbs[i], crate::specs::part1_magnitude_limb_or_zero(limbs, i - 1));
        assert(0u64 >> 63 == 0) by(bit_vector);
    }
    production_magnitude_double_telescope(limbs, shifted, high);
}

pub proof fn production_magnitude_left_bit_value(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(crate::specs::part1_magnitude_left(limbs, 1))
        == (crate::specs::part1_magnitude_value(limbs) * 2) % crate::specs::part1_magnitude_capacity(),
{
    let shifted = crate::specs::part1_magnitude_left(limbs, 1);
    production_magnitude_left_bit_equation(limbs);
    production_magnitude_value_bound(shifted);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
        (crate::specs::part1_magnitude_value(limbs) * 2) as int,
        crate::specs::part1_magnitude_capacity() as int, (limbs[5] >> 63) as int,
        crate::specs::part1_magnitude_value(shifted) as int,
    );
}

pub proof fn production_magnitude_zero_value(limbs: Seq<u64>)
    requires limbs.len() == 6, crate::specs::part1_magnitude_zero(limbs),
    ensures crate::specs::part1_magnitude_value(limbs) == 0,
{
    production_magnitude_prefix_properties(limbs, 6);
}

pub proof fn production_magnitude_right_shift_value(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(crate::specs::part1_magnitude_shift(limbs, shift))
        == crate::specs::part1_magnitude_value(limbs) / vstd::arithmetic::power2::pow2(shift as nat),
    decreases shift,
{
    let shifted = crate::specs::part1_magnitude_shift(limbs, shift);
    if shift == 0 {
        assert forall |i: int| 0 <= i < 6 implies shifted[i] == limbs[i] by {
            production_magnitude_right_projection(limbs, shift, i);
        }
        assert(shifted =~= limbs);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::div_mod::lemma_div_basics_2(crate::specs::part1_magnitude_value(limbs) as int);
        assert(crate::specs::part1_magnitude_value(shifted)
            == crate::specs::part1_magnitude_value(limbs) / vstd::arithmetic::power2::pow2(shift as nat));
    } else if shift >= 384 {
        assert(crate::specs::part1_magnitude_zero(shifted));
        production_magnitude_zero_value(shifted);
        production_magnitude_value_bound(limbs);
        if shift > 384 {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(384, shift as nat);
        }
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(
            crate::specs::part1_magnitude_value(limbs) as int,
            vstd::arithmetic::power2::pow2(shift as nat) as int, 0,
            crate::specs::part1_magnitude_value(limbs) as int,
        );
        assert(crate::specs::part1_magnitude_value(shifted)
            == crate::specs::part1_magnitude_value(limbs) / vstd::arithmetic::power2::pow2(shift as nat));
    } else {
        let previous = crate::specs::part1_magnitude_shift(limbs, (shift - 1) as u16);
        production_magnitude_right_composes_one(limbs, shift);
        production_magnitude_right_shift_value(limbs, (shift - 1) as u16);
        production_magnitude_right_bit_value(previous);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma_pow2_pos((shift - 1) as nat);
        vstd::arithmetic::power2::lemma_pow2_adds((shift - 1) as nat, 1);
        vstd::arithmetic::div_mod::lemma_div_denominator(
            crate::specs::part1_magnitude_value(limbs) as int,
            vstd::arithmetic::power2::pow2((shift - 1) as nat) as int, 2,
        );
        assert(crate::specs::part1_magnitude_value(shifted)
            == crate::specs::part1_magnitude_value(limbs) / vstd::arithmetic::power2::pow2(shift as nat));
    }
}

pub proof fn production_magnitude_left_shift_value(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(crate::specs::part1_magnitude_left(limbs, shift))
        == (crate::specs::part1_magnitude_value(limbs) * vstd::arithmetic::power2::pow2(shift as nat))
            % crate::specs::part1_magnitude_capacity(),
    decreases shift,
{
    let shifted = crate::specs::part1_magnitude_left(limbs, shift);
    let value = crate::specs::part1_magnitude_value(limbs);
    let capacity = crate::specs::part1_magnitude_capacity();
    vstd::arithmetic::power2::lemma_pow2_pos(384);
    if shift == 0 {
        assert forall |i: int| 0 <= i < 6 implies shifted[i] == limbs[i] by {
            production_magnitude_left_projection(limbs, shift, i);
        }
        assert(shifted =~= limbs);
        production_magnitude_value_bound(limbs);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::mul::lemma_mul_basics(value as int);
        vstd::arithmetic::div_mod::lemma_small_mod(value, capacity);
    } else if shift >= 384 {
        assert(crate::specs::part1_magnitude_zero(shifted));
        production_magnitude_zero_value(shifted);
        vstd::arithmetic::power2::lemma_pow2_adds(384, (shift - 384) as nat);
        let power = vstd::arithmetic::power2::pow2(shift as nat);
        let remainder_power = vstd::arithmetic::power2::pow2((shift - 384) as nat);
        assert(value * power == (value * remainder_power) * capacity) by(nonlinear_arith)
            requires power == capacity * remainder_power;
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic((value * remainder_power) as int, capacity as int);
    } else {
        let previous = crate::specs::part1_magnitude_left(limbs, (shift - 1) as u16);
        production_magnitude_left_composes_one(limbs, shift);
        production_magnitude_left_shift_value(limbs, (shift - 1) as u16);
        production_magnitude_left_bit_value(previous);
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma_pow2_adds((shift - 1) as nat, 1);
        let power = vstd::arithmetic::power2::pow2(shift as nat);
        let previous_power = vstd::arithmetic::power2::pow2((shift - 1) as nat);
        assert(value * power == (value * previous_power) * 2) by(nonlinear_arith)
            requires power == previous_power * 2;
        vstd::arithmetic::div_mod::lemma_mul_mod_noop_left((value * previous_power) as int, 2, capacity as int);
    }
}

pub proof fn production_magnitude_word_zero_split(low: u64, high: u64, partial: u32)
    requires 0 < partial < 64,
    ensures
        (crate::specs::part1_magnitude_right_word(low, high, partial) == 0)
            == ((low >> partial) == 0 && (high << ((64 - partial) as u32)) == 0),
        ((low >> partial) == 0 && (low << ((64 - partial) as u32)) == 0) == (low == 0),
{
    assert((((low >> partial) | (high << ((64 - partial) as u32))) == 0)
        == ((low >> partial) == 0 && (high << ((64 - partial) as u32)) == 0)) by(bit_vector)
        requires 0 < partial < 64;
    assert(((low >> partial) == 0 && (low << ((64 - partial) as u32)) == 0) == (low == 0)) by(bit_vector)
        requires 0 < partial < 64;
}

pub proof fn production_magnitude_left_fits_high_bits(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6, 0 < shift < 384,
    ensures crate::specs::part1_magnitude_left_fits(limbs, shift)
        == crate::specs::part1_magnitude_zero(crate::specs::part1_magnitude_shift(limbs, (384 - shift) as u16)),
{
    let cutoff = (384 - shift) as u16;
    let high = crate::specs::part1_magnitude_shift(limbs, cutoff);
    let whole = shift / 64;
    let partial = (shift % 64) as u32;
    let base = cutoff / 64;
    let right = (cutoff % 64) as u32;
    if crate::specs::part1_magnitude_zero(high) {
        assert forall |i: int| 0 <= i < 6 implies
            if i + whole >= 6 { limbs[i] == 0 }
            else if partial != 0 && i + whole == 5 { limbs[i] >> ((64 - partial) as u32) == 0 }
            else { true }
        by {
            if partial == 0 {
                if i + whole >= 6 {
                    production_magnitude_right_projection(limbs, cutoff, i - base);
                    assert(high[i - base] == 0);
                }
            } else if i + whole >= 5 {
                production_magnitude_right_projection(limbs, cutoff, i - base);
                assert(high[i - base] == 0);
                production_magnitude_word_zero_split(
                    limbs[i], crate::specs::part1_magnitude_limb_or_zero(limbs, i + 1), right,
                );
                if i > base {
                    production_magnitude_right_projection(limbs, cutoff, i - base - 1);
                    assert(high[i - base - 1] == 0);
                    production_magnitude_word_zero_split(limbs[i - 1], limbs[i], right);
                    production_magnitude_word_zero_split(limbs[i], 0, right);
                }
            }
        }
    }
    if crate::specs::part1_magnitude_left_fits(limbs, shift) {
        assert forall |i: int| 0 <= i < 6 implies high[i] == 0 by {
            production_magnitude_right_projection(limbs, cutoff, i);
            let source = i + base;
            let low = crate::specs::part1_magnitude_limb_or_zero(limbs, source);
            let next = crate::specs::part1_magnitude_limb_or_zero(limbs, source + 1);
            if source < 6 {
                if partial == 0 || source > base {
                    assert(limbs[source] == 0);
                } else {
                    assert(limbs[source] >> right == 0);
                }
            }
            if source + 1 < 6 {
                assert(limbs[source + 1] == 0);
            }
            production_magnitude_zero_words(right);
            if right > 0 {
                assert((low >> right) | (0u64 << ((64 - right) as u32)) == low >> right) by(bit_vector)
                    requires 0 < right < 64;
            }
        }
    }
}

pub proof fn production_magnitude_left_fits_value(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_left_fits(limbs, shift)
        == (crate::specs::part1_magnitude_value(limbs) * vstd::arithmetic::power2::pow2(shift as nat)
            < crate::specs::part1_magnitude_capacity()),
{
    let value = crate::specs::part1_magnitude_value(limbs);
    let capacity = crate::specs::part1_magnitude_capacity();
    let power = vstd::arithmetic::power2::pow2(shift as nat);
    production_magnitude_prefix_properties(limbs, 6);
    vstd::arithmetic::power2::lemma_pow2_pos(384);
    if shift == 0 {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::mul::lemma_mul_basics(value as int);
    } else if shift >= 384 {
        if shift > 384 {
            vstd::arithmetic::power2::lemma_pow2_strictly_increases(384, shift as nat);
        }
        assert((value * power < capacity) == (value == 0)) by(nonlinear_arith)
            requires 0 <= value, 0 < capacity <= power;
    } else {
        let cutoff = (384 - shift) as u16;
        let threshold = vstd::arithmetic::power2::pow2(cutoff as nat);
        let high = crate::specs::part1_magnitude_shift(limbs, cutoff);
        production_magnitude_left_fits_high_bits(limbs, shift);
        production_magnitude_right_shift_value(limbs, cutoff);
        production_magnitude_prefix_properties(high, 6);
        vstd::arithmetic::power2::lemma_pow2_pos(cutoff as nat);
        vstd::arithmetic::power2::lemma_pow2_pos(shift as nat);
        vstd::arithmetic::power2::lemma_pow2_adds(cutoff as nat, shift as nat);
        vstd::arithmetic::div_mod::lemma_small_div_converse(value as int, threshold as int);
        if value < threshold {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_div(value as int, threshold as int, 0, value as int);
        }
        assert((value * power < capacity) == (value < threshold)) by(nonlinear_arith)
            requires capacity == threshold * power, threshold > 0, power > 0;
    }
}

pub proof fn production_magnitude_left_prefix_complete(limbs: Seq<u64>, shift: u16)
    requires limbs.len() == 6, shift < 384,
    ensures crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, 6)
        == crate::specs::part1_magnitude_left(limbs, shift),
{
    assert forall |i: int| 0 <= i < 6 implies
        crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, 6)[i]
            == crate::specs::part1_magnitude_left(limbs, shift)[i]
    by {
        let partial = (shift % 64) as u32;
        let source = i - shift / 64;
        let low = crate::specs::part1_magnitude_limb_or_zero(limbs, source);
        production_magnitude_zero_words(partial);
        if partial == 0 {
            assert(low << 0 == low) by(bit_vector);
            assert(low | 0u64 == low) by(bit_vector);
        } else {
            assert(0u64 >> ((64 - partial) as u32) == 0) by(bit_vector)
                requires 0 < partial < 64;
            assert(0u64 << partial == 0) by(bit_vector)
                requires partial < 64;
            assert(0u64 | 0u64 == 0) by(bit_vector);
        }
    }
    assert(crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, 6)
        =~= crate::specs::part1_magnitude_left(limbs, shift));
}

pub proof fn production_magnitude_or_zero(word: u64)
    ensures word | 0u64 == word, 0u64 | word == word,
{
    assert(word | 0u64 == word) by(bit_vector);
    assert(0u64 | word == word) by(bit_vector);
}

pub proof fn production_magnitude_left_prefix_discard(limbs: Seq<u64>, shift: u16, count: nat)
    requires limbs.len() == 6, shift < 384, count < 6, count + shift / 64 >= 6,
    ensures crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count)
        == crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count + 1),
{
    assert(crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count)
        =~= crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count + 1));
}

pub proof fn production_magnitude_left_prefix_step(limbs: Seq<u64>, shift: u16, count: nat)
    requires limbs.len() == 6, shift < 384, count < 6, count + shift / 64 < 6,
    ensures {
        let before = crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count);
        let destination = count + shift / 64;
        let partial = (shift % 64) as u32;
        let first = before.update(destination as int, before[destination as int] | (limbs[count as int] << partial));
        let after = if partial > 0 && destination + 1 < 6 {
            first.update(destination as int + 1, first[destination as int + 1]
                | (limbs[count as int] >> ((64 - partial) as u32)))
        } else { first };
        after == crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count + 1)
    },
{
    let before = crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count);
    let destination = count + shift / 64;
    let partial = (shift % 64) as u32;
    let low = limbs[count as int] << partial;
    let first = before.update(destination as int, before[destination as int] | low);
    let after = if partial > 0 && destination + 1 < 6 {
        first.update(destination as int + 1, first[destination as int + 1]
            | (limbs[count as int] >> ((64 - partial) as u32)))
    } else { first };
    production_magnitude_or_zero(0);
    assert forall |i: int| 0 <= i < 6 implies
        after[i] == crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count + 1)[i]
    by {
        if i == destination {
            let high = if partial > 0 && count > 0 {
                limbs[count as int - 1] >> ((64 - partial) as u32)
            } else { 0u64 };
            production_magnitude_or_zero(high);
            assert(high | low == low | high) by(bit_vector);
        } else if partial > 0 && i == destination + 1 {
            let high = limbs[count as int] >> ((64 - partial) as u32);
            production_magnitude_or_zero(high);
        }
    }
    assert(after =~= crate::proofs::internal_specs::magnitude_left_prefix(limbs, shift, count + 1));
}

pub proof fn production_magnitude_add_limb(sum: u128)
    requires sum <= 36893488147419103231,
    ensures (sum as u64 as nat) + (if sum > u64::MAX as u128 { 18446744073709551616nat } else { 0nat }) == sum as nat,
{
    assert(sum == ((((sum as u64) as u128)
        + if sum > u64::MAX as u128 { 18446744073709551616u128 } else { 0u128 }) as u128)) by(bit_vector)
        requires sum <= 36893488147419103231;
}

pub proof fn production_magnitude_prefix_order(left: Seq<u64>, right: Seq<u64>, count: nat)
    requires left.len() == 6, right.len() == 6, count <= 6,
    ensures crate::specs::part1_magnitude_prefix_less(left, right, count)
        == (crate::specs::part1_magnitude_prefix_value(left, count) < crate::specs::part1_magnitude_prefix_value(right, count)),
    decreases count,
{
    if count > 0 {
        let last = (count - 1) as nat;
        production_magnitude_prefix_order(left, right, last);
        production_magnitude_prefix_properties(left, last);
        production_magnitude_prefix_properties(right, last);
        vstd::arithmetic::power2::lemma_pow2_pos(64 * last);
        let a = left[last as int] as nat;
        let b = right[last as int] as nat;
        let low_a = crate::specs::part1_magnitude_prefix_value(left, last);
        let low_b = crate::specs::part1_magnitude_prefix_value(right, last);
        let weight = vstd::arithmetic::power2::pow2(64 * last);
        if a < b {
            assert(crate::specs::part1_magnitude_prefix_less(left, right, count));
            assert(low_a + a * weight < low_b + b * weight) by(nonlinear_arith)
                requires low_a < weight, low_b < weight, weight > 0, a < b;
        } else if b < a {
            if crate::specs::part1_magnitude_prefix_less(left, right, count) {
                let witness = choose |i: int| 0 <= i < count && left[i] < right[i]
                    && forall |j: int| i < j < count ==> left[j] == right[j];
                assert(witness < last);
                assert(left[last as int] == right[last as int]);
            }
            assert(low_b + b * weight < low_a + a * weight) by(nonlinear_arith)
                requires low_a < weight, low_b < weight, weight > 0, b < a;
        } else {
            if crate::specs::part1_magnitude_prefix_less(left, right, count) {
                let witness = choose |i: int| 0 <= i < count && left[i] < right[i]
                    && forall |j: int| i < j < count ==> left[j] == right[j];
                assert(witness < last);
                assert(crate::specs::part1_magnitude_prefix_less(left, right, last));
            }
            if crate::specs::part1_magnitude_prefix_less(left, right, last) {
                let witness = choose |i: int| 0 <= i < last && left[i] < right[i]
                    && forall |j: int| i < j < last ==> left[j] == right[j];
                assert forall |j: int| witness < j < count implies left[j] == right[j] by {
                    if j != last { assert(j < last); }
                }
                assert(crate::specs::part1_magnitude_prefix_less(left, right, count));
            }
        }
    }
}

pub proof fn production_magnitude_sub_prefix_step(
    left: Seq<u64>, right: Seq<u64>, output: Seq<u64>, index: nat, digit: u64, old_borrow: bool, next_borrow: bool,
)
    requires left.len() == 6, right.len() == 6, output.len() == 6, index < 6,
        crate::specs::part1_magnitude_prefix_value(left, index) + (if old_borrow { vstd::arithmetic::power2::pow2(64 * index) } else { 0nat })
            == crate::specs::part1_magnitude_prefix_value(right, index) + crate::specs::part1_magnitude_prefix_value(output, index),
        left[index as int] as nat + (if next_borrow { 18446744073709551616nat } else { 0nat })
            == right[index as int] as nat + (if old_borrow { 1nat } else { 0nat }) + digit as nat,
    ensures crate::specs::part1_magnitude_prefix_value(left, index + 1) + (if next_borrow { vstd::arithmetic::power2::pow2(64 * (index + 1)) } else { 0nat })
        == crate::specs::part1_magnitude_prefix_value(right, index + 1)
            + crate::specs::part1_magnitude_prefix_value(output.update(index as int, digit), index + 1),
{
    vstd::arithmetic::power2::lemma_pow2_adds(64 * index, 64);
    vstd::arithmetic::power2::lemma2_to64();
    production_magnitude_prefix_update(output, index, digit);
    production_magnitude_add_prefix_step(
        crate::specs::part1_magnitude_prefix_value(right, index),
        crate::specs::part1_magnitude_prefix_value(output, index),
        crate::specs::part1_magnitude_prefix_value(left, index),
        right[index as int], digit, left[index as int], old_borrow, next_borrow,
        vstd::arithmetic::power2::pow2(64 * index), vstd::arithmetic::power2::pow2(64 * (index + 1)),
    );
}

pub proof fn production_magnitude_prefix_agrees(left: Seq<u64>, right: Seq<u64>, count: nat)
    requires left.len() == 6, right.len() == 6, count <= 6,
        forall |i: int| 0 <= i < count ==> left[i] == right[i],
    ensures crate::specs::part1_magnitude_prefix_value(left, count)
        == crate::specs::part1_magnitude_prefix_value(right, count),
    decreases count,
{
    if count > 0 {
        production_magnitude_prefix_agrees(left, right, (count - 1) as nat);
    }
}

pub proof fn production_magnitude_prefix_update(limbs: Seq<u64>, index: nat, digit: u64)
    requires limbs.len() == 6, index < 6,
    ensures
        crate::specs::part1_magnitude_prefix_value(limbs.update(index as int, digit), index)
            == crate::specs::part1_magnitude_prefix_value(limbs, index),
        crate::specs::part1_magnitude_prefix_value(limbs.update(index as int, digit), index + 1)
            == crate::specs::part1_magnitude_prefix_value(limbs, index)
                + (digit as nat) * vstd::arithmetic::power2::pow2(64 * index),
{
    production_magnitude_prefix_agrees(limbs, limbs.update(index as int, digit), index);
}

pub proof fn production_magnitude_add_prefix_step(
    left: nat, right: nat, output: nat, a: u64, b: u64, digit: u64,
    previous_carry: bool, next_carry: bool, weight: nat, next_weight: nat,
)
    requires
        left + right == output + if previous_carry { weight } else { 0nat },
        (digit as nat) + (if next_carry { 18446744073709551616nat } else { 0nat })
            == (a as nat) + (b as nat) + if previous_carry { 1nat } else { 0nat },
        next_weight == weight * 18446744073709551616,
    ensures
        left + (a as nat) * weight + right + (b as nat) * weight
            == output + (digit as nat) * weight + if next_carry { next_weight } else { 0nat },
{
    let old = if previous_carry { 1nat } else { 0nat };
    let new = if next_carry { 1nat } else { 0nat };
    vstd::arithmetic::mul::lemma_mul_basics(weight as int);
    vstd::arithmetic::mul::lemma_mul_basics(next_weight as int);
    assert(left + (a as nat) * weight + right + (b as nat) * weight
        == output + (digit as nat) * weight + new * next_weight) by(nonlinear_arith)
        requires left + right == output + old * weight,
            (digit as nat) + new * 18446744073709551616 == (a as nat) + (b as nat) + old,
            next_weight == weight * 18446744073709551616;
}

pub proof fn production_magnitude_low_word(limbs: Seq<u64>)
    requires limbs.len() == 6,
    ensures crate::specs::part1_magnitude_value(limbs) % 18446744073709551616 == limbs[0] as nat,
{
    production_magnitude_value_expansion(limbs);
    let upper = (limbs[1] as nat)
        + (limbs[2] as nat) * 18446744073709551616
        + (limbs[3] as nat) * 340282366920938463463374607431768211456
        + (limbs[4] as nat) * 6277101735386680763835789423207666416102355444464034512896
        + (limbs[5] as nat) * 115792089237316195423570985008687907853269984665640564039457584007913129639936;
    assert(crate::specs::part1_magnitude_value(limbs) == upper * 18446744073709551616 + (limbs[0] as nat));
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse_mod(
        crate::specs::part1_magnitude_value(limbs) as int, 18446744073709551616, upper as int, limbs[0] as int,
    );
}

pub proof fn production_layer_scan_empty(channels: Seq<crate::specs::Part2LayerChannel>, color_count: nat)
    ensures crate::specs::part2_layer_channel_scan(channels, color_count, 0)
        == Ok((Seq::new(color_count, |i: int| None), Seq::empty())),
{
    reveal(crate::specs::part2_layer_channel_scan);
}

pub proof fn production_layer_scan_step(
    channels: Seq<crate::specs::Part2LayerChannel>, color_count: nat, count: nat,
)
    requires count < channels.len(),
    ensures crate::specs::part2_layer_channel_scan(channels, color_count, count + 1)
        == match crate::specs::part2_layer_channel_scan(channels, color_count, count) {
            Err(error) => Err(error),
            Ok((colors, alphas)) => crate::specs::part2_layer_channel_scan_step(colors, alphas, channels[count as int]),
        },
{
    reveal_with_fuel(crate::specs::part2_layer_channel_scan, 1);
}

pub proof fn production_layer_scan_error(
    channels: Seq<crate::specs::Part2LayerChannel>, color_count: nat, count: nat, end: nat,
    error: crate::DecodeError,
)
    requires count <= end <= channels.len(),
        crate::specs::part2_layer_channel_scan(channels, color_count, count) == Err(error),
    ensures crate::specs::part2_layer_channel_scan(channels, color_count, end) == Err(error),
    decreases end - count,
{
    if end > count {
        production_layer_scan_error(channels, color_count, count, (end - 1) as nat, error);
        production_layer_scan_step(channels, color_count, (end - 1) as nat);
    }
}

pub proof fn production_layer_alpha_empty(alphas: Seq<crate::specs::Part2LayerAlpha>, area: nat)
    ensures crate::specs::part2_layer_alpha_fold(alphas, area, 0) == Ok(None),
{
    reveal(crate::specs::part2_layer_alpha_fold);
}

pub proof fn production_layer_alpha_product_step(first: Seq<u16>, second: Seq<u16>, count: nat)
    requires count < first.len(), first.len() == second.len(),
    ensures crate::proofs::internal_specs::part2_layer_alpha_product_prefix(first, second, count + 1)
        == crate::proofs::internal_specs::part2_layer_alpha_product_prefix(first, second, count)
            .update(count as int, crate::specs::part2_normalized_sample_product(first[count as int], second[count as int]) as u16),
{
    assert(crate::proofs::internal_specs::part2_layer_alpha_product_prefix(first, second, count + 1)
        =~= crate::proofs::internal_specs::part2_layer_alpha_product_prefix(first, second, count)
            .update(count as int, crate::specs::part2_normalized_sample_product(first[count as int], second[count as int]) as u16));
}

pub proof fn production_layer_alpha_step(alphas: Seq<crate::specs::Part2LayerAlpha>, area: nat, count: nat)
    requires count < alphas.len(),
    ensures crate::specs::part2_layer_alpha_fold(alphas, area, count + 1)
        == match crate::specs::part2_layer_alpha_fold(alphas, area, count) {
            Err(error) => Err(error),
            Ok(previous) => crate::specs::part2_layer_alpha_merge(previous, alphas[count as int], area),
        },
{
    reveal_with_fuel(crate::specs::part2_layer_alpha_fold, 1);
}

pub proof fn production_layer_alpha_error(
    alphas: Seq<crate::specs::Part2LayerAlpha>, area: nat, count: nat, end: nat,
    error: crate::DecodeError,
)
    requires count <= end <= alphas.len(),
        crate::specs::part2_layer_alpha_fold(alphas, area, count) == Err(error),
    ensures crate::specs::part2_layer_alpha_fold(alphas, area, end) == Err(error),
    decreases end - count,
{
    if end > count {
        production_layer_alpha_error(alphas, area, count, (end - 1) as nat, error);
        production_layer_alpha_step(alphas, area, (end - 1) as nat);
    }
}

pub proof fn production_composition_canvas_empty(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: crate::specs::Part2CompositionGeometry, expand_grayscale: bool,
)
    requires geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
    ensures crate::specs::part2_composition_canvas_prefix(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale, 0,
    ) == (true, destination, destination_alpha),
{
    reveal(crate::specs::part2_composition_canvas_prefix);
}

pub proof fn production_composition_canvas_step(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: crate::specs::Part2CompositionGeometry, expand_grayscale: bool,
    x: nat, y: nat, source_index: nat, destination_index: nat,
)
    requires
        geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
        x < geometry.copy_width,
        crate::specs::part2_composition_canvas_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            y * geometry.copy_width + x,
        ).0,
        source_index == (geometry.source_y + y * geometry.source_crop_height / geometry.target_height) * geometry.source_width
            + geometry.source_x + x * geometry.source_crop_width / geometry.target_width,
        destination_index == (geometry.target_y + y) * geometry.canvas_width + geometry.target_x + x,
    ensures
        crate::specs::part2_composition_canvas_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            y * geometry.copy_width + x + 1,
        ) == crate::specs::part2_composition_pixel_transition(
            source, source_alpha,
            crate::specs::part2_composition_canvas_prefix(
                source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
                y * geometry.copy_width + x,
            ).1,
            crate::specs::part2_composition_canvas_prefix(
                source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
                y * geometry.copy_width + x,
            ).2,
            source_index, destination_index, expand_grayscale,
        ),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (y * geometry.copy_width + x) as int, geometry.copy_width as int, y as int, x as int,
    );
    reveal_with_fuel(crate::specs::part2_composition_canvas_prefix, 2);
}

pub proof fn production_composition_raster_prefix_bound(width: nat, height: nat, x: nat, y: nat)
    requires width > 0 && height > 0 && x < width && y < height,
    ensures y * width + x + 1 <= width * height,
{
    assert(x + 1 <= width && y + 1 <= height);
    assert((y + 1) * width == y * width + width) by(nonlinear_arith);
    vstd::arithmetic::mul::lemma_mul_inequality((y + 1) as int, height as int, width as int);
    assert(height * width == width * height) by(nonlinear_arith);
}

pub proof fn production_composition_prefix_observation(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: crate::specs::Part2CompositionGeometry, expand_grayscale: bool, initial_work: nat,
    final_colors: Seq<Seq<u16>>, final_alpha: Seq<u16>, final_work: nat, completed: nat,
)
    requires
        geometry.source_crop_width > 0 && geometry.source_crop_height > 0,
        geometry.target_width > 0 && geometry.target_height > 0,
        geometry.copy_width > 0 && geometry.copy_height > 0,
        crate::specs::part2_composition_layer_prefix_matches(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale, initial_work,
            final_colors, final_alpha, final_work, completed,
        ),
    ensures crate::specs::part2_composition_layer_prefix_safe(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale, initial_work,
        final_colors, final_alpha, final_work,
    ),
{
    assert(exists |count: nat| count == completed && crate::specs::part2_composition_layer_prefix_matches(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale, initial_work,
        final_colors, final_alpha, final_work, count,
    ));
}

pub proof fn production_composition_budgeted_empty(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: crate::specs::Part2CompositionGeometry, expand_grayscale: bool,
    initial_work: nat, work_limit: u64,
)
    requires geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
    ensures crate::specs::part2_composition_budgeted_prefix(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale, initial_work, work_limit, 0,
    ) == (Ok(()), destination, destination_alpha, initial_work),
{
    reveal(crate::specs::part2_composition_budgeted_prefix);
}

pub proof fn production_composition_budgeted_step(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: crate::specs::Part2CompositionGeometry, expand_grayscale: bool,
    initial_work: nat, work_limit: u64, x: nat, y: nat,
)
    requires
        geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
        x < geometry.copy_width,
        crate::specs::part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            initial_work, work_limit, y * geometry.copy_width + x,
        ).0.is_ok(),
    ensures crate::specs::part2_composition_budgeted_prefix(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
        initial_work, work_limit, y * geometry.copy_width + x + 1,
    ) == crate::specs::part2_composition_budgeted_step(
        source, source_alpha,
        crate::specs::part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            initial_work, work_limit, y * geometry.copy_width + x,
        ).1,
        crate::specs::part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            initial_work, work_limit, y * geometry.copy_width + x,
        ).2,
        geometry, expand_grayscale,
        crate::specs::part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            initial_work, work_limit, y * geometry.copy_width + x,
        ).3, work_limit, x, y,
    ),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        (y * geometry.copy_width + x) as int, geometry.copy_width as int, y as int, x as int,
    );
    reveal_with_fuel(crate::specs::part2_composition_budgeted_prefix, 2);
}

pub proof fn production_composition_budgeted_failure_absorbs(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: crate::specs::Part2CompositionGeometry, expand_grayscale: bool,
    initial_work: nat, work_limit: u64, stopped: nat, count: nat,
)
    requires
        geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
        stopped <= count,
        crate::specs::part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            initial_work, work_limit, stopped,
        ).0.is_err(),
    ensures crate::specs::part2_composition_budgeted_prefix(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
        initial_work, work_limit, count,
    ) == crate::specs::part2_composition_budgeted_prefix(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
        initial_work, work_limit, stopped,
    ),
    decreases count,
{
    if count > stopped {
        production_composition_budgeted_failure_absorbs(
            source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
            initial_work, work_limit, stopped, (count - 1) as nat,
        );
        reveal_with_fuel(crate::specs::part2_composition_budgeted_prefix, 2);
    }
}

pub proof fn production_ads_parser_uses_independent_field_padding(depths: nat, splits: nat)
    ensures
        ads_payload_bytes(depths, splits)
            == 3 + (depths + 3) / 4 + (splits + 3) / 4,
{
    reveal(ads_payload_bytes);
    reveal(crate::specs::packed_two_bit_bytes);
}

pub proof fn production_atk_inverse_visits_each_step_in_reverse(step: nat, steps: nat)
    requires
        step < steps,
    ensures
        atk_reconstruction_step(step, steps) < steps,
{
    reveal(atk_reconstruction_step);
}

pub proof fn production_atk_inverse_alternates_subsequences(initial_odd: bool, step: nat)
    ensures
        atk_update_parity(initial_odd, step + 1)
            != atk_update_parity(initial_odd, step),
{
    reveal(atk_update_parity);
}

pub proof fn production_cbd_rejects_tile_header_scope()
    ensures
        valid_cbd_scope(true),
        !valid_cbd_scope(false),
{
    reveal(valid_cbd_scope);
}

pub proof fn box_header_and_payload_partition(
    header_length: nat,
    total_length: nat,
)
    requires
        valid_box_lengths(header_length, total_length),
    ensures
        header_length + (total_length - header_length) == total_length,
{
}

pub proof fn checked_geometry_area_is_symmetric(width: nat, height: nat)
    ensures
        width * height == height * width,
{
}

pub proof fn production_selection_region_is_bounded(
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
        image_x0 <= region_x0,
        region_x1 <= image_x1,
        image_y0 <= region_y0,
        region_y1 <= image_y1,
{
    reveal(valid_selection_region);
}

pub proof fn production_jpip_fragment_is_parent_bounded(
    offset: nat,
    length: nat,
    limit: nat,
)
    requires
        valid_jpip_fragment(offset, length, limit),
    ensures
        offset + length <= limit,
{
    reveal(valid_jpip_fragment);
}

pub proof fn production_part9_header_and_vbas_contracts_are_exact(
    form: nat,
    value: nat,
    group: nat,
)
    ensures
        part9_header_form_valid(form) == (1 <= form && form <= 3),
        part9_header_has_explicit_class(form) == (form >= 2),
        part9_header_has_explicit_codestream(form) == (form == 3),
        part9_vbas_step(value, group) == value * 128 + group,
{
    reveal(part9_header_form_valid);
    reveal(part9_header_has_explicit_class);
    reveal(part9_header_has_explicit_codestream);
    reveal(part9_vbas_step);
}

pub proof fn production_part9_aux_eor_and_class_contracts_are_exact(
    class_identifier: nat,
    header: nat,
    body: nat,
)
    ensures
        part9_auxiliary_present(class_identifier) == (class_identifier % 2 == 1),
        part9_eor_extent(header, body) == header + body,
        part9_class_identifier_valid(class_identifier) == (class_identifier <= 8),
{
    reveal(part9_auxiliary_present);
    reveal(part9_eor_extent);
    reveal(part9_class_identifier_valid);
}

pub proof fn production_part9_identity_contract_is_exact(
    first_class: nat,
    first_codestream: nat,
    first_in_class: nat,
    second_class: nat,
    second_codestream: nat,
    second_in_class: nat,
)
    ensures
        part9_databin_identity(
            first_class,
            first_codestream,
            first_in_class,
            second_class,
            second_codestream,
            second_in_class,
        ) == (
            crate::specs::part9_class_key(first_class) == crate::specs::part9_class_key(second_class)
            && first_codestream == second_codestream
            && first_in_class == second_in_class
        ),
{
    reveal(part9_databin_identity);
}

pub proof fn production_part9_flat_precinct_identity_is_exact(
    tile: nat,
    tile_count: nat,
    component_precinct: nat,
)
    ensures
        part9_precinct_flat_identity(tile, tile_count, component_precinct)
            == tile + component_precinct * tile_count,
{
    reveal(part9_precinct_flat_identity);
}

pub proof fn production_part9_transaction_and_merge_contracts_are_exact(
    first: nat,
    second: nat,
    equal: bool,
)
    ensures
        part9_overlap_consistent(equal) == equal,
        part9_transaction_commit(equal) == equal,
        part9_merge_start(first, second) <= first,
        part9_merge_start(first, second) <= second,
        part9_merge_end(first, second) >= first,
        part9_merge_end(first, second) >= second,
{
    reveal(part9_overlap_consistent);
    reveal(part9_transaction_commit);
    reveal(part9_merge_start);
    reveal(part9_merge_end);
}

pub proof fn production_part9_range_accounting_is_exact(required: nat, missing: nat)
    requires
        missing <= required,
    ensures
        part9_missing_length(required, missing) == required - missing,
        part9_available_bytes(required, missing) == required - missing,
{
    reveal(part9_missing_length);
    reveal(part9_available_bytes);
}

pub proof fn production_part9_metadata_descent_rejects_cycle(
    depth: nat,
    maximum_depth: nat,
)
    ensures
        !part9_metadata_descent_allowed(depth, maximum_depth, true),
{
    reveal(part9_metadata_descent_allowed);
}

pub proof fn production_part9_reconstruction_and_reframing_lengths_are_exact(
    main: nat,
    tile: nat,
    packet: nat,
    eoc: nat,
    sop: bool,
    eph: bool,
)
    ensures
        part9_reconstruction_length(main, tile, packet, eoc) == main + tile + packet + eoc,
        part9_packet_reframed_length(packet, sop, eph)
            == packet + (if sop { 6 as nat } else { 0 as nat })
                + (if eph { 2 as nat } else { 0 as nat }),
{
    reveal(part9_reconstruction_length);
    reveal(part9_packet_reframed_length);
}

pub proof fn production_part9_all_progressions_and_reframed_markers_are_classified(
    order: nat,
    marker: nat,
    tile: bool,
)
    ensures
        part9_progression_supported(order) == (order <= 4),
        part9_reframed_marker_removed(marker, tile) == (
            if tile {
                marker == 0xff58 || marker == 0xff61
            } else {
                marker == 0xff55 || marker == 0xff57 || marker == 0xff60
            }
        ),
{
    reveal(part9_progression_supported);
    reveal(part9_reframed_marker_removed);
}

pub proof fn production_jpip_final_length_conflict_policy_is_deterministic(
    existing: nat,
    announced: nat,
)
    requires
        consistent_jpip_final_length(existing, announced),
    ensures
        existing == announced,
{
    reveal(consistent_jpip_final_length);
}

pub proof fn production_jpip_completeness_requires_full_prefix(
    prefix: nat,
    final_length: nat,
)
    requires
        complete_jpip_databin(prefix, final_length),
    ensures
        prefix == final_length,
{
    reveal(complete_jpip_databin);
}

pub proof fn production_jpip_packet_range_requires_all_bytes(available: nat, required: nat)
    requires
        complete_jpip_range(available, required),
    ensures
        available == required,
{
    reveal(complete_jpip_range);
}

pub proof fn production_jpip_progressive_quality_is_monotonic(
    previous_layers: nat,
    available_layers: nat,
    planned_layers: nat,
)
    requires
        valid_jpip_progressive_update(previous_layers, available_layers, planned_layers),
    ensures
        previous_layers <= available_layers,
        available_layers <= planned_layers,
{
    reveal(valid_jpip_progressive_update);
}

pub proof fn production_jpip_transcode_is_parent_bounded(
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

pub proof fn production_jpip_precinct_identifier_matches_formula(
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

pub proof fn production_jpip_progressive_decode_uses_available_prefix(
    available: nat,
    requested: nat,
)
    requires
        jpip_quality_prefix_available(available, requested),
    ensures
        requested <= available,
{
    reveal(jpip_quality_prefix_available);
}

pub proof fn production_jpip_metadata_box_length_is_header_plus_payload(
    header: nat,
    payload: nat,
)
    ensures
        jpip_reconstructed_box_length(header, payload) == header + payload,
{
    reveal(jpip_reconstructed_box_length);
}

pub proof fn production_jpip_functional_transition_requires_packet_boundary(
    later_functional: bool,
    preceding_packet_count_known: bool,
    preceding_exact_consumption_known: bool,
)
    requires
        jpip_tile_transition_sufficient(
            later_functional,
            preceding_packet_count_known,
            preceding_exact_consumption_known,
        ),
        later_functional,
    ensures
        preceding_packet_count_known || preceding_exact_consumption_known,
{
    reveal(jpip_tile_transition_sufficient);
}

pub proof fn checked_palette_position_is_within_table(
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

pub proof fn ordinal_codestream_header_association_is_in_range(
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

pub proof fn production_jph_branding_is_canonical()
    ensures
        valid_jph_branding(true, 0, 1, true),
{
}

pub proof fn production_part15_signals_are_consistent(has_corresponding_profile: bool)
    ensures
        consistent_part15_signaling(true, true, true, has_corresponding_profile),
{
}

pub proof fn production_ht_style_prefixes_exclude_reserved_value()
    ensures
        valid_ht_style_prefix(0),
        valid_ht_style_prefix(1),
        !valid_ht_style_prefix(2),
        valid_ht_style_prefix(3),
{
}

pub proof fn ht_cleanup_partition_is_parent_bounded(cleanup_length: nat, scup: nat)
    requires
        valid_ht_cleanup_partition(cleanup_length, scup),
    ensures
        cleanup_length - scup <= cleanup_length,
        (cleanup_length - scup) + scup == cleanup_length,
{
    reveal(valid_ht_cleanup_partition);
}

pub proof fn production_ht_cleanup_fusion_is_single_byte(
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
    crate::proofs::spec_properties::ht_cleanup_shared_byte_is_unique(
        mel_byte, vlc_byte, terminal_byte, value, shared_a, shared_b,
    );
}

pub proof fn production_ht_quad_metadata_has_bounded_origin(
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
{
    reveal(valid_ht_quad_origin);
}

pub proof fn production_ht_kappa_completion_is_monotonic(
    u_base: nat,
    gamma: bool,
    exponent: nat,
)
    ensures
        ht_completed_u(u_base, gamma, exponent) == u_base
            + ht_kappa_extension(gamma, exponent),
        ht_completed_u(u_base, gamma, exponent) >= u_base,
{
    reveal(ht_completed_u);
    reveal(ht_kappa_extension);
}

pub proof fn production_ht_pass_group_has_placeholders_and_bounded_substantive_set(
    packet_passes: nat,
)
    requires
        valid_ht_pass_group(packet_passes),
    ensures
        packet_passes >= 1,
        ht_placeholder_passes(packet_passes) % 3 == 0,
        ht_substantive_passes(packet_passes) >= 1,
        ht_substantive_passes(packet_passes) <= 3,
{
    reveal(valid_ht_pass_group);
    reveal(ht_placeholder_passes);
    reveal(ht_substantive_passes);
}

pub proof fn production_ht_refinement_segment_is_bounded(bytes: nat, passes: nat)
    requires
        valid_ht_refinement_segment(bytes, passes),
    ensures
        bytes <= 2046,
        passes == 1 || passes == 2,
{
    reveal(valid_ht_refinement_segment);
}

pub proof fn production_quantization_error_persists(
    coefficients: Seq<crate::specs::Part1QuantizedCoefficient>, shift: u8,
    step: i64, reversible: bool, completed: nat, total: nat, error: crate::DecodeError,
)
    requires
        completed <= total <= coefficients.len(),
        crate::specs::part1_quantized_prefix(coefficients, shift, step, reversible, completed) == Err(error),
    ensures
        crate::specs::part1_quantized_prefix(coefficients, shift, step, reversible, total) == Err(error),
    decreases total - completed,
{
    if completed < total {
        production_quantization_error_persists(
            coefficients, shift, step, reversible, completed, (total - 1) as nat, error,
        );
    }
}

pub proof fn production_lifting_sample_frame(
    original: Seq<i64>, current: Seq<i64>, index: nat, target_even: bool, kind: u8, factor: i64,
)
    requires
        original.len() == current.len(),
        index < original.len(),
        forall |i: int| 0 <= i < current.len() && (i >= index || (i % 2 == 0) != target_even) ==>
            current[i] == original[i],
    ensures
        crate::specs::part1_lifting_sample(original, index, target_even, kind, factor)
            == crate::specs::part1_lifting_sample(current, index, target_even, kind, factor),
{
    if (index % 2 == 0) == target_even && original.len() > 1 {
        let left = if index == 0 { 1int } else { index - 1 };
        let right = if index + 1 < original.len() { index as int + 1 } else { index - 1 };
        assert((left % 2 == 0) != target_even);
        assert((right % 2 == 0) != target_even);
        assert(current[left] == original[left]);
        assert(current[right] == original[right]);
    }
}

pub proof fn production_index_parity(index: usize)
    ensures (index & 1 == 0) == (index % 2 == 0),
{
    assert((index & 1) == index % 2) by(bit_vector);
}

pub proof fn production_scaling_error_persists(
    samples: Seq<i64>, target_even: bool, factor: i64, completed: nat, total: nat,
)
    requires
        completed <= total <= samples.len(),
        crate::specs::part1_scaling_prefix(samples, target_even, factor, completed).0.is_err(),
    ensures
        crate::specs::part1_scaling_prefix(samples, target_even, factor, total)
            == crate::specs::part1_scaling_prefix(samples, target_even, factor, completed),
    decreases total - completed,
{
    if completed < total {
        production_scaling_error_persists(samples, target_even, factor, completed, (total - 1) as nat);
    }
}

pub proof fn production_horizontal_error_persists(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    low_first: bool, irreversible: bool, completed: nat, total: nat, error: crate::DecodeError,
)
    requires
        completed <= total,
        crate::specs::part1_horizontal_prefix(low, high, low_first, irreversible, completed) == Err(error),
    ensures
        crate::specs::part1_horizontal_prefix(low, high, low_first, irreversible, total) == Err(error),
    decreases total - completed,
{
    if completed < total {
        production_horizontal_error_persists(low, high, low_first, irreversible, completed, (total - 1) as nat, error);
    }
}

pub proof fn production_column_error_persists(
    samples: Seq<i64>, width: u32, x: u32, completed: nat, total: nat, error: crate::DecodeError,
)
    requires
        completed <= total,
        crate::specs::part1_column_prefix(samples, width, x, completed) == Err(error),
    ensures
        crate::specs::part1_column_prefix(samples, width, x, total) == Err(error),
    decreases total - completed,
{
    if completed < total {
        production_column_error_persists(samples, width, x, completed, (total - 1) as nat, error);
    }
}

pub proof fn production_vertical_error_persists(
    low: crate::specs::Part1WaveletBand, high: crate::specs::Part1WaveletBand,
    height: u32, low_first: bool, irreversible: bool, length: usize,
    completed: nat, total: nat, error: crate::DecodeError,
)
    requires
        completed <= total,
        crate::specs::part1_vertical_prefix(low, high, height, low_first, irreversible, length, completed) == Err(error),
    ensures
        crate::specs::part1_vertical_prefix(low, high, height, low_first, irreversible, length, total) == Err(error),
    decreases total - completed,
{
    if completed < total {
        production_vertical_error_persists(
            low, high, height, low_first, irreversible, length, completed, (total - 1) as nat, error,
        );
    }
}

pub proof fn production_quantized_row_error_persists(
    band: crate::specs::Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, y: u32, completed: nat, total: nat,
)
    requires
        completed <= total,
        crate::specs::part1_quantized_block_row(band, source, block_width, placement_x, placement_y, y, completed).0.is_err(),
    ensures
        crate::specs::part1_quantized_block_row(band, source, block_width, placement_x, placement_y, y, total)
            == crate::specs::part1_quantized_block_row(band, source, block_width, placement_x, placement_y, y, completed),
    decreases total - completed,
{
    if completed < total {
        production_quantized_row_error_persists(band, source, block_width, placement_x, placement_y, y, completed, (total - 1) as nat);
    }
}

pub proof fn production_quantized_block_error_persists(
    band: crate::specs::Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, completed: nat, total: nat,
)
    requires
        completed <= total,
        crate::specs::part1_quantized_block_rows(band, source, block_width, placement_x, placement_y, completed).0.is_err(),
    ensures
        crate::specs::part1_quantized_block_rows(band, source, block_width, placement_x, placement_y, total)
            == crate::specs::part1_quantized_block_rows(band, source, block_width, placement_x, placement_y, completed),
    decreases total - completed,
{
    if completed < total {
        production_quantized_block_error_persists(band, source, block_width, placement_x, placement_y, completed, (total - 1) as nat);
    }
}

pub proof fn production_component_transform_error_persists(
    image: crate::specs::Part1DecodedImageModel, irreversible: bool, completed: nat, total: nat,
)
    requires
        completed <= total,
        crate::specs::part1_component_transform_prefix(image, irreversible, completed).0.is_err(),
    ensures
        crate::specs::part1_component_transform_prefix(image, irreversible, total)
            == crate::specs::part1_component_transform_prefix(image, irreversible, completed),
    decreases total - completed,
{
    if completed < total {
        production_component_transform_error_persists(image, irreversible, completed, (total - 1) as nat);
    }
}

pub proof fn production_conversion_error_persists(
    samples: Seq<i64>, fraction_bits: u8, shift: i64, minimum: i64, maximum: i64,
    completed: nat, total: nat, error: crate::DecodeError,
)
    requires
        completed <= total <= samples.len(),
        crate::specs::part1_conversion_prefix(samples, fraction_bits, shift, minimum, maximum, completed) == Err(error),
    ensures
        crate::specs::part1_conversion_prefix(samples, fraction_bits, shift, minimum, maximum, total) == Err(error),
    decreases total - completed,
{
    if completed < total {
        production_conversion_error_persists(
            samples, fraction_bits, shift, minimum, maximum, completed, (total - 1) as nat, error,
        );
    }
}

pub proof fn production_store_column_error_persists(
    output: Seq<i64>, width: u32, x: u32, column: Seq<i64>, completed: nat, total: nat,
)
    requires
        completed <= total,
        crate::specs::part1_store_column_prefix(output, width, x, column, completed).0.is_err(),
    ensures
        crate::specs::part1_store_column_prefix(output, width, x, column, total)
            == crate::specs::part1_store_column_prefix(output, width, x, column, completed),
    decreases total - completed,
{
    if completed < total {
        production_store_column_error_persists(output, width, x, column, completed, (total - 1) as nat);
    }
}

pub proof fn production_nine_seven_error_persists(
    samples: Seq<i64>, low_first: bool, completed: nat, total: nat,
)
    requires
        completed <= total,
        crate::specs::part1_nine_seven_lifting_prefix(samples, low_first, completed).0.is_err(),
    ensures
        crate::specs::part1_nine_seven_lifting_prefix(samples, low_first, total)
            == crate::specs::part1_nine_seven_lifting_prefix(samples, low_first, completed),
    decreases total - completed,
{
    if completed < total {
        production_nine_seven_error_persists(samples, low_first, completed, (total - 1) as nat);
    }
}

pub proof fn production_lifting_error_persists(
    samples: Seq<i64>, target_even: bool, kind: u8, factor: i64, completed: nat, total: nat,
)
    requires
        completed <= total <= samples.len(),
        crate::specs::part1_lifting_prefix(samples, target_even, kind, factor, completed).0.is_err(),
    ensures
        crate::specs::part1_lifting_prefix(samples, target_even, kind, factor, total)
            == crate::specs::part1_lifting_prefix(samples, target_even, kind, factor, completed),
    decreases total - completed,
{
    if completed < total {
        production_lifting_error_persists(samples, target_even, kind, factor, completed, (total - 1) as nat);
    }
}

pub proof fn production_magnitude_bit_selects_bounded_limb(bit: nat)
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

pub proof fn production_magnitude_shift_is_capacity_bounded(highest_bit: nat, shift: nat)
    requires
        magnitude_shift_fits(highest_bit, shift),
    ensures
        highest_bit + shift < 384,
{
    reveal(magnitude_shift_fits);
}

pub proof fn production_magnitude_comparison_is_transitive(
    left: nat,
    middle: nat,
    right: nat,
)
    requires
        magnitude_less(left, middle),
        magnitude_less(middle, right),
    ensures
        magnitude_less(left, right),
{
    reveal(magnitude_less);
}

pub proof fn production_magnitude_addition_is_monotonic(left: nat, right: nat)
    ensures
        magnitude_addition(left, right) >= left,
        magnitude_addition(left, right) >= right,
{
    reveal(magnitude_addition);
}

pub proof fn production_maxshift_undo_is_nonexpanding(magnitude: nat, threshold: nat)
    requires
        threshold > 0,
    ensures
        maxshift_restored_magnitude(magnitude, threshold) <= magnitude,
{
    reveal(maxshift_restored_magnitude);
}

pub proof fn production_mixed_block_selection_is_deterministic(
    lblock: nat,
    first_length_bit_is_zero: bool,
)
    ensures
        mixed_block_selects_ht(lblock, first_length_bit_is_zero)
            == (lblock > 3 && first_length_bit_is_zero),
{
    reveal(mixed_block_selects_ht);
}

pub proof fn clamped_color_sample_is_u16_bounded(value: int)
    ensures
        0 <= clamp_color_sample(value),
        clamp_color_sample(value) <= 65535,
{
}

pub proof fn production_signed_color_is_shifted_to_nominal(value: int, level: nat)
    requires
        valid_signed_color_sample(value, level),
    ensures
        0 <= signed_color_to_nominal(value, level),
        signed_color_to_nominal(value, level) < 2 * level,
{
    reveal(valid_signed_color_sample);
    reveal(signed_color_to_nominal);
}

pub proof fn production_color_resampling_is_component_bounded(
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

pub proof fn converted_color_storage_is_two_bytes_per_sample(pixels: nat, channels: nat)
    ensures
        color_output_bytes(pixels, channels) == pixels * channels * 2,
{
}

pub proof fn production_layer_reference_is_checked(index: nat, codestreams: nat)
    requires
        valid_layer_codestream_reference(index, codestreams),
    ensures
        index < codestreams,
{
}

pub proof fn production_implicit_layers_follow_codestream_count(codestreams: nat)
    ensures
        effective_jpx_layer_count(0, codestreams) == codestreams,
{
}

pub proof fn production_rejects_contradictory_jp2_primary_brand()
    ensures
        !valid_jp2_primary_brand(true, true),
{
}

pub proof fn production_jpip_layout_has_complete_pairs(tile_pairs: nat)
    ensures
        valid_jpip_codestream_layout(3 + tile_pairs * 2),
{
}

pub proof fn production_tile_transform_does_not_cross_slice(
    start: nat,
    components: nat,
    total: nat,
)
    requires
        tile_transform_scope(start, components, total),
    ensures
        start + components <= total,
{
}

pub proof fn production_layer_crop_is_canvas_bounded(
    offset: nat,
    extent: nat,
    canvas: nat,
)
    ensures
        clipped_composition_extent(offset, extent, canvas) <= extent,
        offset < canvas ==> clipped_composition_extent(offset, extent, canvas) <= canvas - offset,
{
}

pub proof fn production_composition_storage_accounting(pixels: nat, colors: nat)
    ensures
        composition_output_bytes(pixels, colors) == pixels * (colors + 1) * 2,
{
}

pub proof fn production_u32_product_bounds(left: u32, right: u32)
    ensures
        (left as int) * (right as int) <= 18446744065119617025,
{
    vstd::arithmetic::mul::lemma_mul_upper_bound(left as int, 4294967295, right as int, 4294967295);
}

pub proof fn production_composition_mapped_bounds(position: u32, source_extent: u32, target_extent: u32)
    requires
        target_extent > 0,
    ensures
        position < target_extent && source_extent > 0 ==>
            crate::specs::part2_composition_mapped_offset(position, source_extent, target_extent) < source_extent,
{
    if position < target_extent && source_extent > 0 {
        let p = position as int;
        let s = source_extent as int;
        let t = target_extent as int;
        let n = p * s;
        vstd::arithmetic::mul::lemma_mul_strict_inequality(p, t, s);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, t);
        vstd::arithmetic::div_mod::lemma_mod_bound(n, t);
        vstd::arithmetic::mul::lemma_mul_is_commutative(n / t, t);
        vstd::arithmetic::mul::lemma_mul_is_commutative(t, s);
        vstd::arithmetic::mul::lemma_mul_strict_inequality_converse(n / t, s, t);
    }
}

pub proof fn production_composition_index_bounds(width: u32, height: u32, x: u32, y: u32)
    requires
        x < width,
        y < height,
    ensures
        crate::specs::part2_row_major_index(width, x, y) < (width as nat) * (height as nat),
{
    assert((y as int) * (width as int) + (x as int) < (width as int) * (height as int))
        by (nonlinear_arith)
        requires 0 <= x < width, 0 <= y < height,
    {}
}

pub proof fn production_source_over_term_bounds(left: u64, right: u64, other: u64)
    requires
        left <= 65535,
        right <= 65535,
        other <= 65535,
    ensures
        (left as int) * (right as int) <= 4294836225,
        (left as int) * (right as int) * (other as int) <= 281462092005375,
{
    vstd::arithmetic::mul::lemma_mul_upper_bound(left as int, 65535, right as int, 65535);
    vstd::arithmetic::mul::lemma_mul_upper_bound(
        (left as int) * (right as int), 4294836225, other as int, 65535,
    );
}

pub proof fn production_frame_materialization_bound(frames: nat, layers: nat)
    ensures
        composition_instruction_work(frames, layers)
            == frames * if layers == 0 { 1 } else { layers },
{
}

pub proof fn production_registered_channel_accounting(prior: nat, added: nat)
    ensures
        registered_channel_count(prior, added) == prior + added,
{
}

pub proof fn production_nested_metadata_accounting(boxes: nat, depth: nat)
    ensures
        nested_metadata_work(boxes, depth) == boxes + depth,
{
}

pub proof fn production_loop_frame_is_bounded(index: nat, frames: nat)
    requires
        frames > 0,
    ensures
        bounded_loop_frame(index, frames) < frames,
{
}

pub proof fn production_mct_matrix_is_square(
    components: nat,
    matrix_elements: nat,
    offset_elements: nat,
)
    requires
        valid_mct_dimensions(components, matrix_elements, offset_elements),
    ensures
        matrix_elements == components * components,
        offset_elements == 0 || offset_elements == components,
{
}

pub proof fn production_mct_work_counts_products_and_outputs(pixels: nat, components: nat)
    ensures
        mct_work_units(pixels, components) == pixels * components * (components + 1),
{
}

pub proof fn production_mct_stage_order_is_dag(parent: nat, child: nat, stages: nat)
    requires
        valid_mct_stage_edge(parent, child, stages),
    ensures
        parent < child,
        child < stages,
{
}

pub proof fn production_mct_matrix_is_component_bounded(
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

pub proof fn production_mct_fragment_index_is_contiguous(
    index: nat,
    expected: nat,
    final_index: nat,
)
    requires
        valid_mct_fragment_index(index, expected, final_index),
    ensures
        index == expected,
        index <= final_index,
{
    reveal(valid_mct_fragment_index);
}

pub proof fn production_mct_fragment_completeness_reaches_final(final_index: nat)
    ensures
        complete_mct_fragment_series(final_index + 1, final_index),
{
    reveal(complete_mct_fragment_series);
}

pub proof fn production_reversible_dependency_coefficients_are_triangular(components: nat)
    requires
        components > 0,
    ensures
        mct_dependency_coefficients(components, true)
            == ((components * (components + 1) / 2 - 1) as nat),
{
    reveal(mct_dependency_coefficients);
}

pub proof fn production_irreversible_dependency_coefficients_are_strictly_triangular(
    components: nat,
)
    requires
        components > 0,
    ensures
        mct_dependency_coefficients(components, false)
            == ((components * (components - 1) / 2) as nat),
{
    reveal(mct_dependency_coefficients);
}

pub proof fn production_mct_wavelet_partition_preserves_component_count(
    low_components: nat,
    high_components: nat,
    output_components: nat,
)
    requires
        valid_mct_wavelet_partition(low_components, high_components, output_components),
    ensures
        low_components + high_components == output_components,
{
    reveal(valid_mct_wavelet_partition);
}

pub proof fn production_mct_wavelet_work_is_explicit(
    pixels: nat,
    components: nat,
    levels: nat,
)
    ensures
        mct_wavelet_work_units(pixels, components, levels)
            == pixels * components * (levels + 1) * 8,
{
    reveal(mct_wavelet_work_units);
}

}
#[cfg(verus_keep_ghost)]
verus! {
    pub proof fn production_ht_plane_samples_error(
        state: crate::specs::HtPlaneState, quad: crate::tier1::HtQuadMetadata, width: u16, height: u16,
        column: nat, completed_u: u8, bitplanes: u16, prefix: nat, count: nat,
    )
        requires prefix <= count <= 4, column + 1 < state.current.len(),
            crate::specs::ht_plane_samples(state, quad, width, height, column, completed_u, bitplanes, prefix).0.is_err(),
        ensures crate::specs::ht_plane_samples(state, quad, width, height, column, completed_u, bitplanes, count)
            == crate::specs::ht_plane_samples(state, quad, width, height, column, completed_u, bitplanes, prefix),
        decreases count - prefix,
    {
        if prefix < count {
            production_ht_plane_samples_error(state, quad, width, height, column, completed_u, bitplanes, prefix, (count - 1) as nat);
            reveal(crate::specs::ht_plane_samples);
        }
    }

    pub proof fn production_ht_plane_quads_error(
        state: crate::specs::HtPlaneState, quads: Seq<crate::tier1::HtQuadMetadata>, width: u16, height: u16,
        maximum_u: u8, bitplanes: u16, quads_per_row: nat, prefix: nat, count: nat,
    )
        requires prefix <= count <= quads.len(), 0 < quads_per_row <= 32768,
            state.current.len() == quads_per_row + 1, state.previous.len() == quads_per_row + 1,
            crate::specs::ht_plane_quads(state, quads, width, height, maximum_u, bitplanes, quads_per_row, prefix).0.is_err(),
        ensures crate::specs::ht_plane_quads(state, quads, width, height, maximum_u, bitplanes, quads_per_row, count)
            == crate::specs::ht_plane_quads(state, quads, width, height, maximum_u, bitplanes, quads_per_row, prefix),
        decreases count - prefix,
    {
        if prefix < count {
            production_ht_plane_quads_error(state, quads, width, height, maximum_u, bitplanes, quads_per_row, prefix, (count - 1) as nat);
            reveal(crate::specs::ht_plane_quads);
        }
    }
}
