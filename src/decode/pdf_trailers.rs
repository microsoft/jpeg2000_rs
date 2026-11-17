use super::execution::{
    account_planned_tile, collect_tile_parts, prepare_tile_decode_metadata,
    reconstruct_planned_tile, validate_part2_execution,
};
use super::planning::plan_progression_tile_at_selected;
use super::selection::validate_selection;
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn trailer_components_outcome(
        result: Result<(DecodedTileComponents, u8), DecodeError>,
    ) -> Result<(crate::specs::Part2DecodedTileComponents, u8), DecodeError> {
        match result { Err(error) => Err(error), Ok((value, discarded)) =>
            Ok((decoded_tile_components_view(&value), discarded)) }
    }

    pub(crate) open spec fn trailer_tile_outcome(
        result: Result<(DecodedLayoutTile, u8), DecodeError>,
    ) -> Result<(crate::specs::Part2DecodedLayoutTile, u8), DecodeError> {
        match result { Err(error) => Err(error), Ok((value, discarded)) =>
            Ok((decoded_layout_tile_view(&value), discarded)) }
    }

    pub(crate) open spec fn trailer_layout_outcome(
        result: Result<(DecodedImage, TileTrailerRecoveryReport), DecodeError>,
    ) -> Result<crate::specs::Part2TrailerReconstructed, DecodeError> {
        match result { Err(error) => Err(error), Ok((image, report)) =>
            Ok((crate::image::decoded_image_view(image), report)) }
    }

    pub open spec fn trailer_typed_outcome(
        result: Result<TileTrailerRecoveredImage, DecodeError>,
    ) -> Result<crate::specs::Part2TrailerTyped, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) =>
            Ok((crate::image::typed_image_value_view(value.image), value.report)) }
    }

    pub open spec fn trailer_reconstructed_outcome(
        result: Result<TileTrailerRecoveredReconstructedImage, DecodeError>,
    ) -> Result<crate::specs::Part2TrailerReconstructed, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) =>
            Ok((crate::image::decoded_image_view(value.image), value.report)) }
    }
}

/// Bytes discarded only after a complete scheduled packet/body decode.
///
/// The fixed sixteen-byte allowance is cumulative across selected tiles in this
/// call, not renewed per tile or part. It is not normative JPEG 2000 padding.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct TileTrailerRecoveryReport {
    pub discarded_tile_trailer_bytes: u8,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct TileTrailerRecoveredImage {
    pub image: TypedImage,
    pub report: TileTrailerRecoveryReport,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct TileTrailerRecoveredReconstructedImage {
    pub image: DecodedImage,
    pub report: TileTrailerRecoveryReport,
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_planned_result(
        progression_plan_view(&plan), codestream::tile_parts_owned_view(parts@), codestream::tile_part_owned_view(first),
        size, standard, counts@, limits, prepared_components_view(prepared@), work, discarded, trailer_components_outcome(result)),
        trailer_components_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_components_outcome(result) == crate::specs::part2_trailer_planned_value(
                progression_plan_view(&plan), codestream::tile_parts_owned_view(parts@), codestream::tile_part_owned_view(first),
                size, standard, counts@, limits, prepared_components_view(prepared@), work, discarded),
))]
fn decode_planned_trailer_tile(
    plan: ProgressionTilePlan,
    parts: &[TilePartPayload<'_>],
    first: &TilePartPayload<'_>,
    size: &ImageSize,
    standard: (bool, bool),
    counts: &[u8],
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    work: u64,
    discarded: u8,
) -> Result<(DecodedTileComponents, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = progression_plan_view(&plan);
        let ghost initial = prepared_components_view(prepared@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(progression_plan_view);
        codestream::owned_extensions_registry_known(&first.part2_extensions);
        crate::specs::part2_trailer_planned_normal(before, codestream::tile_parts_owned_view(parts@),
            codestream::tile_part_owned_view(first), size, standard, counts@, limits, initial, work, discarded);
    }
    let mut active = plan;
    let packets = {
        let precincts = active.precincts.as_mut_slice();
        #[cfg(verus_keep_ghost)]
        proof! { crate::packet::packet_precinct_vector_known_fields(precincts); }
        let result = crate::packet::decode_progression_tile_packets_recover_trailer_selected(
            parts,
            &active.grid,
            precincts,
            Some(counts),
            limits,
            discarded,
        );
        #[cfg(verus_keep_ghost)]
        proof! { crate::packet::packet_precinct_vector_known_fields(precincts); }
        result
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost after = planning_precincts_view(active.precincts@); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_trailer_packet_result(
            codestream::tile_parts_owned_view(parts@), before.grid, before.precincts,
            Some(counts@), limits, discarded, (packets, after)));
        if let Err(error) = packets {
            crate::specs::part2_trailer_planned_packet_error(before, codestream::tile_parts_owned_view(parts@),
                codestream::tile_part_owned_view(first), size, standard, counts@, limits, initial, work, discarded, error, after);
        }
    }
    let (_decoded_packets, total) = packets?;
    #[cfg(verus_keep_ghost)]
    proof! {
        planning_precinct_planes_known_fields(active.precincts@);
        reveal(planned_components_view);
        assert(planned_components_view(&active) =~= before.components);
        assert(prepare_precincts_view(active.precincts@) == crate::specs::part2_precinct_decoder_planes(after));
    }
    let mut components = prepared;
    let mut actual_work = work;
    let reconstructed = reconstruct_planned_tile(
        &active,
        first,
        size,
        standard,
        limits,
        &mut components,
        &mut actual_work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_trailer_planned_extract_actual(before, codestream::tile_parts_owned_view(parts@),
            codestream::tile_part_owned_view(first), size, standard, counts@, limits, initial, work, discarded,
            _decoded_packets, after, total, (reconstructed, prepared_components_view(components@), actual_work));
        reveal(decoded_tile_components_view);
    }
    reconstructed?;
    Ok((
        DecodedTileComponents {
            prepared: components,
            mct_work: actual_work,
        },
        total,
    ))
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_tile_result(size, tile, codestream::tile_parts_owned_view(parts@),
        codestream::codestream_profile_capabilities(profile), discard, limits,
        prepared_components_view(prepared@), initial, work, discarded, trailer_tile_outcome(result)),
        trailer_tile_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_tile_outcome(result) == crate::specs::part2_trailer_tile_value(
                size, tile, codestream::tile_parts_owned_view(parts@), codestream::codestream_profile_capabilities(profile),
                discard, limits, prepared_components_view(prepared@), initial, work, discarded),
))]
fn decode_trailer_tile(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: u8,
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    work: u64,
    discarded: u8,
) -> Result<(DecodedLayoutTile, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost prior = prepared_components_view(prepared@);
        let ghost source = codestream::tile_parts_owned_view(parts@);
        let ghost caps = codestream::codestream_profile_capabilities(profile);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(size);
        reveal(codestream::tile_part_owned_view);
        crate::specs::part2_trailer_tile_normal(size, tile, source, caps, discard, limits, prior, initial, work, discarded);
    }
    let metadata_result = prepare_tile_decode_metadata(parts, size.components, Some(discard));
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = metadata_result {
            crate::specs::part2_trailer_tile_metadata_actual(
                size, tile, source, caps, discard, limits, prior, initial, work, discarded, Err(error), Err(error));
        }
    }
    let metadata = metadata_result?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost metadata_value = tile_decode_metadata_view(&metadata); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(tile_decode_metadata_view); }
    let first = metadata.first;
    let plan_result = plan_progression_tile_at_selected(
        size,
        tile,
        first.coding_style,
        &first.component_coding_styles,
        &first.component_quantizations,
        &first.roi_shifts,
        discard,
        profile.part15_allows_multiple_ht_sets(),
        profile.part15_magnitude_bound(),
        profile.part15_requires_all_ht_blocks(),
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = plan_result {
            crate::specs::part2_trailer_tile_plan_actual(
                size, tile, source, caps, discard, limits, prior, initial, work, discarded, metadata_value, Err(error), Err(error));
            crate::specs::part2_trailer_tile_metadata_actual(
                size, tile, source, caps, discard, limits, prior, initial, work, discarded, Ok(metadata_value), Err(error));
        }
    }
    let plan = plan_result?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost plan_value = progression_plan_view(&plan); }
    let counters_result =
        account_planned_tile(&plan, Some(&metadata.resolution_counts), initial, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = counters_result {
            crate::specs::part2_trailer_tile_account_error(
                size, source, metadata_value, limits, prior, initial, work, discarded, plan_value, error);
            crate::specs::part2_trailer_tile_plan_actual(
                size, tile, source, caps, discard, limits, prior, initial, work, discarded, metadata_value, Ok(plan_value), Err(error));
            crate::specs::part2_trailer_tile_metadata_actual(
                size, tile, source, caps, discard, limits, prior, initial, work, discarded, Ok(metadata_value), Err(error));
        }
    }
    let counters = counters_result?;
    let decoded_result = decode_planned_trailer_tile(
        plan,
        parts,
        first,
        size,
        metadata.standard,
        &metadata.resolution_counts,
        limits,
        prepared,
        work,
        discarded,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let outcome = trailer_components_outcome(decoded_result);
        let output = crate::specs::part2_trailer_tile_output(counters, outcome);
        crate::specs::part2_trailer_tile_planned_actual(
            size, source, metadata_value, limits, prior, initial, work, discarded, plan_value, counters, outcome);
        crate::specs::part2_trailer_tile_plan_actual(
            size, tile, source, caps, discard, limits, prior, initial, work, discarded, metadata_value, Ok(plan_value), output);
        crate::specs::part2_trailer_tile_metadata_actual(
            size, tile, source, caps, discard, limits, prior, initial, work, discarded, Ok(metadata_value), output);
        reveal(decoded_layout_tile_view);
    }
    let (decoded, total) = decoded_result?;
    Ok((
        DecodedLayoutTile {
            prepared: decoded.prepared,
            counters,
            mct_work: decoded.mct_work,
        },
        total,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_layout_result(
        codestream::decoder_layout_input_view(layout), crate::options::decode_selection_view(requested),
        limits, trailer_layout_outcome(result)),
        trailer_layout_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_layout_outcome(result) == crate::specs::part2_trailer_layout_value(
                codestream::decoder_layout_input_view(layout), crate::options::decode_selection_view(requested), limits),
))]
pub(super) fn decode_trailer_layout(
    layout: &CodestreamLayout<'_>,
    requested: &DecodeSelection,
    limits: &ResourceLimits,
) -> Result<(DecodedImage, TileTrailerRecoveryReport), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source = codestream::decoder_layout_input_view(layout);
        let ghost requested_input = crate::options::decode_selection_view(requested);
        let ghost goal = crate::specs::part2_trailer_layout_value(source, requested_input, limits);
        let ghost mut prefix: Seq<crate::specs::Part2JpipSnapshotEvent> = Seq::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        super::decoder_execution_inputs_known(layout);
        crate::specs::part2_trailer_layout_normal(source, requested_input, limits);
    }
    validate_part2_execution(layout)?;
    let selected = validate_selection(&layout.info.image_size, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        let root = |events| crate::specs::part2_trailer_layout_run(source, requested_input, limits, events);
        let child = |events| crate::specs::part2_validate_selection_run(
            codestream::selection_geometry_view(&layout.info.image_size), requested_input, events);
        let next = |selection: crate::specs::Part2ValidatedSelection, rest|
            crate::specs::part2_trailer_after_selection_run(source, selection, limits, rest);
        match selected {
            Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
            Ok(selection) => {
                prefix = crate::specs::part2_decode_prefix_advance(root, child, next, prefix,
                    validated_selection_view(selection));
            },
        }
    }
    let selection = selected?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(validated_selection_view); reveal(validated_selection_outcome);
        assert(selection.region@.len() == 4);
        assert([selection.region@[0], selection.region@[1], selection.region@[2], selection.region@[3]] == selection.region);
    }
    let mut prepared = Vec::new();
    let mut counters = (0_u64, 0_u64, 0_u64);
    let mut work = 0_u64;
    let mut discarded = 0_u8;
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(prepared_components_view(prepared@) =~= Seq::empty());
        reveal(layout_accumulation_view);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= selection.tiles.len(),
            source == codestream::decoder_layout_input_view(layout),
            requested_input == crate::options::decode_selection_view(requested),
            crate::specs::part2_trailer_layout_result(source, requested_input, limits, goal),
            goal == crate::specs::part2_trailer_layout_value(source, requested_input, limits),
            forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_trailer_layout_run(source, requested_input, limits, prefix + tail)
                    == crate::specs::part2_trailer_selected_run(&source.size, source.parts, source.capabilities,
                        selection.tiles@, selection.region, selection.discard_levels, limits, index as nat,
                        layout_accumulation_view(prepared@, counters, work), discarded, tail),
            goal == crate::specs::part2_trailer_selected_value(&layout.info.image_size,
                codestream::tile_parts_owned_view(layout.tile_parts@), codestream::codestream_profile_capabilities(&layout.info.profile),
                selection.tiles@, selection.region, selection.discard_levels, limits, index as nat,
                layout_accumulation_view(prepared@, counters, work), discarded),
        decreases selection.tiles.len() - index,
    ))]
    while index < selection.tiles.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            codestream::decoder_layout_input_fields(layout);
            reveal(layout_accumulation_view);
            reveal_with_fuel(crate::specs::part2_trailer_selected_value, 1);
        }
        let tile = *selection.tiles.get(index).ok_or_else(invalid_decode)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = layout_accumulation_view(prepared@, counters, work);
            let ghost root = |events| crate::specs::part2_trailer_layout_run(source, requested_input, limits, events);
            let ghost next_tile = |after: (crate::specs::Part2DecodedLayoutTile, u8), rest|
                crate::specs::part2_trailer_selected_run(&source.size, source.parts, source.capabilities, selection.tiles@,
                    selection.region, selection.discard_levels, limits, index as nat + 1, after.0, after.1, rest);
            let ghost after_parts = |selected: Seq<crate::specs::Part2OwnedTilePart>, rest|
                crate::specs::part2_jpip_snapshot_bind(
                    crate::specs::part2_trailer_tile_run(&source.size, tile, selected, source.capabilities,
                        selection.discard_levels, limits, before.prepared, before.counters, before.mct_work, discarded, rest),
                    next_tile);
        }
        let collected = collect_tile_parts(&layout.tile_parts, tile);
        #[cfg(verus_keep_ghost)]
        proof! {
            let child = |events| crate::specs::part2_collected_parts_run(source.parts, tile, events);
            crate::specs::part2_trailer_selected_step(&source.size, source.parts, source.capabilities, selection.tiles@,
                selection.region, selection.discard_levels, limits, index as nat, before, discarded);
            assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                root(prefix + tail) == crate::specs::part2_jpip_snapshot_bind(child(tail), after_parts) by {
                assert(root(prefix + tail) == crate::specs::part2_trailer_selected_run(&source.size, source.parts,
                    source.capabilities, selection.tiles@, selection.region, selection.discard_levels, limits, index as nat, before, discarded, tail));
            }
            match collected_tile_parts_outcome(collected) {
                Err(error) => crate::specs::part2_decode_prefix_error(root, child, after_parts, prefix, error),
                Ok(selected) => { prefix = crate::specs::part2_decode_prefix_advance(root, child, after_parts, prefix, selected); },
            }
        }
        let parts = collected?;
        let decoded_result = decode_trailer_tile(
            &layout.info.image_size,
            tile,
            &parts,
            &layout.info.profile,
            selection.discard_levels,
            limits,
            prepared,
            counters,
            work,
            discarded,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            let child = |events| crate::specs::part2_trailer_tile_run(&source.size, tile, codestream::tile_parts_owned_view(parts@),
                source.capabilities, selection.discard_levels, limits, before.prepared, before.counters, before.mct_work, discarded, events);
            let next = next_tile;
            assert forall|tail| root(prefix + tail) == crate::specs::part2_jpip_snapshot_bind(child(tail), next) by {
                assert(root(prefix + tail) == after_parts(codestream::tile_parts_owned_view(parts@), tail));
            }
            match trailer_tile_outcome(decoded_result) {
                Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
                Ok(after) => { prefix = crate::specs::part2_decode_prefix_advance(root, child, next, prefix, after); },
            }
        }
        let (decoded, total) = decoded_result?;
        prepared = decoded.prepared;
        counters = decoded.counters;
        work = decoded.mct_work;
        discarded = total;
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_trailer_selected_value, 1);
        reveal_with_fuel(crate::specs::part2_trailer_selected_run, 1);
        reveal(layout_accumulation_view);
    }
    let assembled = assemble_prepared_components(
        &layout.info.image_size,
        &prepared,
        Some((selection.region, selection.discard_levels)),
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let size=crate::image::assembly_size_view(&layout.info.image_size);
        let values=prepared_components_view(prepared@);
        let maximum=crate::limits::resource_decoded_bytes_limit(limits);
        let outcome=crate::image::decoded_image_outcome(assembled);
        crate::specs::part2_trailer_assembly_observed(size,values,selection.region,selection.discard_levels,maximum,discarded,outcome);
        let root=|events|crate::specs::part2_trailer_layout_run(source,requested_input,limits,events);
        let child=|events|crate::specs::part2_trailer_assembly_run(size,values,selection.region,selection.discard_levels,maximum,discarded,events);
        assert(source.size==layout.info.image_size);
        assert forall|events|root(prefix+events)==child(events) by {
            assert(crate::specs::part2_trailer_layout_run(source,requested_input,limits,prefix+events)
                ==crate::specs::part2_trailer_selected_run(&source.size,source.parts,source.capabilities,selection.tiles@,selection.region,selection.discard_levels,limits,index as nat,
                    layout_accumulation_view(prepared@,counters,work),discarded,events));
        }
        crate::specs::part2_decode_eta(child,crate::specs::part2_trailer_reported(outcome,discarded));
        crate::specs::part2_cold_prefix_result(root,child,prefix,crate::specs::part2_trailer_reported(outcome,discarded));
    }
    let image = assembled?;
    Ok((
        image,
        TileTrailerRecoveryReport {
            discarded_tile_trailer_bytes: discarded,
        },
    ))
}

/// Decode selected raw samples with the explicit terminal-trailer policy.
///
/// At most sixteen bytes are discarded cumulatively, only in final tile parts
/// after all scheduled packets and bodies complete, without packed headers or
/// packet-length tables. No packet/entropy decode is retried and no input prefix
/// is searched or trimmed. Strict APIs and other recovery policies are unchanged.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_raw_typed_result(input@,
        crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), trailer_typed_outcome(result)),
        trailer_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_typed_outcome(result) == crate::specs::part2_trailer_raw_typed_value(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options)),
))]
pub fn decode_codestream_recover_trailer_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TileTrailerRecoveredImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        reveal(crate::specs::part2_typed_layout);
        crate::specs::part2_trailer_raw_value_unfold(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
        crate::specs::part2_trailer_raw_normal(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
    }
    let parsed = codestream::parse_layout(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_trailer_raw_parse_error(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); codestream::decoder_layout_input_fields(&layout); }
    let decoded_result = decode_trailer_layout(&layout, selection, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Ok(raw) = crate::specs::part1_parse_layout(input@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_trailer_raw_layout_actual(input@, raw,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options),
                trailer_layout_outcome(decoded_result));
        }
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost recovered=trailer_layout_outcome(decoded_result);}
    let (decoded, report) = decoded_result?;
    let converted = typed_layout(
        &layout,
        decoded,
        selection.discard_levels(),
        options.limits(),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=converted {
            if let Ok(raw)=crate::specs::part1_parse_layout(input@,crate::options::decode_options_limits(options)) {
                if let Ok(value)=recovered {
                    crate::specs::part2_trailer_raw_conversion_error(input@,raw,crate::options::decode_selection_view(selection),
                        crate::options::decode_options_limits(options),value,error);
                }
            }
        }
    }
    let image = converted?;
    super::api::validate_part1_output_shape(input.len(), &layout, &image)?;
    Ok(TileTrailerRecoveredImage { image, report })
}

/// Apply the same terminal-trailer policy before output rounding or clipping.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_raw_reconstructed_result(input@,
        crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), trailer_reconstructed_outcome(result)),
        trailer_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_reconstructed_outcome(result) == crate::specs::part2_trailer_raw_reconstructed_value(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options)),
))]
pub fn decode_codestream_reconstructed_recover_trailer_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TileTrailerRecoveredReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_trailer_raw_value_unfold(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
        crate::specs::part2_trailer_raw_normal(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
    }
    let parsed = codestream::parse_layout(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_trailer_raw_parse_error(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); codestream::decoder_layout_input_fields(&layout); }
    let decoded = decode_trailer_layout(&layout, selection, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Ok(raw) = crate::specs::part1_parse_layout(input@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_trailer_raw_layout_actual(input@, raw,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options),
                trailer_layout_outcome(decoded));
        }
    }
    let (image, report) = decoded?;
    super::api::validate_reconstruction_transforms(&layout)?;
    super::api::validate_reconstructed_output_shape(input.len(), &layout, &image)?;
    Ok(TileTrailerRecoveredReconstructedImage { image, report })
}

/// Decode a selected JP2 image with the same explicit terminal-trailer policy.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_jp2_typed_result(input@,
        crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), trailer_typed_outcome(result)),
        trailer_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_typed_outcome(result) == crate::specs::part2_trailer_jp2_typed_value(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_recover_trailer_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TileTrailerRecoveredImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_trailer_jp2_value_unfold(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
        crate::specs::part2_trailer_jp2_normal(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
    }
    let inspected = match jp2::parse_and_inspect_for_display(input, options.limits()) {
        Ok(inspected) => inspected,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_trailer_jp2_inspection_error(input@,
                    crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), error);
            }
            return Err(error);
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    let profile = super::api::validate_jp2_display_profile(inspected.file());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = profile {
            crate::specs::part2_trailer_jp2_profile_error(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options),
                jp2::raw_inspected_container_view(&inspected), error);
        }
    }
    profile?;
    let stream = inspected.file().codestream(0)?;
    let decoded_result =
        decode_codestream_recover_trailer_selected(stream.data(), options, selection);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_trailer_jp2_typed_actual(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options),
            jp2::raw_inspected_container_view(&inspected), trailer_typed_outcome(decoded_result));
    }
    let decoded = decoded_result?;
    let image = apply_jp2_output(decoded.image, inspected.file().header(), options.limits())?;
    Ok(TileTrailerRecoveredImage {
        image,
        report: decoded.report,
    })
}

/// Recover a selected JP2 terminal trailer while retaining centered samples.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_trailer_jp2_reconstructed_result(input@,
        crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), trailer_reconstructed_outcome(result)),
        trailer_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            trailer_reconstructed_outcome(result) == crate::specs::part2_trailer_jp2_reconstructed_value(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_reconstructed_recover_trailer_selected(
    input: &[u8],
    options: &DecodeOptions,
    selection: &DecodeSelection,
) -> Result<TileTrailerRecoveredReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_trailer_jp2_value_unfold(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
        crate::specs::part2_trailer_jp2_normal(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options));
    }
    let inspected = match jp2::parse_and_inspect_for_display(input, options.limits()) {
        Ok(inspected) => inspected,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_trailer_jp2_inspection_error(input@,
                    crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options), error);
            }
            return Err(error);
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    let profile = super::api::validate_jp2_display_profile(inspected.file());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = profile {
            crate::specs::part2_trailer_jp2_profile_error(input@,
                crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options),
                jp2::raw_inspected_container_view(&inspected), error);
        }
    }
    profile?;
    let stream = inspected.file().codestream(0)?;
    let decoded_result =
        decode_codestream_reconstructed_recover_trailer_selected(stream.data(), options, selection);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_trailer_jp2_reconstructed_actual(input@,
            crate::options::decode_selection_view(selection), crate::options::decode_options_limits(options),
            jp2::raw_inspected_container_view(&inspected), trailer_reconstructed_outcome(decoded_result));
    }
    let decoded = decoded_result?;
    super::api::validate_jp2_reconstruction_output(inspected.file().header())?;
    if let Some(association) = stream.codestream_header() {
        let header = association
            .parsed_header()
            .ok_or(DecodeError::UnsupportedFeature {
                feature: "unparsed JPX header on reconstruction samples",
            })?;
        super::api::validate_jp2_reconstruction_output(header)?;
    }
    Ok(decoded)
}
