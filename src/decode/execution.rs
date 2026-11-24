use super::{
    CodestreamLayout, CodingStyle, ComponentCodingStyles, DecodeError, DecodeSelection,
    DecodedImage, DecodedLayoutTile, DecodedTileComponents, ImageSize, MalformedKind,
    PlannedTileComponent, PreparedTileComponent, ProgressionTilePlan, Resource, ResourceLimits,
    SelectionError, TileDecodeMetadata, TilePartPayload, WaveletTransform,
    apply_tile_multiple_component_transform, arithmetic_overflow, assemble_prepared_components,
    codestream, invalid_decode, plan_progression_tile_at_selected,
    prepare_tile_component_with_kernel, validate_selection, wavelet_transforms_equal,
};
#[cfg(verus_keep_ghost)]
use super::{
    collected_tile_parts_outcome, decoded_layout_tile_outcome, decoded_layout_tile_view,
    decoded_tile_components_outcome, decoded_tile_components_view, execution_header_view,
    execution_tile_headers, layout_accumulation_view, planned_components_view,
    planning_components_view, planning_precinct_planes_known_fields, planning_precincts_view,
    prepare_plan_view, prepare_precincts_view, prepared_components_view, progression_plan_view,
    resolution_counts_outcome_for_tile, tile_decode_metadata_outcome, tile_decode_metadata_view,
    tile_mct_option, tile_part_mct_view, validated_selection_outcome, validated_selection_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_optional_mct_identity(tile_mct_option(left), tile_mct_option(right)),
))]
pub(crate) fn optional_multiple_component_transforms_equal(
    left: Option<&codestream::MultipleComponentTransform>,
    right: Option<&codestream::MultipleComponentTransform>,
) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left.equals(right),
        (None, None) => true,
        _ => false,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_tile_resolutions_result(styles,main,components,discard,resolution_counts_outcome_for_tile(result)),
        resolution_counts_outcome_for_tile(result)!=Err(DecodeError::AllocationFailed) ==>
        resolution_counts_outcome_for_tile(result) == crate::specs::part2_tile_component_resolutions(
        styles, main, components, discard,
    ),
))]
pub(crate) fn prepare_tile_component_resolutions(
    styles: &ComponentCodingStyles,
    main: CodingStyle,
    components: u16,
    discard: Option<u8>,
) -> Result<Vec<u8>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_tile_resolutions_normal(styles,main,components,discard);}
    let discard_levels = match discard {
        None => {
            if main.multiple_component_transform {
                let count = components.min(3);
                let mut component = 0_u16;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant component <= count, count == if components <= 3 { components } else { 3u16 },
                        discard.is_none(), main.multiple_component_transform,
                        crate::specs::part2_tile_resolutions_result(styles,main,components,discard,crate::specs::part2_tile_component_resolutions(styles,main,components,discard)),
                        crate::specs::part2_full_tile_style_admission(styles, main, components, 0)
                            == crate::specs::part2_full_tile_style_admission(styles, main, components, component),
                    decreases count - component,
                ))]
                while component < count {
                    #[cfg(verus_keep_ghost)]
                    proof! { reveal_with_fuel(crate::specs::part2_full_tile_style_admission, 1); }
                    let style = styles.style(component)?;
                    if !wavelet_transforms_equal(style.transform, main.transform) {
                        return Err(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidCodingStyle,
                        });
                    }
                    component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                #[cfg(verus_keep_ghost)]
                proof! { reveal_with_fuel(crate::specs::part2_full_tile_style_admission, 1); }
            }
            return Ok(Vec::new());
        }
        Some(levels) => levels,
    };
    let reserved = if components == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(usize::from(components))
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_tile_metadata_capacity_observed(crate::specs::Part2TileMetadataCapacityContext::SelectedResolutions {styles:*styles,main,components,discard:discard_levels},
            match reserved {Ok(_)=>Ok(()),Err(error)=>Err(error)});
        if reserved.is_err(){crate::specs::part2_tile_resolutions_refused(styles,main,components,discard_levels);}
    }
    let mut counts = reserved?;
    let mut component = 0_u16;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= components,
            discard == Some(discard_levels),
            crate::specs::part2_tile_resolutions_result(styles,main,components,discard,crate::specs::part2_tile_component_resolutions(styles,main,components,discard)),
            crate::specs::part2_selected_tile_resolutions(styles, main, components, discard_levels, 0, Seq::empty())
                == crate::specs::part2_selected_tile_resolutions(styles, main, components, discard_levels, component, counts@),
        decreases components - component,
    ))]
    while component < components {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_selected_tile_resolutions, 1); }
        let style = styles.style(component)?;
        if discard_levels > style.maximum_isotropic_reduction() {
            return Err(DecodeError::InvalidSelection {
                reason: SelectionError::ReductionTooLarge,
            });
        }
        if main.multiple_component_transform
            && component < 3
            && !wavelet_transforms_equal(style.transform, main.transform)
        {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        let levels = match style.decomposition_levels.checked_add(1) {
            Some(levels) => levels,
            None => {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::ReductionTooLarge,
                });
            }
        };
        let levels = match levels.checked_sub(discard_levels) {
            Some(levels) => levels,
            None => {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::ReductionTooLarge,
                });
            }
        };
        counts.push(levels);
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_selected_tile_resolutions, 1); }
    Ok(counts)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_tile_metadata_result(codestream::tile_parts_owned_view(parts@),components,discard,tile_decode_metadata_outcome(result)),
        tile_decode_metadata_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        tile_decode_metadata_outcome(result) == crate::specs::part2_tile_decode_metadata(parts@, components, discard),
))]
pub(crate) fn prepare_tile_decode_metadata<'a, 'data>(
    parts: &'a [TilePartPayload<'data>],
    components: u16,
    discard: Option<u8>,
) -> Result<TileDecodeMetadata<'a, 'data>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(codestream::tile_part_owned_view);
        crate::specs::part2_tile_metadata_normal(codestream::tile_parts_owned_view(parts@),components,discard);
    }
    let first = match parts.first() {
        Some(first) => first,
        None => {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidTilePart,
            });
        }
    };
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= parts.len(), parts.len() > 0, *first == parts@[0],
            crate::specs::part2_tile_metadata_result(codestream::tile_parts_owned_view(parts@),components,discard,crate::specs::part2_tile_decode_metadata(parts@,components,discard)),
            forall |i: int| 0 <= i < index ==> tile_part_mct_view(&parts@[i]) == tile_part_mct_view(first),
        decreases parts.len() - index,
    ))]
    while index < parts.len() {
        let part = parts.get(index).ok_or_else(invalid_decode)?;
        if !optional_multiple_component_transforms_equal(
            part.multiple_component_transform.as_ref(),
            first.multiple_component_transform.as_ref(),
        ) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(codestream::tile_parts_owned_view(parts@)[index as int].multiple_component_transform
                    != codestream::tile_parts_owned_view(parts@)[0].multiple_component_transform);
            }
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidTransform,
            });
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let main = first.coding_style;
    let irreversible = match main.transform {
        WaveletTransform::Irreversible9x7 => true,
        WaveletTransform::Reversible5x3 => false,
        WaveletTransform::Arbitrary(index) => {
            #[cfg(verus_keep_ghost)]
            proof! { codestream::owned_extensions_registry_known(&first.part2_extensions); }
            let kernel = match first.part2_extensions.arbitrary_kernel(index) {
                Some(kernel) => kernel,
                None => {
                    return Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::MissingRequiredStructure,
                    });
                }
            };
            !kernel.reversible()
        }
    };
    let standard = (main.multiple_component_transform, irreversible);
    let resolution_result = prepare_tile_component_resolutions(
        &first.component_coding_styles,
        main,
        components,
        discard,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=resolution_result {
        crate::specs::part2_tile_metadata_resolution_error(codestream::tile_parts_owned_view(parts@),components,discard,
            codestream::tile_part_owned_view(first),standard,error);
    }}
    let resolution_counts = resolution_result?;
    Ok(TileDecodeMetadata {
        first,
        standard,
        resolution_counts,
    })
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_tile_decode_result(size,tile,codestream::tile_parts_owned_view(parts@),
            codestream::codestream_profile_capabilities(profile),discard,limits,prepared_components_view(prepared@),initial,mct_work,
            decoded_layout_tile_outcome(result)),
        decoded_layout_tile_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        decoded_layout_tile_outcome(result) == crate::specs::part2_decode_tile_parts_at(
        size, tile, parts@, codestream::codestream_profile_capabilities(profile), discard, limits,
        prepared_components_view(prepared@), initial, mct_work,
    ),
))]
pub(crate) fn decode_tile_parts_at(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    mct_work: u64,
) -> Result<DecodedLayoutTile, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(size); reveal(codestream::tile_part_owned_view);
        crate::specs::part2_tile_decode_normal(size,tile,codestream::tile_parts_owned_view(parts@),
            codestream::codestream_profile_capabilities(profile),discard,limits,prepared_components_view(prepared@),initial,mct_work);
    }
    let metadata_result = prepare_tile_decode_metadata(parts, size.components, discard);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=metadata_result {
        crate::specs::part2_tile_metadata_decode_error(size,tile,codestream::tile_parts_owned_view(parts@),codestream::codestream_profile_capabilities(profile),
            discard,limits,prepared_components_view(prepared@),initial,mct_work,error);
    }}
    let metadata = metadata_result?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(tile_decode_metadata_view); }
    let first = metadata.first;
    let maximum_resolution_counts = match discard {
        None => None,
        Some(_) => Some(metadata.resolution_counts.as_slice()),
    };
    let plan_result = plan_progression_tile_at_selected(
        size,
        tile,
        first.coding_style,
        &first.component_coding_styles,
        &first.component_quantizations,
        &first.roi_shifts,
        discard.unwrap_or(0),
        profile.part15_allows_multiple_ht_sets(),
        profile.part15_magnitude_bound(),
        profile.part15_requires_all_ht_blocks(),
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=plan_result {
        crate::specs::part2_tile_grid_plan_error(size,tile,codestream::tile_parts_owned_view(parts@),codestream::codestream_profile_capabilities(profile),
            discard,limits,prepared_components_view(prepared@),initial,mct_work,tile_decode_metadata_view(&metadata),error);
    }}
    let plan = plan_result?;
    let counters = account_planned_tile(&plan, maximum_resolution_counts, initial, limits)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_prepared=prepared_components_view(prepared@);
        let ghost source_plan=progression_plan_view(&plan);
    }
    let decoded_result = decode_planned_tile_components(
        plan,
        parts,
        first,
        size,
        metadata.standard,
        maximum_resolution_counts,
        limits,
        prepared,
        mct_work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_tile_decode_components_actual(size,tile,codestream::tile_parts_owned_view(parts@),
            codestream::codestream_profile_capabilities(profile),discard,limits,initial_prepared,initial,mct_work,
            tile_decode_metadata_view(&metadata),source_plan,counters,decoded_tile_components_outcome(decoded_result));
    }
    let decoded = decoded_result?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(decoded_tile_components_view); reveal(decoded_layout_tile_view); }
    Ok(DecodedLayoutTile {
        prepared: decoded.prepared,
        counters,
        mct_work: decoded.mct_work,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_collected_parts_result(
        codestream::tile_parts_owned_view(parts@), tile, collected_tile_parts_outcome(result)),
        collected_tile_parts_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            collected_tile_parts_outcome(result) == crate::specs::part2_collect_tile_parts(
                codestream::tile_parts_owned_view(parts@), tile),
))]
pub(crate) fn collect_tile_parts<'data>(
    parts: &[TilePartPayload<'data>],
    tile: u16,
) -> Result<Vec<TilePartPayload<'data>>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source = codestream::tile_parts_owned_view(parts@);
        let ghost mut prefix = Seq::<crate::specs::Part2JpipSnapshotEvent>::empty();
    }
    let mut count = 0;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= parts.len(), count <= index,
            source == codestream::tile_parts_owned_view(parts@),
            crate::specs::part2_collected_part_count(source, tile, 0)
                == count as nat + crate::specs::part2_collected_part_count(source, tile, index as nat),
        decreases parts.len() - index,
    ))]
    while index < parts.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_collected_part_count, 1);
            codestream::tile_part_owned_tile_known(&parts[index as int]);
        }
        if parts[index].tile_index == tile {
            count += 1;
        }
        index += 1;
    }
    let reserved = if count == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_collected_part_count, 1);
        crate::specs::part2_collected_capacity_observed(source, tile, count,
            crate::allocation::inspection_capacity_outcome(reserved));
        let root = |events| crate::specs::part2_collected_parts_run(source, tile, events);
        let child = |events| crate::specs::part2_collected_capacity_run(source, tile, events);
        let next = |_: (), rest| crate::specs::part2_collected_loop_run(source, tile, 0, Seq::empty(), rest);
        match reserved {
            Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
            Ok(_) => { prefix = crate::specs::part2_decode_prefix_advance(root, child, next, prefix, ()); },
        }
    }
    let mut output = reserved?;
    #[cfg(verus_keep_ghost)]
    proof! { assert(codestream::tile_parts_owned_view(output@) =~= Seq::empty()); }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= parts.len(),
            source == codestream::tile_parts_owned_view(parts@),
            forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                #[trigger] crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                    == crate::specs::part2_collected_loop_run(
                        source, tile, index as nat, codestream::tile_parts_owned_view(output@), tail),
            crate::specs::part2_collect_tile_parts(codestream::tile_parts_owned_view(parts@), tile)
                == Ok(crate::specs::part2_collect_tile_parts_run(
                    codestream::tile_parts_owned_view(parts@), tile, index as nat, codestream::tile_parts_owned_view(output@),
                )),
        decreases parts.len() - index,
    ))]
    while index < parts.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = codestream::tile_parts_owned_view(output@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_collect_tile_parts_run, 1);
            reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
        }
        let part = parts.get(index).ok_or_else(invalid_decode)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            codestream::tile_part_owned_tile_known(&part);
            assert(codestream::tile_part_owned_view(part) == source[index as int]);
        }
        if part.tile_index == tile {
            let copied = part.try_duplicate();
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_payload_copy_observed(codestream::tile_part_owned_view(part),
                    codestream::tile_part_copy_outcome(copied));
                let root = |events| crate::specs::part2_collected_parts_run(source, tile, events);
                let child = |events| crate::specs::part2_payload_copy_run(codestream::tile_part_owned_view(part), events);
                let next = |after: crate::specs::Part2OwnedTilePart, rest|
                    crate::specs::part2_collected_loop_run(source, tile, index as nat + 1, before.push(after), rest);
                assert forall|tail| root(prefix + tail) == crate::specs::part2_jpip_snapshot_bind(child(tail), next) by {
                    assert(root(prefix + tail)
                        == crate::specs::part2_collected_loop_run(source, tile, index as nat, before, tail));
                    reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
                }
                match codestream::tile_part_copy_outcome(copied) {
                    Err(error) => crate::specs::part2_decode_prefix_error(root, child, next, prefix, error),
                    Ok(after) => { prefix = crate::specs::part2_decode_prefix_advance(root, child, next, prefix, after); },
                }
            }
            let part = copied?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost copied = codestream::tile_part_owned_view(&part); }
            output.push(part);
            #[cfg(verus_keep_ghost)]
            proof! { assert(codestream::tile_parts_owned_view(output@) =~= before.push(copied)); }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                    crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                        == crate::specs::part2_collected_loop_run(source, tile, index as nat + 1, before, tail) by {
                    assert(crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                        == crate::specs::part2_collected_loop_run(source, tile, index as nat, before, tail));
                    reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
                }
            }
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_collect_tile_parts_run, 1);
        reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
        assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
            crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                == Some((Ok(codestream::tile_parts_owned_view(output@)), tail)) by {
            assert(crate::specs::part2_collected_parts_run(source, tile, prefix + tail)
                == crate::specs::part2_collected_loop_run(
                    source, tile, index as nat, codestream::tile_parts_owned_view(output@), tail));
            reveal_with_fuel(crate::specs::part2_collected_loop_run, 1);
        }
        assert(crate::specs::part2_cold_prefix(
            |events| crate::specs::part2_collected_parts_run(source, tile, events), prefix,
            Ok(codestream::tile_parts_owned_view(output@))));
    }
    Ok(output)
}

pub(super) enum SelectedTileParts<'a, 'data> {
    Borrowed(&'a [TilePartPayload<'data>]),
    Owned(Vec<TilePartPayload<'data>>),
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) open spec fn selected_tile_parts_view(value: &SelectedTileParts<'_, '_>)
        -> Seq<crate::specs::Part2OwnedTilePart> {
        match value {
            SelectedTileParts::Borrowed(slice) => codestream::tile_parts_owned_view(slice@),
            SelectedTileParts::Owned(values) => codestream::tile_parts_owned_view(values@),
        }
    }

    pub(super) open spec fn selected_tile_parts_outcome(result: Result<SelectedTileParts<'_, '_>, DecodeError>)
        -> Result<Seq<crate::specs::Part2OwnedTilePart>, DecodeError> {
        match result { Ok(value) => Ok(selected_tile_parts_view(&value)), Err(error) => Err(error) }
    }
}

impl<'a, 'data> SelectedTileParts<'a, 'data> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures codestream::tile_parts_owned_view(result@) == selected_tile_parts_view(self),
    ))]
    pub(super) fn as_slice(&self) -> &[TilePartPayload<'data>] {
        match self {
            Self::Borrowed(slice) => slice,
            Self::Owned(parts) => parts.as_slice(),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Ok(Some((start, end))) => start < end && crate::specs::part2_tile_run_bounds(
            codestream::tile_parts_owned_view(parts@), tile, parts.len() as int, start as int, end as int),
        Ok(None) => !crate::specs::part2_has_contiguous_tile_run(codestream::tile_parts_owned_view(parts@), tile),
        Err(_) => false,
    },
))]
// Return only a nonempty run containing every matching tile part. Part ordinals
// and counts are interpreted by packet preparation, not by this storage choice.
fn contiguous_tile_run(
    parts: &[TilePartPayload<'_>],
    tile: u16,
) -> Result<Option<(usize, usize)>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost source = codestream::tile_parts_owned_view(parts@); }
    let mut start = 0;
    let mut end = 0;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant source == codestream::tile_parts_owned_view(parts@),
            crate::specs::part2_tile_run_bounds(source, tile, index as int, start as int, end as int),
            start < end || (start == 0 && end == 0),
        decreases parts.len() - index,
    ))]
    while index < parts.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        #[cfg(verus_keep_ghost)]
        proof! { codestream::tile_part_owned_tile_known(&parts[index as int]); }
        if parts[index].tile_index == tile {
            if start == end {
                start = index;
            } else if end != index {
                #[cfg(verus_keep_ghost)]
                proof! {
                    if crate::specs::part2_has_contiguous_tile_run(source, tile) {
                        let (lo, hi) = choose|lo: int, hi: int| lo < hi &&
                            #[trigger] crate::specs::part2_tile_run_bounds(source, tile, source.len() as int, lo, hi);
                        assert(source[start as int].tile_index == tile);
                        assert(source[end as int].tile_index != tile);
                        assert(source[index as int].tile_index == tile);
                        assert(lo <= start < end < index < hi);
                        assert(false);
                    }
                }
                return Ok(None);
            }
            end = index + 1;
        }
        index += 1;
    }
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    if start == end {
        #[cfg(verus_keep_ghost)]
        proof! {
            if crate::specs::part2_has_contiguous_tile_run(source, tile) {
                let (lo, hi) = choose|lo: int, hi: int| lo < hi &&
                    #[trigger] crate::specs::part2_tile_run_bounds(source, tile, source.len() as int, lo, hi);
                assert(source[lo].tile_index == tile);
                assert(source[lo].tile_index != tile);
            }
        }
        Ok(None)
    } else {
        Ok(Some((start, end)))
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_select_tile_parts_result(
        codestream::tile_parts_owned_view(parts@), tile, selected_tile_parts_outcome(result)),
        selected_tile_parts_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            selected_tile_parts_outcome(result) == crate::specs::part2_collect_tile_parts(
                codestream::tile_parts_owned_view(parts@), tile),
))]
pub(super) fn select_tile_parts<'a, 'data>(
    parts: &'a [TilePartPayload<'data>],
    tile: u16,
) -> Result<SelectedTileParts<'a, 'data>, DecodeError> {
    let bounds = contiguous_tile_run(parts, tile)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost source = codestream::tile_parts_owned_view(parts@); }
    match bounds {
        Some((start, end)) => {
            let slice = parts.get(start..end).ok_or_else(invalid_decode)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_has_contiguous_tile_run(source, tile));
                assert(codestream::tile_parts_owned_view(slice@) =~= source.subrange(start as int, end as int));
                crate::specs::part2_tile_run_value(source, tile, start as int, end as int);
                crate::specs::part2_select_tile_parts_join(source, tile, true, Ok(codestream::tile_parts_owned_view(slice@)));
            }
            Ok(SelectedTileParts::Borrowed(slice))
        }
        None => {
            let owned = collect_tile_parts(parts, tile);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_select_tile_parts_join(source, tile, false, collected_tile_parts_outcome(owned));
            }
            Ok(SelectedTileParts::Owned(owned?))
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_layout_decode_result(codestream::decoder_layout_input_view(layout),Some(crate::options::decode_selection_view(requested)),limits,
            crate::image::decoded_image_outcome(result)),
        crate::image::decoded_image_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        crate::image::decoded_image_outcome(result) == crate::specs::part2_decode_layout_selected(layout, requested, limits),
))]
pub(super) fn decode_layout_selected(
    layout: &CodestreamLayout<'_>,
    requested: &DecodeSelection,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part2_decode_layout_selected(layout, requested, limits);
        let ghost source = codestream::decoder_layout_input_view(layout);
        let ghost requested_input=Some(crate::options::decode_selection_view(requested));
        let ghost prefix: Seq<crate::specs::Part2JpipSnapshotEvent> = Seq::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        super::decoder_execution_inputs_known(layout);
        crate::specs::part2_layout_decode_normal(source,requested_input,limits);
    }
    validate_part2_execution(layout)?;
    let selected = validate_selection(&layout.info.image_size, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_layout_decode_result);
        let root = |events| crate::specs::part2_layout_decode_run(source, requested_input, limits, events);
        let child = |events| crate::specs::part2_validate_selection_run(
            codestream::selection_geometry_view(&layout.info.image_size),
            crate::options::decode_selection_view(requested), events);
        let next = |selection: crate::specs::Part2ValidatedSelection, rest|
            crate::specs::part2_layout_after_selection_run(source, selection, limits, rest);
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
        reveal(validated_selection_view);
        reveal(validated_selection_outcome);
        assert(selection.region@.len() == 4);
        assert([selection.region@[0], selection.region@[1], selection.region@[2], selection.region@[3]] == selection.region);
    }
    let mut prepared = Vec::new();
    let mut total_packets = 0_u64;
    let mut total_precincts = 0_u64;
    let mut total_code_blocks = 0_u64;
    let mut total_mct_work = 0_u64;
    let mut selected_tile = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(prepared_components_view(prepared@) =~= Seq::empty());
        reveal(layout_accumulation_view);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant selected_tile <= selection.tiles.len(),
                source==codestream::decoder_layout_input_view(layout),
                requested_input==Some(crate::options::decode_selection_view(requested)),
                crate::specs::part2_layout_decode_result(source,requested_input,limits,goal),
                forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|
                    crate::specs::part2_layout_decode_run(source,requested_input,limits,prefix+tail)
                        ==crate::specs::part2_selected_decode_run(&source.size,source.parts,source.capabilities,selection.tiles@,
                            selection.region,selection.discard_levels,limits,selected_tile as nat,
                            layout_accumulation_view(prepared@,(total_packets,total_precincts,total_code_blocks),total_mct_work),tail),
                goal == crate::specs::part2_decode_layout_selected(layout, requested, limits),
                goal == crate::specs::part2_selected_layout_tiles(
                    &layout.info.image_size, codestream::tile_parts_owned_view(layout.tile_parts@),
                    codestream::codestream_profile_capabilities(&layout.info.profile), selection.tiles@,
                    selection.region, selection.discard_levels, limits, selected_tile as nat,
                    layout_accumulation_view(prepared@, (total_packets, total_precincts, total_code_blocks), total_mct_work),
                ),
            decreases selection.tiles.len() - selected_tile,
        )
    )]
    while selected_tile < selection.tiles.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            codestream::decoder_layout_input_fields(layout);
            reveal(layout_accumulation_view);
            reveal_with_fuel(crate::specs::part2_selected_layout_tiles, 1);
        }
        let tile_index = *selection
            .tiles
            .get(selected_tile)
            .ok_or_else(invalid_decode)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before=layout_accumulation_view(prepared@,(total_packets,total_precincts,total_code_blocks),total_mct_work);
            let ghost root=|events|crate::specs::part2_layout_decode_run(source,requested_input,limits,events);
            let ghost next_tile=|after:crate::specs::Part2DecodedLayoutTile,rest|
                crate::specs::part2_selected_decode_run(&source.size,source.parts,source.capabilities,
                    selection.tiles@,selection.region,selection.discard_levels,limits,selected_tile as nat+1,after,rest);
            let ghost after_parts=|selected:Seq<crate::specs::Part2OwnedTilePart>,rest|
                crate::specs::part2_jpip_snapshot_bind(
                    crate::specs::part2_tile_decode_run(&source.size,tile_index,selected,source.capabilities,
                        Some(selection.discard_levels),limits,before.prepared,before.counters,before.mct_work,rest),next_tile);
        }
        let collected = select_tile_parts(&layout.tile_parts, tile_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            let child=|events|crate::specs::part2_select_tile_parts_run(source.parts,tile_index,events);
            crate::specs::part2_selected_decode_step(&source.size,source.parts,source.capabilities,selection.tiles@,
                selection.region,selection.discard_levels,limits,selected_tile as nat,before);
            assert forall|tail|root(prefix+tail)==crate::specs::part2_jpip_snapshot_bind(child(tail),after_parts) by {
                assert(root(prefix+tail)==crate::specs::part2_selected_decode_run(&source.size,source.parts,
                    source.capabilities,selection.tiles@,selection.region,selection.discard_levels,limits,selected_tile as nat,before,tail));
            }
            match selected_tile_parts_outcome(collected) {
                Err(error)=>{
                    crate::specs::part2_decode_prefix_error(root,child,after_parts,prefix,error);
                    reveal(crate::specs::part2_layout_decode_result);
                },
                Ok(selected)=>{prefix=crate::specs::part2_decode_prefix_advance(root,child,after_parts,prefix,selected);},
            }
        }
        let tile_parts = collected?;
        let tile_parts = tile_parts.as_slice();
        let decoded_result = decode_tile_parts_at(
            &layout.info.image_size,
            tile_index,
            tile_parts,
            &layout.info.profile,
            Some(selection.discard_levels),
            limits,
            prepared,
            (total_packets, total_precincts, total_code_blocks),
            total_mct_work,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_tile_decode_result);
            let child=|events|crate::specs::part2_tile_decode_run(&source.size,tile_index,codestream::tile_parts_owned_view(tile_parts@),
                source.capabilities,Some(selection.discard_levels),limits,before.prepared,before.counters,before.mct_work,events);
            let next=next_tile;
            assert forall|tail|root(prefix+tail)==crate::specs::part2_jpip_snapshot_bind(child(tail),next) by {
                assert(root(prefix+tail)==after_parts(codestream::tile_parts_owned_view(tile_parts@),tail));
            }
            match decoded_layout_tile_outcome(decoded_result) {
                Err(error)=>{
                    crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);
                    reveal(crate::specs::part2_layout_decode_result);
                },
                Ok(after)=>{prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,after);},
            }
        }
        let decoded = decoded_result?;
        prepared = decoded.prepared;
        total_packets = decoded.counters.0;
        total_precincts = decoded.counters.1;
        total_code_blocks = decoded.counters.2;
        total_mct_work = decoded.mct_work;
        selected_tile = selected_tile
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_selected_layout_tiles, 1); reveal(layout_accumulation_view); }
    let assembled = assemble_prepared_components(
        &layout.info.image_size,
        &prepared,
        Some((selection.region, selection.discard_levels)),
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_selected_decode_run,1);
        reveal(crate::specs::part2_layout_decode_result);
        let root=|events|crate::specs::part2_layout_decode_run(source,requested_input,limits,events);
        let child=|events|crate::specs::part2_assemble_prepared_storage_run(crate::image::assembly_size_view(&layout.info.image_size),
            prepared_components_view(prepared@),Some((selection.region,selection.discard_levels)),crate::limits::resource_decoded_bytes_limit(limits),events);
        crate::specs::part2_decode_eta(child,crate::image::decoded_image_outcome(assembled));
        assert(source.size==layout.info.image_size);
        assert forall|events|root(prefix+events)==child(events) by {
            assert(crate::specs::part2_layout_decode_run(source,requested_input,limits,prefix+events)
                ==crate::specs::part2_selected_decode_run(&source.size,source.parts,source.capabilities,selection.tiles@,
                    selection.region,selection.discard_levels,limits,selected_tile as nat,
                    layout_accumulation_view(prepared@,(total_packets,total_precincts,total_code_blocks),total_mct_work),events));
        }
        crate::specs::part2_cold_prefix_result(root,child,prefix,crate::image::decoded_image_outcome(assembled));
    }
    assembled
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_prepared_standard_admission(prepared_components_view(prepared@), irreversible),
))]
pub(super) fn validate_prepared_standard_components(
    prepared: &[PreparedTileComponent],
    irreversible: bool,
) -> Result<usize, DecodeError> {
    if prepared.len() < 3 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        });
    }
    let (red, rest) = prepared.split_first().ok_or_else(invalid_decode)?;
    let (green, rest) = rest.split_first().ok_or_else(invalid_decode)?;
    let blue = rest.first().ok_or_else(invalid_decode)?;
    if (red.x, red.y, red.width, red.height) != (green.x, green.y, green.width, green.height)
        || (red.x, red.y, red.width, red.height) != (blue.x, blue.y, blue.width, blue.height)
        || red.samples.len() != green.samples.len()
        || red.samples.len() != blue.samples.len()
        || red.fraction_bits != green.fraction_bits
        || red.fraction_bits != blue.fraction_bits
        || (!irreversible && red.fraction_bits != 0)
        || (irreversible && red.fraction_bits != 16)
    {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidTransform,
        });
    }
    Ok(red.samples.len())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_prepared_sample(prepared_components_view(prepared@), component, index),
))]
pub(super) fn prepared_sample(
    prepared: &[PreparedTileComponent],
    component: usize,
    index: usize,
) -> Result<i64, DecodeError> {
    let component = prepared.get(component).ok_or_else(invalid_decode)?;
    Ok(*component.samples.get(index).ok_or_else(invalid_decode)?)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, prepared_components_view(final(prepared)@)) == crate::specs::part1_prepared_store_sample(
        prepared_components_view(old(prepared)@), component, index, value),
))]
pub(super) fn store_prepared_sample(
    prepared: &mut [PreparedTileComponent],
    component: usize,
    index: usize,
    value: i64,
) -> Result<(), DecodeError> {
    let component = prepared.get_mut(component).ok_or_else(invalid_decode)?;
    *component
        .samples
        .get_mut(index)
        .ok_or_else(invalid_decode)? = value;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, prepared_components_view(final(prepared)@)) == crate::specs::part1_prepared_standard_pixel(
        prepared_components_view(old(prepared)@), index, irreversible),
))]
pub(super) fn apply_prepared_standard_pixel(
    prepared: &mut [PreparedTileComponent],
    index: usize,
    irreversible: bool,
) -> Result<(), DecodeError> {
    let y = prepared_sample(prepared, 0, index)?;
    let cb = prepared_sample(prepared, 1, index)?;
    let cr = prepared_sample(prepared, 2, index)?;
    let (red, green, blue) = crate::image::inverse_component_values(y, cb, cr, irreversible)?;
    store_prepared_sample(prepared, 0, index, red)?;
    store_prepared_sample(prepared, 1, index, green)?;
    store_prepared_sample(prepared, 2, index, blue)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_mct_line_finish_result(prepared_components_view(old(prepared)@),
        codestream::image_size_component_count(size),codestream::image_size_component_infos(size),tile_mct_option(mct),standard,*old(work),
        crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
        (result,prepared_components_view(final(prepared)@),*final(work))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, prepared_components_view(final(prepared)@), *final(work)) == crate::specs::part2_finish_prepared_tile(
        prepared_components_view(old(prepared)@), codestream::image_size_component_count(size), codestream::image_size_component_infos(size),
        tile_mct_option(mct), standard, *old(work), crate::limits::resource_work_limit(limits),
        crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub(super) fn finish_prepared_tile(
    prepared: &mut [PreparedTileComponent],
    size: &ImageSize,
    mct: Option<&codestream::MultipleComponentTransform>,
    standard: (bool, bool),
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=prepared_components_view(prepared@);let ghost initial_work=*work;}
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_mct_line_finish_normal(before,codestream::image_size_component_count(size),codestream::image_size_component_infos(size),
    tile_mct_option(mct),standard,initial_work,crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));}
    if let Some(transform) = mct {
        let transformed =
            apply_tile_multiple_component_transform(prepared, size, transform, limits, work);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_mct_line_finish_observed(before,codestream::image_size_component_count(size),codestream::image_size_component_infos(size),
        codestream::multiple_component_transform_view(transform),standard,initial_work,crate::limits::resource_work_limit(limits),
        crate::limits::resource_decoded_bytes_limit(limits),(transformed,prepared_components_view(prepared@),*work));}
        transformed?;
    }
    apply_prepared_component_transform(prepared, standard)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_extraction_tile_result(
            prepared_components_view(old(prepared)@),planned_components_view(plan),prepare_precincts_view(plan.precincts@),first.component_coding_styles,
            codestream::part2_kernel_registry(&first.part2_extensions),codestream::image_size_component_count(size),codestream::image_size_component_infos(size),
            tile_part_mct_view(first),standard,*old(work),crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
            (result,prepared_components_view(final(prepared)@),*final(work))),
        result!=Err(DecodeError::AllocationFailed) ==> (result, prepared_components_view(final(prepared)@), *final(work)) == crate::specs::part2_reconstruct_planned_tile(
        prepared_components_view(old(prepared)@), planned_components_view(plan), prepare_precincts_view(plan.precincts@),
        first.component_coding_styles, codestream::part2_kernel_registry(&first.part2_extensions),
        codestream::image_size_component_count(size), codestream::image_size_component_infos(size),
        tile_part_mct_view(first), standard, *old(work),
        crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub(super) fn reconstruct_planned_tile(
    plan: &ProgressionTilePlan,
    first: &TilePartPayload<'_>,
    size: &ImageSize,
    standard: (bool, bool),
    limits: &ResourceLimits,
    prepared: &mut Vec<PreparedTileComponent>,
    work: &mut u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = prepared_components_view(prepared@);
        let ghost plans = planned_components_view(plan);
        let ghost precincts = prepare_precincts_view(plan.precincts@);
        let ghost kernels = codestream::part2_kernel_registry(&first.part2_extensions);
        let ghost initial_work = *work;
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_extraction_tile_normal(initial,plans,precincts,first.component_coding_styles,kernels,
    codestream::image_size_component_count(size),codestream::image_size_component_infos(size),tile_part_mct_view(first),standard,initial_work,
    crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits));}
    let start = prepared.len();
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_reconstruct_components_empty(
            initial, plans, precincts, first.component_coding_styles, kernels, crate::limits::resource_decoded_bytes_limit(limits));
    }
    let mut component_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component_index <= plan.components.len(), plans == planned_components_view(plan),
        precincts == prepare_precincts_view(plan.precincts@),
        kernels == codestream::part2_kernel_registry(&first.part2_extensions),
        initial == prepared_components_view(old(prepared)@), initial_work == *old(work), *work == initial_work,
        crate::specs::part2_extraction_tile_result(initial,plans,precincts,first.component_coding_styles,kernels,
            codestream::image_size_component_count(size),codestream::image_size_component_infos(size),tile_part_mct_view(first),standard,initial_work,
            crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),
            crate::specs::part2_reconstruct_planned_tile(initial,plans,precincts,first.component_coding_styles,kernels,
                codestream::image_size_component_count(size),codestream::image_size_component_infos(size),tile_part_mct_view(first),standard,initial_work,
                crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits))),
        start == initial.len(), start <= prepared.len(),
        prepared_components_view(prepared@).take(start as int) == initial,
        crate::specs::part2_reconstruct_components_prefix(initial, plans, precincts, first.component_coding_styles,
            kernels, crate::limits::resource_decoded_bytes_limit(limits), component_index as nat)
                == (Ok(()), prepared_components_view(prepared@)),
        decreases plan.components.len() - component_index,
    ))]
    while component_index < plan.components.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_reconstruct_components_step(initial, plans, precincts,
                first.component_coding_styles, kernels, crate::limits::resource_decoded_bytes_limit(limits), component_index as nat);
            crate::proofs::production_impl::production_reconstruct_components_error(initial, plans, precincts,
                first.component_coding_styles, kernels, crate::limits::resource_decoded_bytes_limit(limits), component_index as nat + 1, plans.len());
        }
        let planned = plan
            .components
            .get(component_index)
            .ok_or_else(invalid_decode)?;
        let style = first.component_coding_styles.style(planned.component)?;
        let kernel = match style.transform {
            WaveletTransform::Arbitrary(index) => first.part2_extensions.arbitrary_kernel(index),
            _ => None,
        };
        let component_result =
            prepare_tile_component_with_kernel(planned, &plan.precincts, style, kernel, limits);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_extraction_reconstruct_component_observed(plans[component_index as int],precincts,first.component_coding_styles,kernels,
        crate::limits::resource_decoded_bytes_limit(limits),style,crate::decode::prepared_component_outcome(component_result));
        if let Err(error)=component_result{crate::specs::part2_extraction_tile_component_error(initial,plans,precincts,first.component_coding_styles,kernels,
            codestream::image_size_component_count(size),codestream::image_size_component_infos(size),tile_part_mct_view(first),standard,initial_work,
            crate::limits::resource_work_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),component_index as nat,prepared_components_view(prepared@),error);}}
        let component = component_result?;
        let reserved = crate::allocation::reserve_additional(prepared, 1);
        #[cfg(verus_keep_ghost)]
        proof! {
            let context=crate::specs::Part2PreparedComponentContext {
                before:prepared_components_view(prepared@),plans,precincts,styles:first.component_coding_styles,kernels,
                maximum:crate::limits::resource_decoded_bytes_limit(limits),index:component_index as nat,value:crate::decode::prepared_component_view(component)};
            crate::specs::part2_prepared_component_capacity_observed(context,crate::allocation::inspection_capacity_outcome(reserved));
            if reserved.is_err(){crate::specs::part2_extraction_tile_publication_refused(initial,context,
                codestream::image_size_component_count(size),codestream::image_size_component_infos(size),tile_part_mct_view(first),standard,initial_work,
                crate::limits::resource_work_limit(limits));}
        }
        reserved?;
        prepared.push(component);
        component_index = component_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost folded = prepared_components_view(prepared@); }
    let suffix = prepared.get_mut(start..).ok_or_else(invalid_decode)?;
    #[cfg(verus_keep_ghost)]
    proof! { assert(prepared_components_view(suffix@) =~= folded.skip(start as int)); }
    let result = finish_prepared_tile(
        suffix,
        size,
        first.multiple_component_transform.as_ref(),
        standard,
        limits,
        work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let suffix_values = prepared_components_view(suffix@);
        assert(prepared_components_view(prepared@).skip(start as int) =~= suffix_values);
        let finished = (result,suffix_values,*work);
        crate::specs::part2_extraction_tile_finish_observed(initial,plans,precincts,first.component_coding_styles,kernels,
            codestream::image_size_component_count(size), codestream::image_size_component_infos(size),
            tile_part_mct_view(first), standard, initial_work,
            crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),folded,finished);
        assert((result, prepared_components_view(prepared@).skip(start as int), *work) == finished);
        assert(prepared_components_view(prepared@) =~= initial + finished.1);
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, prepared_components_view(final(prepared)@)) == crate::specs::part1_prepared_standard_transform(
        prepared_components_view(old(prepared)@), transform),
))]
pub(super) fn apply_prepared_component_transform(
    prepared: &mut [PreparedTileComponent],
    transform: (bool, bool),
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = prepared_components_view(prepared@); }
    if !transform.0 {
        return Ok(());
    }
    let length = validate_prepared_standard_components(prepared, transform.1)?;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_prepared_standard_empty(before, transform.1); }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= length, transform.0,
            before == prepared_components_view(old(prepared)@),
            crate::specs::part1_prepared_standard_admission(before, transform.1) == Ok(length),
            crate::specs::part1_prepared_standard_prefix(before, transform.1, index as nat) == (Ok(()), prepared_components_view(prepared@)),
            decreases length - index,
        )
    )]
    while index < length {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_prepared_standard_step(before, transform.1, index as nat);
            crate::proofs::production_impl::production_prepared_standard_error(before, transform.1, index as nat + 1, length as nat);
        }
        apply_prepared_standard_pixel(prepared, index, transform.1)?;
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_validate_execution_component(
            execution_header_view(*styles, extensions), component),
    )
)]
pub(super) fn validate_part2_component(
    styles: &ComponentCodingStyles,
    extensions: &codestream::Part2Extensions,
    component: u16,
) -> Result<(), DecodeError> {
    validate_part2_coding_style(styles.style(component)?, extensions)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_execution_components_prefix(
            execution_header_view(*styles, extensions), count as nat),
    )
)]
pub(super) fn validate_part2_components(
    styles: &ComponentCodingStyles,
    extensions: &codestream::Part2Extensions,
    count: u16,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost header = execution_header_view(*styles, extensions); }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_execution_components_empty(header); }
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= count, header == execution_header_view(*styles, extensions),
                crate::specs::part2_execution_components_prefix(header, component as nat) == Ok(()),
            decreases count - component,
        )
    )]
    while component < count {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_execution_components_step(header, component as nat); }
        let result = validate_part2_component(styles, extensions, component);
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = result {
                assert(crate::specs::part2_execution_components_prefix(header, component as nat + 1) == Err(error));
                crate::proofs::production_impl::production_execution_components_error(header, component as nat + 1, count as nat);
            } else { crate::proofs::production_impl::production_mct_unit_result(result); }
        }
        result?;
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_validate_execution_tile(
            execution_header_view(part.component_coding_styles, &part.part2_extensions),
            codestream::part2_component_depths(main), count),
    )
)]
pub(super) fn validate_part2_tile_execution(
    part: &TilePartPayload<'_>,
    main: &codestream::Part2Extensions,
    count: u16,
) -> Result<(), DecodeError> {
    part.part2_extensions.validate_executable()?;
    validate_part2_components(&part.component_coding_styles, &part.part2_extensions, count)?;
    if !part.part2_extensions.component_bit_depths().is_empty()
        && !part.part2_extensions.component_bit_depths_equal(main)
    {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidMarkerOrder,
        });
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_validate_execution_layout(
            layout.info.image_size.components,
            execution_header_view(layout.info.component_coding_styles, &layout.info.part2_extensions),
            execution_tile_headers(layout.tile_parts@)),
    )
)]
pub(crate) fn validate_part2_execution(layout: &CodestreamLayout<'_>) -> Result<(), DecodeError> {
    layout.info.part2_extensions.validate_executable()?;
    validate_part2_components(
        &layout.info.component_coding_styles,
        &layout.info.part2_extensions,
        layout.info.image_size.components,
    )?;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_execution_tiles_empty(
            execution_tile_headers(layout.tile_parts@), codestream::part2_component_depths(&layout.info.part2_extensions),
            layout.info.image_size.components);
    }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= layout.tile_parts.len(),
                crate::specs::part2_execution_components_prefix(
                    execution_header_view(layout.info.component_coding_styles, &layout.info.part2_extensions),
                    layout.info.image_size.components as nat) == Ok(()),
                crate::specs::part2_execution_tiles_prefix(execution_tile_headers(layout.tile_parts@),
                    codestream::part2_component_depths(&layout.info.part2_extensions),
                    layout.info.image_size.components, index as nat) == Ok(()),
            decreases layout.tile_parts.len() - index,
        )
    )]
    while index < layout.tile_parts.len() {
        let tile_part = layout
            .tile_parts
            .get(index)
            .ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_execution_tiles_step(
                execution_tile_headers(layout.tile_parts@), codestream::part2_component_depths(&layout.info.part2_extensions),
                layout.info.image_size.components, index as nat);
        }
        let result = validate_part2_tile_execution(
            tile_part,
            &layout.info.part2_extensions,
            layout.info.image_size.components,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Err(error) = result {
                assert(crate::specs::part2_execution_tiles_prefix(execution_tile_headers(layout.tile_parts@),
                    codestream::part2_component_depths(&layout.info.part2_extensions),
                    layout.info.image_size.components, index as nat + 1) == Err(error));
                crate::proofs::production_impl::production_execution_tiles_error(
                    execution_tile_headers(layout.tile_parts@), codestream::part2_component_depths(&layout.info.part2_extensions),
                    layout.info.image_size.components, index as nat + 1, layout.tile_parts@.len());
            } else { crate::proofs::production_impl::production_mct_unit_result(result); }
        }
        result?;
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::part2_validate_execution_style(
            style, codestream::part2_execution_registry(extensions), codestream::part2_kernel_registry(extensions)),
    )
)]
pub(crate) fn validate_part2_coding_style(
    style: CodingStyle,
    extensions: &crate::codestream::Part2Extensions,
) -> Result<(), DecodeError> {
    let missing_decomposition = match style.decomposition_structure {
        Some(index) => {
            extensions.decomposition_structure(index).is_none()
                && extensions.arbitrary_decomposition(index).is_none()
        }
        None => false,
    };
    if missing_decomposition {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::MissingRequiredStructure,
        });
    }
    let missing_kernel = match style.transform {
        WaveletTransform::Arbitrary(index) => extensions.arbitrary_kernel(index).is_none(),
        _ => false,
    };
    if missing_kernel {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::MissingRequiredStructure,
        });
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_selected_component_blocks(prepare_plan_view(plan), 0, total),
))]
pub(crate) fn count_selected_component_blocks(
    plan: &PlannedTileComponent,
    total: u64,
) -> Result<u64, DecodeError> {
    let mut count = total;
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= plan.placements.len(),
            crate::specs::part2_selected_component_blocks(prepare_plan_view(plan), 0, total)
                == crate::specs::part2_selected_component_blocks(prepare_plan_view(plan), index as nat, count),
        decreases plan.placements.len() - index,
    ))]
    while index < plan.placements.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(prepare_plan_view); reveal_with_fuel(crate::specs::part2_selected_component_blocks, 1); }
        let placement = plan.placements.get(index).ok_or_else(invalid_decode)?;
        let band = plan
            .subbands
            .get(placement.subband_index)
            .ok_or_else(invalid_decode)?;
        if band.resolution <= plan.output_resolution {
            count = count.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(prepare_plan_view); reveal_with_fuel(crate::specs::part2_selected_component_blocks, 1); }
    Ok(count)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_planned_tile_accounting(
        progression_plan_view(plan), crate::packet::packet_selection_view(maximum_resolution_counts), initial, limits,
    ),
))]
pub(crate) fn account_planned_tile(
    plan: &ProgressionTilePlan,
    maximum_resolution_counts: Option<&[u8]>,
    initial: (u64, u64, u64),
    limits: &ResourceLimits,
) -> Result<(u64, u64, u64), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(progression_plan_view); }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_planned_tile_accounting(
        progression_plan_view(plan), crate::packet::packet_selection_view(maximum_resolution_counts), initial, limits,
    ); }
    let selected = maximum_resolution_counts.is_some();
    let packets = match maximum_resolution_counts {
        None => plan.grid.packet_count(),
        Some(counts) => plan.grid.selected_packet_count(counts)?,
    };
    let total_packets = initial
        .0
        .checked_add(packets)
        .ok_or_else(arithmetic_overflow)?;
    if total_packets > limits.maximum_packets() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: limits.maximum_packets(),
            actual: total_packets,
        });
    }
    let precincts = if selected {
        packets
            .checked_div(u64::from(plan.coding_style.layers))
            .ok_or_else(arithmetic_overflow)?
    } else {
        plan.grid.total_precinct_count()?
    };
    let total_precincts = initial
        .1
        .checked_add(precincts)
        .ok_or_else(arithmetic_overflow)?;
    if total_precincts > limits.maximum_precincts() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Precincts,
            limit: limits.maximum_precincts(),
            actual: total_precincts,
        });
    }
    let mut total_blocks = initial.2;
    let mut component = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant component <= plan.components.len(),
            goal == crate::specs::part2_planned_tile_accounting(
                progression_plan_view(plan), crate::packet::packet_selection_view(maximum_resolution_counts), initial, limits,
            ),
            goal == match crate::specs::part2_account_plan_blocks(
                planning_components_view(plan.components@), selected, crate::limits::resource_code_block_limit(limits),
                component as nat, total_blocks,
            ) {
                Err(error) => Err(error),
                Ok(blocks) => Ok((total_packets, total_precincts, blocks)),
            },
        decreases plan.components.len() - component,
    ))]
    while component < plan.components.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(progression_plan_view); reveal_with_fuel(crate::specs::part2_account_plan_blocks, 1); }
        let planned = plan.components.get(component).ok_or_else(invalid_decode)?;
        if selected {
            total_blocks = count_selected_component_blocks(planned, total_blocks)?;
        } else {
            total_blocks = total_blocks
                .checked_add(planned.placements.len() as u64)
                .ok_or_else(arithmetic_overflow)?;
            if total_blocks > limits.maximum_code_blocks() {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::CodeBlocks,
                    limit: limits.maximum_code_blocks(),
                    actual: total_blocks,
                });
            }
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_account_plan_blocks, 1); }
    if selected && total_blocks > limits.maximum_code_blocks() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: total_blocks,
        });
    }
    Ok((total_packets, total_precincts, total_blocks))
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_planned_decode_result(progression_plan_view(&plan),codestream::tile_parts_owned_view(tile_parts@),
            codestream::tile_part_owned_view(first),size,standard,crate::packet::packet_selection_view(maximum_resolution_counts),
            limits,prepared_components_view(prepared@),mct_work,decoded_tile_components_outcome(result)),
        decoded_tile_components_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        decoded_tile_components_outcome(result) == crate::specs::part2_decode_planned_tile_components(
        progression_plan_view(&plan), tile_parts@, first, size, standard,
        crate::packet::packet_selection_view(maximum_resolution_counts), limits, prepared_components_view(prepared@), mct_work,
    ),
))]
pub(crate) fn decode_planned_tile_components(
    plan: ProgressionTilePlan,
    tile_parts: &[TilePartPayload<'_>],
    first: &TilePartPayload<'_>,
    size: &ImageSize,
    standard: (bool, bool),
    maximum_resolution_counts: Option<&[u8]>,
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    mct_work: u64,
) -> Result<DecodedTileComponents, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(codestream::tile_part_owned_view);
        codestream::owned_extensions_registry_known(&first.part2_extensions);
        crate::specs::part2_planned_decode_normal(progression_plan_view(&plan),codestream::tile_parts_owned_view(tile_parts@),
            codestream::tile_part_owned_view(first),size,standard,crate::packet::packet_selection_view(maximum_resolution_counts),
            limits,prepared_components_view(prepared@),mct_work);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = progression_plan_view(&plan);
        let ghost initial_prepared=prepared_components_view(prepared@);
        let ghost execution = crate::specs::part1_progression_tile_decode(
            tile_parts@, before.grid, before.precincts,
            crate::packet::packet_selection_view(maximum_resolution_counts), limits,
        );
    }
    let mut active = plan;
    let _decoded_packets;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(progression_plan_view); }
    {
        let precincts = active.precincts.as_mut_slice();
        #[cfg(verus_keep_ghost)]
        proof! { crate::packet::packet_precinct_vector_known_fields(precincts); }
        let packets = match maximum_resolution_counts {
            None => crate::packet::decode_progression_tile_packets(
                tile_parts,
                &active.grid,
                precincts,
                limits,
            ),
            Some(counts) => crate::packet::decode_progression_tile_packets_selected(
                tile_parts,
                &active.grid,
                precincts,
                Some(counts),
                limits,
            ),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            if maximum_resolution_counts.is_none() {
                crate::specs::part2_packet_public_result_equivalent(tile_parts@,before.grid,before.precincts,None,limits);
            }
            if let Err(error)=packets {
                crate::specs::part2_planned_decode_packet_error(before,codestream::tile_parts_owned_view(tile_parts@),
                    codestream::tile_part_owned_view(first),size,standard,crate::packet::packet_selection_view(maximum_resolution_counts),
                    limits,prepared_components_view(prepared@),mct_work,error,crate::packet::packet_precinct_vector_view(precincts));
            }
        }
        _decoded_packets = packets?;
        #[cfg(verus_keep_ghost)]
        proof! { crate::packet::packet_precinct_vector_known_fields(precincts); }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        planning_precinct_planes_known_fields(active.precincts@);
        reveal(planned_components_view);
        assert(planning_precincts_view(active.precincts@) == execution.1);
        assert(execution.0.is_ok());
        assert(planned_components_view(&active) =~= before.components);
        assert(prepare_precincts_view(active.precincts@) == crate::specs::part2_precinct_decoder_planes(execution.1));
    }
    let mut components = prepared;
    let mut work = mct_work;
    let reconstructed = reconstruct_planned_tile(
        &active,
        first,
        size,
        standard,
        limits,
        &mut components,
        &mut work,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=reconstructed{crate::specs::part2_planned_extraction_error(before,codestream::tile_parts_owned_view(tile_parts@),codestream::tile_part_owned_view(first),
    size,standard,crate::packet::packet_selection_view(maximum_resolution_counts),limits,initial_prepared,mct_work,_decoded_packets,
    planning_precincts_view(active.precincts@),prepared_components_view(components@),work,error);}}
    reconstructed?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(decoded_tile_components_view); }
    Ok(DecodedTileComponents {
        prepared: components,
        mct_work: work,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_layout_decode_result(codestream::decoder_layout_input_view(layout),None,limits,crate::image::decoded_image_outcome(result)),
        crate::image::decoded_image_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        crate::image::decoded_image_outcome(result) == crate::specs::part2_decode_layout(layout, limits),
))]
pub(super) fn decode_layout(
    layout: &CodestreamLayout<'_>,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part2_decode_layout(layout, limits);
        let ghost source = codestream::decoder_layout_input_view(layout);
        let ghost prefix: Seq<crate::specs::Part2JpipSnapshotEvent> = Seq::empty();
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        super::decoder_execution_inputs_known(layout);
        crate::specs::part2_layout_decode_normal(source,None,limits);
    }
    validate_part2_execution(layout)?;
    let tile_count = layout.info.image_size.tile_count()?;
    if tile_count > u64::from(u16::MAX) + 1 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidImageGeometry,
        });
    }
    let mut prepared = Vec::new();
    let mut total_packets = 0_u64;
    let mut total_precincts = 0_u64;
    let mut total_code_blocks = 0_u64;
    let mut total_mct_work = 0_u64;
    let mut tile = 0_u64;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(prepared_components_view(prepared@) =~= Seq::empty());
        reveal(layout_accumulation_view);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant tile <= tile_count,
                tile_count <= u16::MAX as u64 + 1,
                source==codestream::decoder_layout_input_view(layout),
                crate::specs::part2_layout_decode_result(source,None,limits,goal),
                forall|tail:Seq<crate::specs::Part2JpipSnapshotEvent>|
                    crate::specs::part2_layout_decode_run(source,None,limits,prefix+tail)
                        ==crate::specs::part2_full_decode_run(&source.size,source.parts,source.capabilities,limits,tile_count,tile,
                            layout_accumulation_view(prepared@,(total_packets,total_precincts,total_code_blocks),total_mct_work),tail),
                goal == crate::specs::part2_decode_layout(layout, limits),
                goal == crate::specs::part2_full_layout_tiles(
                    &layout.info.image_size, codestream::tile_parts_owned_view(layout.tile_parts@),
                    codestream::codestream_profile_capabilities(&layout.info.profile), limits, tile_count, tile,
                    layout_accumulation_view(prepared@, (total_packets, total_precincts, total_code_blocks), total_mct_work),
                ),
            decreases tile_count - tile,
        )
    )]
    while tile < tile_count {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof! { codestream::decoder_layout_input_fields(layout); reveal_with_fuel(crate::specs::part2_full_layout_tiles, 1); reveal(layout_accumulation_view); }
        let tile_index = match u16::try_from(tile) {
            Ok(index) => index,
            Err(_) => return Err(arithmetic_overflow()),
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before=layout_accumulation_view(prepared@,(total_packets,total_precincts,total_code_blocks),total_mct_work);
            let ghost root=|events|crate::specs::part2_layout_decode_run(source,None,limits,events);
            let ghost next_tile=|after:crate::specs::Part2DecodedLayoutTile,rest|
                crate::specs::part2_full_decode_run(&source.size,source.parts,source.capabilities,limits,tile_count,(tile+1) as u64,after,rest);
            let ghost after_parts=|selected:Seq<crate::specs::Part2OwnedTilePart>,rest|
                crate::specs::part2_jpip_snapshot_bind(
                    crate::specs::part2_tile_decode_run(&source.size,tile_index,selected,source.capabilities,None,limits,
                        before.prepared,before.counters,before.mct_work,rest),next_tile);
        }
        let collected = select_tile_parts(&layout.tile_parts, tile_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            let child=|events|crate::specs::part2_select_tile_parts_run(source.parts,tile_index,events);
            crate::specs::part2_full_decode_step(&source.size,source.parts,source.capabilities,limits,tile_count,tile,before);
            assert forall|tail|root(prefix+tail)==crate::specs::part2_jpip_snapshot_bind(child(tail),after_parts) by {
                assert(root(prefix+tail)==crate::specs::part2_full_decode_run(&source.size,source.parts,source.capabilities,
                    limits,tile_count,tile,before,tail));
            }
            match selected_tile_parts_outcome(collected) {
                Err(error)=>{
                    crate::specs::part2_decode_prefix_error(root,child,after_parts,prefix,error);
                    reveal(crate::specs::part2_layout_decode_result);
                },
                Ok(selected)=>{prefix=crate::specs::part2_decode_prefix_advance(root,child,after_parts,prefix,selected);},
            }
        }
        let tile_parts = collected?;
        let tile_parts = tile_parts.as_slice();
        let decoded_result = decode_tile_parts_at(
            &layout.info.image_size,
            tile_index,
            tile_parts,
            &layout.info.profile,
            None,
            limits,
            prepared,
            (total_packets, total_precincts, total_code_blocks),
            total_mct_work,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_tile_decode_result);
            let child=|events|crate::specs::part2_tile_decode_run(&source.size,tile_index,codestream::tile_parts_owned_view(tile_parts@),
                source.capabilities,None,limits,before.prepared,before.counters,before.mct_work,events);
            let next=next_tile;
            assert forall|tail|root(prefix+tail)==crate::specs::part2_jpip_snapshot_bind(child(tail),next) by {
                assert(root(prefix+tail)==after_parts(codestream::tile_parts_owned_view(tile_parts@),tail));
            }
            match decoded_layout_tile_outcome(decoded_result) {
                Err(error)=>{
                    crate::specs::part2_decode_prefix_error(root,child,next,prefix,error);
                    reveal(crate::specs::part2_layout_decode_result);
                },
                Ok(after)=>{prefix=crate::specs::part2_decode_prefix_advance(root,child,next,prefix,after);},
            }
        }
        let decoded = decoded_result?;
        prepared = decoded.prepared;
        total_packets = decoded.counters.0;
        total_precincts = decoded.counters.1;
        total_code_blocks = decoded.counters.2;
        total_mct_work = decoded.mct_work;
        tile = tile.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_full_layout_tiles, 1); reveal(layout_accumulation_view); }
    let assembled = assemble_prepared_components(&layout.info.image_size, &prepared, None, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_full_decode_run,1);
        reveal(crate::specs::part2_layout_decode_result);
        let root=|events|crate::specs::part2_layout_decode_run(source,None,limits,events);
        let child=|events|crate::specs::part2_assemble_prepared_storage_run(crate::image::assembly_size_view(&layout.info.image_size),
            prepared_components_view(prepared@),None,crate::limits::resource_decoded_bytes_limit(limits),events);
        crate::specs::part2_decode_eta(child,crate::image::decoded_image_outcome(assembled));
        assert(source.size==layout.info.image_size);
        assert forall|events|root(prefix+events)==child(events) by {
            assert(crate::specs::part2_layout_decode_run(source,None,limits,prefix+events)
                ==crate::specs::part2_full_decode_run(&source.size,source.parts,source.capabilities,limits,tile_count,tile,
                    layout_accumulation_view(prepared@,(total_packets,total_precincts,total_code_blocks),total_mct_work),events));
        }
        crate::specs::part2_cold_prefix_result(root,child,prefix,crate::image::decoded_image_outcome(assembled));
    }
    assembled
}
