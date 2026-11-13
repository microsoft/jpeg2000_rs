//! Caller-planned and automatic progressive decoding and cache snapshots.

use super::{
    AutomaticHeaders, AutomaticPacket, AutomaticSnapshot, AutomaticSnapshotResult, AutomaticTile,
    DatabinCache, DatabinId, DecodeError, EOC, JpipAutomaticProgressiveDecoder, JpipByteView,
    JpipMissingRange, JpipPacketSelection, JpipPrecinctCodestreamPlan, JpipProgressiveDecoder,
    JpipProgressiveStatus, JpipProgressiveUpdate, MalformedKind, Resource, ResourceLimits,
    append_empty_packet, automatic_precinct_in_class, build_automatic_transition_template,
    copy_bytes, jpip_resolution_selected, jpip_tile_selected, normalize_automatic_tile_headers,
    normalize_main_header, parse_tile_part_transitions, partition_automatic_tile_parts,
    siz_cardinality, validate_packet_component_selection, write_u32_be,
};
#[cfg(verus_keep_ghost)]
use super::{
    jpip_cache_view, jpip_optional_image_borrow_view, jpip_optional_image_view,
    jpip_parsed_packet_matrix, jpip_parsed_packet_matrix_update, jpip_parsed_packet_row_update,
    jpip_parsed_packet_value, jpip_plan_view, jpip_progressive_decoder_view,
    jpip_progressive_image_borrow, jpip_progressive_image_owner, jpip_progressive_outcome,
    jpip_progressive_plan_owner, jpip_progressive_update_view, jpip_transcode_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(test)]
#[path = "progressive_result_tests.rs"]
mod result_tests;

impl JpipProgressiveUpdate {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_progressive_update_view(self).0,))]
    pub const fn status(&self) -> JpipProgressiveStatus {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_update_view); }
        self.status
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_progressive_update_view(self).1,))]
    pub const fn previous_layers(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_update_view); }
        self.previous_layers
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_progressive_update_view(self).2,))]
    pub const fn available_layers(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_update_view); }
        self.available_layers
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@.map_values(|range: JpipMissingRange| super::jpip_missing_view(range))
            == jpip_progressive_update_view(self).3,
    ))]
    pub fn missing_ranges(&self) -> &[JpipMissingRange] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_update_view); }
        &self.missing
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_optional_image_borrow_view(result) == jpip_progressive_update_view(self).4,
            result == jpip_progressive_image_borrow(self),
    ))]
    pub const fn image(&self) -> Option<&crate::image::TypedImage> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_update_view); reveal(jpip_progressive_image_borrow); }
        self.image.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_optional_image_view(result) == jpip_progressive_update_view(&self).4,
            result == *jpip_progressive_image_owner(&self),
    ))]
    pub fn into_image(self) -> Option<crate::image::TypedImage> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_update_view); reveal(jpip_progressive_image_owner); }
        self.image
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipProgressiveDecoder {
    pub const fn new(plan: JpipPrecinctCodestreamPlan) -> Self {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Self| {
            vstd::prelude::equal(
                jpip_progressive_decoder_view(&result),
                (jpip_plan_view(&plan), 0_u16),
            ) && vstd::prelude::equal(*jpip_progressive_plan_owner(&result), plan)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_decoder_view); reveal(jpip_progressive_plan_owner); }
        Self {
            plan,
            decoded_layers: 0,
        }
    }

    pub const fn plan(&self) -> &JpipPrecinctCodestreamPlan {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: &JpipPrecinctCodestreamPlan| {
            vstd::prelude::equal(
                jpip_plan_view(result),
                jpip_progressive_decoder_view(self).0,
            ) && vstd::prelude::equal(result, jpip_progressive_plan_owner(self))
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_decoder_view); reveal(jpip_progressive_plan_owner); }
        &self.plan
    }

    pub const fn decoded_layers(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u16| {
            vstd::prelude::equal(result, jpip_progressive_decoder_view(self).1)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_progressive_decoder_view); }
        self.decoded_layers
    }
}

impl JpipProgressiveDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (jpip_progressive_outcome(result), jpip_progressive_decoder_view(final(self)))
            == crate::specs::part2_jpip_progressive_update(jpip_cache_view(cache),
                jpip_progressive_decoder_view(old(self)), options, None),
            jpip_progressive_plan_owner(final(self)) == jpip_progressive_plan_owner(old(self)),
    ))]
    pub fn update(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        self.update_inner(cache, options, None)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (jpip_progressive_outcome(result), jpip_progressive_decoder_view(final(self)))
            == crate::specs::part2_jpip_progressive_update(jpip_cache_view(cache),
                jpip_progressive_decoder_view(old(self)), options, Some(selection)),
            jpip_progressive_plan_owner(final(self)) == jpip_progressive_plan_owner(old(self)),
    ))]
    pub fn update_selected(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
        selection: &crate::DecodeSelection,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        self.update_inner(cache, options, Some(selection))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (jpip_progressive_outcome(result), jpip_progressive_decoder_view(final(self)))
            == crate::specs::part2_jpip_progressive_update(jpip_cache_view(cache),
                jpip_progressive_decoder_view(old(self)), options, selection),
            jpip_progressive_plan_owner(final(self)) == jpip_progressive_plan_owner(old(self)),
    ))]
    fn update_inner(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
        selection: Option<&crate::DecodeSelection>,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(jpip_progressive_decoder_view); reveal(jpip_progressive_plan_owner);
            reveal(jpip_progressive_update_view); reveal(jpip_transcode_view);
        }
        let previous_layers = self.decoded_layers;
        let (available_layers, missing) = cache.progressive_availability(&self.plan)?;
        if !crate::refinement::jpip_progressive_update_valid(
            previous_layers,
            available_layers,
            self.plan.layers(),
        ) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        if !crate::refinement::jpip_quality_prefix_available(available_layers, previous_layers)
            || available_layers <= previous_layers
        {
            return Ok(JpipProgressiveUpdate {
                status: if available_layers == self.plan.layers() {
                    JpipProgressiveStatus::Complete
                } else {
                    JpipProgressiveStatus::WaitingForData
                },
                previous_layers,
                available_layers,
                missing,
                image: None,
            });
        }
        let transcoded = cache.transcode_precinct_codestream(&self.plan, available_layers)?;
        let view = transcoded
            .codestream
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure),
                ))]
                || DecodeError::malformed(0, MalformedKind::MissingRequiredStructure),
            )?;
        let image = match selection {
            Some(selection) => {
                crate::decode_codestream_selected(view.as_ref(), options, selection)?
            }
            None => crate::decode_codestream(view.as_ref(), options)?,
        };
        self.decoded_layers = available_layers;
        Ok(JpipProgressiveUpdate {
            status: if available_layers == self.plan.layers() {
                JpipProgressiveStatus::Complete
            } else {
                JpipProgressiveStatus::QualityAdvanced
            },
            previous_layers,
            available_layers,
            missing,
            image: Some(image),
        })
    }
}

impl JpipAutomaticProgressiveDecoder {
    pub const fn new(codestream: u64) -> Self {
        Self {
            codestream,
            decoded_layers: 0,
        }
    }

    pub const fn codestream(&self) -> u64 {
        self.codestream
    }

    pub const fn decoded_layers(&self) -> u16 {
        self.decoded_layers
    }

    pub fn update(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        self.update_inner(cache, options, None, &JpipPacketSelection::all_components())
    }

    pub fn update_selected(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
        selection: &crate::DecodeSelection,
        packets: &JpipPacketSelection,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        self.update_inner(cache, options, Some(selection), packets)
    }

    fn update_inner(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
        selection: Option<&crate::DecodeSelection>,
        packets: &JpipPacketSelection,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        let previous_layers = self.decoded_layers;
        let result = cache.build_automatic_snapshot(
            self.codestream,
            selection,
            packets,
            options.limits(),
        )?;
        let Some(snapshot) = result.ready else {
            return Ok(JpipProgressiveUpdate {
                status: JpipProgressiveStatus::WaitingForData,
                previous_layers,
                available_layers: 0,
                missing: result.missing,
                image: None,
            });
        };
        if !crate::refinement::jpip_progressive_update_valid(
            previous_layers,
            snapshot.available_layers,
            snapshot.layers,
        ) {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        if !crate::refinement::jpip_quality_prefix_available(
            snapshot.available_layers,
            previous_layers,
        ) || snapshot.available_layers <= previous_layers
        {
            return Ok(JpipProgressiveUpdate {
                status: if snapshot.available_layers == snapshot.layers {
                    JpipProgressiveStatus::Complete
                } else {
                    JpipProgressiveStatus::WaitingForData
                },
                previous_layers,
                available_layers: snapshot.available_layers,
                missing: snapshot.missing,
                image: None,
            });
        }
        let image = match selection {
            Some(selection) => {
                crate::decode_codestream_selected(snapshot.codestream.as_ref(), options, selection)?
            }
            None => crate::decode_codestream(snapshot.codestream.as_ref(), options)?,
        };
        self.decoded_layers = snapshot.available_layers;
        Ok(JpipProgressiveUpdate {
            status: if snapshot.available_layers == snapshot.layers {
                JpipProgressiveStatus::Complete
            } else {
                JpipProgressiveStatus::QualityAdvanced
            },
            previous_layers,
            available_layers: snapshot.available_layers,
            missing: snapshot.missing,
            image: Some(image),
        })
    }
}

impl DatabinCache {
    #[allow(clippy::manual_map)]
    pub(super) fn build_automatic_snapshot(
        &self,
        codestream: u64,
        selection: Option<&crate::DecodeSelection>,
        packet_selection: &JpipPacketSelection,
        limits: &ResourceLimits,
    ) -> Result<AutomaticSnapshotResult, DecodeError> {
        let main_id = DatabinId::new(6, codestream, 0)?;
        if !self.is_complete(main_id) {
            return Ok(AutomaticSnapshotResult {
                ready: None,
                missing: self.complete_databin_missing(main_id),
            });
        }
        let main = self.databin_view(main_id)?.into_bytes();
        let (tile_count, components) = siz_cardinality(&main, limits)?;
        validate_packet_component_selection(packet_selection, components)?;
        let mut tile_headers = crate::allocation::empty_with_capacity(
            usize::try_from(tile_count)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        )?;
        let mut header_missing = Vec::new();
        let mut tile = 0_u64;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile <= tile_count,
                decreases tile_count - tile,
            )
        )]
        while tile < tile_count {
            let tile_id = DatabinId::new(2, codestream, tile)?;
            if self.is_complete(tile_id) {
                tile_headers.push(self.databin_view(tile_id)?.into_bytes());
            } else {
                let additional = self.complete_databin_missing(tile_id);
                let mut missing_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant missing_index <= additional.len(),
                        decreases additional.len() - missing_index,
                    )
                )]
                while missing_index < additional.len() {
                    header_missing.push(additional[missing_index]);
                    missing_index += 1;
                }
            }
            tile = tile
                .checked_add(1)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        }
        if !header_missing.is_empty() {
            return Ok(AutomaticSnapshotResult {
                ready: None,
                missing: header_missing,
            });
        }

        let normalized_main = normalize_main_header(&main)?;
        let mut normalized_tiles = crate::allocation::empty_with_capacity(tile_headers.len())?;
        let mut tile_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_index <= tile_headers.len(),
                decreases tile_headers.len() - tile_index,
            )
        )]
        while tile_index < tile_headers.len() {
            normalized_tiles.push(normalize_automatic_tile_headers(
                tile_headers
                    .get(tile_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
                u16::try_from(tile_index)
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            )?);
            tile_index += 1;
        }
        let template =
            build_automatic_transition_template(&normalized_main, &normalized_tiles, limits)?;
        let layout = crate::codestream::parse_layout(&template, limits)?;
        let mut automatic_tiles = crate::allocation::empty_with_capacity(normalized_tiles.len())?;
        let mut maximum_layers = 0_u16;
        tile_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_index <= normalized_tiles.len(),
                decreases normalized_tiles.len() - tile_index,
            )
        )]
        while tile_index < normalized_tiles.len() {
            let tile_number = u16::try_from(tile_index)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            let tile_parts_iterator = layout
                .tile_parts
                .iter()
                .filter(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
                        ensures result == (crate::codestream::tile_part_owned_view(*part).tile_index == tile_number),
                    ))]
                    |part| part.tile_index == tile_number,
                );
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost filtered = tile_parts_iterator;
                let ghost source = vstd::std_specs::iter::filter_iter(filtered);
                let ghost keep = vstd::std_specs::iter::filter_keep(filtered);
            }
            let tile_parts: Vec<_> = tile_parts_iterator.collect();
            #[cfg(verus_keep_ghost)]
            proof! {
                use vstd::std_specs::iter::IteratorSpec;
                broadcast use vstd::std_specs::iter::group_iter_axioms;
                assert(filtered.will_return_none());
                assert(keep.len() == layout.tile_parts.len());
                assert(tile_parts@ == filtered.remaining());
                assert(source.remaining().subrange(0, keep.len() as int) =~= source.remaining());
                assert(filtered.remaining()
                    == source.remaining().subrange(0, keep.len() as int).filter_index(|index: int| keep[index]));
                assert(tile_parts@ == source.remaining().filter_index(|index: int| keep[index]));
                let project = |part: &crate::codestream::TilePartPayload<'_>|
                    crate::codestream::tile_part_owned_view(part);
                let predicate = |part: crate::specs::Part2OwnedTilePart| part.tile_index == tile_number;
                assert(source.remaining().map_values(|part: &crate::codestream::TilePartPayload<'_>|
                    crate::codestream::tile_part_owned_view(part))
                    =~= crate::codestream::tile_parts_owned_view(layout.tile_parts@));
                assert forall|index: int| 0 <= index < source.remaining().len()
                    implies keep[index] == (crate::codestream::tile_part_owned_view(
                        #[trigger] source.remaining()[index]).tile_index == tile_number) by {
                }
                super::jpip_filter_projection(source.remaining(), keep, project, predicate);
                assert(tile_parts@.map_values(project) == source.remaining().map_values(project).filter(predicate));
                assert(tile_parts@.map_values(project)
                    == crate::codestream::tile_parts_owned_view(layout.tile_parts@).filter(predicate));
            }
            let tile_part = *tile_parts
                .first()
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?;
            let mut plan = crate::decode::plan_progression_tile_at_with_component_overrides(
                &layout.info.image_size,
                tile_number,
                tile_part.coding_style,
                &tile_part.component_coding_styles,
                &tile_part.component_quantizations,
                &tile_part.roi_shifts,
                limits,
            )?;
            maximum_layers = maximum_layers.max(tile_part.coding_style.layers);
            let precinct_count = plan.precincts().len();
            let layer_count = usize::from(tile_part.coding_style.layers);
            let mut ordinals = vec![vec![None; layer_count]; precinct_count];
            let mut order = Vec::new();
            let mut iterator = crate::packet::ProgressionPacketIterator::new(
                plan.grid(),
                tile_part.coding_style.progression_order,
                &tile_part.progression_changes,
                limits,
            )?;
            let progression_code = match tile_part.coding_style.progression_order {
                crate::codestream::ProgressionOrder::Lrcp => 0,
                crate::codestream::ProgressionOrder::Rlcp => 1,
                crate::codestream::ProgressionOrder::Rpcl => 2,
                crate::codestream::ProgressionOrder::Pcrl => 3,
                crate::codestream::ProgressionOrder::Cprl => 4,
            };
            if !crate::refinement::jpip_progression_supported(progression_code) {
                return Err(DecodeError::malformed(
                    0,
                    MalformedKind::InvalidProgressionOrderChange,
                ));
            }
            let mut ordinal = 0_u64;
            let mut remaining_packets = limits.maximum_work_units();
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(decreases remaining_packets,)
            )]
            while let Some(coordinate) = iterator.next_packet()? {
                if remaining_packets == 0 {
                    return Err(DecodeError::malformed(
                        0,
                        MalformedKind::InvalidProgressionOrderChange,
                    ));
                }
                remaining_packets -= 1;
                let execution = plan.grid().precinct_index(
                    coordinate.component,
                    coordinate.resolution,
                    coordinate.precinct,
                )?;
                let sequence = u16::try_from(ordinal & u64::from(u16::MAX))
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost before_ordinals = ordinals@.map_values(|row: Vec<Option<u16>>| row@);
                }
                let layer_slot = match ordinals.get_mut(execution) {
                    Some(layers) => layers.get_mut(usize::from(coordinate.layer)),
                    None => None,
                }
                .ok_or_else(|| {
                    DecodeError::malformed(0, MalformedKind::InvalidProgressionOrderChange)
                })?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert((execution as nat) < before_ordinals.len());
                    assert((coordinate.layer as nat) < before_ordinals[execution as int].len());
                    assert(*layer_slot == before_ordinals[execution as int][coordinate.layer as int]);
                }
                if layer_slot.is_some() {
                    return Err(DecodeError::malformed(
                        0,
                        MalformedKind::InvalidProgressionOrderChange,
                    ));
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(before_ordinals[execution as int][coordinate.layer as int].is_none());
                }
                *layer_slot = Some(sequence);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(ordinals@.map_values(|row: Vec<Option<u16>>| row@)
                        == before_ordinals.update(execution as int,
                            before_ordinals[execution as int].update(coordinate.layer as int, Some(sequence))));
                    assert(crate::specs::part2_jpip_ordinal_matrix_write(before_ordinals,
                        ordinals@.map_values(|row: Vec<Option<u16>>| row@),
                        execution, coordinate.layer, sequence));
                }
                order.push((coordinate, execution));
                ordinal = ordinal
                    .checked_add(1)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            }

            let mut parsed = vec![vec![None; layer_count]; precinct_count];
            let mut offsets = vec![0_u64; precinct_count];
            let mut databins = crate::allocation::empty_with_capacity(precinct_count)?;
            let grid = plan.grid();
            let mut mapping_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant mapping_index <= precinct_count,
                    decreases precinct_count - mapping_index,
                )
            )]
            while mapping_index < precinct_count {
                let (component, resolution, precinct) = plan
                    .precincts()
                    .get(mapping_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
                    .coordinate();
                let in_class = automatic_precinct_in_class(
                    tile_count,
                    u64::from(components),
                    tile_index as u64,
                    component,
                    resolution,
                    precinct,
                    grid,
                )?;
                databins.push(DatabinId::new(0, codestream, in_class)?);
                mapping_index += 1;
            }
            let source_tile_header = tile_headers
                .get(tile_index)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            let transitions = parse_tile_part_transitions(source_tile_header, tile_number)?;
            let mut transition_index = 0_usize;
            let mut transition_packets = 0_u64;
            let mut transition_bytes = 0_u64;
            let mut blocked = vec![false; precinct_count];
            let mut order_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant order_index <= order.len(),
                    decreases order.len() - order_index,
                )
            )]
            while order_index < order.len() {
                let (coordinate, execution) = order[order_index];
                if *blocked
                    .get(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
                {
                    order_index += 1;
                    continue;
                }
                let state = *tile_parts
                    .get(transition_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?;
                let databin = *databins
                    .get(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let prefix = self.databin_prefix(databin);
                let offset = *offsets
                    .get(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let start = usize::try_from(offset)
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                if start >= prefix.len() {
                    *blocked.get_mut(execution).ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })? = true;
                    order_index += 1;
                    continue;
                }
                let sequence = u16::try_from(order_index & usize::from(u16::MAX))
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let precinct_decoder = plan
                    .precincts_mut()
                    .get_mut(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                match crate::packet::decode_jpip_precinct_packet(
                    state,
                    &prefix[start..],
                    sequence,
                    coordinate.layer,
                    precinct_decoder,
                    limits,
                ) {
                    Ok(consumed) => {
                        if consumed == 0 {
                            return Err(DecodeError::malformed(
                                offset,
                                MalformedKind::InvalidPacketLength,
                            ));
                        }
                        let end = start.checked_add(consumed).ok_or_else(|| {
                            DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow)
                        })?;
                        let packet_slice = prefix.get(start..end).ok_or_else(|| {
                            DecodeError::malformed(offset, MalformedKind::Truncated)
                        })?;
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost before_native = parsed@;
                            let ghost before_parsed = jpip_parsed_packet_matrix(parsed@);
                        }
                        *(match parsed.get_mut(execution) {
                            Some(layers) => layers.get_mut(usize::from(coordinate.layer)),
                            None => None,
                        })
                        .ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                        })? = Some(copy_bytes(packet_slice));
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert((execution as nat) < before_parsed.len());
                            assert((coordinate.layer as nat) < before_parsed[execution as int].len());
                            assert(parsed@ =~= before_native.update(execution as int, parsed@[execution as int]));
                            assert(parsed@[execution as int]@ =~= before_native[execution as int]@.update(
                                coordinate.layer as int, parsed@[execution as int]@[coordinate.layer as int]));
                            assert(jpip_parsed_packet_value(
                                parsed@[execution as int]@[coordinate.layer as int]) == Some(packet_slice@));
                            jpip_parsed_packet_matrix_update(before_native, execution as int, parsed@[execution as int]);
                            jpip_parsed_packet_row_update(before_native[execution as int], parsed@[execution as int],
                                coordinate.layer as int, parsed@[execution as int]@[coordinate.layer as int]);
                            assert(jpip_parsed_packet_matrix(parsed@) == before_parsed.update(
                                execution as int, before_parsed[execution as int].update(
                                    coordinate.layer as int, Some(packet_slice@))));
                            assert(crate::specs::part2_jpip_packet_matrix_write(
                                before_parsed, jpip_parsed_packet_matrix(parsed@),
                                execution, coordinate.layer, packet_slice@));
                        }
                        *offsets.get_mut(execution).ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                        })? = end as u64;
                        transition_packets =
                            transition_packets.checked_add(1).ok_or_else(|| {
                                DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                            })?;
                        transition_bytes = transition_bytes
                            .checked_add(consumed as u64)
                            .ok_or_else(|| {
                                DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                            })?;
                        let transition = transitions.get(transition_index).ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidTilePart)
                        })?;
                        let boundary = match transition.packet_count() {
                            Some(count) => transition_packets == count,
                            None => match transition.data_length() {
                                Some(length) => transition_bytes == length,
                                None => false,
                            },
                        };
                        let next_transition = transition_index.checked_add(1).ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                        })?;
                        if boundary && next_transition < transitions.len() {
                            transition_index = next_transition;
                            transition_packets = 0;
                            transition_bytes = 0;
                        }
                    }
                    Err(DecodeError::MalformedInput {
                        kind: MalformedKind::Truncated,
                        ..
                    }) if !self.is_complete(databin) => {
                        *blocked.get_mut(execution).ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                        })? = true;
                    }
                    Err(error) => return Err(error),
                }
                order_index += 1;
            }

            let tile_is_selected = jpip_tile_selected(selection, tile_number);
            let mut packets = crate::allocation::empty_with_capacity(order.len())?;
            let mut order_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant order_index <= order.len(),
                    decreases order.len() - order_index,
                )
            )]
            while order_index < order.len() {
                let (coordinate, execution) = order[order_index];
                let required = tile_is_selected
                    && packet_selection.includes_component(coordinate.component)
                    && jpip_resolution_selected(
                        selection,
                        coordinate.component,
                        coordinate.resolution,
                        &tile_part.component_coding_styles,
                    )?;
                let parsed_layers = parsed
                    .get(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let packet_bytes = match parsed_layers
                    .get(usize::from(coordinate.layer))
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
                {
                    Some(bytes) => Some(bytes.clone()),
                    None => None,
                };
                packets.push(AutomaticPacket {
                    databin: *databins.get(execution).ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })?,
                    bytes: packet_bytes,
                    next_offset: *offsets.get(execution).ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })?,
                    required,
                    ordinal: u16::try_from(order_index & usize::from(u16::MAX)).map_err(|_| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })?,
                    layer: coordinate.layer,
                });
                order_index += 1;
            }
            let Some(parts) = partition_automatic_tile_parts(
                normalized_tiles
                    .get(tile_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
                &tile_parts,
                &transitions,
                &packets,
            )?
            else {
                let mut missing = Vec::new();
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= packets.len(),
                        decreases packets.len() - packet_index,
                    )
                )]
                while packet_index < packets.len() {
                    let packet = packets.get(packet_index).ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })?;
                    if packet.bytes.is_none()
                        && !missing
                            .iter()
                            .any(|entry: &JpipMissingRange| entry.databin().same_as(packet.databin))
                    {
                        missing.push(JpipMissingRange {
                            databin: packet.databin,
                            offset: packet.next_offset,
                            length: self
                                .status(packet.databin)
                                .and_then(|status| status.final_length())
                                .map(|length| length.saturating_sub(packet.next_offset)),
                        });
                    }
                    packet_index += 1;
                }
                return Ok(AutomaticSnapshotResult {
                    ready: None,
                    missing,
                });
            };
            automatic_tiles.push(AutomaticTile { parts });
            tile_index += 1;
        }

        let mut available_layers = maximum_layers;
        let mut tile_packet_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_packet_index <= automatic_tiles.len(),
                decreases automatic_tiles.len() - tile_packet_index,
            )
        )]
        while tile_packet_index < automatic_tiles.len() {
            let tile = &automatic_tiles[tile_packet_index];
            let mut part_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part_index <= tile.parts.len(),
                    decreases tile.parts.len() - part_index,
                )
            )]
            while part_index < tile.parts.len() {
                let part = &tile.parts[part_index];
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= part.packets.len(),
                        decreases part.packets.len() - packet_index,
                    )
                )]
                while packet_index < part.packets.len() {
                    let packet = &part.packets[packet_index];
                    let layer = packet.layer;
                    if packet.required && packet.bytes.is_none() {
                        available_layers = available_layers.min(layer);
                    }
                    packet_index += 1;
                }
                part_index += 1;
            }
            tile_packet_index += 1;
        }
        let mut missing = Vec::new();
        tile_packet_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_packet_index <= automatic_tiles.len(),
                decreases automatic_tiles.len() - tile_packet_index,
            )
        )]
        while tile_packet_index < automatic_tiles.len() {
            let tile = &automatic_tiles[tile_packet_index];
            let mut part_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part_index <= tile.parts.len(),
                    decreases tile.parts.len() - part_index,
                )
            )]
            while part_index < tile.parts.len() {
                let part = &tile.parts[part_index];
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= part.packets.len(),
                        decreases part.packets.len() - packet_index,
                    )
                )]
                while packet_index < part.packets.len() {
                    let packet = &part.packets[packet_index];
                    let layer = packet.layer;
                    if packet.required
                        && layer == available_layers
                        && packet.bytes.is_none()
                        && !missing
                            .iter()
                            .any(|entry: &JpipMissingRange| entry.databin().same_as(packet.databin))
                    {
                        let status = self.status(packet.databin);
                        let length = match status.and_then(|value| value.final_length()) {
                            Some(final_length) if final_length > packet.next_offset => {
                                Some(final_length - packet.next_offset)
                            }
                            Some(_) => Some(1),
                            None => None,
                        };
                        missing.push(JpipMissingRange {
                            databin: packet.databin,
                            offset: packet.next_offset,
                            length,
                        });
                    }
                    packet_index += 1;
                }
                part_index += 1;
            }
            tile_packet_index += 1;
        }
        if available_layers == 0 {
            return Ok(AutomaticSnapshotResult {
                ready: Some(AutomaticSnapshot {
                    codestream: JpipByteView { bytes: Vec::new() },
                    available_layers,
                    layers: maximum_layers,
                    missing,
                }),
                missing: Vec::new(),
            });
        }

        let mut bytes = normalized_main;
        tile_packet_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_packet_index <= automatic_tiles.len(),
                decreases automatic_tiles.len() - tile_packet_index,
            )
        )]
        while tile_packet_index < automatic_tiles.len() {
            let tile = &automatic_tiles[tile_packet_index];
            let mut part_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part_index <= tile.parts.len(),
                    decreases tile.parts.len() - part_index,
                )
            )]
            while part_index < tile.parts.len() {
                let part = &tile.parts[part_index];
                let tile_start = bytes.len();
                bytes.extend_from_slice(&part.header);
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= part.packets.len(),
                        decreases part.packets.len() - packet_index,
                    )
                )]
                while packet_index < part.packets.len() {
                    let packet = &part.packets[packet_index];
                    let layer = packet.layer;
                    if packet.required && layer < available_layers {
                        let packet_bytes = packet.bytes.as_ref().ok_or_else(|| {
                            DecodeError::malformed(
                                packet.next_offset,
                                MalformedKind::MissingRequiredStructure,
                            )
                        })?;
                        bytes.extend_from_slice(packet_bytes);
                    } else {
                        append_empty_packet(&mut bytes, part.sop, part.eph, packet.ordinal)?;
                    }
                    packet_index += 1;
                }
                let tile_length = bytes
                    .len()
                    .checked_sub(tile_start)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let tile_length = u32::try_from(tile_length)
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                let length_position = tile_start
                    .checked_add(6)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                write_u32_be(&mut bytes, length_position, tile_length)?;
                part_index += 1;
            }
            tile_packet_index += 1;
        }
        bytes.extend_from_slice(&EOC);
        if bytes.len() as u64 > limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                limits.maximum_input_bytes(),
                bytes.len() as u64,
            ));
        }
        crate::codestream::parse_layout(&bytes, limits)?;
        Ok(AutomaticSnapshotResult {
            ready: Some(AutomaticSnapshot {
                codestream: JpipByteView { bytes },
                available_layers,
                layers: maximum_layers,
                missing,
            }),
            missing: Vec::new(),
        })
    }

    pub(super) fn automatic_headers(
        &self,
        codestream: u64,
    ) -> Result<AutomaticHeaders, DecodeError> {
        let main = self
            .databin_view(DatabinId::new(6, codestream, 0)?)?
            .into_bytes();
        let (tile_count, components) = siz_cardinality(&main, &self.limits)?;
        let mut tiles = crate::allocation::empty_with_capacity(
            usize::try_from(tile_count)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        )?;
        let mut tile = 0_u64;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile <= tile_count,
                decreases tile_count - tile,
            )
        )]
        while tile < tile_count {
            tiles.push(
                self.databin_view(DatabinId::new(2, codestream, tile)?)?
                    .into_bytes(),
            );
            tile += 1;
        }
        let main = normalize_main_header(&main)?;
        let mut normalized = crate::allocation::empty_with_capacity(tiles.len())?;
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= tiles.len(),
                decreases tiles.len() - index,
            )
        )]
        while index < tiles.len() {
            let headers = normalize_automatic_tile_headers(
                &tiles[index],
                u16::try_from(index)
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            )?;
            normalized.push(
                headers
                    .first()
                    .ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::MissingRequiredStructure)
                    })?
                    .clone(),
            );
            index += 1;
        }
        Ok(AutomaticHeaders {
            main,
            tiles: normalized,
            tile_count,
            components,
        })
    }
}
