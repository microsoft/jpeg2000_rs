//! Caller-planned and automatic progressive decoding and cache snapshots.

use super::{
    AutomaticHeaders, AutomaticPacket, AutomaticSnapshot, AutomaticSnapshotResult, AutomaticTile,
    DatabinCache, DatabinId, DecodeError, EOC, JpipAutomaticProgressiveDecoder, JpipByteView,
    JpipMissingRange, JpipPacketSelection, JpipPrecinctCodestreamPlan, JpipProgressiveDecoder,
    JpipProgressiveStatus, JpipProgressiveUpdate, MalformedKind, Resource, ResourceLimits,
    automatic_precinct_in_class, build_automatic_order, build_automatic_transition_template,
    copy_bytes, decode_automatic_precinct, emit_automatic_tile_part, jpip_resolution_selected,
    jpip_tile_selected, normalize_automatic_tile_headers, normalize_main_header,
    parse_tile_part_transitions, partition_automatic_tile_parts, siz_cardinality,
    validate_packet_component_selection,
};
#[cfg(verus_keep_ghost)]
use super::{
    jpip_automatic_headers_outcome, jpip_automatic_headers_view, jpip_automatic_headers_witness,
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

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipAutomaticProgressiveDecoder {
    pub const fn new(codestream: u64) -> Self {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Self| {
            vstd::prelude::equal(
                super::jpip_automatic_progressive_decoder_view(&result),
                (codestream, 0_u16),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(super::jpip_automatic_progressive_decoder_view); }
        Self {
            codestream,
            decoded_layers: 0,
        }
    }

    pub const fn codestream(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u64| {
            vstd::prelude::equal(
                result,
                super::jpip_automatic_progressive_decoder_view(self).0,
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(super::jpip_automatic_progressive_decoder_view); }
        self.codestream
    }

    pub const fn decoded_layers(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u16| {
            vstd::prelude::equal(
                result,
                super::jpip_automatic_progressive_decoder_view(self).1,
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(super::jpip_automatic_progressive_decoder_view); }
        self.decoded_layers
    }
}

impl JpipAutomaticProgressiveDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_automatic_progressive_update_result(jpip_cache_view(cache),
            super::jpip_automatic_progressive_decoder_view(old(self)), options, None, Seq::empty(),
            (jpip_progressive_outcome(result), super::jpip_automatic_progressive_decoder_view(final(self)), jpip_cache_view(cache))),
            super::jpip_automatic_progressive_decoder_view(final(self)).0
                == super::jpip_automatic_progressive_decoder_view(old(self)).0,
    ))]
    pub fn update(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        self.update_inner(cache, options, None, &JpipPacketSelection::all_components())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_automatic_progressive_update_result(jpip_cache_view(cache),
            super::jpip_automatic_progressive_decoder_view(old(self)), options, Some(selection),
            super::jpip_packet_selection_view(packets),
            (jpip_progressive_outcome(result), super::jpip_automatic_progressive_decoder_view(final(self)), jpip_cache_view(cache))),
            super::jpip_automatic_progressive_decoder_view(final(self)).0
                == super::jpip_automatic_progressive_decoder_view(old(self)).0,
    ))]
    pub fn update_selected(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
        selection: &crate::DecodeSelection,
        packets: &JpipPacketSelection,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        self.update_inner(cache, options, Some(selection), packets)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_automatic_progressive_update_result(jpip_cache_view(cache),
            super::jpip_automatic_progressive_decoder_view(old(self)), options, selection,
            super::jpip_packet_selection_view(packets),
            (jpip_progressive_outcome(result), super::jpip_automatic_progressive_decoder_view(final(self)), jpip_cache_view(cache))),
            super::jpip_automatic_progressive_decoder_view(final(self)).0
                == super::jpip_automatic_progressive_decoder_view(old(self)).0,
    ))]
    fn update_inner(
        &mut self,
        cache: &DatabinCache,
        options: &crate::DecodeOptions,
        selection: Option<&crate::DecodeSelection>,
        packets: &JpipPacketSelection,
    ) -> Result<JpipProgressiveUpdate, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::jpip_automatic_progressive_decoder_view);
            reveal(jpip_progressive_update_view);
            reveal(super::jpip_automatic_snapshot_result_view);
            reveal(super::jpip_automatic_snapshot_view);
            reveal(super::jpip_byte_view);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial_decoder = super::jpip_automatic_progressive_decoder_view(self);
            let ghost input = crate::specs::Part2JpipSnapshotInput {
                cache: jpip_cache_view(cache), stream: self.codestream,
                selected: super::jpip_snapshot_selection_view(selection),
                components: super::jpip_packet_selection_view(packets),
                limits: crate::options::decode_options_limits(options),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_automatic_snapshot_errors_known();
            super::jpip_automatic_update_errors_known();
            assert forall|error: DecodeError|
                #[trigger] crate::specs::part2_jpip_automatic_snapshot_result(input.cache, input.stream, input.selected,
                    input.components, input.limits, Err(error))
                implies crate::specs::part2_jpip_automatic_progressive_update_result(input.cache, initial_decoder,
                    options, selection, input.components, (Err(error), initial_decoder, input.cache)) by {
                super::jpip_automatic_snapshot_first_error(input.cache, initial_decoder, options, selection, input.components, error);
            }
            assert(initial_decoder == (self.codestream, self.decoded_layers));
            assert(input.stream == initial_decoder.0);
            assert(input.cache == jpip_cache_view(cache));
            assert(input.selected == super::jpip_snapshot_selection_view(selection));
            assert(input.components == super::jpip_packet_selection_view(packets));
            assert forall|error: DecodeError|
                #[trigger] crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(cache), self.codestream,
                    super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packets),
                    crate::options::decode_options_limits(options), Err(error))
                implies crate::specs::part2_jpip_automatic_progressive_update_result(jpip_cache_view(cache),
                    initial_decoder, options, selection, super::jpip_packet_selection_view(packets),
                    (jpip_progressive_outcome(Err(error)), super::jpip_automatic_progressive_decoder_view(self), jpip_cache_view(cache))) by {
                super::jpip_automatic_snapshot_first_error(jpip_cache_view(cache), initial_decoder,
                    options, selection, super::jpip_packet_selection_view(packets), error);
            }
        }
        let previous_layers = self.decoded_layers;
        let result = cache.build_automatic_snapshot(
            self.codestream,
            selection,
            packets,
            options.limits(),
        )?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_automatic_snapshot_result); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost snapshot_value = super::jpip_automatic_snapshot_result_view(&result);
            let ghost snapshot_events = choose|events: Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_jpip_snapshot_run(input, events) == Some((Ok(snapshot_value), Seq::empty()));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_jpip_automatic_progressive_run_unfold(input.cache, initial_decoder,
                options, selection, input.components, snapshot_events);
        }
        let Some(snapshot) = result.ready else {
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_automatic_progressive_witness(input.cache, initial_decoder, options, selection,
                    input.components, snapshot_events, (Ok((JpipProgressiveStatus::WaitingForData,
                        previous_layers, 0, super::jpip_missing_views(&result.missing), None)), initial_decoder, input.cache));
            }
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
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_automatic_progressive_witness(input.cache, initial_decoder, options, selection,
                    input.components, snapshot_events, (Err(crate::specs::part2_jpip_plan_invalid(0)), initial_decoder, input.cache));
            }
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        if !crate::refinement::jpip_quality_prefix_available(
            snapshot.available_layers,
            previous_layers,
        ) || snapshot.available_layers <= previous_layers
        {
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_automatic_progressive_witness(input.cache, initial_decoder, options, selection,
                    input.components, snapshot_events, (Ok((
                        if snapshot.available_layers == snapshot.layers { JpipProgressiveStatus::Complete }
                        else { JpipProgressiveStatus::WaitingForData },
                        previous_layers, snapshot.available_layers, super::jpip_missing_views(&snapshot.missing), None)),
                        initial_decoder, input.cache));
            }
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
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|error: DecodeError|
                crate::specs::part2_decode_raw_codestream(super::jpip_byte_view(&snapshot.codestream),
                    crate::options::decode_options_limits(options), selection) == Err(error)
                implies crate::specs::part2_jpip_automatic_progressive_update_result(input.cache, initial_decoder,
                    options, selection, input.components, (Err(error), initial_decoder, input.cache)) by {
                super::jpip_automatic_progressive_witness(input.cache, initial_decoder, options, selection,
                    input.components, snapshot_events, (Err(error), initial_decoder, input.cache));
            }
        }
        let image = match selection {
            Some(selection) => {
                crate::decode_codestream_selected(snapshot.codestream.as_ref(), options, selection)?
            }
            None => crate::decode_codestream(snapshot.codestream.as_ref(), options)?,
        };
        self.decoded_layers = snapshot.available_layers;
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_automatic_progressive_witness(input.cache, initial_decoder, options, selection,
                input.components, snapshot_events, (Ok((
                    if snapshot.available_layers == snapshot.layers { JpipProgressiveStatus::Complete }
                    else { JpipProgressiveStatus::QualityAdvanced },
                    previous_layers, snapshot.available_layers, super::jpip_missing_views(&snapshot.missing),
                    Some(crate::image::typed_image_value_view(image)))), (self.codestream, self.decoded_layers), input.cache));
        }
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
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
            super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
            limits, super::jpip_automatic_snapshot_outcome(result)),
    ))]
    pub(super) fn build_automatic_snapshot(
        &self,
        codestream: u64,
        selection: Option<&crate::DecodeSelection>,
        packet_selection: &JpipPacketSelection,
        limits: &ResourceLimits,
    ) -> Result<AutomaticSnapshotResult, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = crate::specs::Part2JpipSnapshotInput {
                cache: jpip_cache_view(self), stream: codestream,
                selected: super::jpip_snapshot_selection_view(selection),
                components: super::jpip_packet_selection_view(packet_selection), limits,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|error: DecodeError|
                crate::specs::part2_jpip_cache_complete(input.cache,
                    (6u64, super::DatabinClass::MainHeader, codestream, 0u64))
                    && crate::specs::part2_jpip_snapshot_admit(input) == Err(error)
                implies crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                    input.stream, input.selected, input.components, input.limits, Err(error)) by {
                super::jpip_snapshot_admission_error(input, error);
            }
        }
        let main_id = DatabinId::new(6, codestream, 0)?;
        if !self.is_complete(main_id) {
            #[cfg(verus_keep_ghost)]
            proof! { super::jpip_snapshot_main_waiting(input); }
            return Ok(AutomaticSnapshotResult {
                ready: None,
                missing: self.complete_databin_missing(main_id),
            });
        }
        let main = self.databin_view(main_id)?.into_bytes();
        let (tile_count, components) = siz_cardinality(&main, limits)?;
        validate_packet_component_selection(packet_selection, components)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            if tile_count <= usize::MAX as u64 {
                super::jpip_snapshot_header_capacity_error(input, main@, tile_count, components);
            }
        }
        let mut tile_headers =
            crate::allocation::empty_with_capacity(usize::try_from(tile_count).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(0),
                    ))]
                |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?)?;
        let mut header_missing = Vec::new();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost raw_main = main@;
            let ghost gather_goal = crate::specs::part2_jpip_snapshot_gather(
                input, tile_count, 0, Seq::empty(), Seq::empty());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_snapshot_gather_continuation(input, raw_main, tile_count, components);
            assert(tile_headers@.map_values(|value: Vec<u8>| value@) =~= Seq::<Seq<u8>>::empty());
            assert(super::jpip_missing_views(&header_missing) =~= Seq::<crate::specs::Part2JpipMissing>::empty());
        }
        let mut tile = 0_u64;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile <= tile_count,
                    super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                    crate::specs::part2_jpip_cache_complete(input.cache,
                        (6u64, super::DatabinClass::MainHeader, codestream, 0u64)),
                    crate::specs::part2_jpip_snapshot_admit(input) == Ok((raw_main, tile_count, components)),
                    tile_count <= usize::MAX as u64,
                    gather_goal == crate::specs::part2_jpip_snapshot_gather(input, tile_count, tile,
                        tile_headers@.map_values(|value: Vec<u8>| value@), super::jpip_missing_views(&header_missing)),
                    forall|error: DecodeError| gather_goal == Err(error) ==>
                        crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                            input.stream, input.selected, input.components, input.limits, Err(error)),
                decreases tile_count - tile,
            )
        )]
        while tile < tile_count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_snapshot_gather); }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_headers = tile_headers@.map_values(|value: Vec<u8>| value@);
                let ghost previous_missing = super::jpip_missing_views(&header_missing);
            }
            let tile_id = DatabinId::new(2, codestream, tile)?;
            if self.is_complete(tile_id) {
                tile_headers.push(self.databin_view(tile_id)?.into_bytes());
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(tile_headers@.map_values(|value: Vec<u8>| value@) =~=
                        previous_headers.push(tile_headers@[tile_headers.len() as int - 1]@));
                }
            } else {
                let additional = self.complete_databin_missing(tile_id);
                let mut missing_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant missing_index <= additional.len(),
                            gather_goal == crate::specs::part2_jpip_snapshot_gather(input, tile_count,
                                (tile + 1) as u64, previous_headers,
                                previous_missing + super::jpip_missing_views(&additional)),
                            super::jpip_missing_views(&header_missing) == previous_missing
                                + super::jpip_missing_views(&additional).subrange(0, missing_index as int),
                        decreases additional.len() - missing_index,
                    )
                )]
                while missing_index < additional.len() {
                    #[cfg(verus_keep_ghost)]
                    proof_decl! { let ghost previous_views = super::jpip_missing_views(&header_missing); }
                    header_missing.push(additional[missing_index]);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(super::jpip_missing_views(&header_missing) =~= previous_views.push(
                            super::jpip_missing_view(additional@[missing_index as int])));
                        assert(previous_views.push(super::jpip_missing_view(additional@[missing_index as int]))
                            =~= previous_missing + super::jpip_missing_views(&additional).subrange(0, missing_index as int + 1));
                    }
                    missing_index += 1;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(super::jpip_missing_views(&additional).subrange(0, additional.len() as int)
                        =~= super::jpip_missing_views(&additional));
                }
            }
            tile = tile
                .checked_add(1)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_snapshot_gather); }
        if !header_missing.is_empty() {
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_snapshot_headers_waiting(input, raw_main, tile_count, components,
                    tile_headers@.map_values(|value: Vec<u8>| value@), super::jpip_missing_views(&header_missing));
            }
            return Ok(AutomaticSnapshotResult {
                ready: None,
                missing: header_missing,
            });
        }

        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost raw_tiles = tile_headers@.map_values(|value: Vec<u8>| value@);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(super::jpip_missing_views(&header_missing) =~= Seq::<crate::specs::Part2JpipMissing>::empty());
            assert forall|error: DecodeError|
                crate::specs::part2_jpip_main_header_result(raw_main, Err(error))
                implies crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                    input.stream, input.selected, input.components, input.limits, Err(error)) by {
                super::jpip_snapshot_main_normalization_error(input, raw_main, tile_count, components, raw_tiles, error);
            }
        }
        let normalized_main = normalize_main_header(&main)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost main_calls = choose|calls: Seq<crate::specs::Part2JpipStorageEvent>|
                crate::specs::part2_jpip_normalize_main_header(raw_main, calls) == Some(Ok(normalized_main@));
            let ghost normalized_goal = crate::specs::part2_jpip_snapshot_normalize_tiles(raw_tiles, 0, Seq::empty());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_snapshot_normalization_continuation(input, raw_main, tile_count, components,
                raw_tiles, normalized_main@, main_calls);
            super::jpip_snapshot_normalized_continuation(input, raw_main, tile_count, components,
                raw_tiles, normalized_main@, main_calls);
        }
        let mut normalized_tiles = crate::allocation::empty_with_capacity(tile_headers.len())?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                parts@.map_values(|header: Vec<u8>| header@)) =~= Seq::<Seq<Seq<u8>>>::empty());
        }
        let mut tile_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_index <= tile_headers.len(),
                    normalized_tiles.len() == tile_index,
                    forall|index: int| 0 <= index < tile_index ==>
                        index <= u16::MAX as nat
                            && crate::specs::part2_jpip_parse_transitions(raw_tiles[index], index as u16).is_ok(),
                    super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                    raw_tiles == tile_headers@.map_values(|value: Vec<u8>| value@),
                    forall|headers: Seq<Seq<Seq<u8>>>, tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                        normalized_goal == Ok(headers) ==>
                            crate::specs::part2_jpip_snapshot_run(input,
                                crate::specs::part2_jpip_snapshot_normalized_events(
                                    tile_count, raw_tiles.len() as usize, main_calls) + tail)
                            == crate::specs::part2_jpip_snapshot_after_normalized(
                                input, normalized_main@, raw_tiles, tile_count, components, headers, tail),
                    normalized_goal == crate::specs::part2_jpip_snapshot_normalize_tiles(raw_tiles, tile_index as nat,
                        normalized_tiles@.map_values(|parts: Vec<Vec<u8>>| parts@.map_values(|header: Vec<u8>| header@))),
                    forall|error: DecodeError| normalized_goal == Err(error) ==>
                        crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                            input.stream, input.selected, input.components, input.limits, Err(error)),
                decreases tile_headers.len() - tile_index,
            )
        )]
        while tile_index < tile_headers.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_snapshot_normalize_tiles); }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost previous = normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
            parts@.map_values(|header: Vec<u8>| header@)); }
            normalized_tiles.push(normalize_automatic_tile_headers(
                tile_headers
                    .get(tile_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
                u16::try_from(tile_index).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?,
            )?);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_jpip_normalize_automatic_tile_headers(
                    raw_tiles[tile_index as int], tile_index as u16).is_ok());
                crate::specs::part2_jpip_normalized_transition_parse_known(
                    raw_tiles[tile_index as int], tile_index as u16);
                assert(normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                    parts@.map_values(|header: Vec<u8>| header@)) =~= previous.push(
                        normalized_tiles@[tile_index as int]@.map_values(|header: Vec<u8>| header@)));
            }
            tile_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_snapshot_normalize_tiles);
            assert(normalized_tiles.len() == tile_headers.len());
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost headers = normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                parts@.map_values(|header: Vec<u8>| header@));
            let ghost normalized_bytes = normalized_main@;
            let ghost prefix = crate::specs::part2_jpip_snapshot_normalized_events(
                tile_count, raw_tiles.len() as usize, main_calls);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(normalized_goal == Ok(headers));
            assert forall|error: DecodeError|
                crate::specs::part2_jpip_transition_template(normalized_bytes, headers, limits) == Err(error)
                    implies crate::specs::part2_jpip_automatic_snapshot_result(input.cache,
                        input.stream, input.selected, input.components, input.limits, Err(error)) by {
                assert(prefix + Seq::empty() =~= prefix);
                assert(crate::specs::part2_jpip_snapshot_run(input, prefix + Seq::empty())
                    == crate::specs::part2_jpip_snapshot_after_normalized(input, normalized_bytes, raw_tiles,
                        tile_count, components, headers, Seq::empty()));
                super::jpip_snapshot_result_witness(input, prefix, Err(error));
            }
        }
        let template =
            build_automatic_transition_template(&normalized_main, &normalized_tiles, limits)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_jpip_transition_template(normalized_main@,
                normalized_tiles@.map_values(|tile: Vec<Vec<u8>>|
                    tile@.map_values(|header: Vec<u8>| header@)), limits) == Ok(template@));
            assert(crate::specs::part2_jpip_transition_template(normalized_bytes, headers, input.limits) == Ok(template@));
            assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                crate::specs::part2_jpip_snapshot_run(input, prefix + tail)
                    == crate::specs::part2_jpip_snapshot_after_normalized(
                        input, normalized_bytes, raw_tiles, tile_count, components, headers, tail) by {
            }
            assert(super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits));
            assert forall|error: DecodeError|
                crate::codestream::complete_layout_outcome(Err(error))
                    == crate::specs::part1_parse_layout(template@, limits)
                implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self),
                    codestream, super::jpip_snapshot_selection_view(selection),
                    super::jpip_packet_selection_view(packet_selection), limits, Err(error)) by {
                super::jpip_snapshot_template_parse_error(input, prefix, normalized_bytes, raw_tiles,
                    tile_count, components, headers, template@, error);
            }
        }
        let layout = crate::codestream::parse_layout(&template, limits)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_snapshot_layout_capacity_error(input, prefix, normalized_bytes, raw_tiles,
                tile_count, components, headers, template@, &layout);
        }
        let mut automatic_tiles = crate::allocation::empty_with_capacity(normalized_tiles.len())?;
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_snapshot_layout_continuation(input, prefix, normalized_bytes, raw_tiles,
                tile_count, components, headers, template@, &layout);
        }
        let mut maximum_layers = 0_u16;
        tile_index = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost mut tile_root = crate::specs::Part2JpipSnapshotTileRoot {
                input, events: prefix + seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                    site: 2, tile: 0, elements: normalized_tiles.len(), succeeded: true }],
                count: tile_count, components, main: normalized_main@, raw: raw_tiles, headers,
                layout: crate::codestream::decoder_layout_input_view(&layout),
                tile: 0, before: Seq::empty(), maximum: 0,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::jpip_automatic_tiles_view);
            assert(super::jpip_automatic_tiles_view(automatic_tiles@) =~= Seq::empty());
            assert(crate::specs::part2_jpip_snapshot_tile_root(tile_root));
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_index <= normalized_tiles.len(),
                    crate::specs::part2_jpip_snapshot_tile_root(tile_root),
                    super::jpip_snapshot_inputs_match(tile_root.input, self, codestream, selection, packet_selection, limits),
                    tile_root.count == tile_count, tile_root.components == components,
                    tile_root.main == normalized_main@,
                    tile_root.raw == raw_tiles,
                    tile_root.headers == normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                        parts@.map_values(|header: Vec<u8>| header@)),
                    tile_root.layout == crate::codestream::decoder_layout_input_view(&layout),
                    tile_root.tile == tile_index as nat,
                    tile_root.before == super::jpip_automatic_tiles_view(automatic_tiles@),
                    tile_root.maximum == maximum_layers,
                    normalized_tiles.len() == tile_headers.len(),
                    raw_tiles == tile_headers@.map_values(|header: Vec<u8>| header@),
                    forall|index: int| 0 <= index < raw_tiles.len() ==>
                        index <= u16::MAX as nat
                            && crate::specs::part2_jpip_parse_transitions(raw_tiles[index], index as u16).is_ok(),
                decreases normalized_tiles.len() - tile_index,
            )
        )]
        while tile_index < normalized_tiles.len() {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost current_root = tile_root; }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::codestream::decoder_layout_input_fields(&layout);
                assert(tile_index <= u16::MAX as nat);
            }
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
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost native_parts = tile_parts@.map_values(
                    |part: &crate::codestream::TilePartPayload<'_>| crate::codestream::tile_part_owned_view(part));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                if native_parts.len() == 0 {
                    super::jpip_snapshot_tile_root_error(current_root, Seq::empty(),
                        crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidTilePart));
                }
            }
            let tile_part = *tile_parts
                .first()
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidTilePart),
                    ))]
                    || DecodeError::malformed(0, MalformedKind::InvalidTilePart),
                )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(native_parts[0] == crate::codestream::tile_part_owned_view(tile_part));
                assert(native_parts == current_root.layout.parts.filter(
                    |part: crate::specs::Part2OwnedTilePart| part.tile_index == current_root.tile as u16));
                super::jpip_snapshot_plan_errors(current_root, native_parts);
            }
            let mut plan = crate::decode::plan_progression_tile_at_with_component_overrides(
                &layout.info.image_size,
                tile_number,
                tile_part.coding_style,
                &tile_part.component_coding_styles,
                &tile_part.component_quantizations,
                &tile_part.roi_shifts,
                limits,
            )?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost initial_plan = crate::decode::progression_plan_view(&plan); }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_progression_tile_plan(&layout.info.image_size,
                    tile_part.coding_style, &tile_part.component_coding_styles,
                    &tile_part.component_quantizations, &tile_part.roi_shifts,
                    (tile_number, 0), (false, 74, false), limits)
                    == Ok(crate::decode::progression_plan_view(&plan)));
            }
            maximum_layers = maximum_layers.max(tile_part.coding_style.layers);
            let precinct_count = plan.precincts().len();
            let layer_count = usize::from(tile_part.coding_style.layers);
            let mut ordinals = vec![vec![None; layer_count]; precinct_count];
            let mut order = Vec::new();
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_snapshot_iterator_errors(current_root, native_parts, initial_plan);
            }
            let mut iterator = crate::packet::ProgressionPacketIterator::new(
                plan.grid(),
                tile_part.coding_style.progression_order,
                &tile_part.progression_changes,
                limits,
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part1_progression_iterator_initial(
                    crate::decode::progression_plan_view(&plan).grid,
                    tile_part.coding_style.progression_order,
                    crate::codestream::progression_changes_view(&tile_part.progression_changes),
                    crate::limits::resource_work_limit(limits))
                    == Ok(crate::packet::progression_packet_iterator_view(&iterator)));
            }
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
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost order_grid = crate::decode::progression_plan_view(&plan).grid;
                let ghost order_iterator = crate::packet::progression_packet_iterator_view(&iterator);
                let ghost order_ordinals = ordinals@.map_values(|row: Vec<Option<u16>>| row@);
                let ghost order_initial = order@;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(order_initial.len() == 0);
                assert(order_ordinals.len() == precinct_count);
                assert forall|row: int| 0 <= row < order_ordinals.len()
                    implies #[trigger] order_ordinals[row].len() == layer_count by {
                }
                assert forall|row: int, layer: int|
                    0 <= row < order_ordinals.len() && 0 <= layer < layer_count
                        implies #[trigger] order_ordinals[row][layer] == None::<u16> by {
                    super::jpip_none_row_clone_law::<u16>();
                    reveal(vstd::pervasive::cloned);
                    reveal(vstd::pervasive::strictly_cloned);
                }
                assert forall|row: int| 0 <= row < order_ordinals.len()
                    implies #[trigger] order_ordinals[row]
                        == Seq::new(tile_part.coding_style.layers as nat, |_layer: int| None::<u16>) by {
                    assert(order_ordinals[row] =~= Seq::new(layer_count as nat, |_layer: int| None::<u16>));
                }
                assert(order_ordinals =~= Seq::new(initial_plan.precincts.len(), |_row: int|
                    Seq::new(tile_part.coding_style.layers as nat, |_layer: int| None::<u16>)));
                super::jpip_snapshot_order_errors(current_root, native_parts, initial_plan, order_iterator);
            }
            build_automatic_order(&plan, &mut iterator, &mut ordinals, &mut order, limits)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_jpip_snapshot_order(order_iterator,
                    crate::limits::resource_work_limit(limits), 0, order_ordinals, order_initial) == Ok(order@));
                assert(super::jpip_snapshot_plan_order_known(
                    current_root, native_parts, initial_plan, order_iterator, order@));
                crate::specs::part2_jpip_order_phase_prefix_bounds(order_grid, order_iterator,
                    order_ordinals, order_initial, 0, crate::limits::resource_work_limit(limits));
                assert forall|index: int| 0 <= index < order.len()
                    implies (#[trigger] order@[index].1 as nat) < precinct_count by {
                }
                assert forall|index: int| 0 <= index < order.len()
                    implies (#[trigger] order@[index].0.layer as nat) < layer_count by {
                }
            }

            let mut parsed = vec![vec![None; layer_count]; precinct_count];
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(parsed.len() == precinct_count);
                assert forall|row: int| 0 <= row < parsed.len()
                    implies #[trigger] parsed@[row]@.len() == layer_count by {
                }
            }
            let mut offsets = vec![0_u64; precinct_count];
            #[cfg(verus_keep_ghost)]
            proof! { super::jpip_snapshot_mapping_capacity_error(current_root, native_parts, initial_plan, order_iterator, order@); }
            let mut databins = crate::allocation::empty_with_capacity(precinct_count)?;
            let grid = plan.grid();
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost mapping_input = crate::specs::Part2JpipSnapshotInput {
                    cache: jpip_cache_view(self), stream: codestream,
                    selected: super::jpip_snapshot_selection_view(selection),
                    components: super::jpip_packet_selection_view(packet_selection), limits,
                };
                let ghost mapping_plan = crate::decode::progression_plan_view(&plan);
                let ghost mapping_goal = crate::specs::part2_jpip_snapshot_databins(
                    mapping_input, tile_count, components, tile_index, mapping_plan, 0, Seq::empty());
                let ghost tile_capacity = crate::specs::Part2JpipSnapshotEvent::Capacity {
                    site: 3, tile: tile_index, elements: precinct_count, succeeded: true };
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(databins@.map_values(|id: DatabinId| super::databin_id_view(id))
                    =~= Seq::<crate::specs::Part2JpipDatabin>::empty());
                assert forall|row: int, layer: int|
                    0 <= row < parsed.len() && 0 <= layer < layer_count
                        implies #[trigger] parsed@[row]@[layer].is_none() by {
                    super::jpip_none_row_clone_law::<Vec<u8>>();
                    reveal(vstd::pervasive::cloned);
                    reveal(vstd::pervasive::strictly_cloned);
                }
                assert forall|row: int| 0 <= row < parsed.len()
                    implies #[trigger] jpip_parsed_packet_matrix(parsed@)[row]
                        == Seq::new(native_parts[0].coding_style.layers as nat, |_layer: int| None::<Seq<u8>>) by {
                    assert(jpip_parsed_packet_matrix(parsed@)[row]
                        =~= Seq::new(layer_count as nat, |_layer: int| None::<Seq<u8>>));
                }
                assert(jpip_parsed_packet_matrix(parsed@) =~= Seq::new(initial_plan.precincts.len(),
                    |_row: int| Seq::new(native_parts[0].coding_style.layers as nat, |_layer: int| None::<Seq<u8>>)));
                assert(offsets@ =~= Seq::new(initial_plan.precincts.len(), |_row: int| 0u64));
                assert forall|error: DecodeError| mapping_goal == Err(error)
                    implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                        super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                        limits, Err(error)) by {
                    super::jpip_snapshot_mapping_error(current_root, native_parts, initial_plan, order_iterator, order@, error);
                }
            }
            let mut mapping_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant mapping_index <= precinct_count,
                        databins.len() == mapping_index,
                        super::jpip_snapshot_inputs_match(mapping_input, self, codestream, selection, packet_selection, limits),
                        mapping_plan == crate::decode::progression_plan_view(&plan),
                        initial_plan == mapping_plan,
                        super::jpip_snapshot_inputs_match(current_root.input, self, codestream, selection, packet_selection, limits),
                        super::jpip_snapshot_root_frame(current_root, normalized_main@,
                            tile_headers@.map_values(|header: Vec<u8>| header@),
                            normalized_tiles@.map_values(|parts: Vec<Vec<u8>>| parts@.map_values(|header: Vec<u8>| header@)),
                            crate::codestream::decoder_layout_input_view(&layout), super::jpip_automatic_tiles_view(automatic_tiles@)),
                        maximum_layers == if tile_part.coding_style.layers > current_root.maximum {
                            tile_part.coding_style.layers } else { current_root.maximum },
                        super::jpip_snapshot_active_tile(current_root, tile_count, components, tile_index,
                            raw_tiles, normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                                parts@.map_values(|header: Vec<u8>| header@))),
                        super::jpip_snapshot_plan_order_known(current_root, native_parts, initial_plan, order_iterator, order@),
                        native_parts[0] == crate::codestream::tile_part_owned_view(tile_part),
                        native_parts == tile_parts@.map_values(
                            |part: &crate::codestream::TilePartPayload<'_>| crate::codestream::tile_part_owned_view(part)),
                        jpip_parsed_packet_matrix(parsed@) == Seq::new(initial_plan.precincts.len(),
                            |_row: int| Seq::new(native_parts[0].coding_style.layers as nat, |_layer: int| None::<Seq<u8>>)),
                        offsets@ == Seq::new(initial_plan.precincts.len(), |_row: int| 0u64),
                        tile_capacity == (crate::specs::Part2JpipSnapshotEvent::Capacity {
                            site: 3, tile: tile_index, elements: precinct_count, succeeded: true }),
                        crate::packet::packet_grid_view(grid) == mapping_plan.grid,
                        mapping_plan.precincts.len() == precinct_count,
                        mapping_goal == crate::specs::part2_jpip_snapshot_databins(
                            mapping_input, tile_count, components, tile_index, mapping_plan, 0, Seq::empty()),
                        mapping_goal == crate::specs::part2_jpip_snapshot_databins(
                            mapping_input, tile_count, components, tile_index, mapping_plan, mapping_index as nat,
                            databins@.map_values(|id: DatabinId| super::databin_id_view(id))),
                        forall|error: DecodeError| mapping_goal == Err(error) ==>
                            crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                                super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                                limits, Err(error)),
                        tile_index < tile_headers.len(),
                        tile_number as nat == tile_index as nat,
                        raw_tiles == tile_headers@.map_values(|header: Vec<u8>| header@),
                        forall|index: int| 0 <= index < raw_tiles.len() ==>
                            index <= u16::MAX as nat
                                && crate::specs::part2_jpip_parse_transitions(raw_tiles[index], index as u16).is_ok(),
                        forall|index: int| 0 <= index < order.len() ==>
                            (#[trigger] order@[index].1 as nat) < precinct_count,
                        forall|index: int| 0 <= index < order.len() ==>
                            (#[trigger] order@[index].0.layer as nat) < layer_count,
                        parsed.len() == precinct_count,
                        forall|row: int| 0 <= row < parsed.len() ==>
                            #[trigger] parsed@[row]@.len() == layer_count,
                    decreases precinct_count - mapping_index,
                )
            )]
            while mapping_index < precinct_count {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_snapshot_databins); }
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost before_databins = databins@.map_values(
                        |id: DatabinId| super::databin_id_view(id));
                }
                let (component, resolution, precinct) = plan
                    .precincts()
                    .get(mapping_index)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
                    .coordinate();
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert((component, resolution, precinct) == (
                        mapping_plan.precincts[mapping_index as int].component,
                        mapping_plan.precincts[mapping_index as int].resolution,
                        mapping_plan.precincts[mapping_index as int].precinct));
                }
                let in_class = automatic_precinct_in_class(
                    tile_count,
                    u64::from(components),
                    tile_index as u64,
                    component,
                    resolution,
                    precinct,
                    grid,
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part2_jpip_snapshot_in_class(tile_count, components as u64,
                        tile_index as u64, component, resolution, precinct,
                        crate::packet::packet_grid_view(grid)) == Ok(in_class));
                }
                databins.push(DatabinId::new(0, codestream, in_class)?);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(databins@.map_values(|id: DatabinId| super::databin_id_view(id))
                        =~= before_databins.push(super::databin_id_view(databins@[mapping_index as int])));
                }
                mapping_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_snapshot_databins);
                assert(mapping_goal == Ok(databins@.map_values(|id: DatabinId| super::databin_id_view(id))));
                assert(tile_index < tile_headers.len());
            }
            let source_tile_header = tile_headers
                .get(tile_index)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(source_tile_header@ == raw_tiles[tile_index as int]);
                assert(crate::specs::part2_jpip_parse_transitions(source_tile_header@, tile_number).is_ok());
                assert forall|error: DecodeError|
                    super::jpip_transitions_outcome(Err(error))
                        != crate::specs::part2_jpip_parse_transitions(source_tile_header@, tile_number) by {
                }
                assert forall|error: DecodeError|
                    super::jpip_transitions_outcome(Err(error))
                        == crate::specs::part2_jpip_parse_transitions(source_tile_header@, tile_number)
                    implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self),
                        codestream, super::jpip_snapshot_selection_view(selection),
                        super::jpip_packet_selection_view(packet_selection), limits, Err(error)) by {
                }
            }
            let transitions = parse_tile_part_transitions(source_tile_header, tile_number)?;
            let mut transition_index = 0_usize;
            let mut transition_packets = 0_u64;
            let mut transition_bytes = 0_u64;
            let mut blocked = vec![false; precinct_count];
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost acquisition_input = crate::specs::Part2JpipSnapshotInput {
                    cache: jpip_cache_view(self), stream: codestream,
                    selected: super::jpip_snapshot_selection_view(selection),
                    components: super::jpip_packet_selection_view(packet_selection), limits,
                };
                let ghost acquisition_parts = tile_parts@.map_values(
                    |part: &crate::codestream::TilePartPayload<'_>| crate::codestream::tile_part_owned_view(part));
                let ghost acquisition_transitions = super::jpip_transitions_view(&transitions);
                let ghost acquisition_databins = databins@.map_values(
                    |id: DatabinId| super::databin_id_view(id));
                let ghost acquisition_order = order@;
                let ghost acquisition_initial = crate::specs::Part2JpipSnapshotPacketState {
                    precincts: crate::decode::progression_plan_view(&plan).precincts,
                    parsed: jpip_parsed_packet_matrix(parsed@), offsets: offsets@, blocked: blocked@,
                    transition: transition_index, packets: transition_packets, bytes: transition_bytes,
                };
                let ghost acquisition_goal = crate::specs::part2_jpip_snapshot_parse_packets(
                    acquisition_input, acquisition_parts, acquisition_transitions, acquisition_databins,
                    acquisition_order, 0, acquisition_initial);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(current_root.input == acquisition_input);
                assert(acquisition_parts == native_parts);
                let canonical = super::jpip_snapshot_initial_packets(initial_plan, native_parts[0].coding_style.layers);
                assert(acquisition_initial.precincts == canonical.precincts);
                assert(acquisition_initial.parsed == canonical.parsed);
                assert(acquisition_initial.offsets == canonical.offsets);
                assert(blocked@ =~= Seq::new(precinct_count as nat, |_index: int| false)) by {
                    reveal(vstd::pervasive::cloned);
                    reveal(vstd::pervasive::strictly_cloned);
                }
                assert(acquisition_initial.blocked == canonical.blocked);
                assert(acquisition_initial.transition == canonical.transition);
                assert(acquisition_initial.packets == canonical.packets);
                assert(acquisition_initial.bytes == canonical.bytes);
                assert(acquisition_initial == super::jpip_snapshot_initial_packets(
                    initial_plan, native_parts[0].coding_style.layers));
                super::jpip_snapshot_tile_acquisition_prefix(current_root, native_parts, initial_plan,
                    order_iterator, acquisition_order, acquisition_databins, acquisition_transitions, acquisition_initial);
                assert(super::jpip_snapshot_tile_acquisition_known(current_root, acquisition_parts,
                    acquisition_transitions, acquisition_databins, acquisition_order, acquisition_initial, tile_capacity));
                assert forall|error: DecodeError| acquisition_goal == Err(error)
                    implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                        super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                        limits, Err(error)) by {
                    super::jpip_snapshot_acquisition_error(current_root, acquisition_parts, acquisition_transitions,
                        acquisition_databins, acquisition_order, acquisition_initial, tile_capacity, error);
                }
            }
            let mut order_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant order_index <= order.len(),
                        super::jpip_snapshot_inputs_match(current_root.input, self, codestream, selection, packet_selection, limits),
                        super::jpip_snapshot_root_frame(current_root, normalized_main@,
                            tile_headers@.map_values(|header: Vec<u8>| header@),
                            normalized_tiles@.map_values(|parts: Vec<Vec<u8>>| parts@.map_values(|header: Vec<u8>| header@)),
                            crate::codestream::decoder_layout_input_view(&layout), super::jpip_automatic_tiles_view(automatic_tiles@)),
                        maximum_layers == if tile_part.coding_style.layers > current_root.maximum {
                            tile_part.coding_style.layers } else { current_root.maximum },
                        super::jpip_snapshot_active_tile(current_root, tile_count, components, tile_index,
                            raw_tiles, normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                                parts@.map_values(|header: Vec<u8>| header@))),
                        current_root.input == acquisition_input,
                        acquisition_parts.len() != 0,
                        acquisition_parts[0] == crate::codestream::tile_part_owned_view(tile_part),
                        super::jpip_snapshot_tile_acquisition_known(current_root, acquisition_parts,
                            acquisition_transitions, acquisition_databins, acquisition_order, acquisition_initial, tile_capacity),
                        tile_capacity == (crate::specs::Part2JpipSnapshotEvent::Capacity {
                            site: 3, tile: tile_index, elements: precinct_count, succeeded: true }),
                        acquisition_input.cache == jpip_cache_view(self),
                        acquisition_input.limits == limits,
                        acquisition_input.selected == super::jpip_snapshot_selection_view(selection),
                        acquisition_input.components == super::jpip_packet_selection_view(packet_selection),
                        tile_number as nat == tile_index as nat,
                        acquisition_parts == tile_parts@.map_values(
                            |part: &crate::codestream::TilePartPayload<'_>| crate::codestream::tile_part_owned_view(part)),
                        acquisition_transitions == super::jpip_transitions_view(&transitions),
                        acquisition_databins == databins@.map_values(|id: DatabinId| super::databin_id_view(id)),
                        acquisition_order == order@,
                        acquisition_goal == crate::specs::part2_jpip_snapshot_parse_packets(
                            acquisition_input, acquisition_parts, acquisition_transitions, acquisition_databins,
                            acquisition_order, 0, acquisition_initial),
                        forall|error: DecodeError| acquisition_goal == Err(error) ==>
                            crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                                super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                                limits, Err(error)),
                        acquisition_goal == crate::specs::part2_jpip_snapshot_parse_packets(
                            acquisition_input, acquisition_parts, acquisition_transitions, acquisition_databins,
                            acquisition_order, order_index as nat, crate::specs::Part2JpipSnapshotPacketState {
                                precincts: crate::decode::progression_plan_view(&plan).precincts,
                                parsed: jpip_parsed_packet_matrix(parsed@), offsets: offsets@, blocked: blocked@,
                                transition: transition_index, packets: transition_packets, bytes: transition_bytes,
                            }),
                        blocked.len() == precinct_count,
                        forall|index: int| 0 <= index < order.len() ==>
                            (#[trigger] order@[index].1 as nat) < precinct_count,
                        forall|index: int| 0 <= index < order.len() ==>
                            (#[trigger] order@[index].0.layer as nat) < layer_count,
                        parsed.len() == precinct_count,
                        forall|row: int| 0 <= row < parsed.len() ==>
                            #[trigger] parsed@[row]@.len() == layer_count,
                    decreases order.len() - order_index,
                )
            )]
            while order_index < order.len() {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_snapshot_parse_packets); }
                let (coordinate, execution) = order[order_index];
                #[cfg(verus_keep_ghost)]
                proof! { assert(execution < blocked.len()); }
                if *blocked
                    .get(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
                {
                    order_index += 1;
                    continue;
                }
                let state = *tile_parts
                    .get(transition_index)
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidTilePart),
                        ))]
                        || DecodeError::malformed(0, MalformedKind::InvalidTilePart),
                    )?;
                let databin = *databins.get(execution).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
                let prefix = self.databin_prefix(databin);
                let offset = *offsets.get(execution).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
                let start = usize::try_from(offset).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
                if start >= prefix.len() {
                    *blocked.get_mut(execution).ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })? = true;
                    order_index += 1;
                    continue;
                }
                #[cfg(verus_keep_ghost)]
                proof! { assert((order_index & 65535usize) <= u16::MAX as usize) by(bit_vector); }
                let sequence = u16::try_from(order_index & usize::from(u16::MAX))
                    .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    if execution < crate::decode::progression_plan_view(&plan).precincts.len() {
                        super::jpip_snapshot_decode_packet_known(
                            crate::decode::progression_plan_view(&plan).precincts[execution as int],
                            state, prefix@.subrange(start as int, prefix.len() as int),
                            sequence, coordinate.layer, limits);
                    }
                }
                match decode_automatic_precinct(
                    &mut plan,
                    execution,
                    state,
                    &prefix,
                    start,
                    sequence,
                    coordinate.layer,
                    limits,
                ) {
                    Ok(consumed) => {
                        if consumed == 0 {
                            return Err(DecodeError::malformed(
                                offset,
                                MalformedKind::InvalidPacketLength,
                            ));
                        }
                        let end = start.checked_add(consumed).ok_or_else(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                ensures result == crate::specs::part2_jpip_range_overflow(offset),
                            ))]
                            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
                        )?;
                        let packet_slice = prefix.get(start..end).ok_or_else(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                ensures result == crate::specs::part2_jpip_cache_error(offset, MalformedKind::Truncated),
                            ))]
                            || { DecodeError::malformed(offset, MalformedKind::Truncated) },
                        )?;
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
                        transition_packets = transition_packets.checked_add(1).ok_or_else(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                                ))]
                            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                        )?;
                        transition_bytes =
                            transition_bytes.checked_add(consumed as u64).ok_or_else(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                                ))]
                                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                            )?;
                        let transition = transitions.get(transition_index).ok_or_else(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidTilePart),
                            ))]
                            || { DecodeError::malformed(0, MalformedKind::InvalidTilePart) },
                        )?;
                        let boundary = match transition.packet_count() {
                            Some(count) => transition_packets == count,
                            None => match transition.data_length() {
                                Some(length) => transition_bytes == length,
                                None => false,
                            },
                        };
                        let next_transition = transition_index.checked_add(1).ok_or_else(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                ensures result == crate::specs::part2_jpip_range_overflow(0),
                            ))]
                            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                        )?;
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
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_snapshot_parse_packets);
                assert(crate::specs::part2_jpip_snapshot_parse_packets(acquisition_input,
                    acquisition_parts, acquisition_transitions, acquisition_databins, acquisition_order,
                    0, acquisition_initial) == Ok(crate::specs::Part2JpipSnapshotPacketState {
                        precincts: crate::decode::progression_plan_view(&plan).precincts,
                        parsed: jpip_parsed_packet_matrix(parsed@), offsets: offsets@, blocked: blocked@,
                        transition: transition_index, packets: transition_packets, bytes: transition_bytes,
                    }));
            }

            let tile_is_selected = jpip_tile_selected(selection, tile_number);
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_snapshot_packet_capacity_error(current_root, acquisition_parts, acquisition_transitions,
                    acquisition_databins, acquisition_order, acquisition_initial,
                    crate::specs::Part2JpipSnapshotPacketState {
                        precincts: crate::decode::progression_plan_view(&plan).precincts,
                        parsed: jpip_parsed_packet_matrix(parsed@), offsets: offsets@, blocked: blocked@,
                        transition: transition_index, packets: transition_packets, bytes: transition_bytes,
                    }, tile_capacity);
            }
            let mut packets = crate::allocation::empty_with_capacity(order.len())?;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost acquisition_final = crate::specs::Part2JpipSnapshotPacketState {
                    precincts: crate::decode::progression_plan_view(&plan).precincts,
                    parsed: jpip_parsed_packet_matrix(parsed@), offsets: offsets@, blocked: blocked@,
                    transition: transition_index, packets: transition_packets, bytes: transition_bytes,
                };
                let ghost packet_events = seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                    site: 4, tile: tile_index, elements: order.len(), succeeded: true }];
                let ghost packet_goal = crate::specs::part2_jpip_snapshot_make_packets(acquisition_input,
                    tile_number, tile_part.component_coding_styles, acquisition_order,
                    acquisition_databins, acquisition_final, 0, Seq::empty());
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(packets@.map_values(|packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet))
                    =~= Seq::<crate::specs::Part2JpipAutomaticPacket>::empty());
                assert forall|error: DecodeError| packet_goal == Err(error)
                    implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                        super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                        limits, Err(error)) by {
                    super::jpip_snapshot_packet_error(current_root, acquisition_parts, acquisition_transitions,
                        acquisition_databins, acquisition_order, acquisition_initial, acquisition_final, tile_capacity, error);
                }
            }
            let mut order_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant order_index <= order.len(),
                        super::jpip_snapshot_inputs_match(current_root.input, self, codestream, selection, packet_selection, limits),
                        super::jpip_snapshot_root_frame(current_root, normalized_main@,
                            tile_headers@.map_values(|header: Vec<u8>| header@),
                            normalized_tiles@.map_values(|parts: Vec<Vec<u8>>| parts@.map_values(|header: Vec<u8>| header@)),
                            crate::codestream::decoder_layout_input_view(&layout), super::jpip_automatic_tiles_view(automatic_tiles@)),
                        maximum_layers == if tile_part.coding_style.layers > current_root.maximum {
                            tile_part.coding_style.layers } else { current_root.maximum },
                        super::jpip_snapshot_active_tile(current_root, tile_count, components, tile_index,
                            raw_tiles, normalized_tiles@.map_values(|parts: Vec<Vec<u8>>|
                                parts@.map_values(|header: Vec<u8>| header@))),
                        current_root.input == acquisition_input,
                        acquisition_parts.len() != 0,
                        acquisition_parts[0] == crate::codestream::tile_part_owned_view(tile_part),
                        super::jpip_snapshot_tile_acquisition_known(current_root, acquisition_parts,
                            acquisition_transitions, acquisition_databins, acquisition_order, acquisition_initial, tile_capacity),
                        tile_capacity == (crate::specs::Part2JpipSnapshotEvent::Capacity {
                            site: 3, tile: tile_index, elements: precinct_count, succeeded: true }),
                        acquisition_input.cache == jpip_cache_view(self),
                        acquisition_input.limits == limits,
                        acquisition_input.selected == super::jpip_snapshot_selection_view(selection),
                        acquisition_input.components == super::jpip_packet_selection_view(packet_selection),
                        tile_number as nat == tile_index as nat,
                        tile_is_selected == crate::specs::part2_jpip_snapshot_tile_selected(
                            acquisition_input.selected, tile_number),
                        acquisition_order == order@,
                        acquisition_databins == databins@.map_values(|id: DatabinId| super::databin_id_view(id)),
                        acquisition_final.parsed == jpip_parsed_packet_matrix(parsed@),
                        acquisition_final.offsets == offsets@,
                        crate::specs::part2_jpip_snapshot_parse_packets(acquisition_input,
                            acquisition_parts, acquisition_transitions, acquisition_databins,
                            acquisition_order, 0, acquisition_initial) == Ok(acquisition_final),
                        packet_events == seq![crate::specs::Part2JpipSnapshotEvent::Capacity {
                            site: 4, tile: tile_index, elements: order.len(), succeeded: true }],
                        packet_goal == crate::specs::part2_jpip_snapshot_make_packets(acquisition_input,
                            tile_number, tile_part.component_coding_styles, acquisition_order,
                            acquisition_databins, acquisition_final, 0, Seq::empty()),
                        forall|error: DecodeError| packet_goal == Err(error) ==>
                            crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                                super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                                limits, Err(error)),
                        packet_goal == crate::specs::part2_jpip_snapshot_make_packets(acquisition_input,
                            tile_number, tile_part.component_coding_styles, acquisition_order,
                            acquisition_databins, acquisition_final, order_index as nat,
                            packets@.map_values(|packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet))),
                        parsed.len() == precinct_count,
                        forall|row: int| 0 <= row < parsed.len() ==>
                            #[trigger] parsed@[row]@.len() == layer_count,
                        forall|index: int| 0 <= index < order.len() ==>
                            (#[trigger] order@[index].1 as nat) < precinct_count
                                && (order@[index].0.layer as nat) < layer_count,
                    decreases order.len() - order_index,
                )
            )]
            while order_index < order.len() {
                let (coordinate, execution) = order[order_index];
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost before_packets = packets@.map_values(
                        |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet));
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_snapshot_make_packets);
                    reveal(super::jpip_automatic_packet_view);
                    assert(packet_events.drop_first() =~= Seq::<crate::specs::Part2JpipSnapshotEvent>::empty());
                    assert forall|error: DecodeError|
                        tile_is_selected
                            && crate::specs::part2_jpip_snapshot_component_included(
                                super::jpip_packet_selection_view(packet_selection), coordinate.component)
                            && crate::specs::part2_jpip_snapshot_resolution(
                                super::jpip_snapshot_selection_view(selection), coordinate.component,
                                coordinate.resolution, tile_part.component_coding_styles) == Err(error)
                        implies crate::specs::part2_jpip_snapshot_acquired_packets(acquisition_input,
                            acquisition_parts, acquisition_transitions, acquisition_databins, acquisition_order,
                            acquisition_initial, tile_index, tile_part.component_coding_styles, packet_events)
                            == Some((Err(error), Seq::empty()))
                            && crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self),
                                codestream, super::jpip_snapshot_selection_view(selection),
                                super::jpip_packet_selection_view(packet_selection), limits, Err(error)) by {
                        crate::specs::part2_jpip_snapshot_acquired_resolution_error(acquisition_input,
                            acquisition_parts, acquisition_transitions, acquisition_databins, acquisition_order,
                            acquisition_initial, acquisition_final, tile_index, tile_part.component_coding_styles,
                            order_index as nat, packets@.map_values(
                                |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet)),
                            packet_events, Seq::empty(), error);
                        assert(crate::specs::part2_jpip_snapshot_tile(current_root.input, current_root.count,
                            current_root.components, current_root.tile as usize, current_root.layout,
                            current_root.raw, current_root.headers, seq![tile_capacity] + packet_events)
                            == Some((Err(error), Seq::empty())));
                        super::jpip_snapshot_tile_root_error(current_root, seq![tile_capacity] + packet_events, error);
                        assert(crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self),
                            codestream, super::jpip_snapshot_selection_view(selection),
                            super::jpip_packet_selection_view(packet_selection), limits, Err(error)));
                    }
                }
                let required = tile_is_selected
                    && packet_selection.includes_component(coordinate.component)
                    && jpip_resolution_selected(
                        selection,
                        coordinate.component,
                        coordinate.resolution,
                        &tile_part.component_coding_styles,
                    )?;
                #[cfg(verus_keep_ghost)]
                proof! { assert(execution < parsed.len()); }
                let parsed_layers = parsed
                    .get(execution)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                #[cfg(verus_keep_ghost)]
                proof! { assert((coordinate.layer as usize) < parsed_layers.len()); }
                let packet_bytes = match parsed_layers
                    .get(usize::from(coordinate.layer))
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?
                {
                    Some(bytes) => Some(bytes.clone()),
                    None => None,
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(jpip_parsed_packet_value(packet_bytes)
                        == acquisition_final.parsed[execution as int][coordinate.layer as int]);
                    assert((order_index & 65535usize) <= u16::MAX as usize) by(bit_vector);
                }
                packets.push(AutomaticPacket {
                    databin: *databins.get(execution).ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                    )?,
                    bytes: packet_bytes,
                    next_offset: *offsets.get(execution).ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                    )?,
                    required,
                    ordinal: u16::try_from(order_index & usize::from(u16::MAX)).map_err(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                        |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                    )?,
                    layer: coordinate.layer,
                });
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(packets@.map_values(|packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet))
                        =~= before_packets.push((acquisition_databins[execution as int],
                            acquisition_final.parsed[execution as int][coordinate.layer as int],
                            acquisition_final.offsets[execution as int], required,
                            ((order_index as usize) & 65535) as u16, coordinate.layer)));
                }
                order_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_snapshot_make_packets);
                assert(packet_goal == Ok(packets@.map_values(
                    |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet))));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost partition_packets = packets@.map_values(
                    |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet));
                let ghost partition_events = seq![tile_capacity] + packet_events;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|error: DecodeError|
                    crate::specs::part2_jpip_partition_automatic_tiles(current_root.headers[current_root.tile as int],
                        acquisition_parts, acquisition_transitions, partition_packets) == Err(error)
                    implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                        super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                        limits, Err(error)) by {
                    assert(partition_events =~= seq![tile_capacity] + packet_events);
                    assert(crate::specs::part2_jpip_snapshot_tile(current_root.input, current_root.count,
                        current_root.components, current_root.tile as usize, current_root.layout,
                        current_root.raw, current_root.headers, partition_events) == Some((Err(error), Seq::empty())));
                    super::jpip_snapshot_tile_root_error(current_root, partition_events, error);
                }
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
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost partition_missing_goal = crate::specs::part2_jpip_snapshot_partition_missing(
                        current_root.input.cache, partition_packets, 0, Seq::empty());
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part2_jpip_snapshot_tile(current_root.input, current_root.count,
                        current_root.components, current_root.tile as usize, current_root.layout,
                        current_root.raw, current_root.headers, partition_events)
                        == Some((Ok((None, partition_packets, tile_part.coding_style.layers)), Seq::empty())));
                }
                let mut missing = Vec::new();
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(super::jpip_missing_views(&missing)
                        =~= Seq::<crate::specs::Part2JpipMissing>::empty());
                }
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= packets.len(),
                            partition_packets == packets@.map_values(
                                |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet)),
                            super::jpip_snapshot_inputs_match(current_root.input, self, codestream, selection, packet_selection, limits),
                            crate::specs::part2_jpip_snapshot_tile_root(current_root), current_root.tile < current_root.headers.len(),
                            crate::specs::part2_jpip_snapshot_tile(current_root.input, current_root.count,
                                current_root.components, current_root.tile as usize, current_root.layout,
                                current_root.raw, current_root.headers, partition_events)
                                == Some((Ok((None, partition_packets, tile_part.coding_style.layers)), Seq::empty())),
                            partition_missing_goal == crate::specs::part2_jpip_snapshot_partition_missing(
                                current_root.input.cache, partition_packets, 0, Seq::empty()),
                            partition_missing_goal == crate::specs::part2_jpip_snapshot_partition_missing(
                                current_root.input.cache, partition_packets, packet_index as nat, super::jpip_missing_views(&missing)),
                        decreases packets.len() - packet_index,
                    )
                )]
                while packet_index < packets.len() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_jpip_snapshot_partition_missing);
                        reveal(super::jpip_automatic_packet_view);
                        reveal(super::jpip_missing_view);
                        broadcast use vstd::std_specs::iter::group_iter_axioms;
                    }
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        let ghost before_missing = super::jpip_missing_views(&missing);
                        let ghost before_native_missing = missing@;
                    }
                    let packet = packets.get(packet_index).ok_or_else(|| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })?;
                    #[cfg(verus_keep_ghost)]
                    proof! { super::jpip_missing_ref_projection(before_native_missing, before_missing, super::databin_id_view(packet.databin)); }
                    if packet.bytes.is_none()
                        && !missing
                            .iter()
                            .any(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
                                    ensures result == crate::specs::part2_jpip_identity(
                                        super::jpip_missing_view(*entry).0, super::databin_id_view(packet.databin)),
                                ))]
                                |entry: &JpipMissingRange| entry.databin().same_as(packet.databin),
                            )
                    {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(!(exists|index: int| 0 <= index < before_missing.len()
                                && crate::specs::part2_jpip_identity(before_missing[index].0,
                                    super::databin_id_view(packet.databin))));
                        }
                        missing.push(JpipMissingRange {
                            databin: packet.databin,
                            offset: packet.next_offset,
                            length: self
                                .status(packet.databin)
                                .and_then(
                                    #[cfg_attr(verus_keep_ghost, verus_spec(result: (Option<u64>) =>
                                        ensures result == super::jpip_status_view(&status).0,
                                    ))]
                                    |status| status.final_length(),
                                )
                                .map(
                                    #[cfg_attr(verus_keep_ghost, verus_spec(result: u64 =>
                                        ensures result == if length > packet.next_offset { length - packet.next_offset } else { 0 },
                                    ))]
                                    |length| length.saturating_sub(packet.next_offset),
                                ),
                        });
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(super::jpip_missing_views(&missing)
                                =~= before_missing.push(super::jpip_missing_view(missing@[missing.len() as int - 1])));
                        }
                    } else {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            if packet.bytes.is_none() {
                                assert(exists|index: int| 0 <= index < before_missing.len()
                                    && crate::specs::part2_jpip_identity(before_missing[index].0,
                                        super::databin_id_view(packet.databin)));
                            }
                        }
                    }
                    packet_index += 1;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_snapshot_partition_missing);
                    super::jpip_snapshot_tile_root_missing(current_root, partition_events, partition_packets,
                        tile_part.coding_style.layers, super::jpip_missing_views(&missing));
                    reveal(super::jpip_automatic_snapshot_result_view);
                }
                return Ok(AutomaticSnapshotResult {
                    ready: None,
                    missing,
                });
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost completed_parts = parts@.map_values(
                    |part: super::AutomaticTilePart| super::jpip_automatic_tile_part_view(&part));
                let ghost completed_packets = packets@.map_values(
                    |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet));
                let ghost completed_events = seq![tile_capacity] + packet_events;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|tail: Seq<crate::specs::Part2JpipSnapshotEvent>|
                    crate::specs::part2_jpip_snapshot_tile(current_root.input, current_root.count,
                        current_root.components, current_root.tile as usize, current_root.layout,
                        current_root.raw, current_root.headers, completed_events + tail)
                        == Some((Ok((Some(completed_parts), completed_packets, tile_part.coding_style.layers)), tail)) by {
                    assert(completed_events + tail =~= seq![tile_capacity] + (packet_events + tail));
                    assert((packet_events + tail).drop_first() =~= tail);
                    assert(crate::specs::part2_jpip_snapshot_acquired_packets(acquisition_input,
                        acquisition_parts, acquisition_transitions, acquisition_databins, acquisition_order,
                        acquisition_initial, tile_index, tile_part.component_coding_styles, packet_events + tail)
                        == Some((Ok(completed_packets), tail)));
                    assert(super::jpip_snapshot_tile_finish(current_root, acquisition_parts,
                        acquisition_transitions, completed_packets, tail)
                        == Some((Ok((Some(completed_parts), completed_packets, tile_part.coding_style.layers)), tail)));
                }
                super::jpip_snapshot_tile_root_advance(current_root, completed_events,
                    completed_parts, completed_packets, tile_part.coding_style.layers);
            }
            automatic_tiles.push(AutomaticTile { parts });
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(super::jpip_automatic_tiles_view);
                assert(super::jpip_automatic_tiles_view(automatic_tiles@)
                    =~= current_root.before.push(completed_parts));
                tile_root = crate::specs::Part2JpipSnapshotTileRoot {
                    events: current_root.events + completed_events, tile: current_root.tile + 1,
                    before: current_root.before.push(completed_parts), maximum: maximum_layers, ..current_root };
            }
            tile_index += 1;
        }

        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost snapshot_tiles = super::jpip_automatic_tiles_view(automatic_tiles@);
            let ghost available_goal = crate::specs::part2_jpip_snapshot_available(
                snapshot_tiles, 0, 0, 0, maximum_layers);
            let ghost ready_goal = crate::specs::part2_jpip_snapshot_ready(
                input.cache, snapshot_tiles, tile_root.main, maximum_layers, input.limits);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::jpip_automatic_tiles_view);
            reveal(super::jpip_automatic_tile_part_view);
            reveal(super::jpip_automatic_packet_view);
            reveal(super::jpip_automatic_snapshot_view);
            reveal(super::jpip_automatic_snapshot_result_view);
            reveal(super::jpip_byte_view);
            assert(super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers));
        }
        let mut available_layers = maximum_layers;
        let mut tile_packet_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_packet_index <= automatic_tiles.len(),
                    snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                    super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers),
                    super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                    ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                        normalized_main@, maximum_layers, input.limits),
                    available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                    available_goal == crate::specs::part2_jpip_snapshot_available(
                        snapshot_tiles, tile_packet_index as nat, 0, 0, available_layers),
                decreases automatic_tiles.len() - tile_packet_index,
            )
        )]
        while tile_packet_index < automatic_tiles.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_snapshot_available);
                reveal(super::jpip_automatic_tiles_view);
                reveal(super::jpip_automatic_tile_part_view);
                reveal(super::jpip_automatic_packet_view);
            }
            let tile = &automatic_tiles[tile_packet_index];
            let mut part_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part_index <= tile.parts.len(),
                        snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                        tile_packet_index < snapshot_tiles.len(),
                        snapshot_tiles[tile_packet_index as int] == tile.parts@.map_values(
                            |part: super::AutomaticTilePart| super::jpip_automatic_tile_part_view(&part)),
                        super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers),
                        super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                        ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                            normalized_main@, maximum_layers, input.limits),
                        available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                        available_goal == crate::specs::part2_jpip_snapshot_available(
                            snapshot_tiles, tile_packet_index as nat, part_index as nat, 0, available_layers),
                    decreases tile.parts.len() - part_index,
                )
            )]
            while part_index < tile.parts.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_snapshot_available);
                    reveal(super::jpip_automatic_tile_part_view);
                }
                let part = &tile.parts[part_index];
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= part.packets.len(),
                            snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                            tile_packet_index < snapshot_tiles.len(),
                            part_index < snapshot_tiles[tile_packet_index as int].len(),
                            snapshot_tiles[tile_packet_index as int][part_index as int]
                                == super::jpip_automatic_tile_part_view(part),
                            super::jpip_automatic_tile_part_view(part).1 == part.packets@.map_values(
                                |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet)),
                            snapshot_tiles[tile_packet_index as int] == tile.parts@.map_values(
                                |part: super::AutomaticTilePart| super::jpip_automatic_tile_part_view(&part)),
                            super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers),
                            super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                            ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                                normalized_main@, maximum_layers, input.limits),
                            available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                            available_goal == crate::specs::part2_jpip_snapshot_available(
                                snapshot_tiles, tile_packet_index as nat, part_index as nat, packet_index as nat, available_layers),
                        decreases part.packets.len() - packet_index,
                    )
                )]
                while packet_index < part.packets.len() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_jpip_snapshot_available);
                        reveal(super::jpip_automatic_packet_view);
                    }
                    let packet = &part.packets[packet_index];
                    let layer = packet.layer;
                    if packet.required && packet.bytes.is_none() {
                        available_layers = available_layers.min(layer);
                    }
                    packet_index += 1;
                }
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_snapshot_available); }
                part_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_snapshot_available); }
            tile_packet_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_snapshot_available);
            assert(available_goal == available_layers);
        }
        let mut missing = Vec::new();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost missing_goal = crate::specs::part2_jpip_snapshot_missing(
                input.cache, snapshot_tiles, available_layers, 0, 0, 0, Seq::empty());
        }
        tile_packet_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_packet_index <= automatic_tiles.len(),
                    snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                    super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers),
                    super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                    ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                        normalized_main@, maximum_layers, input.limits),
                    available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                    available_goal == available_layers,
                    missing_goal == crate::specs::part2_jpip_snapshot_missing(
                        input.cache, snapshot_tiles, available_layers, 0, 0, 0, Seq::empty()),
                    missing_goal == crate::specs::part2_jpip_snapshot_missing(
                        input.cache, snapshot_tiles, available_layers, tile_packet_index as nat, 0, 0,
                        super::jpip_missing_views(&missing)),
                decreases automatic_tiles.len() - tile_packet_index,
            )
        )]
        while tile_packet_index < automatic_tiles.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_snapshot_missing);
                reveal(super::jpip_automatic_tiles_view);
                reveal(super::jpip_automatic_tile_part_view);
                reveal(super::jpip_automatic_packet_view);
            }
            let tile = &automatic_tiles[tile_packet_index];
            let mut part_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part_index <= tile.parts.len(),
                        snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                        tile_packet_index < snapshot_tiles.len(),
                        snapshot_tiles[tile_packet_index as int] == tile.parts@.map_values(
                            |part: super::AutomaticTilePart| super::jpip_automatic_tile_part_view(&part)),
                        super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers),
                        super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                        ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                            normalized_main@, maximum_layers, input.limits),
                        available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                        available_goal == available_layers,
                        missing_goal == crate::specs::part2_jpip_snapshot_missing(
                            input.cache, snapshot_tiles, available_layers, 0, 0, 0, Seq::empty()),
                        missing_goal == crate::specs::part2_jpip_snapshot_missing(
                            input.cache, snapshot_tiles, available_layers, tile_packet_index as nat, part_index as nat, 0,
                            super::jpip_missing_views(&missing)),
                    decreases tile.parts.len() - part_index,
                )
            )]
            while part_index < tile.parts.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_snapshot_missing);
                    reveal(super::jpip_automatic_tile_part_view);
                }
                let part = &tile.parts[part_index];
                let mut packet_index = 0_usize;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant packet_index <= part.packets.len(),
                            snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                            tile_packet_index < snapshot_tiles.len(), part_index < snapshot_tiles[tile_packet_index as int].len(),
                            snapshot_tiles[tile_packet_index as int][part_index as int] == super::jpip_automatic_tile_part_view(part),
                            super::jpip_automatic_tile_part_view(part).1 == part.packets@.map_values(
                                |packet: AutomaticPacket| super::jpip_automatic_packet_view(&packet)),
                            snapshot_tiles[tile_packet_index as int] == tile.parts@.map_values(
                                |part: super::AutomaticTilePart| super::jpip_automatic_tile_part_view(&part)),
                            super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, normalized_main@, maximum_layers),
                            super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                            ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                                normalized_main@, maximum_layers, input.limits),
                            available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                            available_goal == available_layers,
                            missing_goal == crate::specs::part2_jpip_snapshot_missing(
                                input.cache, snapshot_tiles, available_layers, 0, 0, 0, Seq::empty()),
                            missing_goal == crate::specs::part2_jpip_snapshot_missing(
                                input.cache, snapshot_tiles, available_layers, tile_packet_index as nat, part_index as nat,
                                packet_index as nat, super::jpip_missing_views(&missing)),
                        decreases part.packets.len() - packet_index,
                    )
                )]
                while packet_index < part.packets.len() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part2_jpip_snapshot_missing);
                        reveal(super::jpip_automatic_packet_view);
                        reveal(super::jpip_missing_view);
                        broadcast use vstd::std_specs::iter::group_iter_axioms;
                    }
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        let ghost before_missing = super::jpip_missing_views(&missing);
                        let ghost before_native_missing = missing@;
                    }
                    let packet = &part.packets[packet_index];
                    let layer = packet.layer;
                    #[cfg(verus_keep_ghost)]
                    proof! { super::jpip_missing_ref_projection(before_native_missing, before_missing, super::databin_id_view(packet.databin)); }
                    if packet.required
                        && layer == available_layers
                        && packet.bytes.is_none()
                        && !missing
                            .iter()
                            .any(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
                                    ensures result == crate::specs::part2_jpip_identity(
                                        super::jpip_missing_view(*entry).0, super::databin_id_view(packet.databin)),
                                ))]
                                |entry: &JpipMissingRange| entry.databin().same_as(packet.databin),
                            )
                    {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(!(exists|index: int| 0 <= index < before_missing.len()
                                && crate::specs::part2_jpip_identity(before_missing[index].0,
                                    super::databin_id_view(packet.databin))));
                        }
                        let status = self.status(packet.databin);
                        let length = match status.and_then(
                            #[cfg_attr(verus_keep_ghost, verus_spec(result: (Option<u64>) =>
                                ensures result == super::jpip_status_view(&value).0,
                            ))]
                            |value| value.final_length(),
                        ) {
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
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(super::jpip_missing_views(&missing)
                                =~= before_missing.push(super::jpip_missing_view(missing@[missing.len() as int - 1])));
                        }
                    } else {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            if packet.required && layer == available_layers && packet.bytes.is_none() {
                                assert(exists|index: int| 0 <= index < before_missing.len()
                                    && crate::specs::part2_jpip_identity(before_missing[index].0,
                                        super::databin_id_view(packet.databin)));
                            }
                        }
                    }
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(super::jpip_missing_views(&missing) == crate::specs::part2_jpip_snapshot_missing_packet(
                            input.cache, super::jpip_automatic_packet_view(packet), available_layers, before_missing));
                    }
                    packet_index += 1;
                }
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_snapshot_missing); }
                part_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_snapshot_missing); }
            tile_packet_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_snapshot_missing);
            assert(missing_goal == super::jpip_missing_views(&missing));
        }
        if available_layers == 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_snapshot_root_ready_result(tile_root,
                    Ok((Some((Seq::empty(), 0, maximum_layers, missing_goal)), Seq::empty())));
                reveal(super::jpip_automatic_snapshot_view);
                reveal(super::jpip_automatic_snapshot_result_view);
                reveal(super::jpip_byte_view);
            }
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

        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost emission_goal = crate::specs::part2_jpip_snapshot_emit_tiles(
                snapshot_tiles, available_layers, 0, tile_root.main);
        }
        let mut bytes = normalized_main;
        tile_packet_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile_packet_index <= automatic_tiles.len(),
                    snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                    super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, tile_root.main, maximum_layers),
                    super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                    ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                        tile_root.main, maximum_layers, input.limits),
                    available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                    available_goal == available_layers, available_layers > 0,
                    missing_goal == crate::specs::part2_jpip_snapshot_missing(
                        input.cache, snapshot_tiles, available_layers, 0, 0, 0, Seq::empty()),
                    missing_goal == super::jpip_missing_views(&missing),
                    emission_goal == crate::specs::part2_jpip_snapshot_emit_tiles(snapshot_tiles, available_layers, 0, tile_root.main),
                    emission_goal == crate::specs::part2_jpip_snapshot_emit_tiles(
                        snapshot_tiles, available_layers, tile_packet_index as nat, bytes@),
                decreases automatic_tiles.len() - tile_packet_index,
            )
        )]
        while tile_packet_index < automatic_tiles.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_snapshot_emit_tiles);
                reveal(super::jpip_automatic_tiles_view);
            }
            let tile = &automatic_tiles[tile_packet_index];
            let mut part_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant part_index <= tile.parts.len(),
                        snapshot_tiles == super::jpip_automatic_tiles_view(automatic_tiles@),
                        tile_packet_index < snapshot_tiles.len(),
                        snapshot_tiles[tile_packet_index as int] == tile.parts@.map_values(
                            |part: super::AutomaticTilePart| super::jpip_automatic_tile_part_view(&part)),
                        super::jpip_snapshot_ready_context(tile_root, input, snapshot_tiles, tile_root.main, maximum_layers),
                        super::jpip_snapshot_inputs_match(input, self, codestream, selection, packet_selection, limits),
                        ready_goal == crate::specs::part2_jpip_snapshot_ready(input.cache, snapshot_tiles,
                            tile_root.main, maximum_layers, input.limits),
                        available_goal == crate::specs::part2_jpip_snapshot_available(snapshot_tiles, 0, 0, 0, maximum_layers),
                        available_goal == available_layers, available_layers > 0,
                        missing_goal == crate::specs::part2_jpip_snapshot_missing(
                            input.cache, snapshot_tiles, available_layers, 0, 0, 0, Seq::empty()),
                        missing_goal == super::jpip_missing_views(&missing),
                        emission_goal == crate::specs::part2_jpip_snapshot_emit_tiles(
                            snapshot_tiles, available_layers, 0, tile_root.main),
                        emission_goal == match crate::specs::part2_jpip_snapshot_emit_parts(
                            snapshot_tiles[tile_packet_index as int], available_layers, part_index as nat, bytes@) {
                            Err(error) => Err(error),
                            Ok(next) => crate::specs::part2_jpip_snapshot_emit_tiles(
                                snapshot_tiles, available_layers, tile_packet_index as nat + 1, next),
                        },
                    decreases tile.parts.len() - part_index,
                )
            )]
            while part_index < tile.parts.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_snapshot_emit_parts);
                    reveal(super::jpip_automatic_tile_part_view);
                }
                let part = &tile.parts[part_index];
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost before_emission = bytes@; }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|error: DecodeError|
                        crate::specs::part2_jpip_emit_part_phase(before_emission,
                            super::jpip_automatic_tile_part_view(part), available_layers).0 == Err(error)
                        implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                            super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                            limits, Err(error)) by {
                        assert(emission_goal == Err(error));
                        super::jpip_snapshot_root_emit_error(tile_root, available_layers, error);
                    }
                }
                emit_automatic_tile_part(&mut bytes, part, available_layers)?;
                part_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_snapshot_emit_parts); }
            tile_packet_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_snapshot_emit_tiles);
            assert(emission_goal == Ok(bytes@));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost emitted_bytes = bytes@; }
        bytes.extend_from_slice(&EOC);
        #[cfg(verus_keep_ghost)]
        proof! { assert(bytes@ =~= emitted_bytes + seq![0xffu8, 0xd9u8]); }
        if bytes.len() as u64 > limits.maximum_input_bytes() {
            #[cfg(verus_keep_ghost)]
            proof! {
                super::jpip_snapshot_root_ready_result(tile_root,
                    Err(DecodeError::LimitExceeded {
                        resource: crate::Resource::InputBytes,
                        limit: crate::limits::resource_input_byte_limit(limits),
                        actual: bytes.len() as u64,
                    }));
            }
            return Err(DecodeError::limit(
                Resource::InputBytes,
                limits.maximum_input_bytes(),
                bytes.len() as u64,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_jpip_template_finish(emitted_bytes, limits) == Ok(bytes@));
            crate::codestream::decoder_layout_errors_known();
            super::jpip_snapshot_layout_success_known();
            assert forall|error: DecodeError|
                crate::specs::part1_parse_layout(bytes@, limits) == Err(error)
                implies crate::specs::part2_jpip_automatic_snapshot_result(jpip_cache_view(self), codestream,
                    super::jpip_snapshot_selection_view(selection), super::jpip_packet_selection_view(packet_selection),
                    limits, Err(error)) by {
                super::jpip_snapshot_root_ready_result(tile_root, Err(error));
            }
        }
        crate::codestream::parse_layout(&bytes, limits)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_parse_layout(bytes@, limits).is_ok());
            super::jpip_snapshot_root_ready_result(tile_root,
                Ok((Some((bytes@, available_layers, maximum_layers, missing_goal)), Seq::empty())));
            reveal(super::jpip_automatic_snapshot_result_view);
            reveal(super::jpip_automatic_snapshot_view);
            reveal(super::jpip_byte_view);
        }
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

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_automatic_headers_result(
            jpip_cache_view(self), codestream, jpip_automatic_headers_outcome(result)),
    ))]
    pub(super) fn automatic_headers(
        &self,
        codestream: u64,
    ) -> Result<AutomaticHeaders, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost cache = jpip_cache_view(self); }
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_cache_fields(self);
            assert forall|error: DecodeError|
                crate::specs::part2_jpip_cache_view(cache,
                    (6u64, super::DatabinClass::MainHeader, codestream, 0u64)) == Err(error)
                implies crate::specs::part2_jpip_automatic_headers_result(cache, codestream, Err(error)) by {
                reveal(crate::specs::part2_jpip_automatic_headers);
                jpip_automatic_headers_witness(cache, codestream, Seq::empty(), Err(error));
            }
        }
        let main = self
            .databin_view(DatabinId::new(6, codestream, 0)?)?
            .into_bytes();
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost raw_main = main@; }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|error: DecodeError|
                crate::specs::part2_jpip_siz_cardinality(raw_main, &self.limits) == Err(error)
                implies crate::specs::part2_jpip_automatic_headers_result(cache, codestream, Err(error)) by {
                reveal(crate::specs::part2_jpip_automatic_headers);
                jpip_automatic_headers_witness(cache, codestream, Seq::empty(), Err(error));
            }
        }
        let (tile_count, components) = siz_cardinality(&main, &self.limits)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_automatic_headers);
            if tile_count > usize::MAX as u64 {
                jpip_automatic_headers_witness(cache, codestream, Seq::empty(),
                    Err(crate::specs::part2_jpip_range_overflow(0)));
            } else {
                jpip_automatic_headers_witness(cache, codestream,
                    seq![crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                        site: 0, elements: tile_count as usize, succeeded: false }],
                    Err(DecodeError::AllocationFailed));
            }
        }
        let mut tiles =
            crate::allocation::empty_with_capacity(usize::try_from(tile_count).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(0),
                    ))]
                |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost capacity = crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                site: 0, elements: tile_count as usize, succeeded: true };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(tiles@.map_values(|tile: Vec<u8>| tile@) =~= Seq::<Seq<u8>>::empty());
            assert forall|tail: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                crate::specs::part2_jpip_automatic_headers(cache, codestream, seq![capacity] + tail)
                    == crate::specs::part2_jpip_automatic_headers_bins(raw_main,
                        crate::specs::part2_jpip_automatic_raw_tiles(cache, codestream, tile_count, 0,
                            tiles@.map_values(|tile: Vec<u8>| tile@)), tile_count, components, tail) by {
                reveal(crate::specs::part2_jpip_automatic_headers);
                assert((seq![capacity] + tail).drop_first() =~= tail);
            }
        }
        let mut tile = 0_u64;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant tile <= tile_count, tile_count <= usize::MAX as u64,
                    raw_main == main@, cache == jpip_cache_view(self), cache.0 == self.limits,
                    forall|tail: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                        crate::specs::part2_jpip_automatic_headers(cache, codestream, seq![capacity] + tail)
                            == crate::specs::part2_jpip_automatic_headers_bins(raw_main,
                                crate::specs::part2_jpip_automatic_raw_tiles(cache, codestream, tile_count,
                                    tile as nat, tiles@.map_values(|tile: Vec<u8>| tile@)),
                                tile_count, components, tail),
                decreases tile_count - tile,
            )
        )]
        while tile < tile_count {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_tiles = tiles@.map_values(|tile: Vec<u8>| tile@);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_automatic_raw_tiles);
                assert forall|error: DecodeError|
                    crate::specs::part2_jpip_cache_view(cache,
                        (2u64, super::DatabinClass::TileHeader, codestream, tile)) == Err(error)
                    implies crate::specs::part2_jpip_automatic_headers_result(cache, codestream, Err(error)) by {
                    assert(seq![capacity] + Seq::empty() =~= seq![capacity]);
                    assert(crate::specs::part2_jpip_automatic_headers(cache, codestream, seq![capacity] + Seq::empty())
                        == crate::specs::part2_jpip_automatic_headers_bins(raw_main,
                            crate::specs::part2_jpip_automatic_raw_tiles(cache, codestream, tile_count,
                                tile as nat, tiles@.map_values(|tile: Vec<u8>| tile@)),
                            tile_count, components, Seq::empty()));
                    jpip_automatic_headers_witness(cache, codestream, seq![capacity], Err(error));
                }
            }
            tiles.push(
                self.databin_view(DatabinId::new(2, codestream, tile)?)?
                    .into_bytes(),
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_automatic_raw_tiles);
                let bytes = crate::specs::part2_jpip_cache_view(cache,
                    (2u64, super::DatabinClass::TileHeader, codestream, tile)).get_Ok_0();
                assert(crate::specs::part2_jpip_cache_view(cache,
                    (2u64, super::DatabinClass::TileHeader, codestream, tile)) == Ok(bytes));
                assert(tiles@.map_values(|tile: Vec<u8>| tile@) =~= previous_tiles.push(bytes));
                assert forall|tail: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                    crate::specs::part2_jpip_automatic_headers(cache, codestream, seq![capacity] + tail)
                        == crate::specs::part2_jpip_automatic_headers_bins(raw_main,
                            crate::specs::part2_jpip_automatic_raw_tiles(cache, codestream, tile_count,
                                tile as nat + 1, tiles@.map_values(|tile: Vec<u8>| tile@)),
                            tile_count, components, tail) by {
                    assert(crate::specs::part2_jpip_automatic_headers(cache, codestream, seq![capacity] + tail)
                        == crate::specs::part2_jpip_automatic_headers_bins(raw_main,
                            crate::specs::part2_jpip_automatic_raw_tiles(cache, codestream, tile_count,
                                tile as nat, previous_tiles), tile_count, components, tail));
                }
            }
            tile += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost raw_tiles = tiles@.map_values(|tile: Vec<u8>| tile@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_automatic_raw_tiles);
            assert forall|error: DecodeError|
                crate::specs::part2_jpip_main_header_result(raw_main, Err(error))
                implies crate::specs::part2_jpip_automatic_headers_result(cache, codestream, Err(error)) by {
                let calls = choose|calls: Seq<crate::specs::Part2JpipStorageEvent>|
                    crate::specs::part2_jpip_normalize_main_header(raw_main, calls) == Some(Err(error));
                let event = crate::specs::Part2JpipAutomaticHeaderEvent::Main { calls };
                assert(seq![capacity] + seq![event] =~= seq![capacity, event]);
                assert(crate::specs::part2_jpip_automatic_headers(cache, codestream, seq![capacity] + seq![event])
                    == crate::specs::part2_jpip_automatic_headers_bins(raw_main, Ok(raw_tiles),
                        tile_count, components, seq![event]));
                jpip_automatic_headers_witness(cache, codestream, seq![capacity, event], Err(error));
            }
        }
        let main = normalize_main_header(&main)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost calls = choose|calls: Seq<crate::specs::Part2JpipStorageEvent>|
                crate::specs::part2_jpip_normalize_main_header(raw_main, calls) == Some(Ok(main@));
            let ghost main_event = crate::specs::Part2JpipAutomaticHeaderEvent::Main { calls };
            let ghost prefix = seq![capacity, main_event,
                crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                    site: 1, elements: tiles.len(), succeeded: true }];
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(seq![capacity] + seq![main_event,
                crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                    site: 1, elements: tiles.len(), succeeded: false }]
                =~= seq![capacity, main_event,
                    crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                        site: 1, elements: tiles.len(), succeeded: false }]);
            jpip_automatic_headers_witness(cache, codestream,
                seq![capacity, main_event, crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                    site: 1, elements: tiles.len(), succeeded: false }], Err(DecodeError::AllocationFailed));
        }
        let mut normalized = crate::allocation::empty_with_capacity(tiles.len())?;
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(normalized@.map_values(|tile: Vec<u8>| tile@) =~= Seq::<Seq<u8>>::empty());
            assert forall|tail: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                crate::specs::part2_jpip_automatic_headers(cache, codestream, prefix + tail)
                    == match crate::specs::part2_jpip_automatic_first_tiles(raw_tiles, 0, Seq::empty()) {
                        Err(error) => crate::specs::part2_jpip_automatic_headers_finish(Err(error), tail),
                        Ok(tiles) => crate::specs::part2_jpip_automatic_headers_finish(
                            Ok((main@, tiles, tile_count, components)), tail),
                    } by {
                assert(prefix + tail =~= seq![capacity] + seq![main_event,
                    crate::specs::Part2JpipAutomaticHeaderEvent::Capacity {
                        site: 1, elements: tiles.len(), succeeded: true }] + tail);
            }
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= tiles.len(), normalized.len() == index,
                    cache == jpip_cache_view(self), cache.0 == self.limits,
                    raw_tiles == tiles@.map_values(|tile: Vec<u8>| tile@),
                    forall|tail: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                        crate::specs::part2_jpip_automatic_headers(cache, codestream, prefix + tail)
                            == match crate::specs::part2_jpip_automatic_first_tiles(raw_tiles,
                                index as nat, normalized@.map_values(|tile: Vec<u8>| tile@)) {
                                Err(error) => crate::specs::part2_jpip_automatic_headers_finish(Err(error), tail),
                                Ok(tiles) => crate::specs::part2_jpip_automatic_headers_finish(
                                    Ok((main@, tiles, tile_count, components)), tail),
                            },
                decreases tiles.len() - index,
            )
        )]
        while index < tiles.len() {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_normalized = normalized@.map_values(|tile: Vec<u8>| tile@);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_automatic_first_tiles);
                assert forall|error: DecodeError|
                    crate::specs::part2_jpip_automatic_first_tiles(raw_tiles,
                        index as nat, normalized@.map_values(|tile: Vec<u8>| tile@)) == Err(error)
                    implies crate::specs::part2_jpip_automatic_headers_result(cache, codestream, Err(error)) by {
                    assert(prefix + Seq::empty() =~= prefix);
                    assert(crate::specs::part2_jpip_automatic_headers(cache, codestream, prefix + Seq::empty())
                        == crate::specs::part2_jpip_automatic_headers_finish(Err(error), Seq::empty()));
                    jpip_automatic_headers_witness(cache, codestream, prefix, Err(error));
                }
                if index > u16::MAX as usize {
                    assert(crate::specs::part2_jpip_automatic_headers_result(cache, codestream,
                        Err(crate::specs::part2_jpip_range_overflow(0))));
                } else {
                    assert forall|error: DecodeError|
                        crate::specs::part2_jpip_normalize_automatic_tile_headers(raw_tiles[index as int], index as u16)
                            == Err(error)
                        implies crate::specs::part2_jpip_automatic_headers_result(cache, codestream, Err(error)) by {
                        assert(crate::specs::part2_jpip_automatic_first_tiles(raw_tiles,
                            index as nat, normalized@.map_values(|tile: Vec<u8>| tile@)) == Err(error));
                    }
                }
            }
            let headers = normalize_automatic_tile_headers(
                &tiles[index],
                u16::try_from(index).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?,
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_automatic_first_tiles);
                if headers.len() == 0 {
                    assert(crate::specs::part2_jpip_automatic_first_tiles(raw_tiles,
                        index as nat, previous_normalized) == Err(
                            crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure)));
                    assert(crate::specs::part2_jpip_automatic_headers_result(cache, codestream,
                        Err(crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure))));
                }
            }
            normalized.push(
                headers
                    .first()
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::MissingRequiredStructure),
                        ))]
                        || DecodeError::malformed(0, MalformedKind::MissingRequiredStructure),
                    )?
                    .clone(),
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_automatic_first_tiles);
                assert(normalized@[index as int]@ =~= headers@[0]@);
                assert(normalized@.map_values(|tile: Vec<u8>| tile@)
                    =~= previous_normalized.push(headers@[0]@));
                assert forall|tail: Seq<crate::specs::Part2JpipAutomaticHeaderEvent>|
                    crate::specs::part2_jpip_automatic_headers(cache, codestream, prefix + tail)
                        == match crate::specs::part2_jpip_automatic_first_tiles(raw_tiles,
                            index as nat + 1, normalized@.map_values(|tile: Vec<u8>| tile@)) {
                            Err(error) => crate::specs::part2_jpip_automatic_headers_finish(Err(error), tail),
                            Ok(tiles) => crate::specs::part2_jpip_automatic_headers_finish(
                                Ok((main@, tiles, tile_count, components)), tail),
                        } by {
                    assert(crate::specs::part2_jpip_automatic_headers(cache, codestream, prefix + tail)
                        == match crate::specs::part2_jpip_automatic_first_tiles(raw_tiles,
                            index as nat, previous_normalized) {
                            Err(error) => crate::specs::part2_jpip_automatic_headers_finish(Err(error), tail),
                            Ok(tiles) => crate::specs::part2_jpip_automatic_headers_finish(
                                Ok((main@, tiles, tile_count, components)), tail),
                        });
                }
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(jpip_automatic_headers_view);
            reveal(crate::specs::part2_jpip_automatic_first_tiles);
            assert(prefix + Seq::empty() =~= prefix);
            assert(crate::specs::part2_jpip_automatic_headers(cache, codestream, prefix + Seq::empty())
                == crate::specs::part2_jpip_automatic_headers_finish(
                    Ok((main@, normalized@.map_values(|tile: Vec<u8>| tile@), tile_count, components)), Seq::empty()));
            jpip_automatic_headers_witness(cache, codestream, prefix,
                Ok((main@, normalized@.map_values(|tile: Vec<u8>| tile@), tile_count, components)));
        }
        Ok(AutomaticHeaders {
            main,
            tiles: normalized,
            tile_count,
            components,
        })
    }
}
