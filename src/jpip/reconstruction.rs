//! Complete data-bin reconstruction and recursive metadata placeholder expansion.

use super::{
    DatabinCache, DatabinClass, DatabinId, DecodeError, EOC, JpipAvailability, JpipByteView,
    JpipContainerAssembly, JpipMissingRange, JpipPacketSelection, JpipPlaceholder,
    JpipSemanticNeed, JpipSemanticNeedKind, MalformedKind, Resource, SOC, append_missing_ranges,
    copy_bytes, read_u32_be, read_u64_be, write_u32_be, write_u64_be,
};
#[cfg(verus_keep_ghost)]
use super::{
    databin_id_view, jpip_byte_outcome, jpip_byte_view, jpip_cache_view, jpip_layout_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(super) enum PlaceholderSource {
    Original,
    Equivalent,
    Codestream,
    Empty,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) open spec fn semantic_state_view(
        active: Seq<u64>, output: Seq<u8>, missing: Seq<JpipMissingRange>, needs: Seq<JpipSemanticNeed>,
    ) -> crate::specs::Part2JpipSemanticState {
        crate::specs::Part2JpipSemanticState {
            active, output,
            missing: missing.map_values(|range: JpipMissingRange| super::jpip_missing_view(range)),
            needs: needs.map_values(|need: JpipSemanticNeed| super::jpip_semantic_need_view(need)),
        }
    }

    pub(super) open spec fn placeholder_source_view(source: PlaceholderSource) -> u8 {
        match source {
            PlaceholderSource::Original => 0,
            PlaceholderSource::Equivalent => 1,
            PlaceholderSource::Codestream => 2,
            PlaceholderSource::Empty => 3,
        }
    }

    pub(super) open spec fn placeholder_header_option_view(
        header: Option<&[u8]>,
    ) -> Option<Seq<u8>> {
        match header { Some(bytes) => Some(bytes@), None => None }
    }

    pub(super) open spec fn placeholder_reconstruction_outcome(
        value: Result<(PlaceholderSource, &[u8]), DecodeError>,
    ) -> Result<(u8, Seq<u8>), DecodeError> {
        match value {
            Ok((source, header)) => Ok((placeholder_source_view(source), header@)),
            Err(error) => Err(error),
        }
    }

    pub(super) open spec fn placeholder_value_view(
        value: JpipPlaceholder,
    ) -> crate::specs::Part2JpipPlaceholder {
        crate::specs::Part2JpipPlaceholder {
            flags: value.flags, bin: value.bin,
            original_header: value.original_header@, original_type: value.original_type,
            equivalent_bin: value.equivalent_bin,
            equivalent_header: match value.equivalent_header {
                Some(header) => Some(header@), None => None,
            },
            equivalent_type: value.equivalent_type,
            stream: value.stream, stream_count: value.stream_count,
        }
    }

    pub(super) open spec fn placeholder_parse_outcome(
        result: Result<JpipPlaceholder, DecodeError>,
    ) -> Result<crate::specs::Part2JpipPlaceholder, DecodeError> {
        match result {
            Ok(value) => Ok(placeholder_value_view(value)),
            Err(error) => Err(error),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures placeholder_reconstruction_outcome(result)
        == crate::specs::part2_jpip_placeholder_reconstruction(
            flags, original@, placeholder_header_option_view(equivalent),
        ),
))]
pub(super) fn placeholder_reconstruction<'a>(
    flags: u32,
    original: &'a [u8],
    equivalent: Option<&'a [u8]>,
) -> Result<(PlaceholderSource, &'a [u8]), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_jpip_placeholder_reconstruction); }
    if flags & 1 != 0 {
        Ok((PlaceholderSource::Original, original))
    } else if flags & 2 != 0 {
        match equivalent {
            Some(header) => Ok((PlaceholderSource::Equivalent, header)),
            None => Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents)),
        }
    } else if flags & 4 != 0 {
        Ok((PlaceholderSource::Codestream, original))
    } else {
        Ok((PlaceholderSource::Empty, original))
    }
}

impl DatabinCache {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_byte_outcome(result) == crate::specs::part2_jpip_cache_codestream(
            jpip_cache_view(self), jpip_layout_view(layout)),
    ))]
    pub fn reconstruct_codestream(
        &self,
        layout: &[DatabinId],
    ) -> Result<JpipByteView, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost identifiers = jpip_layout_view(layout); }
        #[cfg(verus_keep_ghost)]
        proof! {
            let length = layout.len();
            assert((length & 1_usize) == length % 2_usize) by(bit_vector);
        }
        if layout.len() < 3 || layout.len() & 1 == 0 {
            return Err(DecodeError::malformed(
                layout.len() as u64,
                MalformedKind::InvalidJpipLayout,
            ));
        }
        let first = layout[0];
        if !matches!(first.class, DatabinClass::MainHeader) || first.in_class != 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        let mut pair = 1_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant pair <= layout.len(),
                    identifiers == jpip_layout_view(layout),
                    identifiers.len() == layout.len(),
                    forall|position: int| 0 <= position < layout.len() ==>
                        #[trigger] identifiers[position] == databin_id_view(layout@[position]),
                    layout.len() >= 3, layout.len() % 2 == 1, pair % 2 == 1,
                    databin_id_view(first) == identifiers[0],
                    first.class == DatabinClass::MainHeader, first.in_class == 0,
                    crate::specs::part2_jpip_codestream_pairs(identifiers, 1) ==
                        crate::specs::part2_jpip_codestream_pairs(identifiers, pair as nat),
                decreases layout.len() - pair,
            )
        )]
        while pair < layout.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_codestream_pairs); }
            let data_index = pair.checked_add(1).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(pair as u64, MalformedKind::ArithmeticOverflow),
                ))]
                || {
                DecodeError::malformed(pair as u64, MalformedKind::ArithmeticOverflow)
            })?;
            let header = *layout.get(pair).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_layout_error(pair as u64),
                ))]
                || DecodeError::malformed(pair as u64, MalformedKind::InvalidJpipLayout),
            )?;
            let data = *layout.get(data_index).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_layout_error(data_index as u64),
                ))]
                || DecodeError::malformed(data_index as u64, MalformedKind::InvalidJpipLayout),
            )?;
            if !matches!(header.class, DatabinClass::TileHeader)
                || !matches!(data.class, DatabinClass::TileData)
                || header.codestream != first.codestream
                || data.codestream != first.codestream
                || header.in_class != data.in_class
            {
                return Err(DecodeError::malformed(
                    pair as u64,
                    MalformedKind::InvalidJpipLayout,
                ));
            }
            pair += 2;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_codestream_pairs); }
        let view = self.reconstruct(layout)?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_byte_view); }
        if !view.bytes.starts_with(&SOC) || !view.bytes.ends_with(&EOC) {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        Ok(view)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_byte_outcome(result) == crate::specs::part2_jpip_cache_container(
            jpip_cache_view(self), jpip_layout_view(layout)),
    ))]
    pub fn reconstruct_container(&self, layout: &[DatabinId]) -> Result<JpipByteView, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost identifiers = jpip_layout_view(layout); }
        if layout.is_empty() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= layout.len(),
                    identifiers == jpip_layout_view(layout),
                    identifiers.len() == layout.len(), layout.len() > 0,
                    forall|position: int| 0 <= position < layout.len() ==>
                        #[trigger] identifiers[position] == databin_id_view(layout@[position]),
                    crate::specs::part2_jpip_metadata_layout(identifiers, 0) ==
                        crate::specs::part2_jpip_metadata_layout(identifiers, index as nat),
                decreases layout.len() - index,
            )
        )]
        while index < layout.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_metadata_layout); }
            if !matches!(layout[index].class, DatabinClass::Metadata) {
                return Err(DecodeError::malformed(
                    index as u64,
                    MalformedKind::InvalidJpipLayout,
                ));
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_metadata_layout); }
        self.reconstruct(layout)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_semantic_assembly_result(jpip_cache_view(self), metadata_codestream,
            super::jpip_container_assembly_outcome(result)),
    ))]
    pub fn assemble_semantic_container(
        &self,
        metadata_codestream: u64,
    ) -> Result<JpipContainerAssembly, DecodeError> {
        let mut output = Vec::new();
        let mut missing = Vec::new();
        let mut needs = Vec::new();
        let mut active = Vec::new();
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost cache = jpip_cache_view(self); }
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_cache_fields(self);
            reveal(super::jpip_container_assembly_view);
            reveal(crate::specs::part2_jpip_semantic_assembly_run);
            assert(semantic_state_view(active@, output@, missing@, needs@).missing =~= Seq::empty());
            assert(semantic_state_view(active@, output@, missing@, needs@).needs =~= Seq::empty());
            assert forall|error: DecodeError, after: crate::specs::Part2JpipSemanticState|
                crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, 0, true, 0, u32::MAX,
                    semantic_state_view(active@, output@, missing@, needs@), Err(error), after)
                implies crate::specs::part2_jpip_semantic_assembly_result(cache, metadata_codestream, Err(error)) by {
                crate::specs::part2_jpip_semantic_assembly_first_error(cache, metadata_codestream, error, after);
            }
        }
        let complete = self.expand_metadata_bin(
            metadata_codestream,
            0,
            true,
            0,
            u32::MAX,
            &mut active,
            &mut output,
            &mut missing,
            &mut needs,
        )?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_semantic_expand_result); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = crate::specs::Part2JpipSemanticState {
                active: Seq::empty(), output: Seq::empty(), missing: Seq::empty(), needs: Seq::empty() };
            let ghost after = semantic_state_view(active@, output@, missing@, needs@);
            let ghost events = choose|events: Seq<crate::specs::Part2JpipSemanticEvent>|
                #[trigger] crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, 0, true, 0, u32::MAX,
                    before, events) == Some((Ok(complete), after, Seq::empty()));
        }
        if !complete {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_jpip_semantic_assembly_witness(cache, metadata_codestream, events,
                    Ok((if output.len() == 0 { JpipAvailability::Missing } else { JpipAvailability::Partial },
                        super::jpip_missing_views(&missing), super::jpip_semantic_needs_view(&needs), None)));
            }
            return Ok(JpipContainerAssembly {
                status: if output.is_empty() {
                    JpipAvailability::Missing
                } else {
                    JpipAvailability::Partial
                },
                missing,
                needs,
                container: None,
            });
        }
        if output.len() as u64 > self.limits.maximum_input_bytes() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_jpip_semantic_assembly_witness(cache, metadata_codestream, events,
                    Err(DecodeError::LimitExceeded { resource: Resource::InputBytes,
                        limit: crate::limits::resource_input_byte_limit(&cache.0), actual: output.len() as u64 }));
            }
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.limits.maximum_input_bytes(),
                output.len() as u64,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|error: DecodeError|
                crate::specs::part2_parse_and_inspect_container(output@, &self.limits) == Err(error)
                implies crate::specs::part2_jpip_semantic_assembly_result(cache, metadata_codestream, Err(error)) by {
                crate::specs::part2_jpip_semantic_assembly_witness(cache, metadata_codestream, events, Err(error));
            }
        }
        crate::jp2::parse_and_inspect(&output, &self.limits)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_jpip_semantic_assembly_witness(cache, metadata_codestream, events,
                Ok((JpipAvailability::Available, super::jpip_missing_views(&missing),
                    super::jpip_semantic_needs_view(&needs), Some(output@))));
        }
        Ok(JpipContainerAssembly {
            status: JpipAvailability::Available,
            missing,
            needs,
            container: Some(JpipByteView { bytes: output }),
        })
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_jpip_semantic_expand_result(jpip_cache_view(self), metadata_codestream,
            bin, boxes, depth, remaining_depth,
            semantic_state_view(old(active)@, old(output)@, old(missing)@, old(needs)@), result,
            semantic_state_view(final(active)@, final(output)@, final(missing)@, final(needs)@)),
            crate::specs::part2_jpip_semantic_expand_trace(jpip_cache_view(self), metadata_codestream,
                bin, boxes, depth, remaining_depth,
                semantic_state_view(old(active)@, old(output)@, old(missing)@, old(needs)@), result,
                semantic_state_view(final(active)@, final(output)@, final(missing)@, final(needs)@)),
            result.is_ok() ==> final(active)@ == old(active)@,
        decreases remaining_depth,
    ))]
    fn expand_metadata_bin(
        &self,
        metadata_codestream: u64,
        bin: u64,
        boxes: bool,
        depth: u32,
        remaining_depth: u32,
        active: &mut Vec<u64>,
        output: &mut Vec<u8>,
        missing: &mut Vec<JpipMissingRange>,
        needs: &mut Vec<JpipSemanticNeed>,
    ) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = semantic_state_view(active@, output@, missing@, needs@);
            let ghost cache = jpip_cache_view(self);
            let ghost semantic_root = crate::specs::Part2JpipSemanticRoot {
                cache, metadata_stream: metadata_codestream, bin, boxes, depth, remaining_depth, before,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            super::jpip_cache_fields(self);
            reveal(crate::specs::part2_jpip_semantic_expand);
        }
        if !crate::refinement::jpip_metadata_descent_allowed(
            depth,
            self.limits.maximum_box_depth(),
            false,
        ) {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                    remaining_depth, before, Err(DecodeError::LimitExceeded { resource: Resource::BoxDepth,
                        limit: crate::limits::resource_box_depth_limit(&cache.0) as u64, actual: depth as u64 }),
                    before, Seq::empty());
            }
            return Err(DecodeError::limit(
                Resource::BoxDepth,
                u64::from(self.limits.maximum_box_depth()),
                u64::from(depth),
            ));
        }
        let mut active_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant active_index <= active.len(),
                    semantic_root == (crate::specs::Part2JpipSemanticRoot {
                        cache, metadata_stream: metadata_codestream, bin, boxes, depth, remaining_depth, before,
                    }),
                    before == semantic_state_view(active@, output@, missing@, needs@),
                    cache == jpip_cache_view(self), cache.0 == self.limits,
                    depth <= crate::limits::resource_box_depth_limit(&cache.0),
                    forall|index: int| 0 <= index < active_index ==> #[trigger] active@[index] != bin,
                decreases active.len() - active_index,
            )
        )]
        while active_index < active.len() {
            if !crate::refinement::jpip_metadata_descent_allowed(
                depth,
                self.limits.maximum_box_depth(),
                active[active_index] == bin,
            ) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_semantic_expand);
                    crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                        remaining_depth, before, Err(crate::specs::part2_jpip_cache_error(bin, MalformedKind::InvalidBoxContents)),
                        before, Seq::empty());
                }
                return Err(DecodeError::malformed(
                    bin,
                    MalformedKind::InvalidBoxContents,
                ));
            }
            active_index += 1;
        }
        let id = DatabinId::new(8, metadata_codestream, bin)?;
        if !self.is_complete(id) {
            append_missing_ranges(missing, &self.complete_databin_missing(id));
            needs.push(JpipSemanticNeed {
                kind: JpipSemanticNeedKind::MetadataBin,
                identifier: bin,
            });
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(super::jpip_semantic_need_view);
                assert(semantic_state_view(active@, output@, missing@, needs@).needs
                    =~= before.needs.push((JpipSemanticNeedKind::MetadataBin, bin)));
                crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                    remaining_depth, before, Ok(false), semantic_state_view(active@, output@, missing@, needs@), Seq::empty());
            }
            return Ok(false);
        }
        let bytes = self.databin_view(id)?.into_bytes();
        if !boxes {
            output.extend_from_slice(&bytes);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(output@ =~= before.output + bytes@);
                crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                    remaining_depth, before, Ok(true), semantic_state_view(active@, output@, missing@, needs@), Seq::empty());
            }
            return Ok(true);
        }
        active.push(bin);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|error: DecodeError|
                crate::specs::part2_box_reader_from_input(bytes@, self.limits) == Err(error)
                implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                    remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@))
                    && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                        remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@)) by {
                reveal(crate::specs::part2_jpip_semantic_expand);
                crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                    remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@), Seq::empty());
            }
        }
        let mut reader = crate::jp2::BoxReader::new(&bytes, &self.limits)?;
        let mut complete = true;
        let mut remaining_boxes = bytes.len();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost mut semantic_events = Seq::<crate::specs::Part2JpipSemanticEvent>::empty();
            let ghost mut reader_before = crate::jp2::box_reader_state(&reader);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(active@ =~= before.active.push(bin));
            assert(!before.active.contains(bin));
            assert(crate::specs::part2_jpip_cache_view(cache, super::databin_id_view(id)) == Ok(bytes@));
            assert(crate::specs::part2_box_reader_from_input(bytes@, cache.0) == Ok(crate::jp2::box_reader_state(&reader)));
            assert(crate::specs::part2_jpip_cache_complete(cache, super::databin_id_view(id)));
            assert(semantic_state_view(active@, output@, missing@, needs@)
                == (crate::specs::Part2JpipSemanticState { active: before.active.push(bin), ..before }));
            crate::specs::part2_jpip_semantic_boxes_prefix(cache, metadata_codestream, bin, depth,
                remaining_depth, before, bytes@, reader_before);
            reveal(crate::specs::part2_jpip_semantic_expand);
            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                    before, semantic_events + tail)
                    == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                        reader_before, remaining_boxes as nat, complete,
                        semantic_state_view(active@, output@, missing@, needs@), tail) by {
                assert(semantic_events + tail =~= tail);
            }
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant cache == jpip_cache_view(self), cache.0 == self.limits,
                    semantic_root == (crate::specs::Part2JpipSemanticRoot {
                        cache, metadata_stream: metadata_codestream, bin, boxes, depth, remaining_depth, before,
                    }),
                    before == semantic_state_view(old(active)@, old(output)@, old(missing)@, old(needs)@),
                    boxes,
                    reader_before.input == bytes@,
                    active@ == before.active.push(bin),
                    forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                        crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail)
                        == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                            reader_before, remaining_boxes as nat, complete,
                            semantic_state_view(active@, output@, missing@, needs@), tail),
                invariant_except_break reader_before == crate::jp2::box_reader_state(&reader),
                ensures crate::specs::part2_box_reader_next_ref(reader_before).0.is_none(),
                decreases remaining_boxes,
            )
        )]
        while let Some(box_result) = reader.next_box_ref() {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost next = crate::specs::part2_box_reader_next_ref(reader_before);
                let ghost prior_remaining_boxes = remaining_boxes as nat;
                let ghost prior_complete = complete;
                let ghost prior_state = semantic_state_view(active@, output@, missing@, needs@);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(next.0 == crate::jp2::box_ref_outcome(Some(box_result)));
                assert(next.1 == crate::jp2::box_reader_state(&reader));
                crate::specs::part2_jpip_semantic_reader_frame(reader_before);
            }
            if remaining_boxes == 0 {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal_with_fuel(crate::specs::part2_jpip_semantic_boxes, 2);
                    assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                        crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail)
                            == Some((Err(crate::specs::part2_jpip_cache_error(bin, MalformedKind::InvalidBoxLength)),
                                prior_state, tail)) by {
                        assert(crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail)
                            == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                reader_before, 0, complete, prior_state, tail));
                        assert(crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                            reader_before, 0, complete, prior_state, tail)
                            == Some((Err(crate::specs::part2_jpip_cache_error(bin, MalformedKind::InvalidBoxLength)), prior_state, tail)));
                    }
                    crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                        remaining_depth, before, Err(crate::specs::part2_jpip_cache_error(bin, MalformedKind::InvalidBoxLength)),
                        prior_state, semantic_events);
                }
                return Err(DecodeError::malformed(bin, MalformedKind::InvalidBoxLength));
            }
            remaining_boxes -= 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Err(error) = box_result {
                    reveal_with_fuel(crate::specs::part2_jpip_semantic_boxes, 2);
                    assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                        crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail) == Some((Err(error), prior_state, tail)) by {
                        assert(crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail)
                            == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                reader_before, prior_remaining_boxes, complete, prior_state, tail));
                        assert(crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                            reader_before, prior_remaining_boxes, complete, prior_state, tail) == Some((Err(error), prior_state, tail)));
                    }
                    crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                        remaining_depth, before, Err(error), prior_state, semantic_events);
                }
            }
            let box_ref = box_result?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(next.0 == Some(Ok(crate::jp2::box_reference_view(box_ref))));
                assert(crate::jp2::box_reference_view(box_ref).1 == box_ref.payload@);
                crate::specs::part2_jpip_semantic_box_bounds(reader_before, crate::jp2::box_reference_view(box_ref));
                crate::jp2::box_header_offset_view(box_ref.header);
            }
            if box_ref
                .header
                .box_type()
                .equals(crate::jp2::BoxType::new(*b"phld"))
            {
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost placeholder_parent_events = semantic_events;
                    let ghost parent_bin = bin;
                    let ghost mut placeholder_events = Seq::<crate::specs::Part2JpipSemanticEvent>::empty();
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(prior_remaining_boxes > 0);
                    assert(crate::jp2::box_reference_view(box_ref).0.0 == crate::jp2::box_type_from_bytes_model(*b"phld"));
                    crate::specs::part2_jpip_semantic_placeholder_box_step(cache, metadata_codestream, bin, depth, remaining_depth,
                        reader_before, prior_remaining_boxes, complete, prior_state, crate::jp2::box_reference_view(box_ref));
                    assert forall|events: Seq<crate::specs::Part2JpipSemanticEvent>|
                        match #[trigger] crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream,
                            box_ref.payload@, depth, remaining_depth, prior_state, events) {
                            Some((Err(error), after, tail)) => crate::specs::part2_jpip_semantic_expand(
                                cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                                before, placeholder_parent_events + events) == Some((Err(error), after, tail)),
                            _ => true,
                        } by {
                        assert(crate::specs::part2_jpip_semantic_expand(
                            cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, placeholder_parent_events + events)
                            == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                reader_before, prior_remaining_boxes, complete, prior_state, events));
                        if let Some((Err(error), after, tail)) = crate::specs::part2_jpip_semantic_placeholder(
                            cache, metadata_codestream, box_ref.payload@, depth, remaining_depth, prior_state, events) {
                            assert(crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                reader_before, prior_remaining_boxes, complete, prior_state, events)
                                == Some((Err(error), after, tail)));
                        }
                    }
                    assert(crate::specs::part2_jpip_semantic_placeholder_error_continuation(
                        cache, metadata_codestream, bin, boxes, depth, remaining_depth, before,
                        placeholder_parent_events, box_ref.payload@, prior_state));
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|error: DecodeError|
                        crate::specs::part2_jpip_parse_placeholder(box_ref.payload@) == Err(error)
                        implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                            remaining_depth, before, Err(error), prior_state)
                            && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                                remaining_depth, before, Err(error), prior_state) by {
                        reveal_with_fuel(crate::specs::part2_jpip_semantic_placeholder, 2);
                        assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                            crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                                before, semantic_events + tail) == Some((Err(error), prior_state, tail)) by {
                            assert(crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream, box_ref.payload@,
                                depth, remaining_depth, prior_state, tail) == Some((Err(error), prior_state, tail)));
                        }
                        crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                            remaining_depth, before, Err(error), prior_state, semantic_events);
                    }
                }
                let placeholder = parse_jpip_placeholder(box_ref.payload)?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_jpip_semantic_placeholder_fields(box_ref.payload@, placeholder_value_view(placeholder));
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|error: DecodeError|
                        crate::specs::part2_jpip_placeholder_reconstruction(placeholder.flags,
                            placeholder.original_header@,
                            match &placeholder.equivalent_header { None => None, Some(bytes) => Some(bytes@) }) == Err(error)
                        implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                            remaining_depth, before, Err(error), prior_state)
                            && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                                remaining_depth, before, Err(error), prior_state) by {
                        reveal_with_fuel(crate::specs::part2_jpip_semantic_placeholder, 2);
                        assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                            crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream, box_ref.payload@,
                                depth, remaining_depth, prior_state, tail) == Some((Err(error), prior_state, tail)) by {
                        }
                        assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                            crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                                before, placeholder_parent_events + tail) == Some((Err(error), prior_state, tail)) by {
                            assert(crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream, box_ref.payload@,
                                depth, remaining_depth, prior_state, tail) == Some((Err(error), prior_state, tail)));
                        }
                        crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                            remaining_depth, before, Err(error), prior_state, placeholder_parent_events);
                    }
                }
                let (source, header) = placeholder_reconstruction(
                    placeholder.flags,
                    &placeholder.original_header,
                    match &placeholder.equivalent_header {
                        Some(header) => Some(header.as_slice()),
                        None => None,
                    },
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_placeholder_reconstruction);
                    assert(placeholder_source_view(source) == 1 ==> placeholder.flags & 2 != 0);
                    assert(placeholder_source_view(source) == 2 ==> placeholder.flags & 4 != 0);
                    if (placeholder_source_view(source) == 0
                        || (placeholder_source_view(source) == 1 && placeholder.equivalent_bin.is_some() && placeholder.equivalent_type.is_some()))
                        && (depth == u32::MAX || remaining_depth == 0) {
                        reveal_with_fuel(crate::specs::part2_jpip_semantic_placeholder, 2);
                        assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                            crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                                before, placeholder_parent_events + tail)
                                == Some((Err(crate::specs::part2_jpip_range_overflow(0)), prior_state, tail)) by {
                            assert(crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream, box_ref.payload@,
                                depth, remaining_depth, prior_state, tail)
                                == Some((Err(crate::specs::part2_jpip_range_overflow(0)), prior_state, tail)));
                        }
                        crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, Err(crate::specs::part2_jpip_range_overflow(0)), prior_state, placeholder_parent_events);
                    }
                }
                let mut payload = Vec::new();
                let mut appended = false;
                let replacement_complete = match source {
                    PlaceholderSource::Original => {
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost child_before = semantic_state_view(active@, payload@, missing@, needs@);
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(child_before == (crate::specs::Part2JpipSemanticState { output: Seq::empty(), ..prior_state }));
                            assert forall|error: DecodeError, child: crate::specs::Part2JpipSemanticState|
                                depth < u32::MAX && remaining_depth > 0
                                && #[trigger] crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, placeholder.bin,
                                    crate::specs::part2_jpip_superbox(placeholder.original_type), (depth + 1) as u32,
                                    (remaining_depth - 1) as u32, child_before, Err(error), child)
                                implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                                    remaining_depth, before, Err(error),
                                    crate::specs::Part2JpipSemanticState { output: prior_state.output, ..child })
                                    && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                                        remaining_depth, before, Err(error),
                                        crate::specs::Part2JpipSemanticState { output: prior_state.output, ..child }) by {
                                crate::specs::part2_jpip_semantic_metadata_error_lift(semantic_root, placeholder_parent_events,
                                    box_ref.payload@, prior_state, placeholder_value_view(placeholder), header@, 0,
                                    placeholder.bin, placeholder.original_type, error, child);
                            }
                        }
                        let replaced = self.expand_metadata_bin(
                            metadata_codestream,
                            placeholder.bin,
                            jpip_superbox(placeholder.original_type),
                            depth.checked_add(1).ok_or_else(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                                ))]
                                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                            )?,
                            remaining_depth.checked_sub(1).ok_or_else(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                                ))]
                                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                            )?,
                            active,
                            &mut payload,
                            missing,
                            needs,
                        )?;
                        #[cfg(verus_keep_ghost)]
                        proof! { reveal(crate::specs::part2_jpip_semantic_expand_trace); }
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost child_after = semantic_state_view(active@, payload@, missing@, needs@);
                            let ghost child_events = choose|events: Seq<crate::specs::Part2JpipSemanticEvent>|
                                #[trigger] crate::specs::part2_jpip_semantic_expand_prefix(cache, metadata_codestream,
                                    placeholder.bin, crate::specs::part2_jpip_superbox(placeholder.original_type),
                                    (depth + 1) as u32, (remaining_depth - 1) as u32,
                                    child_before, Ok(replaced), child_after, events);
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::specs::part2_jpip_semantic_original_success_prefix(cache, metadata_codestream, box_ref.payload@,
                                placeholder_value_view(placeholder), header@, depth, remaining_depth, prior_state, replaced, child_after, child_events);
                            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream,
                                    box_ref.payload@, depth, remaining_depth, prior_state, child_events + tail)
                                    == Some((Ok((replaced, false, header@, payload@)),
                                        semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                            }
                            placeholder_events = child_events;
                        }
                        replaced
                    }
                    PlaceholderSource::Equivalent => {
                        let bin = placeholder.equivalent_bin.ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidBoxContents)
                        })?;
                        let box_type = placeholder.equivalent_type.ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidBoxContents)
                        })?;
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost child_before = semantic_state_view(active@, payload@, missing@, needs@);
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert(child_before == (crate::specs::Part2JpipSemanticState { output: Seq::empty(), ..prior_state }));
                            assert forall|error: DecodeError, child: crate::specs::Part2JpipSemanticState|
                                depth < u32::MAX && remaining_depth > 0
                                && #[trigger] crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin,
                                    crate::specs::part2_jpip_superbox(box_type), (depth + 1) as u32,
                                    (remaining_depth - 1) as u32, child_before, Err(error), child)
                                implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, parent_bin, boxes, depth,
                                    remaining_depth, before, Err(error),
                                    crate::specs::Part2JpipSemanticState { output: prior_state.output, ..child })
                                    && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, parent_bin, boxes, depth,
                                        remaining_depth, before, Err(error),
                                        crate::specs::Part2JpipSemanticState { output: prior_state.output, ..child }) by {
                                crate::specs::part2_jpip_semantic_metadata_error_lift(semantic_root, placeholder_parent_events,
                                    box_ref.payload@, prior_state, placeholder_value_view(placeholder), header@, 1, bin, box_type, error, child);
                            }
                        }
                        let replaced = self.expand_metadata_bin(
                            metadata_codestream,
                            bin,
                            jpip_superbox(box_type),
                            depth.checked_add(1).ok_or_else(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                                ))]
                                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                            )?,
                            remaining_depth.checked_sub(1).ok_or_else(
                                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                                ))]
                                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                            )?,
                            active,
                            &mut payload,
                            missing,
                            needs,
                        )?;
                        #[cfg(verus_keep_ghost)]
                        proof! { reveal(crate::specs::part2_jpip_semantic_expand_trace); }
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost child_after = semantic_state_view(active@, payload@, missing@, needs@);
                            let ghost child_events = choose|events: Seq<crate::specs::Part2JpipSemanticEvent>|
                                #[trigger] crate::specs::part2_jpip_semantic_expand_prefix(cache, metadata_codestream,
                                    bin, crate::specs::part2_jpip_superbox(box_type),
                                    (depth + 1) as u32, (remaining_depth - 1) as u32,
                                    child_before, Ok(replaced), child_after, events);
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::specs::part2_jpip_semantic_equivalent_prefix(cache, metadata_codestream, box_ref.payload@,
                                placeholder_value_view(placeholder), header@, bin, box_type, depth, remaining_depth,
                                prior_state, Ok(replaced), child_after, child_events);
                            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream,
                                    box_ref.payload@, depth, remaining_depth, prior_state, child_events + tail)
                                    == Some((Ok((replaced, false, header@, payload@)),
                                        semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                            }
                            placeholder_events = child_events;
                        }
                        replaced
                    }
                    PlaceholderSource::Codestream => {
                        let first_stream = placeholder.stream.ok_or_else(|| {
                            DecodeError::malformed(0, MalformedKind::InvalidBoxContents)
                        })?;
                        let mut stream_index = 0_u32;
                        let mut streams_complete = true;
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost streams_before = semantic_state_view(active@, output@, missing@, needs@);
                            let ghost payload_before = payload@;
                            let ghost mut stream_events = Seq::<crate::specs::Part2JpipSemanticEvent>::empty();
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            reveal_with_fuel(crate::specs::part2_jpip_semantic_placeholder, 2);
                            assert(payload_before =~= Seq::<u8>::empty());
                            assert(streams_before == prior_state);
                            assert(crate::specs::part2_jpip_semantic_placeholder_streams_known(cache, metadata_codestream,
                                box_ref.payload@, depth, remaining_depth, prior_state, first_stream, placeholder.stream_count, header@));
                        }
                        #[cfg_attr(
                        verus_keep_ghost,
                        verus_spec(
                            invariant stream_index <= placeholder.stream_count,
                                semantic_root == (crate::specs::Part2JpipSemanticRoot {
                                    cache, metadata_stream: metadata_codestream, bin, boxes, depth, remaining_depth, before,
                                }),
                                cache == jpip_cache_view(self), cache.0 == self.limits,
                                before == semantic_state_view(old(active)@, old(output)@, old(missing)@, old(needs)@),
                                streams_before == prior_state, payload_before == Seq::<u8>::empty(),
                                prior_remaining_boxes > 0,
                                prior_remaining_boxes == remaining_boxes as nat + 1,
                                prior_complete == complete,
                                reader_before.input == bytes@,
                                next == crate::specs::part2_box_reader_next_ref(reader_before),
                                next.0 == Some(Ok(crate::jp2::box_reference_view(box_ref))),
                                crate::jp2::box_reference_view(box_ref).0.0 == crate::jp2::box_type_from_bytes_model(*b"phld"),
                                next.1 == crate::jp2::box_reader_state(&reader),
                                forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                    crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                                        before, placeholder_parent_events + tail)
                                    == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                        reader_before, prior_remaining_boxes, prior_complete, prior_state, tail),
                                crate::specs::part2_jpip_semantic_placeholder_streams_known(cache, metadata_codestream,
                                    box_ref.payload@, depth, remaining_depth, prior_state, first_stream, placeholder.stream_count, header@),
                                crate::specs::part2_jpip_semantic_placeholder_error_continuation(
                                    cache, metadata_codestream, bin, boxes, depth, remaining_depth, before,
                                    placeholder_parent_events, box_ref.payload@, prior_state),
                                forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                    crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count, 0,
                                        header@, true, payload_before, streams_before, stream_events + tail)
                                    == crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                        stream_index, header@, streams_complete, payload@,
                                        semantic_state_view(active@, output@, missing@, needs@), tail),
                            decreases placeholder.stream_count - stream_index,
                        )
                    )]
                        while stream_index < placeholder.stream_count {
                            #[cfg(verus_keep_ghost)]
                            proof_decl! {
                                let ghost stream_iteration_events = stream_events;
                                let ghost stream_iteration_state = semantic_state_view(active@, output@, missing@, needs@);
                                let ghost stream_iteration_complete = streams_complete;
                                let ghost stream_iteration_payload = payload@;
                                let ghost stream_point = crate::specs::Part2JpipSemanticStreamPoint {
                                    cache, first: first_stream, count: placeholder.stream_count, index: stream_index,
                                    header: header@, complete: streams_complete, payload: payload@, state: stream_iteration_state,
                                };
                            }
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                crate::specs::part2_jpip_semantic_placeholder_box_step(cache, metadata_codestream, bin, depth, remaining_depth,
                                    reader_before, prior_remaining_boxes, prior_complete, prior_state, crate::jp2::box_reference_view(box_ref));
                                reveal(crate::specs::part2_jpip_semantic_streams);
                                reveal(crate::specs::part2_jpip_semantic_snapshot);
                                reveal(super::jpip_automatic_snapshot_result_view);
                                reveal(super::jpip_automatic_snapshot_view);
                                reveal(super::jpip_semantic_need_view);
                                crate::specs::part2_jpip_semantic_stream_continuation(semantic_root, placeholder_parent_events,
                                    box_ref.payload@, prior_state, stream_events, stream_point);
                                if first_stream as nat + stream_index as nat > u64::MAX as nat {
                                    assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                        crate::specs::part2_jpip_semantic_stream_at(stream_point, Seq::empty() + tail)
                                            == Some((Err(crate::specs::part2_jpip_range_overflow(0)), stream_iteration_state, tail)) by {
                                    }
                                    crate::specs::part2_jpip_semantic_stream_error_lift(semantic_root, placeholder_parent_events + stream_events,
                                        stream_point, crate::specs::part2_jpip_range_overflow(0), stream_iteration_state, Seq::empty());
                                }
                            }
                            let stream = first_stream
                                .checked_add(u64::from(stream_index))
                                .ok_or_else(
                                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                                        ensures result == crate::specs::part2_jpip_range_overflow(0),
                                    ))]
                                    || { DecodeError::malformed(0, MalformedKind::ArithmeticOverflow) },
                                )?;
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                assert forall|error: DecodeError|
                                    crate::specs::part2_jpip_automatic_snapshot_result(cache, stream, None,
                                        Seq::empty(), &self.limits, Err(error))
                                    implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                                        remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@))
                                        && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                                            remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@)) by {
                                    assert(crate::specs::part2_jpip_automatic_snapshot_result(cache, stream, None,
                                        Seq::empty(), &cache.0, Err(error)));
                                    reveal(crate::specs::part2_jpip_automatic_snapshot_result);
                                    let calls = choose|calls: Seq<crate::specs::Part2JpipSnapshotEvent>|
                                        crate::specs::part2_jpip_snapshot_run(crate::specs::Part2JpipSnapshotInput {
                                            cache, stream, selected: None, components: Seq::empty(), limits: &cache.0 }, calls)
                                            == Some((Err(error), Seq::empty()));
                                    let event = crate::specs::Part2JpipSemanticEvent::Snapshot { stream, events: calls };
                                    reveal(crate::specs::part2_jpip_semantic_snapshot);
                                    reveal(crate::specs::part2_jpip_semantic_streams);
                                    assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                        crate::specs::part2_jpip_semantic_stream_at(stream_point, seq![event] + tail)
                                            == Some((Err(error), semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                                    }
                                    crate::specs::part2_jpip_semantic_stream_error_lift(semantic_root, placeholder_parent_events + stream_events,
                                        stream_point, error, stream_iteration_state, seq![event]);
                                }
                            }
                            let snapshot = self.build_automatic_snapshot(
                                stream,
                                None,
                                &JpipPacketSelection::all_components(),
                                &self.limits,
                            )?;
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                assert(crate::specs::part2_jpip_automatic_snapshot_result(cache, stream, None,
                                    Seq::empty(), &cache.0, super::jpip_automatic_snapshot_outcome(Ok(snapshot))));
                                reveal(crate::specs::part2_jpip_automatic_snapshot_result);
                            }
                            #[cfg(verus_keep_ghost)]
                            proof_decl! {
                                let ghost calls = choose|calls: Seq<crate::specs::Part2JpipSnapshotEvent>|
                                    crate::specs::part2_jpip_snapshot_run(crate::specs::Part2JpipSnapshotInput {
                                        cache, stream, selected: None, components: Seq::empty(), limits: &cache.0 }, calls)
                                        == Some((super::jpip_automatic_snapshot_outcome(Ok(snapshot)), Seq::empty()));
                                let ghost snapshot_event = crate::specs::Part2JpipSemanticEvent::Snapshot { stream, events: calls };
                                let ghost snapshot_value = super::jpip_automatic_snapshot_result_view(&snapshot);
                                let ghost expected_step = match snapshot_value.0 {
                                    Some(ready) => if ready.1 == ready.2 {
                                        if placeholder.stream_count == 1 {
                                            (stream_iteration_complete, stream_iteration_payload + ready.0, stream_iteration_state)
                                        } else {
                                            let step = crate::specs::part2_jpip_append_reconstructed_box(stream_iteration_state.output, header@, ready.0);
                                            (stream_iteration_complete, stream_iteration_payload,
                                                crate::specs::Part2JpipSemanticState { output: step.1, ..stream_iteration_state })
                                        }
                                    } else {
                                        (false, stream_iteration_payload, crate::specs::Part2JpipSemanticState {
                                            missing: stream_iteration_state.missing + ready.3,
                                            needs: stream_iteration_state.needs.push((JpipSemanticNeedKind::Codestream, stream)),
                                            ..stream_iteration_state })
                                    },
                                    None => (false, stream_iteration_payload, crate::specs::Part2JpipSemanticState {
                                        missing: stream_iteration_state.missing + snapshot_value.1,
                                        needs: stream_iteration_state.needs.push((JpipSemanticNeedKind::Codestream, stream)),
                                        ..stream_iteration_state }),
                                };
                            }
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                reveal(crate::specs::part2_jpip_semantic_snapshot);
                                reveal(super::jpip_byte_view);
                                assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                    crate::specs::part2_jpip_semantic_snapshot(cache, stream, stream_iteration_state,
                                        seq![snapshot_event] + tail) == Some((Ok(snapshot_value), stream_iteration_state, tail)) by {
                                }
                                stream_events = stream_events + seq![snapshot_event];
                            }
                            match snapshot.ready {
                                Some(snapshot) if snapshot.available_layers == snapshot.layers => {
                                    if placeholder.stream_count == 1 {
                                        payload.extend_from_slice(snapshot.codestream.as_bytes());
                                    } else {
                                        #[cfg(verus_keep_ghost)]
                                        proof! {
                                            assert forall|error: DecodeError|
                                                crate::specs::part2_jpip_append_reconstructed_box(output@, header@,
                                                    super::jpip_byte_view(&snapshot.codestream)).0 == Err(error)
                                                implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                                                    remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@))
                                                    && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                                                        remaining_depth, before, Err(error), semantic_state_view(active@, output@, missing@, needs@)) by {
                                                reveal(crate::specs::part2_jpip_semantic_streams);
                                                reveal(crate::specs::part2_jpip_semantic_snapshot);
                                                assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                                    crate::specs::part2_jpip_semantic_stream_at(stream_point, seq![snapshot_event] + tail)
                                                        == Some((Err(error), stream_iteration_state, tail)) by {
                                                }
                                                crate::specs::part2_jpip_semantic_stream_error_lift(semantic_root, placeholder_parent_events + stream_iteration_events,
                                                    stream_point, error, stream_iteration_state, seq![snapshot_event]);
                                            }
                                        }
                                        append_reconstructed_box(
                                            output,
                                            header,
                                            snapshot.codestream.as_bytes(),
                                        )?;
                                    }
                                }
                                Some(snapshot) => {
                                    append_missing_ranges(missing, &snapshot.missing);
                                    needs.push(JpipSemanticNeed {
                                        kind: JpipSemanticNeedKind::Codestream,
                                        identifier: stream,
                                    });
                                    streams_complete = false;
                                }
                                None => {
                                    append_missing_ranges(missing, &snapshot.missing);
                                    needs.push(JpipSemanticNeed {
                                        kind: JpipSemanticNeedKind::Codestream,
                                        identifier: stream,
                                    });
                                    streams_complete = false;
                                }
                            }
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                reveal(crate::specs::part2_jpip_semantic_streams);
                                reveal(crate::specs::part2_jpip_semantic_snapshot);
                                reveal(super::jpip_automatic_snapshot_result_view);
                                reveal(super::jpip_automatic_snapshot_view);
                                reveal(super::jpip_semantic_need_view);
                                reveal(super::jpip_byte_view);
                                assert(streams_complete == expected_step.0);
                                assert(payload@ =~= expected_step.1);
                                assert(active@ == expected_step.2.active);
                                assert(output@ =~= expected_step.2.output);
                                assert(super::jpip_missing_views(missing) =~= expected_step.2.missing);
                                assert(super::jpip_semantic_needs_view(needs) =~= expected_step.2.needs);
                                assert(semantic_state_view(active@, output@, missing@, needs@) == expected_step.2);
                                assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                    crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                        stream_index, header@, stream_iteration_complete, stream_iteration_payload, stream_iteration_state,
                                        seq![snapshot_event] + tail)
                                        == crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                            (stream_index + 1) as u32, header@, streams_complete, payload@,
                                            semantic_state_view(active@, output@, missing@, needs@), tail) by {
                                }
                                assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                    crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                        0, header@, true, payload_before, streams_before, stream_events + tail)
                                        == crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                            (stream_index + 1) as u32, header@, streams_complete, payload@,
                                            semantic_state_view(active@, output@, missing@, needs@), tail) by {
                                    assert(stream_events + tail =~= stream_iteration_events + (seq![snapshot_event] + tail));
                                    assert(crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                        0, header@, true, payload_before, streams_before, stream_iteration_events + (seq![snapshot_event] + tail))
                                        == crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                            stream_index, header@, stream_iteration_complete, stream_iteration_payload, stream_iteration_state,
                                            seq![snapshot_event] + tail));
                                }
                            }
                            stream_index += 1;
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::specs::part2_jpip_semantic_placeholder_box_step(cache, metadata_codestream, bin, depth, remaining_depth,
                                reader_before, prior_remaining_boxes, prior_complete, prior_state, crate::jp2::box_reference_view(box_ref));
                            reveal(crate::specs::part2_jpip_semantic_streams);
                            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                    0, header@, true, payload_before, streams_before, stream_events + tail)
                                    == Some((Ok((streams_complete, payload@)),
                                        semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                                assert(crate::specs::part2_jpip_semantic_streams(cache, first_stream, placeholder.stream_count,
                                    stream_index, header@, streams_complete, payload@,
                                    semantic_state_view(active@, output@, missing@, needs@), tail)
                                    == Some((Ok((streams_complete, payload@)),
                                        semantic_state_view(active@, output@, missing@, needs@), tail)));
                            }
                            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream,
                                    box_ref.payload@, depth, remaining_depth, prior_state, stream_events + tail)
                                    == Some((Ok((streams_complete, placeholder.stream_count > 1 && streams_complete, header@, payload@)),
                                        semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                            }
                            placeholder_events = stream_events;
                        }
                        appended = placeholder.stream_count > 1 && streams_complete;
                        streams_complete
                    }
                    PlaceholderSource::Empty => {
                        payload.clear();
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            reveal_with_fuel(crate::specs::part2_jpip_semantic_placeholder, 2);
                            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                                crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream,
                                    box_ref.payload@, depth, remaining_depth, prior_state, tail)
                                    == Some((Ok((true, false, header@, payload@)),
                                        semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                            }
                        }
                        true
                    }
                };
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost placeholder_after = semantic_state_view(active@, output@, missing@, needs@); }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                        crate::specs::part2_jpip_semantic_placeholder(cache, metadata_codestream,
                            box_ref.payload@, depth, remaining_depth, prior_state, placeholder_events + tail)
                            == Some((Ok((replacement_complete, appended, header@, payload@)),
                                semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                    }
                    semantic_events = placeholder_parent_events + placeholder_events;
                }
                if replacement_complete {
                    if !appended {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            assert forall|error: DecodeError|
                                crate::specs::part2_jpip_append_reconstructed_box(output@, header@, payload@).0 == Err(error)
                                implies crate::specs::part2_jpip_semantic_expand_result(cache, metadata_codestream, bin, boxes, depth,
                                    remaining_depth, before, Err(error), placeholder_after)
                                    && crate::specs::part2_jpip_semantic_expand_trace(cache, metadata_codestream, bin, boxes, depth,
                                        remaining_depth, before, Err(error), placeholder_after) by {
                                crate::specs::part2_jpip_semantic_placeholder_append_error(semantic_root, reader_before,
                                    prior_remaining_boxes, prior_complete, prior_state, crate::jp2::box_reference_view(box_ref),
                                    placeholder_parent_events, placeholder_events, header@, payload@, placeholder_after, error);
                            }
                        }
                        append_reconstructed_box(output, header, &payload)?;
                    }
                } else {
                    complete = false;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_jpip_semantic_placeholder_advance(semantic_root, reader_before,
                        prior_remaining_boxes, prior_complete, prior_state, crate::jp2::box_reference_view(box_ref),
                        placeholder_parent_events, placeholder_events, (replacement_complete, appended, header@, payload@),
                        placeholder_after, semantic_state_view(active@, output@, missing@, needs@), complete);
                }
            } else {
                let start = usize::try_from(box_ref.header.offset()).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
                let length = usize::try_from(box_ref.header.total_length()).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(0),
                        ))]
                    |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
                let end = start
                    .checked_add(length)
                    .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
                output.extend_from_slice(bytes.get(start..end).ok_or_else(|| {
                    DecodeError::malformed(start as u64, MalformedKind::Truncated)
                })?);
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal_with_fuel(crate::specs::part2_jpip_semantic_boxes, 2);
                    assert(output@ =~= prior_state.output + bytes@.subrange(start as int, end as int));
                    assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                        crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail)
                            == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                next.1, remaining_boxes as nat, complete, semantic_state_view(active@, output@, missing@, needs@), tail) by {
                        assert(crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                            before, semantic_events + tail)
                            == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                                reader_before, prior_remaining_boxes, prior_complete, prior_state, tail));
                    }
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! { reader_before = crate::jp2::box_reader_state(&reader); }
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost terminal_state = semantic_state_view(active@, output@, missing@, needs@); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_jpip_semantic_boxes, 2);
            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                    before, semantic_events + tail)
                    == crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                        reader_before, remaining_boxes as nat, complete, terminal_state, tail) by {
            }
        }
        active.pop();
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_jpip_semantic_boxes, 2);
            assert(active@ == terminal_state.active.drop_last());
            assert(semantic_state_view(active@, output@, missing@, needs@)
                == (crate::specs::Part2JpipSemanticState { active: terminal_state.active.drop_last(), ..terminal_state }));
            assert forall|tail: Seq<crate::specs::Part2JpipSemanticEvent>|
                crate::specs::part2_jpip_semantic_expand(cache, metadata_codestream, bin, boxes, depth, remaining_depth,
                    before, semantic_events + tail)
                    == Some((Ok(complete), semantic_state_view(active@, output@, missing@, needs@), tail)) by {
                assert(crate::specs::part2_jpip_semantic_boxes(cache, metadata_codestream, bin, depth, remaining_depth,
                    reader_before, remaining_boxes as nat, complete, terminal_state, tail)
                    == Some((Ok(complete), semantic_state_view(active@, output@, missing@, needs@), tail)));
            }
            crate::specs::part2_jpip_semantic_expand_witness(cache, metadata_codestream, bin, boxes, depth,
                remaining_depth, before, Ok(complete), semantic_state_view(active@, output@, missing@, needs@), semantic_events);
        }
        Ok(complete)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures placeholder_parse_outcome(result) == crate::specs::part2_jpip_parse_placeholder(payload@),
))]
pub(super) fn parse_jpip_placeholder(payload: &[u8]) -> Result<JpipPlaceholder, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_jpip_parse_placeholder);
        reveal(placeholder_parse_outcome);
        reveal(placeholder_value_view);
    }
    if payload.len() < 20 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let flags = read_u32_be(payload, 0)?;
    let bin_high = u64::from(read_u32_be(payload, 4)?);
    let bin_low = u64::from(read_u32_be(payload, 8)?);
    let bin = (bin_high << 32) | bin_low;
    let original_start = 12_usize;
    let first_length = read_u32_be(payload, original_start)?;
    let header_length = if first_length == 1 { 16_usize } else { 8_usize };
    let original_end = original_start
        .checked_add(header_length)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
            ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
    let original = payload
        .get(original_start..original_end)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidBoxContents),
            ))]
            || DecodeError::malformed(0, MalformedKind::InvalidBoxContents),
        )?;
    let box_type = crate::jp2::BoxType::new([
        *original
            .get(4)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidBoxContents),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidBoxContents),
            )?,
        *original
            .get(5)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidBoxContents),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidBoxContents),
            )?,
        *original
            .get(6)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidBoxContents),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidBoxContents),
            )?,
        *original
            .get(7)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidBoxContents),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidBoxContents),
            )?,
    ]);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_jpip_placeholder_header);
        assert(crate::specs::part2_jpip_read_u32(payload@, 12) == Ok(first_length));
        assert(original@ =~= payload@.subrange(12, original_end as int));
        assert(box_type == crate::jp2::box_type_from_word_model(
            ((original@[4] as u32) << 24) | ((original@[5] as u32) << 16)
                | ((original@[6] as u32) << 8) | original@[7] as u32));
        assert(crate::specs::part2_jpip_placeholder_header(payload@, 12)
            == Ok((original@, box_type, original_end)));
    }
    if flags & !0x0f != 0 || flags & 8 != 0 && flags & 4 == 0 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let mut position = original_end;
    let (equivalent_bin, equivalent_header, equivalent_type) = if flags & 6 != 0 {
        let bin = read_u64_be(payload, position)?;
        position = position
            .checked_add(8)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                ))]
                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?;
        let length = read_u32_be(payload, position)?;
        let header_length = if length == 1 { 16_usize } else { 8_usize };
        let end = position
            .checked_add(header_length)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                ))]
                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?;
        let header = payload
            .get(position..end)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::InvalidBoxContents),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidBoxContents),
            )?;
        let box_type = crate::jp2::BoxType::new([header[4], header[5], header[6], header[7]]);
        position = end;
        (Some(bin), Some(copy_bytes(header)), Some(box_type))
    } else {
        (None, None, None)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_jpip_placeholder_equivalent(payload@, flags, original_end)
            == Ok((equivalent_bin, match equivalent_header {
                Some(header) => Some(header@), None => None,
            }, equivalent_type, position)));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost stream_start = position; }
    let (stream, stream_count) = if flags & 4 != 0 {
        let stream = read_u64_be(payload, position)?;
        position = position
            .checked_add(8)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                ))]
                || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
            )?;
        let count = if flags & 8 != 0 {
            let count = read_u32_be(payload, position)?;
            position = position
                .checked_add(4)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                    ))]
                    || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
            if count == 0 {
                return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
            }
            count
        } else {
            if payload.len().checked_sub(position) == Some(4) {
                read_u32_be(payload, position)?;
                position = position
                    .checked_add(4)
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_cache_error(0, MalformedKind::ArithmeticOverflow),
                        ))]
                        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                    )?;
            }
            1
        };
        (Some(stream), count)
    } else {
        (None, 0)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_jpip_placeholder_stream(payload@, flags, stream_start)
            == Ok((stream, stream_count, position)));
    }
    if position != payload.len() {
        if flags == 4 && payload.len() == original_end + 24 {
            // Compatibility with the previously selected provisional layout.
            return Err(DecodeError::malformed(
                original_end as u64,
                MalformedKind::InvalidBoxContents,
            ));
        } else {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
        }
    }
    Ok(JpipPlaceholder {
        flags,
        bin,
        original_header: copy_bytes(original),
        original_type: box_type,
        equivalent_bin,
        equivalent_header,
        equivalent_type,
        stream,
        stream_count,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_jpip_superbox(box_type),
))]
fn jpip_superbox(box_type: crate::jp2::BoxType) -> bool {
    [
        *b"jp2h", *b"jpch", *b"jplh", *b"cgrp", *b"res ", *b"asoc", *b"comp",
    ]
    .iter()
    .any(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
            ensures result == (box_type == crate::jp2::box_type_from_bytes_model(*value)),
        ))]
        |value| box_type.equals(crate::jp2::BoxType::new(*value)),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part2_jpip_append_reconstructed_box(
        old(output)@, original_header@, payload@),
))]
fn append_reconstructed_box(
    output: &mut Vec<u8>,
    original_header: &[u8],
    payload: &[u8],
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = output@; }
    if original_header.len() != 8 && original_header.len() != 16 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidBoxContents));
    }
    let total = original_header
        .len()
        .checked_add(payload.len())
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_range_overflow(0),
            ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
    if crate::refinement::jpip_box_length(original_header.len() as u64, payload.len() as u64)
        != total as u128
    {
        return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow));
    }
    let mut header = copy_bytes(original_header);
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original_copy = header@; }
    if header.len() == 8 {
        let length = u32::try_from(total).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                ))]
            |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
        write_u32_be(&mut header, 0, length)?;
    } else {
        write_u32_be(&mut header, 0, 1)?;
        write_u64_be(&mut header, 8, total as u64)?;
    }
    output.extend_from_slice(&header);
    output.extend_from_slice(payload);
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= before + header@ + payload@); }
    Ok(())
}
