//! Codestream entry points and main-header/layout orchestration.

use super::mct_resolution::{
    validate_unique_mct_array_indexes, validate_unique_mct_record_indexes,
};
use super::persistent_tile_configuration::inherited_tile_owner;
use super::profile::classify_codestream_profile;
use super::reader::new_parser;
use super::{
    ADS, ATK, CAP, CBD, COC, COD, CPF, CRG, CodestreamInfo, CodestreamLayout,
    ComponentQuantizations, DFS, DecodeError, EOC, ImageSize, MAX_COMPONENTS, MCC, MCO, MCT,
    MalformedKind, MctParameters, NLT, PLM, POC, PPM, PRF, PackedHeaderFrame,
    PackedPacketHeaderSource, PackedPacketHeaders, PacketLengths, Parser, Part2Extensions,
    ProgressionChanges, QCC, QCD, RGN, Resource, ResourceLimits, SIZ, SOC, SOT, TLM, TilePart,
    TilePartLength, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    cap_payload_outcome, complete_codestream_info_outcome, complete_codestream_info_view,
    complete_codestream_profile_outcome, complete_layout_outcome, component_style_owner_view,
    extended_capabilities_view, inherited_tile_configuration_outcome, layout_main_header_outcome,
    layout_prologue_outcome, main_header_accumulator_view, main_header_fields_view,
    mcc_fragment_outcome, mcc_pending_view, mct_array_view, mct_arrays_view, mct_fragment_outcome,
    mct_graph_outcome, mct_parameter_copy_view, mct_parameters_view, mct_pending_view,
    mct_record_view, mct_records_view, multiple_component_transform_view,
    optional_capabilities_view, optional_profile_number_view, optional_roi_shifts_view,
    optional_segment_view, owned_extensions_view, packed_header_frames_view,
    packed_packet_headers_view, packet_length_groups_view, parsed_coding_style_outcome,
    parsed_coding_style_view, parsed_image_size_view, parsed_progression_outcome,
    parsed_quantization_outcome, parsed_quantization_owner_outcome, parsed_quantization_owner_view,
    parsed_style_owner_outcome, parser_initial_outcome, parser_view,
    persistent_tile_configuration_view, persistent_tile_selection_view, persistent_tile_state_view,
    profile_number_outcome, profile_number_view, profile_tile_inputs_view,
    progression_changes_view, quantization_owner_view, quantization_view, roi_shifts_view,
    segment_slots_view, segment_tail_outcome, segment_view, selection_geometry_view,
    tile_part_header_view, tile_part_main_metadata_outcome, tile_part_payload_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures complete_codestream_info_outcome(result) == crate::specs::part1_parse_info(input@, limits),
))]
pub fn parse(input: &[u8], limits: &ResourceLimits) -> Result<CodestreamInfo, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(complete_codestream_info_outcome);
        reveal(complete_layout_outcome);
        crate::specs::part1_parse_info_unfold(input@, limits);
    }
    Ok(parse_layout(input, limits)?.info)
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures complete_layout_outcome(result) == crate::specs::part1_parse_layout(input@, limits),
))]
pub fn parse_layout<'a>(
    input: &'a [u8],
    limits: &'a ResourceLimits,
) -> Result<CodestreamLayout<'a>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(complete_layout_outcome);
        reveal(parser_initial_outcome);
        crate::specs::part1_parse_layout_unfold(input@, limits);
    }
    new_parser(input, limits)?.parse_layout()
}
impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (layout_prologue_outcome(result), parser_view(final(self)))
            == crate::specs::part1_parse_layout_prologue(parser_view(old(self))),
    ))]
    pub(super) fn parse_layout_prologue(&mut self) -> Result<(ImageSize, u16, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_parse_layout_prologue);
            reveal(parser_view);
            reveal(layout_prologue_outcome);
        }
        self.expect_standalone(SOC)?;
        let siz = self.read_segment()?;
        if siz.marker != SIZ {
            return Err(DecodeError::malformed(
                self.offset(siz.offset),
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        let (image_size, r_siz) = self.parse_siz(siz)?;
        let main_header_start = self.position;
        Ok((image_size, r_siz, main_header_start))
    }

    #[inline]
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tile_part_main_metadata_outcome(result)
            == crate::specs::part1_tile_part_main_metadata(
                self.position, tile_part_header_view(tile_part), part_index, lengths@,
                plm_seen, packet_length_groups_view(plm_groups@),
                packed_header_frames_view(ppm_frames@), ppm_fragments, main_header@),
    ))]
    pub(super) fn tile_part_main_metadata(
        &self,
        tile_part: TilePart,
        part_index: u32,
        lengths: &[TilePartLength],
        plm_seen: bool,
        plm_groups: &[PacketLengths<'a>],
        ppm_frames: &[PackedHeaderFrame],
        ppm_fragments: u16,
        main_header: &'a [u8],
    ) -> Result<(PacketLengths<'a>, PackedPacketHeaders<'a>), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_part_main_metadata);
            reveal(tile_part_main_metadata_outcome);
            reveal(tile_part_header_view);
            reveal(packet_length_groups_view);
            reveal(packed_header_frames_view);
            reveal(packed_packet_headers_view);
        }
        if !lengths.is_empty() {
            let entry_index = usize::try_from(part_index).map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::ArithmeticOverflow),
                ))]
                |_conversion_error| self.malformed_here(MalformedKind::ArithmeticOverflow),
            )?;
            let entry = lengths.get(entry_index).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(tile_part.start, MalformedKind::InvalidTilePart),
                ))]
                || DecodeError::malformed(self.offset(tile_part.start), MalformedKind::InvalidTilePart),
            )?;
            if entry.length != tile_part.length
                || matches!(entry.tile_index, Some(index) if index != tile_part.tile_index)
            {
                return Err(DecodeError::malformed(
                    self.offset(tile_part.start),
                    MalformedKind::InvalidTilePart,
                ));
            }
        }
        let main_packet_lengths = if plm_seen {
            *plm_groups
                .get(usize::try_from(part_index).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                        ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::ArithmeticOverflow),
                    ))]
                    |_conversion_error| self.malformed_here(MalformedKind::ArithmeticOverflow),
                )?)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                        ensures error == crate::specs::part1_codestream_malformed(tile_part.start, MalformedKind::InvalidPacketLength),
                    ))]
                    || DecodeError::malformed(self.offset(tile_part.start), MalformedKind::InvalidPacketLength),
                )?
        } else {
            super::packet_lengths_none()
        };
        let packed_packet_headers = if ppm_fragments != 0 {
            let frame = *ppm_frames
                .get(usize::try_from(part_index).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                        ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::ArithmeticOverflow),
                    ))]
                    |_conversion_error| self.malformed_here(MalformedKind::ArithmeticOverflow),
                )?)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                        ensures error == crate::specs::part1_codestream_malformed(tile_part.start, MalformedKind::InvalidPackedPacketHeader),
                    ))]
                    || DecodeError::malformed(self.offset(tile_part.start), MalformedKind::InvalidPackedPacketHeader),
                )?;
            PackedPacketHeaders {
                source: PackedPacketHeaderSource::MarkerSegments {
                    header: main_header,
                    marker: PPM,
                    logical_start: frame.start,
                },
                length: frame.length,
                fragments: ppm_fragments,
            }
        } else {
            super::packed_packet_headers_none()
        };
        Ok((main_packet_lengths, packed_packet_headers))
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)))
            == crate::specs::part1_finish_tile_part_traversal(
                parser_view(old(self)), tile_parts, plm_seen, plm_count,
                ppm_fragments, ppm_count, tlm_count),
    ))]
    pub(super) fn finish_tile_part_traversal(
        &mut self,
        tile_parts: u32,
        plm_seen: bool,
        plm_count: usize,
        ppm_fragments: u16,
        ppm_count: usize,
        tlm_count: usize,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_finish_tile_part_traversal);
            reveal(parser_view);
        }
        if tile_parts == 0 {
            return Err(self.malformed_here(MalformedKind::InvalidMarkerOrder));
        }
        self.expect_standalone(EOC)?;
        if plm_seen && plm_count != tile_parts as usize {
            return Err(self.malformed_here(MalformedKind::InvalidPacketLength));
        }
        if ppm_fragments != 0 && ppm_count != tile_parts as usize {
            return Err(self.malformed_here(MalformedKind::InvalidPackedPacketHeader));
        }
        if tlm_count != 0 && tlm_count != tile_parts as usize {
            return Err(self.malformed_here(MalformedKind::InvalidTilePart));
        }
        if self.position != self.input.len() {
            return Err(self.malformed_here(MalformedKind::TrailingData));
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_main_header_layout_relation(
            crate::specs::part1_read_main_header(parser_view(&self)),
            layout_main_header_outcome(result)),
            complete_layout_outcome(result) == crate::specs::part1_read_layout(parser_view(&self)),
    ))]
    fn parse_layout(self) -> Result<CodestreamLayout<'a>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial_reader = parser_view(&self);
            let ghost main_goal = crate::specs::part1_read_main_header(initial_reader);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_read_main_header);
            reveal(layout_main_header_outcome);
            reveal(complete_layout_outcome);
            reveal(crate::specs::part1_layout_from_main_result);
        }
        let mut parser = self;
        let (mut image_size, r_siz, main_header_start) = parser.parse_layout_prologue()?;
        let mut main_header_segments = 1_u64;
        let mut coding_style = None;
        let mut qcd_segment = None;
        let mut coc_segments = [None; MAX_COMPONENTS];
        let mut qcc_segments = [None; MAX_COMPONENTS];
        let mut roi_shifts = super::quantization::new_roi_shifts();
        let mut roi_seen = [false; MAX_COMPONENTS];
        let mut plm_groups = Vec::new();
        let mut next_plm_index = 0_u16;
        let mut plm_seen = false;
        let mut ppm_bytes = Vec::new();
        let mut next_ppm_index = 0_u16;
        let mut ppm_fragments = 0_u16;
        let mut progression_changes = super::coding_style::new_progression_changes();
        let mut poc_seen = false;
        let mut mct_arrays = Vec::new();
        let mut mct_records = Vec::new();
        let mut mct_order = None;
        let mut pending_mct = Vec::new();
        let mut completed_mct = Vec::new();
        let mut pending_mcc = Vec::new();
        let mut completed_mcc = Vec::new();
        let mut extended_capabilities = None;
        let mut profile = None;
        let mut corresponding_profile = None;
        let mut part2_extensions = super::extensions::new_part2_extensions();
        let mut next_tlm_index = 0_u16;
        let input_length = parser.input.len();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost main_initial = main_header_accumulator_view(
                &image_size, r_siz, main_header_start, main_header_segments,
                coding_style, qcd_segment, coc_segments@, qcc_segments@, &roi_shifts, roi_seen@,
                plm_groups@, next_plm_index, plm_seen, ppm_bytes@, next_ppm_index, ppm_fragments,
                &progression_changes, poc_seen, mct_arrays@, mct_records@, &mct_order,
                pending_mct@, completed_mct@, pending_mcc@, completed_mcc@,
                &extended_capabilities, &profile, &corresponding_profile, &part2_extensions, next_tlm_index);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(main_header_accumulator_view);
            reveal(segment_slots_view);
            reveal(roi_shifts_view);
            reveal(progression_changes_view);
            reveal(mct_arrays_view);
            reveal(mct_records_view);
            reveal(mct_pending_view);
            reveal(mcc_pending_view);
            reveal(optional_segment_view);
            reveal(optional_capabilities_view);
            reveal(optional_profile_number_view);
            reveal(packet_length_groups_view);
            let expected = crate::specs::part1_main_header_initial(
                parsed_image_size_view(&image_size), r_siz, main_header_start);
            assert(main_initial.coc =~= expected.coc);
            assert(main_initial.qcc =~= expected.qcc);
            assert(main_initial.roi =~= expected.roi);
            assert(main_initial.roi_seen =~= expected.roi_seen);
            assert(main_initial.plm =~= expected.plm);
            assert(main_initial.progression =~= expected.progression);
            assert(main_initial.arrays =~= expected.arrays);
            assert(main_initial.records =~= expected.records);
            assert(main_initial.pending_mct =~= expected.pending_mct);
            assert(main_initial.pending_mcc =~= expected.pending_mcc);
            assert(main_initial == crate::specs::part1_main_header_initial(
                parsed_image_size_view(&image_size), r_siz, main_header_start));
        }

        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    initial_reader == parser_view(&self),
                    main_goal == crate::specs::part1_read_main_header(initial_reader),
                    main_goal == crate::specs::part1_main_header_continuation(
                        parser_view(&parser), main_header_accumulator_view(
                            &image_size, r_siz, main_header_start, main_header_segments,
                            coding_style, qcd_segment, coc_segments@, qcc_segments@, &roi_shifts, roi_seen@,
                            plm_groups@, next_plm_index, plm_seen, ppm_bytes@, next_ppm_index, ppm_fragments,
                            &progression_changes, poc_seen, mct_arrays@, mct_records@, &mct_order,
                            pending_mct@, completed_mct@, pending_mcc@, completed_mcc@,
                            &extended_capabilities, &profile, &corresponding_profile, &part2_extensions, next_tlm_index),
                        input_length),
                    input_length == crate::specs::part1_parse_layout_prologue(initial_reader).1.input.len() as usize,
                ensures
                    main_goal == crate::specs::part1_finish_main_header(
                        parser_view(&parser), main_header_accumulator_view(
                            &image_size, r_siz, main_header_start, main_header_segments,
                            coding_style, qcd_segment, coc_segments@, qcc_segments@, &roi_shifts, roi_seen@,
                            plm_groups@, next_plm_index, plm_seen, ppm_bytes@, next_ppm_index, ppm_fragments,
                            &progression_changes, poc_seen, mct_arrays@, mct_records@, &mct_order,
                            pending_mct@, completed_mct@, pending_mcc@, completed_mcc@,
                            &extended_capabilities, &profile, &corresponding_profile, &part2_extensions, next_tlm_index)),
                decreases input_length as int - parser.position as int,
            )
        )]
        loop {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_main_header_continuation, 1);
                reveal(main_header_accumulator_view);
                reveal(parser_view);
                reveal(super::main_header_segment_outcome);
                reveal(crate::specs::part1_parser_progress);
                reveal(crate::specs::part1_codestream_malformed);
                reveal(crate::specs::part1_layout_from_main_result);
            }
            let previous_position = parser.position;
            let Some(segment) = parser.read_main_header_segment(&mut main_header_segments)? else {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part1_read_main_header_segment); }
                break;
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_main_header_payload);
                reveal(crate::specs::part1_main_header_mct_payload);
                reveal(crate::specs::part1_main_header_extension_payload);
                reveal(segment_view);
                reveal(optional_segment_view);
                reveal(segment_slots_view);
                reveal(cap_payload_outcome);
                reveal(extended_capabilities_view);
                reveal(profile_number_outcome);
                reveal(profile_number_view);
                reveal(optional_capabilities_view);
                reveal(optional_profile_number_view);
                reveal(parsed_coding_style_outcome);
                reveal(parsed_progression_outcome);
                reveal(progression_changes_view);
                reveal(mct_parameters_view);
                reveal(mct_fragment_outcome);
                reveal(mcc_fragment_outcome);
                reveal(mct_pending_view);
                reveal(mcc_pending_view);
                reveal(mct_arrays_view);
                reveal(mct_records_view);
                reveal(mct_array_view);
                reveal(mct_record_view);
                reveal(segment_tail_outcome);
                reveal(selection_geometry_view);
                reveal(parsed_image_size_view);
                reveal(roi_shifts_view);
            }
            match segment.marker {
                CAP if extended_capabilities.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                CAP => extended_capabilities = Some(parser.parse_cap(segment)?),
                PRF if profile.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                PRF => profile = Some(parser.parse_profile_number(segment)?),
                CPF if corresponding_profile.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                CPF => corresponding_profile = Some(parser.parse_profile_number(segment)?),
                COD if coding_style.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                COD => coding_style = Some(parser.parse_cod(segment)?),
                COC => {
                    parser.record_component_segment(
                        segment,
                        image_size.components,
                        MalformedKind::InvalidCodingStyle,
                        &mut coc_segments,
                    )?;
                }
                QCD if qcd_segment.is_some() => {
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                QCD => qcd_segment = Some(segment),
                QCC => {
                    parser.record_component_segment(
                        segment,
                        image_size.components,
                        MalformedKind::InvalidQuantization,
                        &mut qcc_segments,
                    )?;
                }
                RGN => {
                    let (component, shift) = parser.parse_rgn(segment, image_size.components)?;
                    let index = usize::from(component);
                    if index >= roi_seen.len() || roi_seen[index] {
                        return Err(DecodeError::malformed(
                            parser.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    roi_seen[index] = true;
                    roi_shifts.set(component, shift)?;
                }
                PLM => {
                    plm_seen = true;
                    parser.parse_plm(segment, &mut next_plm_index, &mut plm_groups)?;
                }
                PPM => {
                    parser.parse_packed_fragment(
                        segment,
                        PPM,
                        &mut next_ppm_index,
                        &mut ppm_fragments,
                        &mut ppm_bytes,
                    )?;
                }
                POC => {
                    if poc_seen {
                        return Err(DecodeError::malformed(
                            parser.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    poc_seen = true;
                    progression_changes = parser.parse_poc(segment, image_size.components)?;
                }
                TLM => parser.parse_tlm(
                    segment,
                    &mut next_tlm_index,
                    image_size.tile_count()?,
                    &mut part2_extensions,
                )?,
                CRG => parser.parse_crg(segment, image_size.components, &mut part2_extensions)?,
                DFS => parser.parse_dfs(segment, &mut part2_extensions)?,
                ADS => parser.parse_ads(segment, &mut part2_extensions)?,
                NLT => parser.parse_nlt(segment, image_size.components, &mut part2_extensions)?,
                CBD => parser.parse_cbd(segment, image_size.components, &mut part2_extensions)?,
                ATK => parser.parse_atk(segment, &mut part2_extensions)?,
                MCT => {
                    if let Some(array) = parser.consume_mct_fragment(
                        segment,
                        &mut pending_mct,
                        &mut completed_mct,
                    )? {
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost appended = mct_arrays_view(mct_arrays@).push(mct_array_view(&array));
                        }
                        mct_arrays.push(array);
                        #[cfg(verus_keep_ghost)]
                        proof! { assert(mct_arrays_view(mct_arrays@) =~= appended); }
                        validate_unique_mct_array_indexes(&mct_arrays, segment.offset)?;
                    }
                }
                MCC => {
                    if let Some(record) = parser.consume_mcc_fragment(
                        segment,
                        image_size.components,
                        &mut pending_mcc,
                        &mut completed_mcc,
                    )? {
                        #[cfg(verus_keep_ghost)]
                        proof_decl! {
                            let ghost appended = mct_records_view(mct_records@).push(mct_record_view(&record));
                        }
                        mct_records.push(record);
                        #[cfg(verus_keep_ghost)]
                        proof! { assert(mct_records_view(mct_records@) =~= appended); }
                        validate_unique_mct_record_indexes(&mct_records, segment.offset)?;
                    }
                }
                MCO => {
                    if mct_order.is_some() {
                        return Err(DecodeError::malformed(
                            parser.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    mct_order = Some(parser.parse_mco(segment)?);
                }
                0xff64 => {}
                marker => {
                    let _ = marker;
                    return Err(DecodeError::malformed(
                        parser.offset(segment.offset),
                        MalformedKind::InvalidMarker,
                    ));
                }
            }
            if !crate::refinement::parser_progress(previous_position, parser.position, input_length)
            {
                return Err(parser.malformed_here(MalformedKind::InvalidMarkerLength));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost raw_main = main_header_accumulator_view(
                &image_size, r_siz, main_header_start, main_header_segments,
                coding_style, qcd_segment, coc_segments@, qcc_segments@, &roi_shifts, roi_seen@,
                plm_groups@, next_plm_index, plm_seen, ppm_bytes@, next_ppm_index, ppm_fragments,
                &progression_changes, poc_seen, mct_arrays@, mct_records@, &mct_order,
                pending_mct@, completed_mct@, pending_mcc@, completed_mcc@,
                &extended_capabilities, &profile, &corresponding_profile, &part2_extensions, next_tlm_index);
            let ghost main_reader = parser_view(&parser);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(main_goal == crate::specs::part1_finish_main_header(main_reader, raw_main));
            reveal(crate::specs::part1_finish_main_header);
            reveal(main_header_accumulator_view);
            reveal(owned_extensions_view);
            reveal(parser_view);
        }
        if !pending_mct.is_empty() || !pending_mcc.is_empty() {
            return Err(parser.malformed_here(MalformedKind::MissingRequiredStructure));
        }
        let incomplete_plm = match plm_groups.last() {
            Some(last) => last.incomplete_plm_offset(),
            None => None,
        };
        if let Some(offset) = incomplete_plm {
            return Err(parser.malformed_at(offset, MalformedKind::InvalidMarkerLength));
        }
        parser
            .apply_component_bit_depths(&mut image_size, &part2_extensions.component_bit_depths)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost depth_main = crate::specs::Part1MainHeaderAccumulator {
                image_size: parsed_image_size_view(&image_size), ..raw_main
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(main_goal == crate::specs::part1_main_header_after_depths(main_reader, depth_main));
            reveal(crate::specs::part1_main_header_after_depths);
            reveal(super::packed_header_frames_outcome);
            reveal(packed_header_frames_view);
            reveal(parsed_coding_style_outcome);
            reveal(parsed_quantization_outcome);
            reveal(parsed_style_owner_outcome);
            reveal(parsed_quantization_owner_outcome);
            reveal(segment_view);
            reveal(optional_segment_view);
        }
        let main_header_end = parser.position;
        let ppm_frames = parser.parse_ppm_frames(&ppm_bytes, ppm_fragments)?;
        let main_header = parser
            .input
            .get(main_header_start..main_header_end)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(
                        parser.position, MalformedKind::InvalidPackedPacketHeader),
                ))]
                || parser.malformed_here(MalformedKind::InvalidPackedPacketHeader),
            )?;

        let coding_style = coding_style
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(0, MalformedKind::MissingRequiredStructure),
                ))]
                || DecodeError::malformed(0, MalformedKind::MissingRequiredStructure),
            )?;
        let qcd_segment = qcd_segment
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(0, MalformedKind::MissingRequiredStructure),
                ))]
                || DecodeError::malformed(0, MalformedKind::MissingRequiredStructure),
            )?;
        let quantization = parser.parse_qcd(qcd_segment, coding_style)?;
        let component_coding_styles = parser.finish_main_component_styles(
            image_size.components,
            coding_style,
            &coc_segments,
            &part2_extensions,
        )?;
        let component_quantizations = parser.finish_main_component_quantizations(
            image_size.components,
            quantization,
            &component_coding_styles,
            &qcc_segments,
        )?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(main_goal == crate::specs::part1_main_header_after_components(
                main_reader, depth_main, packed_header_frames_view(ppm_frames@), main_header@,
                parsed_coding_style_view(coding_style), quantization_view(&quantization),
                component_style_owner_view(&component_coding_styles),
                parsed_quantization_owner_view(&component_quantizations)));
            reveal(crate::specs::part1_main_header_after_components);
            super::tile_part_native_styles_inverse(&component_coding_styles);
        }
        parser.validate_progression_changes(
            &progression_changes,
            coding_style.layers,
            &component_coding_styles,
            0,
        )?;
        if (!mct_arrays.is_empty() || !mct_records.is_empty()) && mct_order.is_none() {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::MissingRequiredStructure,
            ));
        }
        parser.apply_component_registrations(
            &mut image_size,
            &part2_extensions.component_registrations,
        )?;
        let main_mct_parameters = MctParameters {
            arrays: mct_arrays,
            records: mct_records,
            order: mct_order.unwrap_or_default(),
        };
        let multiple_component_transform =
            parser.resolve_multiple_component_transform(&main_mct_parameters)?;
        let tile_count = image_size.tile_count()?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost complete_main = crate::specs::Part1MainHeader {
                reader: parser_view(&parser),
                raw: crate::specs::Part1MainHeaderAccumulator {
                    image_size: parsed_image_size_view(&image_size), ..depth_main
                },
                end: main_header_end, header: main_header@, ppm_frames: packed_header_frames_view(ppm_frames@),
                coding_style: parsed_coding_style_view(coding_style), quantization: quantization_view(&quantization),
                styles: component_style_owner_view(&component_coding_styles),
                quantizations: parsed_quantization_owner_view(&component_quantizations),
                mct: mct_parameters_view(&main_mct_parameters),
                transform: match multiple_component_transform {
                    None => None, Some(transform) => Some(multiple_component_transform_view(&transform)),
                },
                tile_count,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(mct_parameters_view);
            reveal(mct_graph_outcome);
            reveal(selection_geometry_view);
            reveal(parsed_image_size_view);
            assert(main_goal == Ok(complete_main));
            reveal(main_header_fields_view);
            assert(crate::specs::part1_main_header_fields(complete_main) == main_header_fields_view(
                &image_size, coding_style, &quantization, &component_coding_styles, &component_quantizations,
                &roi_shifts, &progression_changes, &multiple_component_transform, &part2_extensions,
                r_siz, &extended_capabilities, &profile, &corresponding_profile, main_header_segments));
        }
        let mut tile_parts = 0_u32;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost layout_goal = crate::specs::part1_read_layout(initial_reader);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_layout_from_main_result); }
        let mut tile_part_payloads: Vec<TilePartPayload<'a>> = Vec::new();
        let tile_state_count = usize::try_from(tile_count).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(
                        parser.position, MalformedKind::ArithmeticOverflow),
                ))]
            |_tile_state_conversion_error| parser.malformed_here(MalformedKind::ArithmeticOverflow),
        )?;
        let mut tile_roi_shifts = vec![None; tile_state_count];
        let mut tile_coding_styles = vec![None; tile_state_count];
        let mut tile_quantizations = vec![None; tile_state_count];
        let mut tile_component_style_parts: Vec<Option<usize>> = vec![None; tile_state_count];
        let mut tile_component_quantizations: Vec<Option<ComponentQuantizations>> =
            vec![None; tile_state_count];
        let mut tile_progression_changes: Vec<Option<ProgressionChanges>> =
            vec![None; tile_state_count];
        let mut tile_mct_parameters: Vec<Option<MctParameters>> = vec![None; tile_state_count];
        let mut tile_part2_extensions: Vec<Option<Part2Extensions>> = vec![None; tile_state_count];

        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial_persistent_state = persistent_tile_state_view(
                tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                tile_component_style_parts@, tile_component_quantizations@,
                tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                tile_part_payloads@);
            let ghost mut persistent_commits: Seq<crate::specs::Part1PersistentTileCommit> = Seq::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(persistent_tile_state_view);
            reveal(persistent_tile_configuration_view);
            reveal(super::persistent_tile_configuration_sequences_view);
            assert(initial_persistent_state == crate::specs::part1_empty_persistent_tile_state(tile_state_count));
            reveal(crate::specs::part1_persistent_tile_state_fold);
            assert(complete_main.reader == parser_view(&parser));
            assert(layout_goal == crate::specs::part1_layout_continuation(
                parser_view(&parser), complete_main, tile_parts, initial_persistent_state, input_length));
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    crate::specs::part1_persistent_tile_state_fold(
                        initial_persistent_state, persistent_commits)
                        == (Ok(()), persistent_tile_state_view(
                            tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                            tile_component_style_parts@, tile_component_quantizations@,
                            tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                            tile_part_payloads@)),
                    tile_component_style_parts.len() == tile_state_count,
                    tile_mct_parameters.len() == tile_state_count,
                    tile_part2_extensions.len() == tile_state_count,
                    forall|tile: int| 0 <= tile < tile_component_style_parts.len() ==>
                        match #[trigger] tile_component_style_parts@[tile] {
                            Some(part) => part < tile_part_payloads.len()
                                && tile_part_payloads@[part as int].tile_index as int == tile
                                && forall|later: int| part < later < tile_part_payloads.len() ==>
                                    (#[trigger] tile_part_payloads@[later]).tile_index as int != tile,
                            None => forall|prior: int| 0 <= prior < tile_part_payloads.len() ==>
                                (#[trigger] tile_part_payloads@[prior]).tile_index as int != tile,
                        },
                    initial_reader == parser_view(&self),
                    main_goal == crate::specs::part1_read_main_header(initial_reader),
                    main_goal == Ok(complete_main),
                    layout_goal == crate::specs::part1_read_layout(initial_reader),
                    complete_main.tile_count == tile_count,
                    complete_main.raw.roi_seen == roi_seen@,
                    complete_main.raw.plm_seen == plm_seen,
                    complete_main.raw.plm == packet_length_groups_view(plm_groups@),
                    complete_main.raw.ppm_fragments == ppm_fragments,
                    complete_main.ppm_frames == packed_header_frames_view(ppm_frames@),
                    complete_main.header == main_header@,
                    complete_main.mct == mct_parameters_view(&main_mct_parameters),
                    crate::specs::part1_main_header_fields(complete_main) == main_header_fields_view(
                        &image_size, coding_style, &quantization, &component_coding_styles, &component_quantizations,
                        &roi_shifts, &progression_changes, &multiple_component_transform, &part2_extensions,
                        r_siz, &extended_capabilities, &profile, &corresponding_profile, main_header_segments),
                invariant_except_break
                    layout_goal == crate::specs::part1_layout_continuation(
                        parser_view(&parser), complete_main, tile_parts, persistent_tile_state_view(
                            tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                            tile_component_style_parts@, tile_component_quantizations@,
                            tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                            tile_part_payloads@), input_length),
                ensures
                    layout_goal == crate::specs::part1_layout_after_tiles(
                        parser_view(&parser), complete_main, tile_parts, persistent_tile_state_view(
                            tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                            tile_component_style_parts@, tile_component_quantizations@,
                            tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                            tile_part_payloads@)),
                decreases input_length as int - parser.position as int,
            )
        )]
        loop {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_layout_continuation, 1);
                reveal(crate::specs::part1_layout_tile_part);
                reveal(crate::specs::part1_layout_inherited_tile_part);
                reveal(crate::specs::part1_commit_persistent_tile_state);
                reveal(main_header_fields_view);
                reveal(persistent_tile_state_view);
                reveal(persistent_tile_configuration_view);
                reveal(super::persistent_tile_configuration_sequences_view);
                reveal(crate::specs::part1_parser_progress);
                reveal(parser_view);
                reveal(tile_part_header_view);
                reveal(tile_part_main_metadata_outcome);
                reveal(inherited_tile_configuration_outcome);
                reveal(parsed_quantization_owner_view);
                reveal(quantization_owner_view);
                reveal(mct_parameter_copy_view);
                reveal(mct_parameters_view);
                reveal(super::tile_part_read_outcome);
                reveal(persistent_tile_selection_view);
                reveal(super::persistent_tile_selection_sequences_view);
                reveal(optional_roi_shifts_view);
                reveal(crate::specs::part1_codestream_malformed);
                let state = persistent_tile_state_view(
                    tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                    tile_component_style_parts@, tile_component_quantizations@,
                    tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@, tile_part_payloads@);
                let selection = super::persistent_tile_selection_sequences_view(
                    tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                    tile_component_style_parts@, tile_part_payloads@);
                assert(selection.0 =~= state.0.0);
                assert(selection == (state.0.0, state.0.1, state.0.2, state.0.3, state.3));
            }
            let previous_position = parser.position;
            match parser.peek_marker()? {
                SOT => {
                    tile_parts = tile_parts.checked_add(1).ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                                ensures error == crate::specs::part1_codestream_malformed(
                                    parser.position, MalformedKind::ArithmeticOverflow),
                            ))]
                        || parser.malformed_here(MalformedKind::ArithmeticOverflow),
                    )?;
                    if tile_parts > parser.limits.maximum_tile_parts() {
                        return Err(DecodeError::limit(
                            Resource::TileParts,
                            u64::from(parser.limits.maximum_tile_parts()),
                            u64::from(tile_parts),
                        ));
                    }
                    let tile_part = parser.read_sot(tile_count)?;
                    #[cfg(verus_keep_ghost)]
                    proof! { assert(tile_parts > 0); }
                    let (main_packet_lengths, packed_packet_headers) = parser
                        .tile_part_main_metadata(
                            tile_part,
                            tile_parts - 1,
                            &part2_extensions.tile_part_lengths,
                            plm_seen,
                            &plm_groups,
                            &ppm_frames,
                            ppm_fragments,
                            main_header,
                        )?;
                    let tile_index = usize::from(tile_part.tile_index);
                    let (
                        previous_roi_shifts,
                        inherited_roi_shifts,
                        inherited_default_style,
                        inherited_default_quantization,
                        inherited_component_styles,
                    ) = parser.select_inherited_tile_configuration(
                        tile_index,
                        &roi_shifts,
                        &coding_style,
                        &quantization,
                        &component_coding_styles,
                        &tile_roi_shifts,
                        &tile_coding_styles,
                        &tile_quantizations,
                        &tile_component_style_parts,
                        &tile_part_payloads,
                    )?;
                    let inherited_component_quantizations = inherited_tile_owner(
                        tile_index,
                        &component_quantizations,
                        &tile_component_quantizations,
                    )
                    .clone();
                    let inherited_progression_changes = inherited_tile_owner(
                        tile_index,
                        &progression_changes,
                        &tile_progression_changes,
                    )
                    .clone();
                    let inherited_mct_parameters = inherited_tile_owner(
                        tile_index,
                        &main_mct_parameters,
                        &tile_mct_parameters,
                    )
                    .clone();
                    let inherited_part2_extensions =
                        inherited_tile_owner(tile_index, &part2_extensions, &tile_part2_extensions)
                            .clone();
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(crate::specs::part1_inherited_tile_owner);
                        assert(quantization_owner_view(&inherited_component_quantizations)
                            == quantization_owner_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, component_quantizations, tile_component_quantizations@)));
                        assert(progression_changes_view(&inherited_progression_changes)
                            == progression_changes_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, progression_changes, tile_progression_changes@)));
                        assert(mct_parameter_copy_view(&inherited_mct_parameters)
                            == mct_parameter_copy_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, main_mct_parameters, tile_mct_parameters@)));
                        assert(owned_extensions_view(&inherited_part2_extensions)
                            == owned_extensions_view(&crate::specs::part1_inherited_tile_owner(
                                tile_index, part2_extensions, tile_part2_extensions@)));
                    }
                    let (payload, tile_parameters, tile_extensions) = parser.read_tile_part(
                        tile_part,
                        (inherited_default_style, inherited_default_quantization),
                        inherited_component_styles,
                        inherited_component_quantizations,
                        inherited_roi_shifts,
                        inherited_progression_changes,
                        inherited_mct_parameters,
                        inherited_part2_extensions,
                        image_size.components,
                        main_packet_lengths,
                        packed_packet_headers,
                    )?;
                    #[cfg(verus_keep_ghost)]
                    proof_decl! {
                        let ghost previous_style_parts = tile_component_style_parts@;
                        let ghost previous_payloads = tile_part_payloads@;
                        let ghost previous_persistent_commits = persistent_commits;
                        let ghost previous_persistent_state = persistent_tile_state_view(
                            tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                            tile_component_style_parts@, tile_component_quantizations@,
                            tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                            tile_part_payloads@);
                        let ghost persistent_commit = crate::specs::Part1PersistentTileCommit {
                            position: parser.position, start: tile_part.start, index: tile_index,
                            previous_roi: optional_roi_shifts_view(previous_roi_shifts),
                            payload: tile_part_payload_view(&payload),
                            parameters: mct_parameter_copy_view(&tile_parameters),
                            extensions: owned_extensions_view(&tile_extensions),
                        };
                    }
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(crate::specs::part1_persistent_tile_state_fold(
                            initial_persistent_state, previous_persistent_commits)
                            == (Ok(()), previous_persistent_state));
                    }
                    parser.commit_persistent_tile_configuration(
                        tile_part.start,
                        tile_index,
                        tile_part_payloads.len(),
                        previous_roi_shifts,
                        &payload,
                        &mut tile_roi_shifts,
                        &mut tile_coding_styles,
                        &mut tile_quantizations,
                        &mut tile_component_style_parts,
                        &mut tile_component_quantizations,
                        &mut tile_progression_changes,
                    )?;
                    *tile_mct_parameters
                        .get_mut(tile_index)
                        .ok_or_else(|| parser.malformed_here(MalformedKind::InvalidTilePart))? =
                        Some(tile_parameters);
                    *tile_part2_extensions
                        .get_mut(tile_index)
                        .ok_or_else(|| parser.malformed_here(MalformedKind::InvalidTilePart))? =
                        Some(tile_extensions);
                    tile_part_payloads.push(payload);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        reveal(persistent_tile_state_view);
                        reveal(persistent_tile_configuration_view);
                        reveal(super::persistent_tile_configuration_sequences_view);
                        reveal(crate::specs::part1_commit_persistent_tile_state);
                        assert(crate::specs::part1_commit_persistent_tile_state(
                            previous_persistent_state, persistent_commit)
                            == (Ok(()), persistent_tile_state_view(
                                tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                                tile_component_style_parts@, tile_component_quantizations@,
                                tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                                tile_part_payloads@)));
                        persistent_commits = persistent_commits.push(persistent_commit);
                        assert(persistent_commits.drop_last() == previous_persistent_commits);
                        assert(persistent_commits.last() == persistent_commit);
                        reveal(crate::specs::part1_persistent_tile_state_fold);
                        assert(crate::specs::part1_persistent_tile_state_fold(
                            initial_persistent_state, persistent_commits)
                            == (Ok(()), persistent_tile_state_view(
                                tile_roi_shifts@, tile_coding_styles@, tile_quantizations@,
                                tile_component_style_parts@, tile_component_quantizations@,
                                tile_progression_changes@, tile_mct_parameters@, tile_part2_extensions@,
                                tile_part_payloads@)));
                        assert forall|tile: int| 0 <= tile < tile_component_style_parts.len() implies
                            match #[trigger] tile_component_style_parts@[tile] {
                                Some(part) => part < tile_part_payloads.len()
                                    && tile_part_payloads@[part as int].tile_index as int == tile
                                    && forall|later: int| part < later < tile_part_payloads.len() ==>
                                        (#[trigger] tile_part_payloads@[later]).tile_index as int != tile,
                                None => forall|prior: int| 0 <= prior < tile_part_payloads.len() ==>
                                    (#[trigger] tile_part_payloads@[prior]).tile_index as int != tile,
                            } by {
                                if tile != tile_index {
                                    assert(tile_component_style_parts@[tile] == previous_style_parts[tile]);
                                    match previous_style_parts[tile] {
                                        Some(part) => {
                                            assert(part < previous_payloads.len());
                                            assert(tile_part_payloads@[part as int] == previous_payloads[part as int]);
                                            assert forall|later: int| part < later < tile_part_payloads.len() implies
                                                (#[trigger] tile_part_payloads@[later]).tile_index as int != tile by {
                                                    if later < previous_payloads.len() {
                                                        assert(tile_part_payloads@[later] == previous_payloads[later]);
                                                        assert(previous_payloads[later].tile_index as int != tile);
                                                    } else {
                                                        assert(later == previous_payloads.len());
                                                        assert(tile_part_payloads@[later].tile_index as int == tile_index);
                                                    }
                                                }
                                        }
                                        None => {
                                            assert forall|prior: int| 0 <= prior < tile_part_payloads.len() implies
                                                (#[trigger] tile_part_payloads@[prior]).tile_index as int != tile by {
                                                    if prior < previous_payloads.len() {
                                                        assert(tile_part_payloads@[prior] == previous_payloads[prior]);
                                                        assert(previous_payloads[prior].tile_index as int != tile);
                                                    } else {
                                                        assert(prior == previous_payloads.len());
                                                        assert(tile_part_payloads@[prior].tile_index as int == tile_index);
                                                    }
                                                }
                                        }
                                    }
                                } else {
                                    assert(tile_component_style_parts@[tile] == Some(previous_payloads.len() as usize));
                                    assert(tile_part_payloads.len() == previous_payloads.len() + 1);
                                    assert(tile_part_payloads@[previous_payloads.len() as int].tile_index as int == tile);
                                }
                            }
                    }
                }
                EOC => {
                    parser.finish_tile_part_traversal(
                        tile_parts,
                        plm_seen,
                        plm_groups.len(),
                        ppm_fragments,
                        ppm_frames.len(),
                        part2_extensions.tile_part_lengths.len(),
                    )?;
                    break;
                }
                _ => return Err(parser.malformed_here(MalformedKind::InvalidMarkerOrder)),
            }
            if !crate::refinement::parser_progress(previous_position, parser.position, input_length)
            {
                return Err(parser.malformed_here(MalformedKind::InvalidTilePart));
            }
        }

        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(main_header_fields_view);
            reveal(crate::specs::part1_layout_after_tiles);
            reveal(profile_tile_inputs_view);
            reveal(tile_part_payload_view);
            reveal(persistent_tile_state_view);
            assert(profile_tile_inputs_view(tile_part_payloads@)
                =~= crate::specs::part1_layout_profile_tiles(
                    tile_part_payloads@.map_values(|part: TilePartPayload<'_>| tile_part_payload_view(&part))));
            assert forall|index: int| 0 <= index < roi_seen@.len()
                implies *roi_seen@.as_ref()[index] == #[trigger] roi_seen@[index] by {
                roi_seen@.lemma_as_ref_index(index);
            }
            assert((exists|index: int| 0 <= index < roi_seen@.len() && *roi_seen@.as_ref()[index])
                == (exists|index: int| 0 <= index < roi_seen@.len() && roi_seen@[index])) by {
                if exists|index: int| 0 <= index < roi_seen@.len() && *roi_seen@.as_ref()[index] {
                    let index = choose|index: int| 0 <= index < roi_seen@.len() && *roi_seen@.as_ref()[index];
                    assert(roi_seen@[index]);
                }
                if exists|index: int| 0 <= index < roi_seen@.len() && roi_seen@[index] {
                    let index = choose|index: int| 0 <= index < roi_seen@.len() && roi_seen@[index];
                    assert(*roi_seen@.as_ref()[index]);
                }
            }
            assert(r_siz == complete_main.raw.r_siz);
            assert(optional_capabilities_view(&extended_capabilities) == complete_main.raw.capabilities);
            assert(optional_profile_number_view(&profile) == complete_main.raw.profile);
            assert(optional_profile_number_view(&corresponding_profile) == complete_main.raw.corresponding_profile);
        }
        let codestream_profile = classify_codestream_profile(
            r_siz,
            extended_capabilities,
            profile,
            corresponding_profile,
            &component_coding_styles,
            &roi_shifts,
            &tile_part_payloads,
            image_size.components,
            roi_seen.iter().any(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: bool =>
                    ensures result == *seen,
                ))]
                |seen| *seen,
            ),
        )?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_classification_preserves_metadata(
                complete_main.raw.r_siz, complete_main.raw.capabilities, complete_main.raw.profile,
                complete_main.raw.corresponding_profile, complete_main.styles, complete_main.raw.roi,
                crate::specs::part1_layout_profile_tiles(
                    tile_part_payloads@.map_values(|part: TilePartPayload<'_>| tile_part_payload_view(&part))),
                complete_main.raw.image_size.components,
                exists|index: int| 0 <= index < complete_main.raw.roi_seen.len()
                    && complete_main.raw.roi_seen[index]);
            reveal(complete_codestream_profile_outcome);
            reveal(super::complete_codestream_profile_view);
            reveal(main_header_fields_view);
            reveal(complete_codestream_info_view);
            let actual_profile = super::complete_codestream_profile_view(&codestream_profile);
            assert(actual_profile.0 == complete_main.raw.r_siz);
            assert(actual_profile.2 == complete_main.raw.capabilities);
            assert(actual_profile.3 == complete_main.raw.profile);
            assert(actual_profile.4 == complete_main.raw.corresponding_profile);
        }
        Ok(CodestreamLayout {
            info: CodestreamInfo {
                image_size,
                coding_style,
                quantization,
                component_coding_styles,
                component_quantizations,
                roi_shifts,
                progression_changes,
                multiple_component_transform,
                part2_extensions,
                profile: codestream_profile,
                main_header_segments,
                tile_parts,
                consumed_bytes: parser.offset(parser.position),
            },
            tile_parts: tile_part_payloads,
        })
    }
}
