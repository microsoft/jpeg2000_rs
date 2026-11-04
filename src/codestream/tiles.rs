//! Tile-part header/payload parsing and owned tile-part construction.

use super::coding_style::new_component_coding_styles;
use super::mct_resolution::{replace_mct_array, replace_mct_record};
use super::quantization::new_component_quantizations;
use super::reader::{is_allowed_tile_header, is_known_segment_marker, read_u16, read_u32};
use super::{
    ADS, ATK, CBD, COC, COD, COM, CodingStyle, ComponentCodingStyles, ComponentQuantizations, DFS,
    DecodeError, MAX_COMPONENTS, MCC, MCO, MCT, MalformedKind, MctParameters, NLT, PLT, POC, PPT,
    PackedPacketHeaders, PacketLengths, Parser, Part2Extensions, ProgressionChanges, QCC, QCD,
    Quantization, RGN, RoiShifts, SOD, SOT, TilePart, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    component_style_owner_view, optional_segment_view, owned_extensions_view,
    parsed_coding_style_view, parsed_quantization_owner_view, parser_view, quantization_view,
    segment_slots_view, tile_component_configuration_outcome, tile_data_window_outcome,
    tile_part_header_outcome, tile_part_owned_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl<'a> Clone for TilePartPayload<'a> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tile_part_owned_view(&result) == crate::specs::part2_tile_part_copy(tile_part_owned_view(self)),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(tile_part_owned_view); }
        Self {
            tile_index: self.tile_index,
            tile_part_index: self.tile_part_index,
            tile_part_count: self.tile_part_count,
            coding_style: self.coding_style,
            quantization: self.quantization,
            component_coding_styles: self.component_coding_styles,
            component_quantizations: self.component_quantizations.clone(),
            roi_shifts: self.roi_shifts,
            progression_changes: self.progression_changes.clone(),
            multiple_component_transform: self.multiple_component_transform.clone(),
            part2_extensions: self.part2_extensions.clone(),
            packet_lengths: self.packet_lengths,
            packed_packet_headers: self.packed_packet_headers,
            has_functional_header_marker: self.has_functional_header_marker,
            has_roi_marker: self.has_roi_marker,
            data: self.data,
        }
    }
}
impl<'a> TilePartPayload<'a> {
    pub fn uniform_for_packet_decoding(
        tile_index: u16,
        tile_part_index: u8,
        tile_part_count: u8,
        components: u16,
        coding_style: CodingStyle,
        roi_shifts: RoiShifts,
        data: &'a [u8],
    ) -> Result<Self, DecodeError> {
        let quantization = Quantization::reversible_default(coding_style);
        Ok(Self {
            tile_index,
            tile_part_index,
            tile_part_count,
            coding_style,
            quantization,
            component_coding_styles: ComponentCodingStyles::uniform(components, coding_style)?,
            component_quantizations: ComponentQuantizations::uniform(components, quantization)?,
            roi_shifts,
            progression_changes: ProgressionChanges::none(),
            multiple_component_transform: None,
            part2_extensions: Part2Extensions::default(),
            packet_lengths: PacketLengths::none(),
            packed_packet_headers: PackedPacketHeaders::none(),
            has_functional_header_marker: false,
            has_roi_marker: false,
            data,
        })
    }
}
impl<'a> Parser<'a> {
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tile_component_configuration_outcome(result) == crate::specs::part1_finish_tile_components(
            components, parsed_coding_style_view(tile_coding_style), tile_cod_seen,
            segment_slots_view(coc_segments@), optional_segment_view(qcd_segment),
            quantization_view(&default_quantization), segment_slots_view(qcc_segments@),
            component_style_owner_view(&inherited_coding_styles),
            parsed_quantization_owner_view(&inherited_quantizations),
            owned_extensions_view(part2_extensions), &self.limits),
    ))]
    pub(super) fn finish_tile_component_configuration(
        &self,
        components: u16,
        tile_coding_style: CodingStyle,
        tile_cod_seen: bool,
        coc_segments: &[Option<super::Segment<'a>>],
        qcd_segment: Option<super::Segment<'a>>,
        default_quantization: Quantization,
        qcc_segments: &[Option<super::Segment<'a>>],
        inherited_coding_styles: ComponentCodingStyles,
        inherited_quantizations: ComponentQuantizations,
        part2_extensions: &Part2Extensions,
    ) -> Result<(ComponentCodingStyles, Quantization, ComponentQuantizations), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_finish_tile_components);
            reveal(crate::specs::part1_component_styles_new);
            reveal(crate::specs::part1_component_quantizations_new);
        }
        let mut component_coding_styles = if tile_cod_seen {
            new_component_coding_styles(components, tile_coding_style)?
        } else {
            inherited_coding_styles
        };
        self.apply_component_style_overrides(
            components,
            tile_coding_style,
            coc_segments,
            &mut component_coding_styles,
        )?;
        self.resolve_decomposition_structures(&mut component_coding_styles, part2_extensions)?;
        let tile_quantization = match qcd_segment {
            Some(segment) => self.parse_qcd(segment, tile_coding_style)?,
            None => default_quantization,
        };
        let mut component_quantizations = if qcd_segment.is_some() {
            new_component_quantizations(components, tile_quantization)?
        } else {
            inherited_quantizations
        };
        self.apply_component_quantization_overrides(
            components,
            &component_coding_styles,
            qcc_segments,
            &mut component_quantizations,
        )?;
        Ok((
            component_coding_styles,
            tile_quantization,
            component_quantizations,
        ))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (tile_part_header_outcome(result), parser_view(final(self))) == crate::specs::part1_codestream_read_sot(
            parser_view(old(self)), tile_count),
    ))]
    pub(super) fn read_sot(&mut self, tile_count: u64) -> Result<TilePart, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_codestream_read_sot); }
        let segment = self.read_segment()?;
        if segment.marker != SOT || segment.payload.len() != 8 {
            return Err(DecodeError::malformed(
                self.offset(segment.offset),
                MalformedKind::InvalidTilePart,
            ));
        }
        let tile_index = read_u16([segment.payload[0], segment.payload[1]]);
        let length = read_u32([
            segment.payload[2],
            segment.payload[3],
            segment.payload[4],
            segment.payload[5],
        ]);
        let tile_part_index = segment.payload[6];
        let tile_part_count = segment.payload[7];
        if u64::from(tile_index) >= tile_count
            || (tile_part_count != 0 && tile_part_index >= tile_part_count)
            || (length != 0 && length < 14)
        {
            return Err(DecodeError::malformed(
                self.offset(segment.offset),
                MalformedKind::InvalidTilePart,
            ));
        }
        Ok(TilePart {
            start: segment.offset,
            length,
            tile_index,
            tile_part_index,
            tile_part_count,
        })
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result {
            Ok((payload, _, _)) => payload.tile_index == tile_part.tile_index,
            Err(_) => true,
        },
    ))]
    pub(super) fn read_tile_part(
        &mut self,
        tile_part: TilePart,
        default_parameters: (CodingStyle, Quantization),
        inherited_coding_styles: ComponentCodingStyles,
        inherited_quantizations: ComponentQuantizations,
        inherited_roi_shifts: RoiShifts,
        inherited_progression_changes: ProgressionChanges,
        mut mct_parameters: MctParameters,
        mut part2_extensions: Part2Extensions,
        components: u16,
        main_packet_lengths: PacketLengths<'a>,
        main_packed_packet_headers: PackedPacketHeaders<'a>,
    ) -> Result<(TilePartPayload<'a>, MctParameters, Part2Extensions), DecodeError> {
        let tile_header_start = self.position;
        let tile_header_end;
        let mut tile_coding_style = default_parameters.0;
        let mut tile_cod_seen = false;
        let mut qcd_segment = None;
        let mut coc_segments = [None; MAX_COMPONENTS];
        let mut qcc_segments = [None; MAX_COMPONENTS];
        let mut tile_roi_shifts = inherited_roi_shifts;
        let mut roi_seen = [false; MAX_COMPONENTS];
        let mut tile_rgn_seen = false;
        let mut has_functional_header_marker = false;
        let mut plt_seen = false;
        let mut next_plt_index = 0_u16;
        let mut plt_packet_count = 0_u64;
        let mut plt_encoded_bytes = 0_u64;
        let mut plt_payload_bytes = 0_u64;
        let mut ppt_bytes = Vec::new();
        let mut next_ppt_index = 0_u16;
        let mut ppt_fragments = 0_u16;
        let mut progression_changes = inherited_progression_changes;
        let mut poc_seen = false;
        let mut tile_mco_seen = false;
        let mut pending_mct = Vec::new();
        let mut completed_mct = Vec::new();
        let mut pending_mcc = Vec::new();
        let mut completed_mcc = Vec::new();
        let input_length = self.input.len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases input_length as int - self.position as int,)
        )]
        loop {
            let previous_position = self.position;
            match self.peek_marker()? {
                SOD => {
                    tile_header_end = self.position;
                    self.expect_standalone(SOD)?;
                    break;
                }
                marker if crate::refinement::tile_header_boundary(marker) => {
                    return Err(self.malformed_here(MalformedKind::InvalidMarkerOrder));
                }
                _ => {
                    let segment = self.read_segment()?;
                    if !is_known_segment_marker(segment.marker) {
                        return Err(DecodeError::malformed(
                            self.offset(segment.offset),
                            MalformedKind::InvalidMarker,
                        ));
                    }
                    if !is_allowed_tile_header(segment.marker) {
                        return Err(DecodeError::malformed(
                            self.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    }
                    if segment.marker != COM && segment.marker != PLT {
                        has_functional_header_marker = true;
                    }
                    if segment.marker == COD {
                        if tile_cod_seen {
                            return Err(DecodeError::malformed(
                                self.offset(segment.offset),
                                MalformedKind::InvalidMarkerOrder,
                            ));
                        }
                        tile_cod_seen = true;
                        tile_coding_style = self.parse_cod(segment)?;
                    } else if segment.marker == COC {
                        self.record_component_segment(
                            segment,
                            components,
                            MalformedKind::InvalidCodingStyle,
                            &mut coc_segments,
                        )?;
                    } else if segment.marker == QCD {
                        if qcd_segment.is_some() {
                            return Err(DecodeError::malformed(
                                self.offset(segment.offset),
                                MalformedKind::InvalidMarkerOrder,
                            ));
                        }
                        qcd_segment = Some(segment);
                    } else if segment.marker == QCC {
                        self.record_component_segment(
                            segment,
                            components,
                            MalformedKind::InvalidQuantization,
                            &mut qcc_segments,
                        )?;
                    } else if segment.marker == RGN {
                        let (component, shift) = self.parse_rgn(segment, components)?;
                        let index = usize::from(component);
                        if index >= roi_seen.len() || roi_seen[index] {
                            return Err(DecodeError::malformed(
                                self.offset(segment.offset),
                                MalformedKind::InvalidMarkerOrder,
                            ));
                        }
                        roi_seen[index] = true;
                        tile_rgn_seen = true;
                        tile_roi_shifts.set(component, shift)?;
                    } else if segment.marker == MCT {
                        if let Some(array) = self.consume_mct_fragment(
                            segment,
                            &mut pending_mct,
                            &mut completed_mct,
                        )? {
                            replace_mct_array(&mut mct_parameters.arrays, array);
                        }
                    } else if segment.marker == MCC {
                        if let Some(record) = self.consume_mcc_fragment(
                            segment,
                            components,
                            &mut pending_mcc,
                            &mut completed_mcc,
                        )? {
                            replace_mct_record(&mut mct_parameters.records, record);
                        }
                    } else if segment.marker == MCO {
                        if tile_mco_seen {
                            return Err(DecodeError::malformed(
                                self.offset(segment.offset),
                                MalformedKind::InvalidMarkerOrder,
                            ));
                        }
                        tile_mco_seen = true;
                        mct_parameters.order = self.parse_mco(segment)?;
                    } else if segment.marker == PLT {
                        self.parse_plt(
                            segment,
                            main_packet_lengths,
                            &mut next_plt_index,
                            &mut plt_seen,
                            &mut plt_packet_count,
                            &mut plt_encoded_bytes,
                            &mut plt_payload_bytes,
                        )?;
                    } else if segment.marker == PPT {
                        self.parse_ppt(
                            segment,
                            main_packed_packet_headers,
                            &mut next_ppt_index,
                            &mut ppt_fragments,
                            &mut ppt_bytes,
                        )?;
                    } else if segment.marker == POC {
                        if poc_seen || tile_part.tile_part_index != 0 {
                            return Err(DecodeError::malformed(
                                self.offset(segment.offset),
                                MalformedKind::InvalidMarkerOrder,
                            ));
                        }
                        poc_seen = true;
                        progression_changes = self.parse_poc(segment, components)?;
                    } else if segment.marker == DFS {
                        self.parse_dfs(segment, &mut part2_extensions)?;
                    } else if segment.marker == ADS {
                        self.parse_ads(segment, &mut part2_extensions)?;
                    } else if segment.marker == NLT {
                        self.parse_nlt(segment, components, &mut part2_extensions)?;
                    } else if segment.marker == CBD {
                        return Err(DecodeError::malformed(
                            self.offset(segment.offset),
                            MalformedKind::InvalidMarkerOrder,
                        ));
                    } else if segment.marker == ATK {
                        self.parse_atk(segment, &mut part2_extensions)?;
                    } else if segment.marker != 0xff64 {
                        return Err(DecodeError::malformed(
                            self.offset(segment.offset),
                            MalformedKind::InvalidMarker,
                        ));
                    }
                }
            }
            if !crate::refinement::parser_progress(previous_position, self.position, input_length) {
                return Err(self.malformed_here(MalformedKind::InvalidTilePart));
            }
        }
        if !pending_mct.is_empty() || !pending_mcc.is_empty() {
            return Err(self.malformed_here(MalformedKind::MissingRequiredStructure));
        }
        let (component_coding_styles, tile_quantization, component_quantizations) = self
            .finish_tile_component_configuration(
                components,
                tile_coding_style,
                tile_cod_seen,
                &coc_segments,
                qcd_segment,
                default_parameters.1,
                &qcc_segments,
                inherited_coding_styles,
                inherited_quantizations,
                &part2_extensions,
            )?;
        self.validate_progression_changes(
            &progression_changes,
            tile_coding_style.layers,
            &component_coding_styles,
            tile_part.start,
        )?;
        let multiple_component_transform =
            self.resolve_multiple_component_transform(&mct_parameters)?;

        let data_start = self.position;
        if tile_part.length == 0 {
            let (_, data) = self.tile_data_window(data_start, tile_part.start, tile_part.length)?;
            let packet_lengths = self.finish_packet_lengths(
                tile_header_start,
                tile_header_end,
                main_packet_lengths,
                plt_seen,
                plt_packet_count,
                plt_encoded_bytes,
                plt_payload_bytes,
                data.len(),
                if main_packed_packet_headers.is_present() {
                    main_packed_packet_headers.len()
                } else {
                    ppt_bytes.len()
                },
                tile_part.start,
            )?;
            let packed_packet_headers = self.finish_packed_packet_headers(
                tile_header_start,
                tile_header_end,
                main_packed_packet_headers,
                ppt_fragments,
                ppt_bytes.len(),
                tile_part.start,
            )?;
            return Ok((
                TilePartPayload {
                    tile_index: tile_part.tile_index,
                    tile_part_index: tile_part.tile_part_index,
                    tile_part_count: tile_part.tile_part_count,
                    coding_style: tile_coding_style,
                    quantization: tile_quantization,
                    component_coding_styles,
                    component_quantizations,
                    roi_shifts: tile_roi_shifts,
                    progression_changes,
                    multiple_component_transform,
                    part2_extensions: part2_extensions.clone(),
                    packet_lengths,
                    packed_packet_headers,
                    has_functional_header_marker,
                    has_roi_marker: tile_rgn_seen,
                    data,
                },
                mct_parameters,
                part2_extensions,
            ));
        }

        let (end, data) = self.tile_data_window(data_start, tile_part.start, tile_part.length)?;
        let packet_lengths = self.finish_packet_lengths(
            tile_header_start,
            tile_header_end,
            main_packet_lengths,
            plt_seen,
            plt_packet_count,
            plt_encoded_bytes,
            plt_payload_bytes,
            data.len(),
            if main_packed_packet_headers.is_present() {
                main_packed_packet_headers.len()
            } else {
                ppt_bytes.len()
            },
            tile_part.start,
        )?;
        let packed_packet_headers = self.finish_packed_packet_headers(
            tile_header_start,
            tile_header_end,
            main_packed_packet_headers,
            ppt_fragments,
            ppt_bytes.len(),
            tile_part.start,
        )?;
        self.position = end;
        Ok((
            TilePartPayload {
                tile_index: tile_part.tile_index,
                tile_part_index: tile_part.tile_part_index,
                tile_part_count: tile_part.tile_part_count,
                coding_style: tile_coding_style,
                quantization: tile_quantization,
                component_coding_styles,
                component_quantizations,
                roi_shifts: tile_roi_shifts,
                progression_changes,
                multiple_component_transform,
                part2_extensions: part2_extensions.clone(),
                packet_lengths,
                packed_packet_headers,
                has_functional_header_marker,
                has_roi_marker: tile_rgn_seen,
                data,
            },
            mct_parameters,
            part2_extensions,
        ))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (tile_data_window_outcome(result), parser_view(final(self)))
            == crate::specs::part1_tile_data_window(parser_view(old(self)), data_start, start, length),
    ))]
    pub(super) fn tile_data_window(
        &mut self,
        data_start: usize,
        start: usize,
        length: u32,
    ) -> Result<(usize, &'a [u8]), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(tile_data_window_outcome);
            reveal(parser_view);
            reveal(crate::specs::part1_tile_data_window);
        }
        if length == 0 {
            let end = self.find_eoc()?;
            self.position = end;
            let data = self.input.get(data_start..end).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                        ensures error == crate::specs::part1_codestream_malformed(
                            self.position, MalformedKind::InvalidTilePart),
                    ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )?;
            return Ok((end, data));
        }
        let tile_part_length = usize::try_from(length).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                ensures error == crate::specs::part1_codestream_malformed(
                    self.position, MalformedKind::InvalidTilePart),
            ))]
            |_error| self.malformed_here(MalformedKind::InvalidTilePart),
        )?;
        let end = start.checked_add(tile_part_length).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                ensures error == crate::specs::part1_codestream_malformed(
                    self.position, MalformedKind::ArithmeticOverflow),
            ))]
            || self.malformed_here(MalformedKind::ArithmeticOverflow),
        )?;
        if end < self.position || end > self.input.len() {
            return Err(DecodeError::malformed(
                self.offset(start),
                MalformedKind::InvalidTilePart,
            ));
        }
        let data = self.input.get(data_start..end).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                ensures error == crate::specs::part1_codestream_malformed(
                    self.position, MalformedKind::InvalidTilePart),
            ))]
            || self.malformed_here(MalformedKind::InvalidTilePart),
        )?;
        Ok((end, data))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self))) == crate::specs::part1_codestream_find_eoc(parser_view(old(self))),
    ))]
    pub(super) fn find_eoc(&mut self) -> Result<usize, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost input = parser_view(self);
            let ghost goal = crate::specs::part1_codestream_find_eoc(input);
        }
        let input_len = self.input.len();
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant input == parser_view(old(self)),
                    self.input@ == input.input, self.limits == input.limits,
                    self.packet_length_bytes == input.packet_length_bytes,
                    self.packet_lengths == input.packet_lengths,
                    input_len == input.input.len(),
                    goal == crate::specs::part1_codestream_find_eoc(input),
                    goal == crate::specs::part1_codestream_find_eoc(parser_view(self)),
                decreases input_len as int - self.position as int,
            )
        )]
        while self.position < input_len {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_codestream_find_eoc, 1); }
            if input_len - self.position < 2 {
                return Err(self.malformed_here(MalformedKind::Truncated));
            }
            let next_position = self
                .position
                .checked_add(1)
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
            if self.position >= self.input.len() || next_position >= self.input.len() {
                return Err(self.malformed_here(MalformedKind::Truncated));
            }
            let is_eoc = self.input[self.position] == 0xff && self.input[next_position] == 0xd9;
            self.charge_work(1)?;
            if is_eoc {
                return Ok(self.position);
            }
            if next_position <= self.position || next_position > input_len {
                return Err(self.malformed_here(MalformedKind::ArithmeticOverflow));
            }
            self.position = next_position;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.position >= input_len || (input_len as int) - (self.position as int) < 2);
            reveal_with_fuel(crate::specs::part1_codestream_find_eoc, 1);
            assert(goal == (Err(crate::specs::part1_codestream_malformed(self.position, MalformedKind::Truncated)), parser_view(self)));
        }
        Err(self.malformed_here(MalformedKind::Truncated))
    }
}
