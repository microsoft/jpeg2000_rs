//! Tile-part header/payload parsing and owned tile-part construction.

use super::coding_style::new_component_coding_styles;
#[cfg(verus_keep_ghost)]
use super::mct_copy::copy_outcome;
use super::quantization::new_component_quantizations;
use super::reader::{read_u16, read_u32};
use super::tile_header_traversal::TileHeaderAccumulator;
use super::{
    CodingStyle, ComponentCodingStyles, ComponentQuantizations, DecodeError, MalformedKind,
    MctParameters, PackedPacketHeaders, PacketLengths, Parser, Part2Extensions, ProgressionChanges,
    Quantization, RoiShifts, SOT, TilePart, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    component_style_owner_view, mct_parameters_view, optional_segment_view, owned_extensions_view,
    packed_packet_headers_view, packet_lengths_view, parsed_coding_style_view,
    parsed_quantization_owner_view, parser_view, progression_changes_view, quantization_owner_view,
    quantization_view, roi_shifts_view, segment_slots_view, tile_component_configuration_outcome,
    tile_data_window_outcome, tile_part_header_outcome, tile_part_header_view,
    tile_part_owned_view, tile_part_read_outcome,
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
            has_progression_marker: self.has_progression_marker,
            has_functional_header_marker: self.has_functional_header_marker,
            has_roi_marker: self.has_roi_marker,
            data: self.data,
        }
    }
}
impl<'a> TilePartPayload<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part2_payload_duplicate_tail(tile_part_owned_view(self), 0), copy_outcome(result)),
            match result { Err(error) => error == DecodeError::AllocationFailed,
                Ok(value) => tile_part_owned_view(&value) == tile_part_owned_view(self) },
    ))]
    pub(crate) fn try_duplicate(&self) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = tile_part_owned_view(self);
            let ghost mut done = Seq::<crate::specs::Part1MctCopyRequest>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(quantization_owner_view); reveal(copy_outcome);
            crate::specs::part1_mct_copy_observed(super::MctCopyPath::Order, 0, Ok(()));
            assert(done + crate::specs::part2_payload_duplicate_tail(source, 0)
                =~= crate::specs::part2_payload_duplicate_tail(source, 0));
        }
        let copied = self
            .component_quantizations
            .try_duplicate_for(super::MctCopyPath::CollectedQuantizations);
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part2_payload_duplicate_advance(source, 0, done, copy_outcome(copied));
        }
        let component_quantizations = copied?;
        let copied = self
            .progression_changes
            .try_duplicate_for(super::MctCopyPath::CollectedProgression);
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part2_payload_duplicate_advance(source, 1, done, copy_outcome(copied));
        }
        let progression_changes = copied?;
        let copied = match &self.multiple_component_transform {
            None => Ok(None),
            Some(transform) => match transform.try_duplicate() {
                Err(error) => Err(error),
                Ok(value) => Ok(Some(value)),
            },
        };
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part2_payload_duplicate_advance(source, 2, done, copy_outcome(copied)); }
        let multiple_component_transform = copied?;
        let copied = self.part2_extensions.try_duplicate_with(true);
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part2_payload_duplicate_advance(source, 3, done, copy_outcome(copied)); }
        let part2_extensions = copied?;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_payload_duplicate_tail, 1);
            assert(done =~= crate::specs::part2_payload_duplicate_tail(source, 0));
        }
        Ok(Self {
            tile_index: self.tile_index,
            tile_part_index: self.tile_part_index,
            tile_part_count: self.tile_part_count,
            coding_style: self.coding_style,
            quantization: self.quantization,
            component_coding_styles: self.component_coding_styles,
            component_quantizations,
            roi_shifts: self.roi_shifts,
            progression_changes,
            multiple_component_transform,
            part2_extensions,
            packet_lengths: self.packet_lengths,
            packed_packet_headers: self.packed_packet_headers,
            has_progression_marker: self.has_progression_marker,
            has_functional_header_marker: self.has_functional_header_marker,
            has_roi_marker: self.has_roi_marker,
            data: self.data,
        })
    }

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
            has_progression_marker: false,
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
        ensures crate::specs::part1_tile_components_cold_result(
            components, parsed_coding_style_view(tile_coding_style), tile_cod_seen,
            segment_slots_view(coc_segments@), optional_segment_view(qcd_segment),
            quantization_view(&default_quantization), segment_slots_view(qcc_segments@),
            component_style_owner_view(&inherited_coding_styles),
            parsed_quantization_owner_view(&inherited_quantizations),
            owned_extensions_view(part2_extensions), &self.limits, tile_component_configuration_outcome(result)),
        tile_component_configuration_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            tile_component_configuration_outcome(result) == crate::specs::part1_finish_tile_components(
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
            crate::specs::part1_tile_components_cold_normal(
                components, parsed_coding_style_view(tile_coding_style), tile_cod_seen,
                segment_slots_view(coc_segments@), optional_segment_view(qcd_segment),
                quantization_view(&default_quantization), segment_slots_view(qcc_segments@),
                component_style_owner_view(&inherited_coding_styles),
                parsed_quantization_owner_view(&inherited_quantizations),
                owned_extensions_view(part2_extensions), &self.limits);
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
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_prepare_tile_quantization); }
        let mut component_quantizations = if qcd_segment.is_some() {
            match new_component_quantizations(components, tile_quantization) {
                Ok(values) => values,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if error == DecodeError::AllocationFailed {
                            crate::specs::part1_tile_components_cold_refused(
                                components, parsed_coding_style_view(tile_coding_style), tile_cod_seen,
                                segment_slots_view(coc_segments@), optional_segment_view(qcd_segment),
                                quantization_view(&default_quantization), segment_slots_view(qcc_segments@),
                                component_style_owner_view(&inherited_coding_styles),
                                parsed_quantization_owner_view(&inherited_quantizations),
                                owned_extensions_view(part2_extensions), &self.limits,
                                (component_style_owner_view(&component_coding_styles), quantization_view(&tile_quantization)), error);
                        }
                    }
                    return Err(error);
                }
            }
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
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_cold_tile_part_result(crate::specs::Part1ColdTileInput {
                reader: parser_view(old(self)), tile: tile_part_header_view(tile_part),
                defaults: (parsed_coding_style_view(default_parameters.0), quantization_view(&default_parameters.1)),
                styles: component_style_owner_view(&inherited_coding_styles),
                quantizations: parsed_quantization_owner_view(&inherited_quantizations),
                roi: roi_shifts_view(&inherited_roi_shifts),
                progression: progression_changes_view(&inherited_progression_changes),
                mct: mct_parameters_view(&mct_parameters), extensions: owned_extensions_view(&part2_extensions),
                components, lengths: packet_lengths_view(&main_packet_lengths),
                headers: packed_packet_headers_view(&main_packed_packet_headers),
            }, (tile_part_read_outcome(result), parser_view(final(self)))),
            tile_part_read_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            (tile_part_read_outcome(result), parser_view(final(self)))
            == crate::specs::part1_read_tile_part(
                parser_view(old(self)), tile_part_header_view(tile_part),
                (parsed_coding_style_view(default_parameters.0), quantization_view(&default_parameters.1)),
                component_style_owner_view(&inherited_coding_styles),
                parsed_quantization_owner_view(&inherited_quantizations),
                roi_shifts_view(&inherited_roi_shifts), progression_changes_view(&inherited_progression_changes),
                mct_parameters_view(&mct_parameters), owned_extensions_view(&part2_extensions),
                components, packet_lengths_view(&main_packet_lengths),
                packed_packet_headers_view(&main_packed_packet_headers)),
            match result {
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
        mct_parameters: MctParameters,
        part2_extensions: Part2Extensions,
        components: u16,
        main_packet_lengths: PacketLengths<'a>,
        main_packed_packet_headers: PackedPacketHeaders<'a>,
    ) -> Result<(TilePartPayload<'a>, MctParameters, Part2Extensions), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost cold_input = crate::specs::Part1ColdTileInput {
                reader: parser_view(self), tile: tile_part_header_view(tile_part),
                defaults: (parsed_coding_style_view(default_parameters.0), quantization_view(&default_parameters.1)),
                styles: component_style_owner_view(&inherited_coding_styles),
                quantizations: parsed_quantization_owner_view(&inherited_quantizations),
                roi: roi_shifts_view(&inherited_roi_shifts),
                progression: progression_changes_view(&inherited_progression_changes),
                mct: mct_parameters_view(&mct_parameters), extensions: owned_extensions_view(&part2_extensions),
                components, lengths: packet_lengths_view(&main_packet_lengths),
                headers: packed_packet_headers_view(&main_packed_packet_headers),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_cold_tile_part_normal(cold_input);
            reveal(crate::specs::part1_read_tile_part);
            reveal(crate::specs::part1_finish_tile_part);
            reveal(crate::specs::part1_tile_part_after_configuration);
            reveal(crate::specs::part1_tile_part_after_window);
            reveal(super::tile_header_read_outcome);
            reveal(super::tile_header_accumulator_view);
            reveal(super::mct_pending_view);
            reveal(super::mcc_pending_view);
            reveal(tile_component_configuration_outcome);
            reveal(tile_part_read_outcome);
            reveal(super::tile_part_payload_view);
            reveal(parser_view);
            reveal(tile_part_header_view);
        }
        let header = match self.read_tile_header(
            default_parameters.0,
            inherited_roi_shifts,
            inherited_progression_changes,
            mct_parameters,
            part2_extensions,
            components,
            tile_part.tile_part_index,
            main_packet_lengths,
            main_packed_packet_headers,
        ) {
            Ok(header) => header,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::specs::part1_cold_tile_header_error(cold_input, error, parser_view(self)); }
                return Err(error);
            }
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost cold_raw = super::tile_header_accumulator_view(&header);
            let ghost header_reader = parser_view(self);
        }
        let TileHeaderAccumulator {
            tile_header_start,
            tile_header_end,
            tile_coding_style,
            tile_cod_seen,
            qcd_segment,
            coc_segments,
            qcc_segments,
            tile_roi_shifts,
            tile_rgn_seen,
            has_functional_header_marker,
            plt_seen,
            plt_packet_count,
            plt_encoded_bytes,
            plt_payload_bytes,
            ppt_bytes,
            ppt_fragments,
            progression_changes,
            poc_seen,
            mct_parameters,
            pending_mct,
            completed_mct: _completed_mct,
            pending_mcc,
            completed_mcc: _completed_mcc,
            part2_extensions,
            ..
        } = header;
        if !pending_mct.is_empty() || !pending_mcc.is_empty() {
            return Err(self.malformed_here(MalformedKind::MissingRequiredStructure));
        }
        let configuration = self.finish_tile_component_configuration(
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
        );
        let (component_coding_styles, tile_quantization, component_quantizations) =
            match configuration {
                Ok(values) => values,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if error == DecodeError::AllocationFailed {
                            crate::specs::part1_cold_tile_part_refused(cold_input, cold_raw, header_reader, error);
                        }
                    }
                    return Err(error);
                }
            };
        #[cfg(verus_keep_ghost)]
        proof! { super::tile_part_native_styles_inverse(&component_coding_styles); }
        let admitted_progression = self.validate_progression_changes(
            &progression_changes,
            tile_coding_style.layers,
            &component_coding_styles,
            tile_part.start,
        );
        #[cfg(verus_keep_ghost)]
        proof! { if let Err(error) = admitted_progression {
            if error == DecodeError::AllocationFailed {
                crate::specs::part1_cold_tile_bitmap_error(cold_input, cold_raw, header_reader, error);
            }
        }}
        admitted_progression?;
        #[cfg(verus_keep_ghost)]
        proof! { assert(crate::specs::part1_tile_graph_prepare(cold_input, cold_raw, header_reader).is_ok()); }
        let multiple_component_transform = match self
            .resolve_multiple_component_transform(&mct_parameters, super::ResolvedCopyRole::Tile)
        {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::specs::part1_cold_tile_graph_error(cold_input, cold_raw, header_reader, error); }
                return Err(error);
            }
        };

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
                    part2_extensions: {
                        let copied = part2_extensions.try_duplicate_with(true);
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            if let Err(error) = copied {
                                crate::specs::part1_cold_tile_payload_error(cold_input, cold_raw, parser_view(self), error);
                            }
                        }
                        copied?
                    },
                    packet_lengths,
                    packed_packet_headers,
                    has_progression_marker: poc_seen,
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
                part2_extensions: {
                    let copied = part2_extensions.try_duplicate_with(true);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if let Err(error) = copied {
                            crate::specs::part1_cold_tile_payload_error(cold_input, cold_raw, parser_view(self), error);
                        }
                    }
                    copied?
                },
                packet_lengths,
                packed_packet_headers,
                has_progression_marker: poc_seen,
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
