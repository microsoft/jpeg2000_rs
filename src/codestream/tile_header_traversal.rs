//! Actual raw tile-header initialization and traversal through SOD.

use super::mct_resolution::{replace_mct_array, replace_mct_record};
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(super) struct TileHeaderAccumulator<'a> {
    pub(super) tile_header_start: usize,
    pub(super) tile_header_end: usize,
    pub(super) tile_coding_style: CodingStyle,
    pub(super) tile_cod_seen: bool,
    pub(super) qcd_segment: Option<Segment<'a>>,
    pub(super) coc_segments: [Option<Segment<'a>>; MAX_COMPONENTS],
    pub(super) qcc_segments: [Option<Segment<'a>>; MAX_COMPONENTS],
    pub(super) tile_roi_shifts: RoiShifts,
    pub(super) roi_seen: [bool; MAX_COMPONENTS],
    pub(super) tile_rgn_seen: bool,
    pub(super) has_functional_header_marker: bool,
    pub(super) plt_seen: bool,
    pub(super) next_plt_index: u16,
    pub(super) plt_packet_count: u64,
    pub(super) plt_encoded_bytes: u64,
    pub(super) plt_payload_bytes: u64,
    pub(super) ppt_bytes: Vec<u8>,
    pub(super) next_ppt_index: u16,
    pub(super) ppt_fragments: u16,
    pub(super) progression_changes: ProgressionChanges,
    pub(super) poc_seen: bool,
    pub(super) mct_parameters: MctParameters,
    pub(super) tile_mco_seen: bool,
    pub(super) pending_mct: Vec<MctFragment>,
    pub(super) completed_mct: Vec<u8>,
    pub(super) pending_mcc: Vec<MccFragment>,
    pub(super) completed_mcc: Vec<u8>,
    pub(super) part2_extensions: Part2Extensions,
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures tile_header_accumulator_view(&result) == crate::specs::part1_tile_header_initial(
        start, parsed_coding_style_view(style), roi_shifts_view(&roi),
        progression_changes_view(&progression), mct_parameters_view(&mct),
        owned_extensions_view(&extensions)),
))]
pub(super) fn new_tile_header_accumulator<'a>(
    start: usize,
    style: CodingStyle,
    roi: RoiShifts,
    progression: ProgressionChanges,
    mct: MctParameters,
    extensions: Part2Extensions,
) -> TileHeaderAccumulator<'a> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(tile_header_accumulator_view);
        reveal(crate::specs::part1_tile_header_initial);
        reveal(segment_slots_view);
        reveal(mct_pending_view);
        reveal(mcc_pending_view);
    }
    let raw = TileHeaderAccumulator {
        tile_header_start: start,
        tile_header_end: start,
        tile_coding_style: style,
        tile_cod_seen: false,
        qcd_segment: None,
        coc_segments: [None; MAX_COMPONENTS],
        qcc_segments: [None; MAX_COMPONENTS],
        tile_roi_shifts: roi,
        roi_seen: [false; MAX_COMPONENTS],
        tile_rgn_seen: false,
        has_functional_header_marker: false,
        plt_seen: false,
        next_plt_index: 0,
        plt_packet_count: 0,
        plt_encoded_bytes: 0,
        plt_payload_bytes: 0,
        ppt_bytes: Vec::new(),
        next_ppt_index: 0,
        ppt_fragments: 0,
        progression_changes: progression,
        poc_seen: false,
        mct_parameters: mct,
        tile_mco_seen: false,
        pending_mct: Vec::new(),
        completed_mct: Vec::new(),
        pending_mcc: Vec::new(),
        completed_mcc: Vec::new(),
        part2_extensions: extensions,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let actual = tile_header_accumulator_view(&raw);
        let expected = crate::specs::part1_tile_header_initial(start, parsed_coding_style_view(style),
            roi_shifts_view(&roi), progression_changes_view(&progression), mct_parameters_view(&mct),
            owned_extensions_view(&extensions));
        assert(actual.coc_segments =~= expected.coc_segments);
        assert(actual.qcc_segments =~= expected.qcc_segments);
        assert(actual.roi_seen =~= expected.roi_seen);
        assert(actual.pending_mct =~= expected.pending_mct);
        assert(actual.pending_mcc =~= expected.pending_mcc);
    }
    raw
}

impl<'a> Parser<'a> {
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), tile_header_accumulator_view(final(raw)))
            == crate::specs::part1_tile_header_dispatch(
                parser_view(old(self)), tile_header_accumulator_view(old(raw)),
                segment_view(segment), components, tile_part_index,
                packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers)),
    ))]
    pub(super) fn dispatch_tile_header_segment(
        &mut self,
        raw: &mut TileHeaderAccumulator<'a>,
        segment: Segment<'a>,
        components: u16,
        tile_part_index: u8,
        main_lengths: PacketLengths<'a>,
        main_headers: PackedPacketHeaders<'a>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_header_dispatch);
            reveal(tile_header_accumulator_view);
            reveal(segment_view);
        }
        if segment.marker != COM && segment.marker != PLT {
            raw.has_functional_header_marker = true;
        }
        self.apply_tile_header_segment(
            raw,
            segment,
            components,
            tile_part_index,
            main_lengths,
            main_headers,
        )
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), tile_header_accumulator_view(final(raw)))
            == crate::specs::part1_tile_header_payload(
                parser_view(old(self)), tile_header_accumulator_view(old(raw)),
                segment_view(segment), components, tile_part_index,
                packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers)),
    ))]
    pub(super) fn apply_tile_header_segment(
        &mut self,
        raw: &mut TileHeaderAccumulator<'a>,
        segment: Segment<'a>,
        components: u16,
        tile_part_index: u8,
        main_lengths: PacketLengths<'a>,
        main_headers: PackedPacketHeaders<'a>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_header_payload);
            reveal(tile_header_accumulator_view);
            reveal(parser_view);
            reveal(segment_view);
            reveal(parsed_coding_style_outcome);
            reveal(parsed_progression_outcome);
            reveal(progression_changes_view);
            reveal(roi_shifts_view);
            reveal(crate::specs::part1_codestream_malformed);
            reveal(crate::specs::part1_codestream_offset);
        }
        match segment.marker {
            COD => {
                if raw.tile_cod_seen {
                    return Err(DecodeError::malformed(
                        self.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                raw.tile_cod_seen = true;
                raw.tile_coding_style = self.parse_cod(segment)?;
            }
            COC => {
                self.record_component_segment(
                    segment,
                    components,
                    MalformedKind::InvalidCodingStyle,
                    &mut raw.coc_segments,
                )?;
            }
            QCD => {
                if raw.qcd_segment.is_some() {
                    return Err(DecodeError::malformed(
                        self.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                raw.qcd_segment = Some(segment);
            }
            QCC => {
                self.record_component_segment(
                    segment,
                    components,
                    MalformedKind::InvalidQuantization,
                    &mut raw.qcc_segments,
                )?;
            }
            RGN => {
                let (component, shift) = self.parse_rgn(segment, components)?;
                let index = usize::from(component);
                if index >= raw.roi_seen.len() || raw.roi_seen[index] {
                    return Err(DecodeError::malformed(
                        self.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                raw.roi_seen[index] = true;
                raw.tile_rgn_seen = true;
                raw.tile_roi_shifts.set(component, shift)?;
            }
            MCT | MCC | MCO => self.apply_tile_header_mct_segment(raw, segment, components)?,
            PLT | PPT => {
                self.apply_tile_header_packet_segment(raw, segment, main_lengths, main_headers)?
            }
            POC => {
                if raw.poc_seen || tile_part_index != 0 {
                    return Err(DecodeError::malformed(
                        self.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                raw.poc_seen = true;
                raw.progression_changes = self.parse_poc(segment, components)?;
            }
            DFS | ADS | NLT | ATK => {
                self.apply_tile_header_extension_segment(raw, segment, components)?
            }
            CBD => {
                return Err(DecodeError::malformed(
                    self.offset(segment.offset),
                    MalformedKind::InvalidMarkerOrder,
                ));
            }
            0xff64 => {}
            _ => {
                return Err(DecodeError::malformed(
                    self.offset(segment.offset),
                    MalformedKind::InvalidMarker,
                ));
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), tile_header_accumulator_view(final(raw)))
            == crate::specs::part1_tile_header_extension_payload(
                parser_view(old(self)), tile_header_accumulator_view(old(raw)), segment_view(segment), components),
    ))]
    pub(super) fn apply_tile_header_extension_segment(
        &mut self,
        raw: &mut TileHeaderAccumulator<'a>,
        segment: Segment<'a>,
        components: u16,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_header_extension_payload);
            reveal(tile_header_accumulator_view);
            reveal(segment_view);
        }
        match segment.marker {
            DFS => {
                self.parse_dfs(segment, &mut raw.part2_extensions)?;
            }
            ADS => {
                self.parse_ads(segment, &mut raw.part2_extensions)?;
            }
            NLT => {
                if raw.part2_extensions.nonlinear_local_count.is_none() {
                    raw.part2_extensions.nonlinear_local_count = Some(0);
                }
                self.parse_nlt(segment, components, &mut raw.part2_extensions)?;
            }
            ATK => {
                self.parse_atk(segment, &mut raw.part2_extensions)?;
            }
            _ => {
                return Err(DecodeError::malformed(
                    self.offset(segment.offset),
                    MalformedKind::InvalidMarker,
                ));
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), tile_header_accumulator_view(final(raw)))
            == crate::specs::part1_tile_header_packet_payload(
                parser_view(old(self)), tile_header_accumulator_view(old(raw)), segment_view(segment),
                packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers)),
    ))]
    pub(super) fn apply_tile_header_packet_segment(
        &mut self,
        raw: &mut TileHeaderAccumulator<'a>,
        segment: Segment<'a>,
        main_lengths: PacketLengths<'a>,
        main_headers: PackedPacketHeaders<'a>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_header_packet_payload);
            reveal(tile_header_accumulator_view);
            reveal(segment_view);
        }
        match segment.marker {
            PLT => self.parse_plt(
                segment,
                main_lengths,
                &mut raw.next_plt_index,
                &mut raw.plt_seen,
                &mut raw.plt_packet_count,
                &mut raw.plt_encoded_bytes,
                &mut raw.plt_payload_bytes,
            )?,
            PPT => self.parse_ppt(
                segment,
                main_headers,
                &mut raw.next_ppt_index,
                &mut raw.ppt_fragments,
                &mut raw.ppt_bytes,
            )?,
            _ => {
                return Err(DecodeError::malformed(
                    self.offset(segment.offset),
                    MalformedKind::InvalidMarker,
                ));
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), tile_header_accumulator_view(final(raw)))
            == crate::specs::part1_tile_header_mct_payload(
                parser_view(old(self)), tile_header_accumulator_view(old(raw)), segment_view(segment), components),
    ))]
    pub(super) fn apply_tile_header_mct_segment(
        &mut self,
        raw: &mut TileHeaderAccumulator<'a>,
        segment: Segment<'a>,
        components: u16,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_tile_header_mct_payload);
            reveal(tile_header_accumulator_view);
            reveal(parser_view);
            reveal(segment_view);
            reveal(mct_parameters_view);
            reveal(mct_fragment_outcome);
            reveal(mcc_fragment_outcome);
            reveal(mct_arrays_view);
            reveal(mct_records_view);
            reveal(mct_array_view);
            reveal(mct_record_view);
            reveal(segment_tail_outcome);
        }
        match segment.marker {
            MCT => {
                if let Some(array) = self.consume_mct_fragment(
                    segment,
                    &mut raw.pending_mct,
                    &mut raw.completed_mct,
                )? {
                    replace_mct_array(&mut raw.mct_parameters.arrays, array);
                }
            }
            MCC => {
                if let Some(record) = self.consume_mcc_fragment(
                    segment,
                    components,
                    &mut raw.pending_mcc,
                    &mut raw.completed_mcc,
                )? {
                    replace_mct_record(&mut raw.mct_parameters.records, record);
                }
            }
            MCO => {
                if raw.tile_mco_seen {
                    return Err(DecodeError::malformed(
                        self.offset(segment.offset),
                        MalformedKind::InvalidMarkerOrder,
                    ));
                }
                raw.tile_mco_seen = true;
                raw.mct_parameters.order = self.parse_mco(segment)?;
            }
            _ => {
                return Err(DecodeError::malformed(
                    self.offset(segment.offset),
                    MalformedKind::InvalidMarker,
                ));
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), tile_header_accumulator_view(final(raw)))
            == crate::specs::part1_traverse_tile_header(
                parser_view(old(self)), tile_header_accumulator_view(old(raw)),
                components, tile_part_index, packet_lengths_view(&main_lengths),
                packed_packet_headers_view(&main_headers)),
    ))]
    pub(super) fn traverse_tile_header(
        &mut self,
        raw: &mut TileHeaderAccumulator<'a>,
        components: u16,
        tile_part_index: u8,
        main_lengths: PacketLengths<'a>,
        main_headers: PackedPacketHeaders<'a>,
    ) -> Result<(), DecodeError> {
        let input_length = self.input.len();
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = crate::specs::part1_tile_header_traversal(
                parser_view(self), tile_header_accumulator_view(raw), components, tile_part_index,
                packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers), input_length);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_traverse_tile_header); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                initial == crate::specs::part1_traverse_tile_header(
                    parser_view(old(self)), tile_header_accumulator_view(old(raw)), components,
                    tile_part_index, packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers)),
                initial == crate::specs::part1_tile_header_traversal(
                    parser_view(self), tile_header_accumulator_view(raw), components, tile_part_index,
                    packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers), input_length),
            decreases input_length as int - self.position as int,
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_tile_header_traversal, 1);
                reveal(tile_header_accumulator_view);
                reveal(parser_view);
                reveal(main_header_segment_outcome);
                reveal(crate::specs::part1_parser_progress);
                reveal(crate::specs::part1_codestream_malformed);
            }
            let previous_position = self.position;
            match self.read_tile_header_segment()? {
                None => {
                    raw.tile_header_end = previous_position;
                    return Ok(());
                }
                Some(segment) => {
                    self.dispatch_tile_header_segment(
                        raw,
                        segment,
                        components,
                        tile_part_index,
                        main_lengths,
                        main_headers,
                    )?;
                }
            }
            if !crate::refinement::parser_progress(previous_position, self.position, input_length) {
                return Err(self.malformed_here(MalformedKind::InvalidTilePart));
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (tile_header_read_outcome(result), parser_view(final(self)))
            == crate::specs::part1_read_tile_header(parser_view(old(self)),
                parsed_coding_style_view(style), roi_shifts_view(&roi),
                progression_changes_view(&progression), mct_parameters_view(&mct),
                owned_extensions_view(&extensions), components, tile_part_index,
                packet_lengths_view(&main_lengths), packed_packet_headers_view(&main_headers)),
    ))]
    pub(super) fn read_tile_header(
        &mut self,
        style: CodingStyle,
        roi: RoiShifts,
        progression: ProgressionChanges,
        mct: MctParameters,
        extensions: Part2Extensions,
        components: u16,
        tile_part_index: u8,
        main_lengths: PacketLengths<'a>,
        main_headers: PackedPacketHeaders<'a>,
    ) -> Result<TileHeaderAccumulator<'a>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(tile_header_read_outcome);
            reveal(crate::specs::part1_read_tile_header);
        }
        let mut raw =
            new_tile_header_accumulator(self.position, style, roi, progression, mct, extensions);
        self.traverse_tile_header(
            &mut raw,
            components,
            tile_part_index,
            main_lengths,
            main_headers,
        )?;
        Ok(raw)
    }
}
