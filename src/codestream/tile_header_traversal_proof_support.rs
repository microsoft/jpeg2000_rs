#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) closed spec fn tile_header_accumulator_view(raw: &tile_header_traversal::TileHeaderAccumulator<'_>)
        -> crate::specs::Part1TileHeaderAccumulator
    {
        crate::specs::Part1TileHeaderAccumulator {
            tile_header_start: raw.tile_header_start, tile_header_end: raw.tile_header_end,
            tile_coding_style: parsed_coding_style_view(raw.tile_coding_style), tile_cod_seen: raw.tile_cod_seen,
            qcd_segment: match raw.qcd_segment { None => None, Some(segment) => Some(segment_view(segment)) },
            coc_segments: segment_slots_view(raw.coc_segments@), qcc_segments: segment_slots_view(raw.qcc_segments@),
            tile_roi_shifts: roi_shifts_view(&raw.tile_roi_shifts), roi_seen: raw.roi_seen@, tile_rgn_seen: raw.tile_rgn_seen,
            has_functional_header_marker: raw.has_functional_header_marker,
            plt_seen: raw.plt_seen, next_plt_index: raw.next_plt_index, plt_packet_count: raw.plt_packet_count,
            plt_encoded_bytes: raw.plt_encoded_bytes, plt_payload_bytes: raw.plt_payload_bytes,
            ppt_bytes: raw.ppt_bytes@, next_ppt_index: raw.next_ppt_index, ppt_fragments: raw.ppt_fragments,
            progression_changes: progression_changes_view(&raw.progression_changes), poc_seen: raw.poc_seen,
            mct_parameters: mct_parameters_view(&raw.mct_parameters), tile_mco_seen: raw.tile_mco_seen,
            pending_mct: mct_pending_view(raw.pending_mct@), completed_mct: raw.completed_mct@,
            pending_mcc: mcc_pending_view(raw.pending_mcc@), completed_mcc: raw.completed_mcc@,
            part2_extensions: owned_extensions_view(&raw.part2_extensions),
        }
    }

    closed spec fn tile_header_read_outcome(
        result: Result<tile_header_traversal::TileHeaderAccumulator<'_>, DecodeError>,
    ) -> Result<crate::specs::Part1TileHeaderAccumulator, DecodeError> {
        match result { Err(error) => Err(error), Ok(raw) => Ok(tile_header_accumulator_view(&raw)) }
    }
}
