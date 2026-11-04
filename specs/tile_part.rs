//! Complete source-derived composition of the sole actual tile-part reader.

use super::*;

verus! {

pub(crate) struct Part1TilePartPayload {
    pub tile_index: u16,
    pub tile_part_index: u8,
    pub tile_part_count: u8,
    pub coding_style: Part1ParsedCodingStyle,
    pub quantization: Part2Quantization,
    pub component_coding_styles: (u16, Seq<Part1ParsedCodingStyle>),
    pub component_quantizations: (u16, Seq<Part2Quantization>),
    pub roi_shifts: Seq<u8>,
    pub progression_changes: Seq<crate::codestream::ProgressionChange>,
    pub multiple_component_transform: Option<Seq<Part2MctStage>>,
    pub part2_extensions: Part2OwnedExtensions,
    pub packet_lengths: Part1PacketLengths,
    pub packed_packet_headers: Part1PackedHeaders,
    pub has_functional_header_marker: bool,
    pub has_roi_marker: bool,
    pub data: Seq<u8>,
}

pub(crate) type Part1TilePartResult =
    Result<(Part1TilePartPayload, Part1MctParameters, Part2OwnedExtensions), crate::DecodeError>;

#[verifier::opaque]
pub(crate) open spec fn part1_tile_part_after_window<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    tile: (usize, u32, u16, u8, u8),
    configuration: ((u16, Seq<Part1ParsedCodingStyle>), Part2Quantization, (u16, Seq<Part2Quantization>)),
    transform: Option<Seq<Part2MctStage>>, end: usize, data: Seq<u8>,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Part1TilePartResult, Part1CodestreamReader<'a>) {
    let packed_length = if !matches!(main_headers.source, Part1PackedHeaderSource::None) {
        main_headers.length
    } else { raw.ppt_bytes.len() as usize };
    match part1_finish_packet_lengths(reader.input, raw.tile_header_start, raw.tile_header_end,
        main_lengths, raw.plt_seen, raw.plt_packet_count, raw.plt_encoded_bytes,
        raw.plt_payload_bytes, data.len() as usize, packed_length, tile.0) {
        Err(error) => (Err(error), reader),
        Ok(lengths) => match part1_finish_packed_packet_headers(reader.input,
            raw.tile_header_start, raw.tile_header_end, main_headers,
            raw.ppt_fragments, raw.ppt_bytes.len() as usize, tile.0) {
            Err(error) => (Err(error), reader),
            Ok(headers) => {
                let committed = if tile.1 == 0 { reader } else { part1_codestream_position(reader, end) };
                (Ok((Part1TilePartPayload {
                    tile_index: tile.2, tile_part_index: tile.3, tile_part_count: tile.4,
                    coding_style: raw.tile_coding_style, quantization: configuration.1,
                    component_coding_styles: configuration.0, component_quantizations: configuration.2,
                    roi_shifts: raw.tile_roi_shifts, progression_changes: raw.progression_changes,
                    multiple_component_transform: transform, part2_extensions: raw.part2_extensions,
                    packet_lengths: lengths, packed_packet_headers: headers,
                    has_functional_header_marker: raw.has_functional_header_marker,
                    has_roi_marker: raw.tile_rgn_seen, data,
                }, raw.mct_parameters, raw.part2_extensions)), committed)
            },
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_part_after_configuration<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    tile: (usize, u32, u16, u8, u8),
    configuration: ((u16, Seq<Part1ParsedCodingStyle>), Part2Quantization, (u16, Seq<Part2Quantization>)),
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Part1TilePartResult, Part1CodestreamReader<'a>) {
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    match part1_validate_progression_changes(tile.0, raw.progression_changes,
        raw.tile_coding_style.layers, &styles, reader.limits) {
        Err(error) => (Err(error), reader),
        Ok(()) => match part1_mct_graph(raw.mct_parameters) {
            Err(error) => (Err(error), reader),
            Ok(transform) => {
                let window = part1_tile_data_window(reader, reader.position, tile.0, tile.1);
                match window.0 {
                    Err(error) => (Err(error), window.1),
                    Ok((end, data)) => part1_tile_part_after_window(window.1, raw, tile,
                        configuration, transform, end, data, main_lengths, main_headers),
                }
            },
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_finish_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    tile: (usize, u32, u16, u8, u8), default_quantization: Part2Quantization,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>),
    inherited_quantizations: (u16, Seq<Part2Quantization>), components: u16,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Part1TilePartResult, Part1CodestreamReader<'a>) {
    if raw.pending_mct.len() != 0 || raw.pending_mcc.len() != 0 {
        (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::MissingRequiredStructure)), reader)
    } else {
        match part1_finish_tile_components(components, raw.tile_coding_style, raw.tile_cod_seen,
            raw.coc_segments, raw.qcd_segment, default_quantization, raw.qcc_segments,
            inherited_styles, inherited_quantizations, raw.part2_extensions, reader.limits) {
            Err(error) => (Err(error), reader),
            Ok(configuration) => part1_tile_part_after_configuration(
                reader, raw, tile, configuration, main_lengths, main_headers),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_read_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, tile: (usize, u32, u16, u8, u8),
    defaults: (Part1ParsedCodingStyle, Part2Quantization),
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>),
    inherited_quantizations: (u16, Seq<Part2Quantization>), roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Part1TilePartResult, Part1CodestreamReader<'a>) {
    let header = part1_read_tile_header(reader, defaults.0, roi, progression,
        mct, extensions, components, tile.3, main_lengths, main_headers);
    match header.0 {
        Err(error) => (Err(error), header.1),
        Ok(raw) => part1_finish_tile_part(header.1, raw, tile, defaults.1,
            inherited_styles, inherited_quantizations, components, main_lengths, main_headers),
    }
}

}
