//! Complete raw model of the executing tile-header traversal, excluding finalizers.

use super::*;

verus! {

pub(crate) open spec fn part1_set_roi_shift(shifts: Seq<u8>, component: u16, shift: u8)
    -> (Result<(), crate::DecodeError>, Seq<u8>)
{
    if component as nat >= shifts.len() {
        (Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidRegionOfInterest)), shifts)
    } else { (Ok(()), shifts.update(component as int, shift)) }
}

pub(crate) struct Part1TileHeaderAccumulator {
    pub tile_header_start: usize,
    pub tile_header_end: usize,
    pub tile_coding_style: Part1ParsedCodingStyle,
    pub tile_cod_seen: bool,
    pub qcd_segment: Option<Part1CodestreamSegment>,
    pub coc_segments: Seq<Option<Part1CodestreamSegment>>,
    pub qcc_segments: Seq<Option<Part1CodestreamSegment>>,
    pub tile_roi_shifts: Seq<u8>,
    pub roi_seen: Seq<bool>,
    pub tile_rgn_seen: bool,
    pub has_functional_header_marker: bool,
    pub plt_seen: bool,
    pub next_plt_index: u16,
    pub plt_packet_count: u64,
    pub plt_encoded_bytes: u64,
    pub plt_payload_bytes: u64,
    pub ppt_bytes: Seq<u8>,
    pub next_ppt_index: u16,
    pub ppt_fragments: u16,
    pub progression_changes: Seq<crate::codestream::ProgressionChange>,
    pub poc_seen: bool,
    pub mct_parameters: Part1MctParameters,
    pub tile_mco_seen: bool,
    pub pending_mct: Seq<Part1MctFragment>,
    pub completed_mct: Seq<u8>,
    pub pending_mcc: Seq<Part1MccFragment>,
    pub completed_mcc: Seq<u8>,
    pub part2_extensions: Part2OwnedExtensions,
}

pub(crate) open spec fn part1_tile_header_initial(
    start: usize, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions,
) -> Part1TileHeaderAccumulator {
    Part1TileHeaderAccumulator {
        tile_header_start: start, tile_header_end: start, tile_coding_style: style, tile_cod_seen: false,
        qcd_segment: None, coc_segments: Seq::new(64, |_: int| None), qcc_segments: Seq::new(64, |_: int| None),
        tile_roi_shifts: roi, roi_seen: Seq::new(64, |_: int| false), tile_rgn_seen: false,
        has_functional_header_marker: false, plt_seen: false, next_plt_index: 0,
        plt_packet_count: 0, plt_encoded_bytes: 0, plt_payload_bytes: 0,
        ppt_bytes: Seq::empty(), next_ppt_index: 0, ppt_fragments: 0,
        progression_changes: progression, poc_seen: false, mct_parameters: mct, tile_mco_seen: false,
        pending_mct: Seq::empty(), completed_mct: Seq::empty(), pending_mcc: Seq::empty(), completed_mcc: Seq::empty(),
        part2_extensions: extensions,
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_header_dispatch<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    let raw = Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58),
        ..raw
    };
    part1_tile_header_payload(reader, raw, segment, components, tile_part_index, main_lengths, main_headers)
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_header_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    let order_error = part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder);
    let marker_error = part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker);
    match segment.marker {
            0xff52 => if raw.tile_cod_seen { (Err(order_error), reader, raw) } else {
                let changed = Part1TileHeaderAccumulator { tile_cod_seen: true, ..raw };
                match part1_parse_cod(segment.offset, segment.payload, reader.limits) {
                    Err(error) => (Err(error), reader, changed),
                    Ok(style) => (Ok(()), reader, Part1TileHeaderAccumulator { tile_coding_style: style, ..changed }),
                }
            },
            0xff53 => {
                let result = part1_record_component_segment(reader, segment, components, crate::MalformedKind::InvalidCodingStyle, raw.coc_segments);
                (result.0, result.2, Part1TileHeaderAccumulator { coc_segments: result.1, ..raw })
            },
            0xff5c => if raw.qcd_segment.is_some() { (Err(order_error), reader, raw) }
                else { (Ok(()), reader, Part1TileHeaderAccumulator { qcd_segment: Some(segment), ..raw }) },
            0xff5d => {
                let result = part1_record_component_segment(reader, segment, components, crate::MalformedKind::InvalidQuantization, raw.qcc_segments);
                (result.0, result.2, Part1TileHeaderAccumulator { qcc_segments: result.1, ..raw })
            },
            0xff5e => match part1_parse_rgn(segment.offset, segment.payload, components) {
                Err(error) => (Err(error), reader, raw),
                Ok((component, shift)) => if component as nat >= raw.roi_seen.len() || raw.roi_seen[component as int] {
                    (Err(order_error), reader, raw)
                } else {
                    let changed = Part1TileHeaderAccumulator {
                        roi_seen: raw.roi_seen.update(component as int, true), tile_rgn_seen: true, ..raw
                    };
                    let result = part1_set_roi_shift(raw.tile_roi_shifts, component, shift);
                    (result.0, reader, Part1TileHeaderAccumulator { tile_roi_shifts: result.1, ..changed })
                },
            },
            0xff74 | 0xff75 | 0xff77 => part1_tile_header_mct_payload(reader, raw, segment, components),
            0xff58 | 0xff61 => part1_tile_header_packet_payload(reader, raw, segment, main_lengths, main_headers),
            0xff5f => if raw.poc_seen || tile_part_index != 0 { (Err(order_error), reader, raw) } else {
                let changed = Part1TileHeaderAccumulator { poc_seen: true, ..raw };
                match part1_parse_poc(segment, components) {
                    Err(error) => (Err(error), reader, changed),
                    Ok(progression) => (Ok(()), reader, Part1TileHeaderAccumulator { progression_changes: progression, ..changed }),
                }
            },
            0xff72 | 0xff73 | 0xff76 | 0xff79 => part1_tile_header_extension_payload(reader, raw, segment, components),
            0xff78 => (Err(order_error), reader, raw),
            0xff64 => (Ok(()), reader, raw),
            _ => (Err(marker_error), reader, raw),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_header_extension_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    match segment.marker {
            0xff72 => {
                let result = part1_parse_dfs(reader, segment, raw.part2_extensions);
                (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw })
            },
            0xff73 => {
                let result = part1_parse_ads(reader, segment, raw.part2_extensions);
                (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw })
            },
            0xff76 => {
                let result = part1_parse_nlt(reader, segment, components, raw.part2_extensions);
                (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw })
            },
            0xff79 => {
                let result = part1_parse_atk(reader, segment, raw.part2_extensions);
                (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw })
            },
            _ => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), reader, raw),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_header_packet_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    match segment.marker {
        0xff58 => {
            let result = part1_parse_plt(reader, segment, main_lengths, raw.next_plt_index,
                raw.plt_seen, raw.plt_packet_count, raw.plt_encoded_bytes, raw.plt_payload_bytes);
            (result.0, result.1, Part1TileHeaderAccumulator {
                next_plt_index: result.2, plt_seen: result.3, plt_packet_count: result.4,
                plt_encoded_bytes: result.5, plt_payload_bytes: result.6, ..raw
            })
        },
        0xff61 => {
            let result = part1_parse_ppt(reader, segment, main_headers, raw.next_ppt_index, raw.ppt_fragments, raw.ppt_bytes);
            (result.0, result.1, Part1TileHeaderAccumulator {
                next_ppt_index: result.2, ppt_fragments: result.3, ppt_bytes: result.4, ..raw
            })
        },
        _ => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), reader, raw),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_header_mct_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    let order_error = part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder);
    let marker_error = part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker);
    match segment.marker {
            0xff74 => {
                let result = part1_consume_mct_fragment(segment, reader.limits, raw.pending_mct, raw.completed_mct);
                let changed = Part1TileHeaderAccumulator { pending_mct: result.1, completed_mct: result.2, ..raw };
                match result.0 {
                    Err(error) => (Err(error), reader, changed),
                    Ok(None) => (Ok(()), reader, changed),
                    Ok(Some(array)) => {
                        let replaced = part1_mct_registry_replace_array(raw.mct_parameters.arrays, array);
                        (Ok(()), reader, Part1TileHeaderAccumulator {
                            mct_parameters: Part1MctParameters { arrays: replaced.1, ..raw.mct_parameters }, ..changed
                        })
                    },
                }
            },
            0xff75 => {
                let result = part1_consume_mcc_fragment(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc);
                let changed = Part1TileHeaderAccumulator { pending_mcc: result.1, completed_mcc: result.2, ..raw };
                match result.0 {
                    Err(error) => (Err(error), reader, changed),
                    Ok(None) => (Ok(()), reader, changed),
                    Ok(Some(record)) => {
                        let replaced = part1_mct_registry_replace_record(raw.mct_parameters.records, record);
                        (Ok(()), reader, Part1TileHeaderAccumulator {
                            mct_parameters: Part1MctParameters { records: replaced.1, ..raw.mct_parameters }, ..changed
                        })
                    },
                }
            },
            0xff77 => if raw.tile_mco_seen { (Err(order_error), reader, raw) } else {
                let changed = Part1TileHeaderAccumulator { tile_mco_seen: true, ..raw };
                match part1_parse_mco(segment) {
                    Err(error) => (Err(error), reader, changed),
                    Ok(order) => (Ok(()), reader, Part1TileHeaderAccumulator {
                        mct_parameters: Part1MctParameters { order, ..raw.mct_parameters }, ..changed
                    }),
                }
            },
            _ => (Err(marker_error), reader, raw),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_header_traversal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    components: u16, tile_part_index: u8, main_lengths: Part1PacketLengths,
    main_headers: Part1PackedHeaders, input_length: usize,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator)
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_tile_header_segment(reader);
    match admitted.0 {
        Err(error) => (Err(error), admitted.1, raw),
        Ok(None) => (Ok(()), admitted.1,
            Part1TileHeaderAccumulator { tile_header_end: reader.position, ..raw }),
        Ok(Some(segment)) => {
            let step = part1_tile_header_dispatch(admitted.1, raw, segment, components, tile_part_index, main_lengths, main_headers);
            match step.0 {
                Err(error) => (Err(error), step.1, step.2),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    (Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidTilePart)), step.1, step.2)
                } else {
                    part1_tile_header_traversal(step.1, step.2, components, tile_part_index, main_lengths, main_headers, input_length)
                },
            }
        },
    }
}

pub(crate) open spec fn part1_traverse_tile_header<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    components: u16, tile_part_index: u8, main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    part1_tile_header_traversal(reader, raw, components, tile_part_index, main_lengths, main_headers, reader.input.len() as usize)
}

pub(crate) open spec fn part1_read_tile_header<'a>(
    reader: Part1CodestreamReader<'a>, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16, tile_part_index: u8,
    main_lengths: Part1PacketLengths, main_headers: Part1PackedHeaders,
) -> (Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>) {
    let result = part1_traverse_tile_header(reader,
        part1_tile_header_initial(reader.position, style, roi, progression, mct, extensions),
        components, tile_part_index, main_lengths, main_headers);
    (match result.0 { Err(error) => Err(error), Ok(()) => Ok(result.2) }, result.1)
}

}
