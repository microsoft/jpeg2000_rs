//! Raw main-header traversal and ordered finalization of the actual layout reader.

use super::*;

verus! {

pub(crate) struct Part1MainHeaderAccumulator {
    pub image_size: Part1ParsedImageSize,
    pub r_siz: u16,
    pub start: usize,
    pub segments: u64,
    pub coding_style: Option<Part1ParsedCodingStyle>,
    pub qcd: Option<Part1CodestreamSegment>,
    pub coc: Seq<Option<Part1CodestreamSegment>>,
    pub qcc: Seq<Option<Part1CodestreamSegment>>,
    pub roi: Seq<u8>,
    pub roi_seen: Seq<bool>,
    pub plm: Seq<Part1PacketLengths>,
    pub next_plm: u16,
    pub plm_seen: bool,
    pub ppm: Seq<u8>,
    pub next_ppm: u16,
    pub ppm_fragments: u16,
    pub progression: Seq<crate::codestream::ProgressionChange>,
    pub poc_seen: bool,
    pub arrays: Seq<Part2MctArray>,
    pub records: Seq<Part1MctRecord>,
    pub order: Option<Seq<u8>>,
    pub pending_mct: Seq<Part1MctFragment>,
    pub completed_mct: Seq<u8>,
    pub pending_mcc: Seq<Part1MccFragment>,
    pub completed_mcc: Seq<u8>,
    pub capabilities: Option<(u32, Seq<u16>)>,
    pub profile: Option<Seq<u16>>,
    pub corresponding_profile: Option<Seq<u16>>,
    pub extensions: Part2OwnedExtensions,
    pub next_tlm: u16,
}

pub(crate) open spec fn part1_empty_extensions() -> Part2OwnedExtensions {
    Part2OwnedExtensions {
        decompositions: Seq::empty(), arbitrary: Seq::empty(), nonlinear: Seq::empty(),
        depths: Seq::empty(), kernels: Seq::empty(), registrations: Seq::empty(),
        lengths: Seq::empty(), metadata_bytes: 0,
    }
}

pub(crate) open spec fn part1_empty_roi_shifts() -> Seq<u8> {
    Seq::new(64, |_: int| 0u8)
}

pub(crate) open spec fn part1_empty_progression_changes() -> Seq<crate::codestream::ProgressionChange> {
    Seq::empty()
}

pub(crate) open spec fn part1_main_header_initial(
    image_size: Part1ParsedImageSize, r_siz: u16, start: usize,
) -> Part1MainHeaderAccumulator {
    Part1MainHeaderAccumulator {
        image_size, r_siz, start, segments: 1, coding_style: None, qcd: None,
        coc: Seq::new(64, |_: int| None), qcc: Seq::new(64, |_: int| None),
        roi: part1_empty_roi_shifts(), roi_seen: Seq::new(64, |_: int| false),
        plm: Seq::empty(), next_plm: 0, plm_seen: false,
        ppm: Seq::empty(), next_ppm: 0, ppm_fragments: 0,
        progression: part1_empty_progression_changes(), poc_seen: false,
        arrays: Seq::empty(), records: Seq::empty(), order: None,
        pending_mct: Seq::empty(), completed_mct: Seq::empty(),
        pending_mcc: Seq::empty(), completed_mcc: Seq::empty(),
        capabilities: None, profile: None, corresponding_profile: None,
        extensions: part1_empty_extensions(), next_tlm: 0,
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_header_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator) {
    let order_error = part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder);
    let components = raw.image_size.components;
    match segment.marker {
        0xff50 => if raw.capabilities.is_some() { (Err(order_error), reader, raw) } else {
            match part1_parse_cap(segment) {
                Err(error) => (Err(error), reader, raw),
                Ok(capabilities) => (Ok(()), reader, Part1MainHeaderAccumulator { capabilities: Some(capabilities), ..raw }),
            }
        },
        0xff56 | 0xff59 => {
            let present = if segment.marker == 0xff56 { raw.profile.is_some() } else { raw.corresponding_profile.is_some() };
            if present { (Err(order_error), reader, raw) } else {
                match part1_parse_profile_number(segment) {
                    Err(error) => (Err(error), reader, raw),
                    Ok(words) => (Ok(()), reader, if segment.marker == 0xff56 {
                        Part1MainHeaderAccumulator { profile: Some(words), ..raw }
                    } else { Part1MainHeaderAccumulator { corresponding_profile: Some(words), ..raw } }),
                }
            }
        },
        0xff52 => if raw.coding_style.is_some() { (Err(order_error), reader, raw) } else {
            match part1_parse_cod(segment.offset, segment.payload, reader.limits) {
                Err(error) => (Err(error), reader, raw),
                Ok(style) => (Ok(()), reader, Part1MainHeaderAccumulator { coding_style: Some(style), ..raw }),
            }
        },
        0xff53 | 0xff5d => {
            let coding = segment.marker == 0xff53;
            let result = part1_record_component_segment(reader, segment, components,
                if coding { crate::MalformedKind::InvalidCodingStyle } else { crate::MalformedKind::InvalidQuantization },
                if coding { raw.coc } else { raw.qcc });
            (result.0, result.2, if coding { Part1MainHeaderAccumulator { coc: result.1, ..raw } }
                else { Part1MainHeaderAccumulator { qcc: result.1, ..raw } })
        },
        0xff5c => if raw.qcd.is_some() { (Err(order_error), reader, raw) }
            else { (Ok(()), reader, Part1MainHeaderAccumulator { qcd: Some(segment), ..raw }) },
        0xff5e => match part1_parse_rgn(segment.offset, segment.payload, components) {
            Err(error) => (Err(error), reader, raw),
            Ok((component, shift)) => if component as nat >= raw.roi_seen.len() || raw.roi_seen[component as int] {
                (Err(order_error), reader, raw)
            } else {
                let result = part1_set_roi_shift(raw.roi, component, shift);
                (result.0, reader, Part1MainHeaderAccumulator {
                    roi_seen: raw.roi_seen.update(component as int, true), roi: result.1, ..raw
                })
            },
        },
        0xff57 => {
            let result = part1_parse_plm(reader, segment, raw.next_plm, raw.plm);
            (result.0, result.1, Part1MainHeaderAccumulator {
                plm_seen: true, next_plm: result.2, plm: result.3, ..raw
            })
        },
        0xff60 => {
            let result = part1_parse_packed_fragment(reader, segment, 0xff60,
                raw.next_ppm, raw.ppm_fragments, raw.ppm);
            (result.0, result.1, Part1MainHeaderAccumulator {
                next_ppm: result.2, ppm_fragments: result.3, ppm: result.4, ..raw
            })
        },
        0xff5f => if raw.poc_seen { (Err(order_error), reader, raw) } else {
            let changed = Part1MainHeaderAccumulator { poc_seen: true, ..raw };
            match part1_parse_poc(segment, components) {
                Err(error) => (Err(error), reader, changed),
                Ok(progression) => (Ok(()), reader, Part1MainHeaderAccumulator { progression, ..changed }),
            }
        },
        0xff74 | 0xff75 | 0xff77 => part1_main_header_mct_payload(reader, raw, segment),
        0xff55 | 0xff63 | 0xff72 | 0xff73 | 0xff76 | 0xff78 | 0xff79 =>
            part1_main_header_extension_payload(reader, raw, segment),
        0xff64 => (Ok(()), reader, raw),
        _ => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), reader, raw),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_header_mct_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator) {
    match segment.marker {
        0xff74 => {
            let result = part1_consume_mct_fragment(segment, reader.limits, raw.pending_mct, raw.completed_mct);
            let changed = Part1MainHeaderAccumulator { pending_mct: result.1, completed_mct: result.2, ..raw };
            match result.0 {
                Err(error) => (Err(error), reader, changed),
                Ok(None) => (Ok(()), reader, changed),
                Ok(Some(array)) => {
                    let arrays = raw.arrays.push(array);
                    (part1_mct_registry_unique_array(arrays, segment.offset), reader,
                        Part1MainHeaderAccumulator { arrays, ..changed })
                },
            }
        },
        0xff75 => {
            let result = part1_consume_mcc_fragment(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc);
            let changed = Part1MainHeaderAccumulator { pending_mcc: result.1, completed_mcc: result.2, ..raw };
            match result.0 {
                Err(error) => (Err(error), reader, changed),
                Ok(None) => (Ok(()), reader, changed),
                Ok(Some(record)) => {
                    let records = raw.records.push(record);
                    (part1_mct_registry_unique_record(records, segment.offset), reader,
                        Part1MainHeaderAccumulator { records, ..changed })
                },
            }
        },
        0xff77 => if raw.order.is_some() {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), reader, raw)
        } else {
            match part1_parse_mco(segment) {
                Err(error) => (Err(error), reader, raw),
                Ok(order) => (Ok(()), reader, Part1MainHeaderAccumulator { order: Some(order), ..raw }),
            }
        },
        _ => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), reader, raw),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_header_extension_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator) {
    let components = raw.image_size.components;
    if segment.marker == 0xff55 {
        match part2_selection_tile_count(raw.image_size.geometry) {
            Err(error) => (Err(error), reader, raw),
            Ok(count) => {
                let result = part1_parse_tlm(reader, segment, raw.next_tlm, count, raw.extensions);
                (result.0, result.1, Part1MainHeaderAccumulator { next_tlm: result.2, extensions: result.3, ..raw })
            },
        }
    } else {
        let result = match segment.marker {
            0xff63 => part1_parse_crg(reader, segment, components, raw.extensions),
            0xff72 => part1_parse_dfs(reader, segment, raw.extensions),
            0xff73 => part1_parse_ads(reader, segment, raw.extensions),
            0xff76 => part1_parse_nlt(reader, segment, components, raw.extensions),
            0xff78 => part1_parse_cbd(reader, segment, components, raw.extensions),
            0xff79 => part1_parse_atk(reader, segment, raw.extensions),
            _ => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), reader, raw.extensions),
        };
        (result.0, result.1, Part1MainHeaderAccumulator { extensions: result.2, ..raw })
    }
}

pub(crate) struct Part1MainHeader<'a> {
    pub reader: Part1CodestreamReader<'a>,
    pub raw: Part1MainHeaderAccumulator,
    pub end: usize,
    pub header: Seq<u8>,
    pub ppm_frames: Seq<(usize, usize)>,
    pub coding_style: Part1ParsedCodingStyle,
    pub quantization: Part2Quantization,
    pub styles: (u16, Seq<Part1ParsedCodingStyle>),
    pub quantizations: (u16, Seq<Part2Quantization>),
    pub mct: Part1MctParameters,
    pub transform: Option<Seq<Part2MctStage>>,
    pub tile_count: u64,
}

pub(crate) type Part1MainHeaderResult<'a> = Result<Part1MainHeader<'a>, crate::DecodeError>;

#[verifier::opaque]
pub(crate) open spec fn part1_main_header_after_components<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    frames: Seq<(usize, usize)>, header: Seq<u8>, style: Part1ParsedCodingStyle,
    quantization: Part2Quantization, styles: (u16, Seq<Part1ParsedCodingStyle>),
    quantizations: (u16, Seq<Part2Quantization>),
) -> Part1MainHeaderResult<'a> {
    let native_styles = crate::codestream::tile_part_native_styles(styles);
    match part1_validate_progression_changes(0, raw.progression, style.layers, &native_styles, reader.limits) {
        Err(error) => Err(error),
        Ok(()) => if (raw.arrays.len() != 0 || raw.records.len() != 0) && raw.order.is_none() {
            Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure))
        } else {
            let registered = part1_apply_component_registrations(raw.image_size, raw.extensions.registrations, reader.position);
            match registered.0 {
                Err(error) => Err(error),
                Ok(()) => {
                    let mct = Part1MctParameters {
                        arrays: raw.arrays, records: raw.records,
                        order: match raw.order { None => Seq::empty(), Some(order) => order },
                    };
                    match part1_mct_graph(mct) {
                        Err(error) => Err(error),
                        Ok(transform) => match part2_selection_tile_count(registered.1.geometry) {
                            Err(error) => Err(error),
                            Ok(tile_count) => Ok(Part1MainHeader {
                                reader,
                                raw: Part1MainHeaderAccumulator { image_size: registered.1, ..raw },
                                end: reader.position, header, ppm_frames: frames, coding_style: style,
                                quantization, styles, quantizations, mct, transform, tile_count,
                            }),
                        },
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_header_after_depths<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
) -> Part1MainHeaderResult<'a> {
    match part1_parse_ppm_frames(raw.ppm, raw.ppm_fragments, reader.limits) {
        Err(error) => Err(error),
        Ok(frames) => if raw.start > reader.position || reader.position > reader.input.len() {
            Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidPackedPacketHeader))
        } else {
            let header = reader.input.subrange(raw.start as int, reader.position as int);
            match raw.coding_style {
                None => Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure)),
                Some(style) => match raw.qcd {
                    None => Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure)),
                    Some(segment) => match part1_parse_qcd_payload(segment.offset, segment.payload, style) {
                        Err(error) => Err(error),
                        Ok(quantization) => match part1_finish_main_styles(raw.image_size.components, style, raw.coc, reader.limits, raw.extensions) {
                            Err(error) => Err(error),
                            Ok(styles) => match part1_finish_main_quantizations(raw.image_size.components, quantization, styles, raw.qcc) {
                                Err(error) => Err(error),
                                Ok(quantizations) => part1_main_header_after_components(reader, raw, frames, header, style, quantization, styles, quantizations),
                            },
                        },
                    },
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_finish_main_header<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
) -> Part1MainHeaderResult<'a> {
    if raw.pending_mct.len() != 0 || raw.pending_mcc.len() != 0 {
        Err(part1_codestream_malformed(reader.position, crate::MalformedKind::MissingRequiredStructure))
    } else if raw.plm.len() != 0 && super::part1_incomplete_plm_offset(raw.plm.last()).is_some() {
        Err(part1_codestream_malformed(super::part1_incomplete_plm_offset(raw.plm.last())->Some_0,
            crate::MalformedKind::InvalidMarkerLength))
    } else {
        let depths = part1_apply_component_depths(raw.image_size, raw.extensions.depths, reader.position);
        match depths.0 {
            Err(error) => Err(error),
            Ok(()) => part1_main_header_after_depths(reader, Part1MainHeaderAccumulator { image_size: depths.1, ..raw }),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_header_continuation<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, input_length: usize,
) -> Part1MainHeaderResult<'a>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    match admitted.0 {
        Err(error) => Err(error),
        Ok(None) => part1_finish_main_header(admitted.1, changed),
        Ok(Some(segment)) => {
            let step = part1_main_header_payload(admitted.1, changed, segment);
            match step.0 {
                Err(error) => Err(error),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidMarkerLength))
                } else { part1_main_header_continuation(step.1, step.2, input_length) },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_read_main_header<'a>(reader: Part1CodestreamReader<'a>) -> Part1MainHeaderResult<'a> {
    let prologue = part1_parse_layout_prologue(reader);
    match prologue.0 {
        Err(error) => Err(error),
        Ok((size, r_siz, start)) => part1_main_header_continuation(prologue.1,
            part1_main_header_initial(size, r_siz, start), prologue.1.input.len() as usize),
    }
}

pub(crate) struct Part1LayoutMainFields {
    pub image_size: Part1ParsedImageSize,
    pub coding_style: Part1ParsedCodingStyle,
    pub quantization: Part2Quantization,
    pub styles: (u16, Seq<Part1ParsedCodingStyle>),
    pub quantizations: (u16, Seq<Part2Quantization>),
    pub roi: Seq<u8>,
    pub progression: Seq<crate::codestream::ProgressionChange>,
    pub transform: Option<Seq<Part2MctStage>>,
    pub extensions: Part2OwnedExtensions,
    pub r_siz: u16,
    pub capabilities: Option<(u32, Seq<u16>)>,
    pub profile: Option<Seq<u16>>,
    pub corresponding_profile: Option<Seq<u16>>,
    pub segments: u64,
}

pub(crate) open spec fn part1_main_header_fields(main: Part1MainHeader<'_>) -> Part1LayoutMainFields {
    Part1LayoutMainFields {
        image_size: main.raw.image_size, coding_style: main.coding_style, quantization: main.quantization,
        styles: main.styles, quantizations: main.quantizations, roi: main.raw.roi,
        progression: main.raw.progression, transform: main.transform, extensions: main.raw.extensions,
        r_siz: main.raw.r_siz, capabilities: main.raw.capabilities, profile: main.raw.profile,
        corresponding_profile: main.raw.corresponding_profile, segments: main.raw.segments,
    }
}

pub(crate) open spec fn part1_main_header_layout_relation(
    main: Part1MainHeaderResult<'_>, layout: Result<Part1LayoutMainFields, crate::DecodeError>,
) -> bool {
    match main {
        Err(error) => layout == Err(error),
        Ok(header) => match layout {
            Err(_) => true,
            Ok(fields) => fields == part1_main_header_fields(header),
        },
    }
}

}
