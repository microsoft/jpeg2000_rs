use super::{
    Part1CodestreamReader, part1_codestream_find_eoc, part1_codestream_malformed,
    part1_codestream_position,
};
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn part1_tile_data_window<'a>(
    state: Part1CodestreamReader<'a>, data_start: usize, start: usize, length: u32,
) -> (Result<(usize, Seq<u8>), crate::DecodeError>, Part1CodestreamReader<'a>)
{
    if length == 0 {
        let searched = part1_codestream_find_eoc(state);
        match searched.0 {
            Err(error) => (Err(error), searched.1),
            Ok(end) => {
                let committed = part1_codestream_position(searched.1, end);
                if data_start > end || end > committed.input.len() {
                    (Err(part1_codestream_malformed(end, crate::MalformedKind::InvalidTilePart)), committed)
                } else {
                    (Ok((end, committed.input.subrange(data_start as int, end as int))), committed)
                }
            },
        }
    } else if length as int > usize::MAX {
        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidTilePart)), state)
    } else if start as int + length as int > usize::MAX {
        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let end = (start + length as usize) as usize;
        if end < state.position || end > state.input.len() {
            (Err(part1_codestream_malformed(start, crate::MalformedKind::InvalidTilePart)), state)
        } else if data_start > end || end > state.input.len() {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidTilePart)), state)
        } else {
            (Ok((end, state.input.subrange(data_start as int, end as int))), state)
        }
    }
}

pub enum Part1PackedHeaderSource {
    None,
    MarkerSegments { header: Seq<u8>, marker: u16, logical_start: usize },
}

pub struct Part1PackedHeaders {
    pub source: Part1PackedHeaderSource,
    pub length: usize,
    pub fragments: u16,
}

pub enum Part1PacketLengthSource {
    None,
    Plm(Seq<u8>),
    PlmSegments(Part1PlmFragments),
    Plt(Seq<u8>),
}

pub struct Part1PlmFragments {
    pub header: Seq<u8>,
    pub first_start: usize,
    pub first_end: usize,
    pub declared: u8,
    pub marker_offset: usize,
}

pub struct Part1PacketLengths {
    pub source: Part1PacketLengthSource,
    pub packet_count: u64,
    pub encoded_bytes: u64,
}

pub struct Part1PacketLengthIter {
    pub source: Part1PacketLengthSource,
    pub position: usize,
    pub segment_end: usize,
}

#[verifier::opaque]
pub open spec fn part1_parse_plt<'a>(
    state: super::Part1CodestreamReader<'a>, segment: super::Part1CodestreamSegment,
    main: Part1PacketLengths, next_index: u16, seen: bool,
    packet_count: u64, encoded_bytes: u64, payload_bytes: u64,
) -> (Result<(), crate::DecodeError>, super::Part1CodestreamReader<'a>, u16, bool, u64, u64, u64) {
    if segment.payload.len() == 0 {
        (Err(part1_packet_input_error(segment.offset, crate::MalformedKind::InvalidMarkerLength)),
            state, next_index, seen, packet_count, encoded_bytes, payload_bytes)
    } else if segment.payload[0] as u16 != next_index {
        (Err(part1_packet_input_error(segment.offset, crate::MalformedKind::InvalidMarkerOrder)),
            state, next_index, seen, packet_count, encoded_bytes, payload_bytes)
    } else {
        let next = (next_index + 1) as u16;
        let encoded = segment.payload.drop_first();
        let admitted = super::part1_validate_packet_lengths(state, encoded, segment.offset);
        match admitted.0 {
            Err(error) => (Err(error), admitted.1, next, seen, packet_count, encoded_bytes, payload_bytes),
            Ok((count, total)) => {
                if packet_count as int + count as int > u64::MAX {
                    (Err(part1_packet_input_error(segment.offset, crate::MalformedKind::ArithmeticOverflow)),
                        admitted.1, next, true, packet_count, encoded_bytes, payload_bytes)
                } else {
                    let packets = (packet_count + count) as u64;
                    if encoded_bytes as int + encoded.len() > u64::MAX {
                        (Err(part1_packet_input_error(segment.offset, crate::MalformedKind::ArithmeticOverflow)),
                            admitted.1, next, true, packets, encoded_bytes, payload_bytes)
                    } else {
                        let bytes = (encoded_bytes as int + encoded.len()) as u64;
                        if payload_bytes as int + total as int > u64::MAX {
                            (Err(part1_packet_input_error(segment.offset, crate::MalformedKind::ArithmeticOverflow)),
                                admitted.1, next, true, packets, bytes, payload_bytes)
                        } else {
                            (Ok(()), admitted.1, next, true, packets, bytes, (payload_bytes + total) as u64)
                        }
                    }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_ppt<'a>(
    state: super::Part1CodestreamReader<'a>, segment: super::Part1CodestreamSegment,
    main: Part1PackedHeaders, next_index: u16, fragments: u16, bytes: Seq<u8>,
) -> (Result<(), crate::DecodeError>, super::Part1CodestreamReader<'a>, u16, u16, Seq<u8>) {
    if !matches!(main.source, Part1PackedHeaderSource::None) {
        (Err(part1_packet_input_error(segment.offset, crate::MalformedKind::InvalidMarkerOrder)),
            state, next_index, fragments, bytes)
    } else {
        super::part1_parse_packed_fragment(state, segment, 0xff61, next_index, fragments, bytes)
    }
}

pub open spec fn part1_packet_input_error(offset: usize, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: offset as u64, kind }
}

pub open spec fn part1_packet_input_limit(resource: crate::Resource, limit: u64, actual: u64) -> crate::DecodeError {
    crate::DecodeError::LimitExceeded { resource, limit, actual }
}

pub open spec fn part1_packet_input_word(input: Seq<u8>, position: usize) -> u16
    recommends position as nat + 1 < input.len(),
{
    super::part1_marker_value(input[position as int], input[position as int + 1])
}

pub struct Part1PackedHeaderScan {
    pub position: usize,
    pub logical_position: usize,
    pub remaining_segments: usize,
    pub output: Seq<u8>,
}

#[verifier::opaque]
pub open spec fn part1_packed_header_scan(
    header: Seq<u8>, marker: u16, logical_start: usize, logical_end: usize,
    length: usize, s: Part1PackedHeaderScan,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases s.remaining_segments,
{
    if s.position >= header.len() {
        if s.output.len() != length {
            Err(part1_packet_input_error(s.logical_position, crate::MalformedKind::InvalidPackedPacketHeader))
        } else { Ok(s.output) }
    } else if s.remaining_segments == 0 {
        Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidMarkerLength))
    } else if header.len() - s.position < 4 {
        Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidPackedPacketHeader))
    } else {
        let segment_length = part1_packet_input_word(header, (s.position + 2) as usize) as usize;
        if segment_length < 2 {
            Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidMarkerLength))
        } else if s.position as nat + 2 > usize::MAX || s.position as nat + 2 + segment_length as nat > usize::MAX {
            Err(part1_packet_input_error(s.position, crate::MalformedKind::ArithmeticOverflow))
        } else {
            let end = (s.position + 2 + segment_length) as usize;
            if end > header.len() {
                Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidMarkerLength))
            } else if part1_packet_input_word(header, s.position) != marker {
                part1_packed_header_scan(header, marker, logical_start, logical_end, length,
                    Part1PackedHeaderScan { position: end, remaining_segments: (s.remaining_segments - 1) as usize, ..s })
            } else if s.position as nat + 5 > usize::MAX {
                Err(part1_packet_input_error(s.position, crate::MalformedKind::ArithmeticOverflow))
            } else {
                let payload = (s.position + 5) as usize;
                if payload > end {
                    Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidMarkerLength))
                } else if s.logical_position as nat + (end - payload) as nat > usize::MAX {
                    Err(part1_packet_input_error(s.position, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    let fragment_end = (s.logical_position + end - payload) as usize;
                    let first = if logical_start > s.logical_position { logical_start } else { s.logical_position };
                    let last = if logical_end < fragment_end { logical_end } else { fragment_end };
                    let output = if first < last {
                        s.output + header.subrange((payload + first - s.logical_position) as int, (payload + last - s.logical_position) as int)
                    } else { s.output };
                    part1_packed_header_scan(header, marker, logical_start, logical_end, length,
                        Part1PackedHeaderScan { position: end, logical_position: fragment_end,
                            remaining_segments: (s.remaining_segments - 1) as usize, output })
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packed_header_reassembly(s: Part1PackedHeaders, maximum: u64) -> Result<Seq<u8>, crate::DecodeError> {
    if s.length as u64 > maximum {
        Err(part1_packet_input_limit(crate::Resource::PacketHeaderBytes, maximum, s.length as u64))
    } else {
        match s.source {
            Part1PackedHeaderSource::None => Ok(Seq::empty()),
            Part1PackedHeaderSource::MarkerSegments { header, marker, logical_start } => {
                if logical_start as nat + s.length as nat > usize::MAX {
                    Err(part1_packet_input_error(0, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    part1_packed_header_scan(header, marker, logical_start, (logical_start + s.length) as usize, s.length,
                        Part1PackedHeaderScan { position: 0, logical_position: 0, remaining_segments: header.len() as usize, output: Seq::empty() })
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_groups(
    encoded: Seq<u8>, start: usize, end: usize, position: usize, value: u32, groups: u8,
) -> Result<(u32, usize), crate::DecodeError>
    decreases if position < end { end - position } else { 0 },
{
    if position >= end || position >= encoded.len() {
        Err(part1_packet_input_error(start, crate::MalformedKind::InvalidPacketLength))
    } else if groups == u8::MAX {
        Err(part1_packet_input_error(start, crate::MalformedKind::ArithmeticOverflow))
    } else {
        let groups = (groups + 1) as u8;
        let byte = encoded[position as int];
        if groups > 5 || (groups == 5 && value > 0x01ff_ffff) {
            Err(part1_packet_input_error(start, crate::MalformedKind::InvalidPacketLength))
        } else if value as nat * 128 + (byte & 0x7f) as nat > u32::MAX {
            Err(part1_packet_input_error(start, crate::MalformedKind::InvalidPacketLength))
        } else if position == usize::MAX {
            Err(part1_packet_input_error(start, crate::MalformedKind::ArithmeticOverflow))
        } else {
            let next = (position + 1) as usize;
            let word = (value as nat * 128 + (byte & 0x7f) as nat) as u32;
            if byte & 0x80 == 0 {
                if word == 0 { Err(part1_packet_input_error(start, crate::MalformedKind::InvalidPacketLength)) }
                else { Ok((word, next)) }
            } else { part1_packet_length_groups(encoded, start, end, next, word, groups) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_decode(encoded: Seq<u8>, start: usize, end: usize) -> Result<(u32, usize), crate::DecodeError> {
    if start >= end || end > encoded.len() {
        Err(part1_packet_input_error(start, crate::MalformedKind::InvalidPacketLength))
    } else { part1_packet_length_groups(encoded, start, end, start, 0, 0) }
}

#[verifier::opaque]
pub open spec fn part1_sum_packet_lengths_from(s: Part1PacketLengthIter, total: u64)
    -> Result<u64, crate::DecodeError>
    decreases if s.position < part1_packet_length_source_size(s.source) {
        part1_packet_length_source_size(s.source) - s.position } else { 0 },
{
    let maximum = part1_packet_length_source_size(s.source);
    if s.position > maximum {
        Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidPacketLength))
    } else {
        let next = part1_packet_length_next(s);
        match next.0 {
            Err(error) => Err(error),
            Ok(None) => Ok(total),
            Ok(Some(length)) => {
                if next.1.position <= s.position || next.1.position > maximum {
                    Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidPacketLength))
                } else if total as int + length as int > u64::MAX {
                    Err(part1_packet_input_error(0, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    part1_sum_packet_lengths_from(
                        Part1PacketLengthIter { source: s.source, ..next.1 }, (total + length) as u64)
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_sum_packet_lengths(source: Part1PacketLengthSource) -> Result<u64, crate::DecodeError> {
    match source {
        Part1PacketLengthSource::None => Ok(0),
        Part1PacketLengthSource::Plt(_) => Err(part1_packet_input_error(0, crate::MalformedKind::InvalidPacketLength)),
        _ => part1_sum_packet_lengths_from(part1_packet_lengths_iter(
            Part1PacketLengths { source, packet_count: 0, encoded_bytes: 0 }), 0),
    }
}

pub open spec fn part1_packet_length_source_size(source: Part1PacketLengthSource) -> nat {
    match source {
        Part1PacketLengthSource::None => 0,
        Part1PacketLengthSource::Plm(bytes) | Part1PacketLengthSource::Plt(bytes) => bytes.len(),
        Part1PacketLengthSource::PlmSegments(fragments) => fragments.header.len(),
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_sources_match_from(left: Part1PacketLengthIter, right: Part1PacketLengthIter)
    -> Result<bool, crate::DecodeError>
    decreases if left.position < part1_packet_length_source_size(left.source) {
        part1_packet_length_source_size(left.source) - left.position } else { 0 },
{
    let first = part1_packet_length_next(left);
    match first.0 {
        Err(error) => Err(error),
        Ok(a) => {
            let second = part1_packet_length_next(right);
            match second.0 {
                Err(error) => Err(error),
                Ok(b) => {
                    if a != b { Ok(false) }
                    else if a.is_none() { Ok(true) }
                    else if first.1.position <= left.position || first.1.position > part1_packet_length_source_size(left.source) {
                        Err(part1_packet_input_error(left.position, crate::MalformedKind::InvalidPacketLength))
                    } else {
                        part1_packet_length_sources_match_from(
                            Part1PacketLengthIter { source: left.source, ..first.1 },
                            Part1PacketLengthIter { source: right.source, ..second.1 })
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_sources_match(first: Part1PacketLengthSource, second: Part1PacketLengthSource)
    -> Result<bool, crate::DecodeError>
{
    part1_packet_length_sources_match_from(
        part1_packet_lengths_iter(Part1PacketLengths { source: first, packet_count: 0, encoded_bytes: 0 }),
        part1_packet_lengths_iter(Part1PacketLengths { source: second, packet_count: 0, encoded_bytes: 0 }))
}

#[verifier::opaque]
pub open spec fn part1_finish_packet_lengths(
    input: Seq<u8>, start: usize, end: usize, main: Part1PacketLengths,
    plt_seen: bool, plt_count: u64, plt_bytes: u64, plt_payload: u64,
    data_length: usize, packed_length: usize, offset: usize,
) -> Result<Part1PacketLengths, crate::DecodeError> {
    if plt_seen && (start > end || end > input.len()) {
        Err(part1_packet_input_error(offset, crate::MalformedKind::InvalidTilePart))
    } else {
        let lengths = if plt_seen {
            Part1PacketLengths {
                source: Part1PacketLengthSource::Plt(input.subrange(start as int, end as int)),
                packet_count: plt_count, encoded_bytes: plt_bytes,
            }
        } else { main };
        let consistency = if plt_seen && !matches!(main.source, Part1PacketLengthSource::None) {
            if main.packet_count != plt_count { Ok(false) }
            else { part1_packet_length_sources_match(main.source, lengths.source) }
        } else { Ok(true) };
        if consistency.is_err() {
            Err(consistency->Err_0)
        } else if !(consistency->Ok_0) {
            Err(part1_packet_input_error(offset, crate::MalformedKind::InvalidPacketLength))
        } else if matches!(lengths.source, Part1PacketLengthSource::None) {
            Ok(lengths)
        } else {
            let declared = if plt_seen { Ok(plt_payload) } else { part1_sum_packet_lengths(lengths.source) };
            match declared {
                Err(error) => Err(error),
                Ok(bytes) => {
                    let logical = data_length as int + packed_length as int;
                    if logical > u64::MAX {
                        Err(part1_packet_input_error(offset, crate::MalformedKind::ArithmeticOverflow))
                    } else if bytes as int != logical {
                        Err(part1_packet_input_error(offset, crate::MalformedKind::InvalidPacketLength))
                    } else { Ok(lengths) }
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_finish_packed_packet_headers(
    input: Seq<u8>, start: usize, end: usize, main: Part1PackedHeaders,
    fragments: u16, length: usize, offset: usize,
) -> Result<Part1PackedHeaders, crate::DecodeError> {
    if fragments == 0 {
        Ok(main)
    } else if start > end || end > input.len() {
        Err(part1_packet_input_error(offset, crate::MalformedKind::InvalidTilePart))
    } else {
        Ok(Part1PackedHeaders {
            source: Part1PackedHeaderSource::MarkerSegments {
                header: input.subrange(start as int, end as int), marker: 0xff61, logical_start: 0,
            },
            length, fragments,
        })
    }
}

pub open spec fn part1_packet_lengths_iter(s: Part1PacketLengths) -> Part1PacketLengthIter {
    match s.source {
        Part1PacketLengthSource::PlmSegments(fragments) => Part1PacketLengthIter {
            source: s.source, position: fragments.first_start, segment_end: fragments.first_end },
        _ => Part1PacketLengthIter { source: s.source, position: 0, segment_end: 0 },
    }
}

pub open spec fn part1_incomplete_plm_offset(s: Part1PacketLengths) -> Option<usize> {
    match s.source {
        Part1PacketLengthSource::PlmSegments(fragments) =>
            if s.encoded_bytes != fragments.declared as u64 { Some(fragments.marker_offset) } else { None },
        _ => None,
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_plt(s: Part1PacketLengthIter) -> (Result<Option<u32>, crate::DecodeError>, Part1PacketLengthIter)
    decreases if s.position < part1_packet_length_source_size(s.source) {
        part1_packet_length_source_size(s.source) - s.position } else { 0 },
{
    let header = match s.source {
        Part1PacketLengthSource::Plt(bytes) => Some(bytes),
        Part1PacketLengthSource::PlmSegments(fragments) => Some(fragments.header),
        _ => None,
    };
    match header {
        Some(header) => {
            let continued = matches!(s.source, Part1PacketLengthSource::PlmSegments(_));
            if s.position < s.segment_end {
                match part1_packet_length_decode(header, s.position, s.segment_end) {
                    Err(error) => (Err(error), s),
                    Ok((value, next)) => (Ok(Some(value)), Part1PacketLengthIter { position: next, ..s }),
                }
            } else if s.position == header.len() { (Ok(None), s) }
            else if s.position > header.len() || header.len() - s.position < 4 {
                (Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidPacketLength)), s)
            } else {
                let marker_length = part1_packet_input_word(header, (s.position + 2) as usize) as usize;
                if marker_length < 2 {
                    (Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidMarkerLength)), s)
                } else if s.position as nat + 2 > usize::MAX || s.position as nat + 2 + marker_length as nat > usize::MAX {
                    (Err(part1_packet_input_error(s.position, crate::MalformedKind::ArithmeticOverflow)), s)
                } else {
                    let end = (s.position + 2 + marker_length) as usize;
                    let marker = part1_packet_input_word(header, s.position);
                    if end > header.len() && !(continued && marker == 0xff57) {
                        (Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidMarkerLength)), s)
                    } else {
                        let fragment_end = if end > header.len() { header.len() as usize } else { end };
                        let next = Part1PacketLengthIter { position: fragment_end, ..s };
                        if marker == if continued { 0xff57u16 } else { 0xff58u16 } {
                            if end < marker_length || (end - marker_length) as nat + 3 > usize::MAX {
                                (Err(part1_packet_input_error(fragment_end, crate::MalformedKind::ArithmeticOverflow)), next)
                            } else {
                                let data = (end - marker_length + 3) as usize;
                                if data > fragment_end {
                                    (Err(part1_packet_input_error(fragment_end, crate::MalformedKind::InvalidMarkerLength)), next)
                                } else {
                                    let next = Part1PacketLengthIter { position: data, segment_end: fragment_end, ..s };
                                    if data <= s.position || data > header.len() {
                                        (Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidPacketLength)), next)
                                    } else { part1_packet_length_plt(next) }
                                }
                            }
                        } else if fragment_end <= s.position || fragment_end > header.len() {
                            (Err(part1_packet_input_error(s.position, crate::MalformedKind::InvalidPacketLength)), next)
                        } else { part1_packet_length_plt(next) }
                    }
                }
            }
        },
        _ => (Ok(None), s),
    }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_next(s: Part1PacketLengthIter) -> (Result<Option<u32>, crate::DecodeError>, Part1PacketLengthIter) {
    match s.source {
        Part1PacketLengthSource::None => (Ok(None), s),
        Part1PacketLengthSource::Plm(bytes) => {
            if s.position == bytes.len() { (Ok(None), s) }
            else {
                match part1_packet_length_decode(bytes, s.position, bytes.len() as usize) {
                    Err(error) => (Err(error), s),
                    Ok((value, next)) => (Ok(Some(value)), Part1PacketLengthIter { position: next, ..s }),
                }
            }
        },
        Part1PacketLengthSource::Plt(_) | Part1PacketLengthSource::PlmSegments(_) => part1_packet_length_plt(s),
    }
}

pub proof fn part1_packed_absent_cap_precedes_source(s: Part1PackedHeaders, maximum: u64)
    ensures matches!(s.source, Part1PackedHeaderSource::None) ==>
        part1_packed_header_reassembly(s, maximum) == (
            if s.length as u64 > maximum {
                Err(part1_packet_input_limit(crate::Resource::PacketHeaderBytes, maximum, s.length as u64))
            } else { Ok(Seq::empty()) }),
{
    reveal(part1_packed_header_reassembly);
}

pub proof fn part1_packet_length_absent_keeps_arbitrary_cursors(s: Part1PacketLengthIter)
    ensures matches!(s.source, Part1PacketLengthSource::None) ==>
        part1_packet_length_next(s) == (Ok(None), s),
{
    reveal(part1_packet_length_next);
}

pub proof fn part1_packet_length_short_plt_commits_before_payload_error()
    ensures part1_packet_length_next(Part1PacketLengthIter {
            source: Part1PacketLengthSource::Plt(seq![0xffu8, 0x58u8, 0u8, 2u8]), position: 0, segment_end: 0 })
        == (Err(part1_packet_input_error(4, crate::MalformedKind::InvalidMarkerLength)),
            Part1PacketLengthIter {
                source: Part1PacketLengthSource::Plt(seq![0xffu8, 0x58u8, 0u8, 2u8]), position: 4, segment_end: 0 }),
{
    reveal(part1_packet_length_next);
    reveal(part1_packet_length_plt);
    reveal(part1_packet_input_word);
    reveal(super::part1_marker_value);
    assert(super::part1_marker_value(0xffu8, 0x58u8) == 0xff58u16) by(bit_vector);
    assert(super::part1_marker_value(0u8, 2u8) == 2u16) by(bit_vector);
}

}
