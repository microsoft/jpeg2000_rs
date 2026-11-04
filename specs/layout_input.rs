//! Source-derived models of the layout prologue and shared raw header admission.

use super::*;

verus! {

#[verifier::opaque]
pub(crate) open spec fn part1_read_tile_header_segment<'a>(
    state: Part1CodestreamReader<'a>,
) -> (Result<Option<Part1CodestreamSegment>, crate::DecodeError>, Part1CodestreamReader<'a>)
{
    match part1_codestream_peek_marker(state) {
        Err(error) => (Err(error), state),
        Ok(marker) => if marker == 0xff93 {
            let sod = part1_codestream_expect_standalone(state, 0xff93);
            match sod.0 {
                Err(error) => (Err(error), sod.1),
                Ok(()) => (Ok(None), sod.1),
            }
        } else if part1_tile_header_boundary(marker) {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidMarkerOrder)), state)
        } else {
            let read = part1_codestream_read_segment(state);
            match read.0 {
                Err(error) => (Err(error), read.1),
                Ok(segment) => if !part1_known_segment_marker(segment.marker) {
                    (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), read.1)
                } else if !part1_allowed_tile_header(segment.marker) {
                    (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), read.1)
                } else {
                    (Ok(Some(segment)), read.1)
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_record_component_segment<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment,
    components: u16, invalid_kind: crate::MalformedKind,
    segments: Seq<Option<Part1CodestreamSegment>>,
) -> (Result<(), crate::DecodeError>, Seq<Option<Part1CodestreamSegment>>, Part1CodestreamReader<'a>)
{
    match part1_parse_component_index(segment.offset, segment.payload, components, invalid_kind) {
        Err(error) => (Err(error), segments, state),
        Ok((component, _)) => if component as nat >= segments.len() {
            (Err(part1_codestream_malformed(segment.offset, invalid_kind)), segments, state)
        } else if segments[component as int].is_some() {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), segments, state)
        } else {
            (Ok(()), segments.update(component as int, Some(segment)), state)
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_parse_layout_prologue<'a>(state: Part1CodestreamReader<'a>)
    -> (Result<(Part1ParsedImageSize, u16, usize), crate::DecodeError>, Part1CodestreamReader<'a>)
{
    let soc = part1_codestream_expect_standalone(state, 0xff4f);
    match soc.0 {
        Err(error) => (Err(error), soc.1),
        Ok(()) => {
            let siz = part1_codestream_read_segment(soc.1);
            match siz.0 {
                Err(error) => (Err(error), siz.1),
                Ok(segment) => if segment.marker != 0xff51 {
                    (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), siz.1)
                } else {
                    match part1_parse_siz(segment, siz.1.limits) {
                        Err(error) => (Err(error), siz.1),
                        Ok((image_size, r_siz)) => (Ok((image_size, r_siz, siz.1.position)), siz.1),
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_read_main_header_segment<'a>(
    state: Part1CodestreamReader<'a>, main_header_segments: u64,
) -> (Result<Option<Part1CodestreamSegment>, crate::DecodeError>, Part1CodestreamReader<'a>, u64)
{
    match part1_codestream_peek_marker(state) {
        Err(error) => (Err(error), state, main_header_segments),
        Ok(marker) => if marker == 0xff90 {
            (Ok(None), state, main_header_segments)
        } else if part1_main_header_boundary(marker) {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidMarkerOrder)), state, main_header_segments)
        } else {
            let read = part1_codestream_read_segment(state);
            match read.0 {
                Err(error) => (Err(error), read.1, main_header_segments),
                Ok(segment) => if main_header_segments == u64::MAX {
                    (Err(part1_codestream_malformed(read.1.position, crate::MalformedKind::ArithmeticOverflow)), read.1, main_header_segments)
                } else {
                    let count = (main_header_segments + 1) as u64;
                    if !part1_known_segment_marker(segment.marker) {
                        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarker)), read.1, count)
                    } else if !part1_allowed_main_header(segment.marker) {
                        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), read.1, count)
                    } else {
                        (Ok(Some(segment)), read.1, count)
                    }
                },
            }
        },
    }
}

}
