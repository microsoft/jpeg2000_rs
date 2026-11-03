//! Source-derived models of the actual layout prologue and main-header admission.

use super::*;

verus! {

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
