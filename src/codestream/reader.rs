//! Bounded marker/segment reading and shared parser accounting.

use super::{
    ADS, ATK, CAP, CBD, COD, CPF, CRG, DFS, DecodeError, EOC, MalformedKind, NLT, POC, PRF, Parser,
    Part2Extensions, QCD, RGN, Resource, ResourceLimits, SIZ, SOC, SOD, SOT, Segment, TLM,
};
#[cfg(verus_keep_ghost)]
use super::{
    main_header_segment_outcome, owned_extensions_view, parser_initial_outcome, parser_view,
    segment_outcome, segment_tail_outcome, segment_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures parser_initial_outcome(result) == crate::specs::part1_codestream_reader_new(input@, limits),
))]
pub(super) fn new_parser<'a>(
    input: &'a [u8],
    limits: &'a ResourceLimits,
) -> Result<Parser<'a>, DecodeError> {
    let input_length = input.len() as u64;
    if input_length > limits.maximum_input_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::InputBytes,
            limit: limits.maximum_input_bytes(),
            actual: input_length,
        });
    }
    Ok(Parser {
        input,
        limits,
        position: 0,
        work_units: 0,
        packet_length_bytes: 0,
        packet_lengths: 0,
    })
}
impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (main_header_segment_outcome(result), parser_view(final(self)), *final(main_header_segments))
            == crate::specs::part1_read_main_header_segment(
                parser_view(old(self)), *old(main_header_segments)),
    ))]
    pub(super) fn read_main_header_segment(
        &mut self,
        main_header_segments: &mut u64,
    ) -> Result<Option<Segment<'a>>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_read_main_header_segment);
            reveal(main_header_segment_outcome);
        }
        let marker = self.peek_marker()?;
        if marker == SOT {
            return Ok(None);
        }
        if crate::refinement::main_header_boundary(marker) {
            return Err(self.malformed_here(MalformedKind::InvalidMarkerOrder));
        }
        let segment = self.read_segment()?;
        *main_header_segments = match main_header_segments.checked_add(1) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if !is_known_segment_marker(segment.marker) {
            return Err(DecodeError::malformed(
                self.offset(segment.offset),
                MalformedKind::InvalidMarker,
            ));
        }
        if !is_allowed_main_header(segment.marker) {
            return Err(DecodeError::malformed(
                self.offset(segment.offset),
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        Ok(Some(segment))
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self)), owned_extensions_view(final(extensions)))
            == crate::specs::part1_charge_extension_metadata(
                parser_view(old(self)), segment_view(segment), owned_extensions_view(old(extensions))),
    ))]
    pub(super) fn charge_extension_metadata(
        &mut self,
        segment: Segment<'a>,
        extensions: &mut Part2Extensions,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_charge_extension_metadata); }
        let bytes = match (segment.payload.len() as u64).checked_add(4) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        extensions.metadata_bytes = match extensions.metadata_bytes.checked_add(bytes) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if extensions.metadata_bytes > self.limits.maximum_metadata_bytes() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::MetadataBytes,
                limit: self.limits.maximum_metadata_bytes(),
                actual: extensions.metadata_bytes,
            });
        }
        self.charge_work(bytes)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_segment_byte(self.position, segment_view(segment), position, relative),
    ))]
    pub(super) fn segment_byte(
        &self,
        segment: Segment<'a>,
        position: usize,
        relative: usize,
    ) -> Result<u8, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_segment_byte); }
        let index = match position.checked_add(relative) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        match segment.payload.get(index) {
            Some(value) => Ok(*value),
            None => Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength)),
        }
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures segment_tail_outcome(result) == crate::specs::part1_copy_segment_tail(segment_view(segment), start),
    ))]
    pub(super) fn copy_segment_tail(
        &self,
        segment: Segment<'a>,
        start: usize,
    ) -> Result<Vec<u8>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_copy_segment_tail); }
        if start > segment.payload.len() {
            return Err(self.malformed_at(segment.offset, MalformedKind::InvalidMarkerLength));
        }
        let mut copied = Vec::with_capacity(segment.payload.len() - start);
        let mut position = start;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant start <= position <= segment.payload.len(),
                    copied@ == segment.payload@.subrange(start as int, position as int),
                decreases segment.payload.len() - position,
            )
        )]
        while position < segment.payload.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_segment_byte); }
            copied.push(self.segment_byte(segment, position, 0)?);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(segment.payload@.subrange(start as int, position as int + 1) =~=
                    segment.payload@.subrange(start as int, position as int).push(segment.payload@[position as int]));
            }
            position = match position.checked_add(1) {
                Some(value) => value,
                None => {
                    return Err(
                        self.malformed_at(segment.offset, MalformedKind::ArithmeticOverflow)
                    );
                }
            };
        }
        Ok(copied)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (segment_outcome(result), parser_view(final(self))) == crate::specs::part1_codestream_read_segment(parser_view(old(self))),
    ))]
    pub(super) fn read_segment(&mut self) -> Result<Segment<'a>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_codestream_read_segment); }
        let offset = self.position;
        let marker = self.peek_marker()?;
        self.charge_work(1)?;
        if is_standalone_marker(marker) && marker != SOT {
            return Err(self.malformed_here(MalformedKind::InvalidMarkerOrder));
        }
        let length_offset = match offset.checked_add(2) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if self.input.len().saturating_sub(length_offset) < 2 {
            return Err(self.malformed_here(MalformedKind::Truncated));
        }
        let length = usize::from(read_u16([
            self.input[length_offset],
            self.input[length_offset + 1],
        ]));
        if length < 2 {
            return Err(self.malformed_here(MalformedKind::InvalidMarkerLength));
        }
        let end = match length_offset.checked_add(length) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if end > self.input.len() {
            return Err(self.malformed_here(MalformedKind::Truncated));
        }
        let payload_start = length_offset + 2;
        if payload_start > end {
            return Err(self.malformed_here(MalformedKind::ArithmeticOverflow));
        }
        self.position = end;
        Ok(Segment {
            marker,
            offset,
            payload: &self.input[payload_start..end],
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self))) == crate::specs::part1_codestream_expect_standalone(parser_view(old(self)), expected),
    ))]
    pub(super) fn expect_standalone(&mut self, expected: u16) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_codestream_expect_standalone); }
        if self.peek_marker()? != expected {
            return Err(self.malformed_here(MalformedKind::InvalidMarkerOrder));
        }
        self.position = match self.position.checked_add(2) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        self.charge_work(1)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_codestream_peek_marker(parser_view(self)),
    ))]
    pub(super) fn peek_marker(&self) -> Result<u16, DecodeError> {
        if self.input.len().saturating_sub(self.position) < 2 {
            return Err(self.malformed_here(MalformedKind::Truncated));
        }
        if self.input[self.position] != 0xff || matches!(self.input[self.position + 1], 0x00 | 0xff)
        {
            return Err(self.malformed_here(MalformedKind::InvalidMarker));
        }
        Ok(read_u16([
            self.input[self.position],
            self.input[self.position + 1],
        ]))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parser_view(final(self))) == crate::specs::part1_codestream_charge_work(parser_view(old(self)), amount),
    ))]
    pub(super) fn charge_work(&mut self, amount: u64) -> Result<(), DecodeError> {
        self.work_units = match self.work_units.checked_add(amount) {
            Some(value) => value,
            None => return Err(self.malformed_here(MalformedKind::ArithmeticOverflow)),
        };
        if self.work_units > self.limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.limits.maximum_work_units(),
                actual: self.work_units,
            });
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_codestream_malformed(self.position, kind),
    ))]
    pub(super) fn malformed_here(&self, kind: MalformedKind) -> DecodeError {
        self.malformed_at(self.position, kind)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_codestream_malformed(value, kind),
    ))]
    pub(super) fn malformed_at(&self, value: usize, kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput {
            offset: self.offset(value),
            kind,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_codestream_offset(value),
    ))]
    pub(super) fn offset(&self, value: usize) -> u64 {
        value as u64
    }
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_codestream_standalone(marker),
))]
pub(super) const fn is_standalone_marker(marker: u16) -> bool {
    matches!(marker, SOC | SOD | EOC | 0xff92)
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_known_segment_marker(marker),
))]
pub(super) const fn is_known_segment_marker(marker: u16) -> bool {
    matches!(
        marker,
        CAP | SIZ
            | 0xff52
            | 0xff53
            | TLM
            | PRF
            | 0xff57
            | 0xff58
            | CPF
            | 0xff5c
            | 0xff5d
            | RGN
            | POC
            | 0xff60
            | 0xff61
            | CRG
            | 0xff64
            | DFS
            | ADS
            | 0xff74
            | 0xff75
            | NLT
            | 0xff77
            | CBD
            | ATK
            | SOT
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_allowed_main_header(marker),
))]
pub(super) const fn is_allowed_main_header(marker: u16) -> bool {
    matches!(
        marker,
        CAP | COD
            | 0xff53
            | TLM
            | PRF
            | 0xff57
            | CPF
            | QCD
            | 0xff5d
            | RGN
            | POC
            | 0xff60
            | CRG
            | 0xff64
            | DFS
            | ADS
            | 0xff74
            | 0xff75
            | NLT
            | 0xff77
            | CBD
            | ATK
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_allowed_tile_header(marker),
))]
pub(super) const fn is_allowed_tile_header(marker: u16) -> bool {
    matches!(
        marker,
        COD | 0xff53
            | 0xff58
            | QCD
            | 0xff5d
            | RGN
            | POC
            | 0xff61
            | 0xff64
            | DFS
            | ADS
            | 0xff74
            | 0xff75
            | NLT
            | 0xff77
            | CBD
            | ATK
    )
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_marker_value(bytes[0], bytes[1]),
))]
pub(super) fn read_u16(bytes: [u8; 2]) -> u16 {
    crate::refinement::marker_value(bytes[0], bytes[1])
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_codestream_u32(bytes[0], bytes[1], bytes[2], bytes[3]),
))]
pub(super) fn read_u32(bytes: [u8; 4]) -> u32 {
    (u32::from(bytes[0]) << 24)
        | (u32::from(bytes[1]) << 16)
        | (u32::from(bytes[2]) << 8)
        | u32::from(bytes[3])
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_codestream_u64(bytes@),
))]
pub(super) fn read_u64(bytes: [u8; 8]) -> u64 {
    (u64::from(bytes[0]) << 56)
        | (u64::from(bytes[1]) << 48)
        | (u64::from(bytes[2]) << 40)
        | (u64::from(bytes[3]) << 32)
        | (u64::from(bytes[4]) << 24)
        | (u64::from(bytes[5]) << 16)
        | (u64::from(bytes[6]) << 8)
        | u64::from(bytes[7])
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_signed_u16(value),
))]
pub(super) fn signed_u16(value: u16) -> i64 {
    let value = i64::from(value);
    if value < 32_768 {
        value
    } else {
        value - 65_536
    }
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_signed_u32(value),
        i32::MIN <= result <= i32::MAX,
))]
pub(super) fn signed_u32(value: u32) -> i64 {
    let value = i64::from(value);
    if value < 2_147_483_648 {
        value
    } else {
        value - 4_294_967_296
    }
}
