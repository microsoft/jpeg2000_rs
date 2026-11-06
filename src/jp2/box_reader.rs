//! Bounded box iteration, box identifiers, offsets, and integer reads.

use super::{
    BoxHeader, BoxReader, BoxRef, BoxType, DecodeError, MalformedKind, Resource, ResourceLimits,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl BoxType {
    pub const SIGNATURE: Self = Self(0x6a50_2020);
    pub const FILE_TYPE: Self = Self(0x6674_7970);
    pub const JP2_HEADER: Self = Self(0x6a70_3268);
    pub const CODESTREAM_HEADER: Self = Self(0x6a70_6368);
    pub const COMPOSITING_LAYER_HEADER: Self = Self(0x6a70_6c68);
    pub const COMPOSITION: Self = Self(0x636f_6d70);
    pub const COMPOSITION_OPTIONS: Self = Self(0x636f_7074);
    pub const INSTRUCTION_SET: Self = Self(0x696e_7374);
    pub const CODESTREAM_REGISTRATION: Self = Self(0x6372_6567);
    pub const COLOR_GROUP: Self = Self(0x6367_7270);
    pub const OPACITY: Self = Self(0x6f70_6374);
    pub const ASSOCIATION: Self = Self(0x6173_6f63);
    pub const CONTIGUOUS_CODESTREAM: Self = Self(0x6a70_3263);
    pub const IMAGE_HEADER: Self = Self(0x6968_6472);
    pub const BITS_PER_COMPONENT: Self = Self(0x6270_6363);
    pub const COLOR_SPECIFICATION: Self = Self(0x636f_6c72);
    pub const PALETTE: Self = Self(0x7063_6c72);
    pub const COMPONENT_MAPPING: Self = Self(0x636d_6170);
    pub const CHANNEL_DEFINITION: Self = Self(0x6364_6566);
    pub const RESOLUTION: Self = Self(0x7265_7320);
    pub const CAPTURE_RESOLUTION: Self = Self(0x7265_7363);
    pub const DISPLAY_RESOLUTION: Self = Self(0x7265_7364);
    pub const JP2_BRAND: Self = Self(0x6a70_3220);
    pub const JPX_BRAND: Self = Self(0x6a70_7820);
    pub const JPX_BASELINE_BRAND: Self = Self(0x6a70_7862);
    pub const JPH_BRAND: Self = Self(0x6a70_6820);

    pub const fn new(bytes: [u8; 4]) -> Self {
        box_type_from_bytes(bytes)
    }

    pub const fn bytes(self) -> [u8; 4] {
        [
            (self.0 >> 24) as u8,
            (self.0 >> 16) as u8,
            (self.0 >> 8) as u8,
            self.0 as u8,
        ]
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self == other),))]
    pub const fn equals(self, other: Self) -> bool {
        self.0 == other.0
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == super::box_type_from_bytes_model(bytes),
))]
pub(super) const fn box_type_from_bytes(bytes: [u8; 4]) -> BoxType {
    BoxType(
        ((bytes[0] as u32) << 24)
            | ((bytes[1] as u32) << 16)
            | ((bytes[2] as u32) << 8)
            | (bytes[3] as u32),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::box_reader_outcome(result)
        == crate::specs::part2_box_reader_from_input(input@, *limits),
    match result { Err(_) => true, Ok(reader) => super::box_reader_input_reference(&reader) == input },
))]
pub(super) fn box_reader_from_input<'a>(
    input: &'a [u8],
    limits: &ResourceLimits,
) -> Result<BoxReader<'a>, DecodeError> {
    let input_length = input.len() as u64;
    if input_length > limits.maximum_input_bytes() {
        return Err(DecodeError::limit(
            Resource::InputBytes,
            limits.maximum_input_bytes(),
            input_length,
        ));
    }
    Ok(BoxReader {
        input,
        limits: *limits,
        position: 0,
        metadata_bytes: 0,
        work_units: 0,
        failed: false,
    })
}

impl BoxHeader {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == super::box_header_view(self).0,))]
    pub const fn box_type(self) -> BoxType {
        self.box_type
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == super::box_header_offset(self),))]
    pub const fn offset(self) -> u64 {
        self.offset
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == super::box_header_view(self).2,))]
    pub const fn header_length(self) -> u64 {
        self.header_length
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == super::box_header_view(self).3,))]
    pub const fn total_length(self) -> u64 {
        self.total_length
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_box_payload_offset(super::box_header_view(self)),
    ))]
    pub fn payload_offset(self) -> Result<u64, DecodeError> {
        self.offset
            .checked_add(self.header_length)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == (DecodeError::MalformedInput { offset: self.offset, kind: MalformedKind::ArithmeticOverflow }),
                ))]
                || DecodeError::malformed(self.offset, MalformedKind::ArithmeticOverflow),
            )
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_box_payload_length(super::box_header_view(self)),
    ))]
    pub fn payload_length(self) -> Result<u64, DecodeError> {
        self.total_length
            .checked_sub(self.header_length)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == (DecodeError::MalformedInput { offset: self.offset, kind: MalformedKind::InvalidBoxLength }),
                ))]
                || DecodeError::malformed(self.offset, MalformedKind::InvalidBoxLength),
            )
    }
}

impl<'a> BoxReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        box_reader_from_input(input, limits)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == super::box_reader_state(self).metadata_bytes,
    ))]
    pub const fn metadata_bytes(&self) -> u64 {
        self.metadata_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (super::box_ref_outcome(result), super::box_reader_state(final(self)))
            == crate::specs::part2_box_reader_next_ref(super::box_reader_state(old(self))),
        super::box_reader_input_reference(final(self)) == super::box_reader_input_reference(old(self)),
    ))]
    pub fn next_box_ref(&mut self) -> Option<Result<BoxRef<'a>, DecodeError>> {
        if self.failed {
            return None;
        }
        match self.next_box() {
            Ok(Some(box_ref)) => Some(Ok(box_ref)),
            Ok(None) => None,
            Err(error) => {
                self.failed = true;
                Some(Err(error))
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (super::box_read_outcome(result), super::box_reader_state(final(self)))
            == crate::specs::part2_box_reader_next(super::box_reader_state(old(self))),
        super::box_reader_input_reference(final(self)) == super::box_reader_input_reference(old(self)),
    ))]
    fn next_box(&mut self) -> Result<Option<BoxRef<'a>>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost position = super::box_reader_state(self).position; }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_box_reader_next);
            reveal(crate::specs::part2_box_reader_after_work);
            reveal(crate::specs::part2_box_reader_after_header);
        }
        if self.position == self.input.len() {
            return Ok(None);
        }

        self.work_units = self
            .work_units
            .checked_add(1)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_box_malformed(position, MalformedKind::ArithmeticOverflow),
                ))]
                || self.malformed_here(MalformedKind::ArithmeticOverflow),
            )?;
        if self.work_units > self.limits.maximum_work_units() {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.limits.maximum_work_units(),
                self.work_units,
            ));
        }

        let offset = self.position;
        let remaining = self
            .input
            .len()
            .checked_sub(offset)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_box_malformed(position, MalformedKind::ArithmeticOverflow),
                ))]
                || self.malformed_here(MalformedKind::ArithmeticOverflow),
            )?;
        if remaining < 8 {
            return Err(self.malformed_here(MalformedKind::Truncated));
        }

        let length32 = read_u32([
            self.input[offset],
            self.input[offset + 1],
            self.input[offset + 2],
            self.input[offset + 3],
        ]);
        let box_type = box_type_from_bytes([
            self.input[offset + 4],
            self.input[offset + 5],
            self.input[offset + 6],
            self.input[offset + 7],
        ]);
        let (header_length, total_length) = match length32 {
            0 => (8_u64, remaining as u64),
            1 => {
                if remaining < 16 {
                    return Err(self.malformed_here(MalformedKind::Truncated));
                }
                (
                    16_u64,
                    read_u64([
                        self.input[offset + 8],
                        self.input[offset + 9],
                        self.input[offset + 10],
                        self.input[offset + 11],
                        self.input[offset + 12],
                        self.input[offset + 13],
                        self.input[offset + 14],
                        self.input[offset + 15],
                    ]),
                )
            }
            2..=7 => return Err(self.malformed_here(MalformedKind::InvalidBoxLength)),
            value => (8_u64, u64::from(value)),
        };

        if total_length < header_length {
            return Err(self.malformed_here(MalformedKind::InvalidBoxLength));
        }
        let total_length_usize = usize::try_from(total_length)
            .map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_box_malformed(position, MalformedKind::InvalidBoxLength),
                ))]
                |_error| self.malformed_here(MalformedKind::InvalidBoxLength),
            )?;
        let end = offset
            .checked_add(total_length_usize)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_box_malformed(position, MalformedKind::ArithmeticOverflow),
                ))]
                || self.malformed_here(MalformedKind::ArithmeticOverflow),
            )?;
        if end > self.input.len() {
            return Err(self.malformed_here(MalformedKind::Truncated));
        }
        let header_length_usize = usize::try_from(header_length)
            .map_err(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_box_malformed(position, MalformedKind::InvalidBoxLength),
                ))]
                |_error| self.malformed_here(MalformedKind::InvalidBoxLength),
            )?;
        let payload_start = offset
            .checked_add(header_length_usize)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_box_malformed(position, MalformedKind::ArithmeticOverflow),
                ))]
                || self.malformed_here(MalformedKind::ArithmeticOverflow),
            )?;

        if !box_type.equals(BoxType::CONTIGUOUS_CODESTREAM) {
            self.metadata_bytes = self
                .metadata_bytes
                .checked_add(total_length)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_box_malformed(position, MalformedKind::ArithmeticOverflow),
                    ))]
                    || self.malformed_here(MalformedKind::ArithmeticOverflow),
                )?;
            if self.metadata_bytes > self.limits.maximum_metadata_bytes() {
                return Err(DecodeError::limit(
                    Resource::MetadataBytes,
                    self.limits.maximum_metadata_bytes(),
                    self.metadata_bytes,
                ));
            }
        }

        self.position = end;
        Ok(Some(BoxRef {
            header: BoxHeader {
                box_type,
                offset: offset as u64,
                header_length,
                total_length,
            },
            payload: &self.input[payload_start..end],
        }))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_box_malformed(super::box_reader_state(self).position, kind),
    ))]
    fn malformed_here(&self, kind: MalformedKind) -> DecodeError {
        DecodeError::malformed(self.position as u64, kind)
    }
}

#[cfg(not(verus_keep_ghost))]
impl<'a> Iterator for BoxReader<'a> {
    type Item = Result<BoxRef<'a>, DecodeError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_box_ref()
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_box_byte_at(input@, position, delta, offset),
))]
pub(super) fn byte_at_checked(
    input: &[u8],
    position: usize,
    delta: usize,
    offset: u64,
) -> Result<u8, DecodeError> {
    let index = position
        .checked_add(delta)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::ArithmeticOverflow }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
    match input.get(index) {
        Some(value) => Ok(*value),
        None => Err(DecodeError::malformed(
            offset,
            MalformedKind::InvalidBoxLength,
        )),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_box_add_offset(base, relative),
))]
pub(super) fn add_offset(base: u64, relative: u64) -> Result<u64, DecodeError> {
    base.checked_add(relative)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset: base, kind: MalformedKind::ArithmeticOverflow }),
            ))]
            || DecodeError::malformed(base, MalformedKind::ArithmeticOverflow),
        )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
))]
pub(super) fn rebase_error(error: DecodeError, base_offset: u64) -> DecodeError {
    match error {
        DecodeError::MalformedInput { offset, kind } => match base_offset.checked_add(offset) {
            Some(rebased) => DecodeError::malformed(rebased, kind),
            None => DecodeError::malformed(base_offset, MalformedKind::ArithmeticOverflow),
        },
        other => other,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (super::required_box_outcome(result), super::box_reader_state(final(reader)))
        == crate::specs::part2_box_reader_required(super::box_reader_state(old(reader)), expected_index),
    super::box_reader_input_reference(final(reader)) == super::box_reader_input_reference(old(reader)),
))]
pub(super) fn required_box<'a>(
    reader: &mut BoxReader<'a>,
    expected_index: u64,
) -> Result<BoxRef<'a>, DecodeError> {
    match reader.next_box_ref() {
        Some(result) => result,
        None => Err(DecodeError::malformed(
            expected_index,
            MalformedKind::MissingRequiredStructure,
        )),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_box_type_at(payload@, position, offset),
))]
pub(super) fn read_box_type_at(
    payload: &[u8],
    position: usize,
    offset: u64,
) -> Result<BoxType, DecodeError> {
    let position1 = position
        .checked_add(1)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::ArithmeticOverflow }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
    let position2 = position
        .checked_add(2)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::ArithmeticOverflow }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
    let position3 = position
        .checked_add(3)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::ArithmeticOverflow }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
    let byte0 = *payload
        .get(position)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::InvalidBoxLength }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::InvalidBoxLength),
        )?;
    let byte1 = *payload
        .get(position1)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::InvalidBoxLength }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::InvalidBoxLength),
        )?;
    let byte2 = *payload
        .get(position2)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::InvalidBoxLength }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::InvalidBoxLength),
        )?;
    let byte3 = *payload
        .get(position3)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == (DecodeError::MalformedInput { offset, kind: MalformedKind::InvalidBoxLength }),
            ))]
            || DecodeError::malformed(offset, MalformedKind::InvalidBoxLength),
        )?;
    Ok(box_type_from_bytes([byte0, byte1, byte2, byte3]))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == crate::specs::part2_box_u32(bytes),))]
pub(super) fn read_u32(bytes: [u8; 4]) -> u32 {
    (u32::from(bytes[0]) << 24)
        | (u32::from(bytes[1]) << 16)
        | (u32::from(bytes[2]) << 8)
        | u32::from(bytes[3])
}

#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == crate::specs::part2_box_u16(bytes),))]
pub(super) fn read_u16(bytes: [u8; 2]) -> u16 {
    (u16::from(bytes[0]) << 8) | u16::from(bytes[1])
}

#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == crate::specs::part2_box_u64(bytes),))]
fn read_u64(bytes: [u8; 8]) -> u64 {
    (u64::from(bytes[0]) << 56)
        | (u64::from(bytes[1]) << 48)
        | (u64::from(bytes[2]) << 40)
        | (u64::from(bytes[3]) << 32)
        | (u64::from(bytes[4]) << 24)
        | (u64::from(bytes[5]) << 16)
        | (u64::from(bytes[6]) << 8)
        | u64::from(bytes[7])
}
