use crate::{
    DecodeError, MalformedKind, Resource, ResourceLimits,
    magnitude::Magnitude,
    mq::{MqContextState, MqDecoder},
    transform::SignedMagnitude,
};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[path = "tier1_ht_tables.rs"]
mod ht_vlc_tables;

use ht_vlc_tables::{HT_VLC_INITIAL, HT_VLC_NON_INITIAL};

const RUN_LENGTH_CONTEXT: usize = 17;
const UNIFORM_CONTEXT: usize = 18;
pub const MAX_TIER1_BITPLANES: u16 = 292;
pub const MAX_TIER1_PASSES: u32 = 874;
const MAX_HT_SCUP: usize = 4_079;
const MAX_HT_CLEANUP_BYTES: usize = 65_534;
const MAX_HT_REFINEMENT_BYTES: usize = 2_046;
const MAX_HT_MAGNITUDE_BITS: u8 = 74;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct RawBitReader<'a> {
    input: &'a [u8],
    next_index: usize,
    current_byte: u8,
    bits_remaining: u8,
    marker_padding_count: u64,
    work_units: u64,
    maximum_work_units: u64,
}

impl<'a> RawBitReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        let input_length = input.len() as u64;
        if input_length > limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                limits.maximum_input_bytes(),
                input_length,
            ));
        }
        Ok(Self {
            input,
            next_index: 0,
            current_byte: 0,
            bits_remaining: 0,
            marker_padding_count: 0,
            work_units: 0,
            maximum_work_units: limits.maximum_work_units(),
        })
    }

    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        if self.bits_remaining == 0 {
            self.load_byte()?;
        }
        if self.bits_remaining == 0 || self.bits_remaining > 8 {
            return Err(DecodeError::malformed(
                self.next_index as u64,
                MalformedKind::InvalidBitStuffing,
            ));
        }
        self.bits_remaining = self.bits_remaining.checked_sub(1).ok_or_else(|| {
            DecodeError::malformed(self.next_index as u64, MalformedKind::ArithmeticOverflow)
        })?;
        let bit = (self.current_byte >> self.bits_remaining) & 1;
        self.work_units = self.work_units.checked_add(1).ok_or_else(|| {
            DecodeError::malformed(self.next_index as u64, MalformedKind::ArithmeticOverflow)
        })?;
        if self.work_units > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.work_units,
            ));
        }
        Ok(bit != 0)
    }

    pub const fn bytes_consumed(&self) -> usize {
        self.next_index
    }

    pub const fn marker_padding_count(&self) -> u64 {
        self.marker_padding_count
    }

    pub fn validate_predictable_termination(&self) -> Result<(), DecodeError> {
        if self.next_index == 0 {
            return if self.input.len() == 1 && self.input[0] == 0x55 {
                Ok(())
            } else {
                Err(invalid_code_block())
            };
        }
        if self.next_index != self.input.len() || self.bits_remaining > 8 {
            return Err(invalid_code_block());
        }
        if self.bits_remaining == 0 {
            return Ok(());
        }
        let unread_mask = u8::MAX >> (8 - self.bits_remaining);
        let expected = 0x55_u8 >> (8 - self.bits_remaining);
        if self.current_byte & unread_mask != expected {
            return Err(invalid_code_block());
        }
        Ok(())
    }

    fn load_byte(&mut self) -> Result<(), DecodeError> {
        let next = if self.next_index < self.input.len() {
            self.input[self.next_index]
        } else {
            0xff
        };
        let stuffed = self.current_byte == 0xff;
        if stuffed && next > 0x8f {
            self.current_byte = 0xff;
            self.bits_remaining = 8;
            self.marker_padding_count =
                self.marker_padding_count.checked_add(1).ok_or_else(|| {
                    DecodeError::malformed(
                        self.next_index as u64,
                        MalformedKind::ArithmeticOverflow,
                    )
                })?;
            return Ok(());
        }
        if self.next_index < self.input.len() {
            self.next_index = self.next_index.checked_add(1).ok_or_else(|| {
                DecodeError::malformed(self.next_index as u64, MalformedKind::ArithmeticOverflow)
            })?;
        }
        self.current_byte = next;
        self.bits_remaining = if stuffed { 7 } else { 8 };
        Ok(())
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Tier1PassKind {
    SignificancePropagation,
    MagnitudeRefinement,
    Cleanup,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtPassGroup {
    pub cleanup_passes: u8,
    pub refinement_passes: u8,
    pub placeholder_passes: u8,
    pub skipped_bitplanes: u8,
}

impl HtPassGroup {
    pub fn from_packet_passes(passes: u8) -> Result<Self, DecodeError> {
        if passes == 0 || passes > 164 {
            return Err(invalid_code_block());
        }
        let placeholder_passes = crate::refinement::ht_placeholder_passes(passes);
        let skipped_bitplanes = placeholder_passes / 3;
        let substantive_passes = crate::refinement::ht_substantive_passes(passes);
        Ok(Self {
            cleanup_passes: placeholder_passes
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?,
            refinement_passes: substantive_passes
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?,
            placeholder_passes,
            skipped_bitplanes,
        })
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum HtStreamDirection {
    Forward,
    Reverse,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtSubstreamView<'a> {
    bytes: &'a [u8],
    offset: u32,
    direction: HtStreamDirection,
}

impl<'a> HtSubstreamView<'a> {
    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub const fn offset(&self) -> u32 {
        self.offset
    }

    pub const fn direction(&self) -> HtStreamDirection {
        self.direction
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtCleanupSegment<'a> {
    encoded: &'a [u8],
    scup: u16,
    mag_sgn: HtSubstreamView<'a>,
    mel_vlc: HtSubstreamView<'a>,
    mel: HtSubstreamView<'a>,
    vlc: HtSubstreamView<'a>,
}

impl<'a> HtCleanupSegment<'a> {
    pub fn encoded(&self) -> &'a [u8] {
        self.encoded
    }

    pub const fn scup(&self) -> u16 {
        self.scup
    }

    pub const fn mag_sgn(&self) -> HtSubstreamView<'a> {
        self.mag_sgn
    }

    pub const fn mel_vlc(&self) -> HtSubstreamView<'a> {
        self.mel_vlc
    }

    pub const fn mel(&self) -> HtSubstreamView<'a> {
        self.mel
    }

    pub const fn vlc(&self) -> HtSubstreamView<'a> {
        self.vlc
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtBitPosition {
    pub byte: u16,
    pub bit: u8,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtForwardMagSgnReader<'a> {
    input: &'a [u8],
    next_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    current_is_physical: bool,
    previous_was_ff: bool,
    physical_bits_read: u64,
    fill_bits_read: u64,
    work_units: u64,
    maximum_work_units: u64,
}

impl<'a> HtForwardMagSgnReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if input.len() > MAX_HT_CLEANUP_BYTES {
            return Err(invalid_code_block());
        }
        Ok(Self {
            input,
            next_byte: 0,
            value: 0,
            next_bit: 0,
            last_bit: 0,
            has_byte: false,
            current_is_physical: false,
            previous_was_ff: false,
            physical_bits_read: 0,
            fill_bits_read: 0,
            work_units: 0,
            maximum_work_units: limits.maximum_work_units(),
        })
    }

    pub const fn physical_bits_read(&self) -> u64 {
        self.physical_bits_read
    }

    pub const fn fill_bits_read(&self) -> u64 {
        self.fill_bits_read
    }

    pub fn read_bits(&mut self, count: u8) -> Result<u64, DecodeError> {
        if count > 39 {
            return Err(invalid_code_block());
        }
        let mut value = 0_u64;
        let mut bit = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant bit <= count,
                decreases count - bit,
            )
        )]
        while bit < count {
            if bit >= 64 {
                return Err(invalid_code_block());
            }
            if self.read_bit()? {
                value |= 1_u64 << bit;
            }
            bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(value)
    }

    pub fn finish(&mut self) -> Result<(), DecodeError> {
        let mut remaining_bits = self
            .input
            .len()
            .checked_mul(8)
            .ok_or_else(arithmetic_overflow)?;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases remaining_bits,)
        )]
        while self.has_pending_physical_bits() {
            if remaining_bits == 0 {
                return Err(invalid_code_block());
            }
            remaining_bits -= 1;
            if !self.read_bit()? {
                return Err(invalid_code_block());
            }
        }
        Ok(())
    }

    fn has_pending_physical_bits(&self) -> bool {
        (self.has_byte && self.current_is_physical && self.next_bit <= self.last_bit)
            || self.next_byte < self.input.len()
    }

    fn read_bit(&mut self) -> Result<bool, DecodeError> {
        if !self.has_byte || self.next_bit > self.last_bit {
            self.load_byte()?;
        }
        if !self.has_byte || self.next_bit > self.last_bit {
            return Err(invalid_code_block());
        }
        if self.next_bit >= 8 {
            return Err(invalid_code_block());
        }
        let bit = self.value >> self.next_bit & 1 != 0;
        self.next_bit = self
            .next_bit
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.current_is_physical {
            self.physical_bits_read = self
                .physical_bits_read
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        } else {
            self.fill_bits_read = self
                .fill_bits_read
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        self.work_units = self
            .work_units
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.work_units > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.work_units,
            ));
        }
        Ok(bit)
    }

    fn load_byte(&mut self) -> Result<(), DecodeError> {
        let stuffed = self.previous_was_ff;
        if self.next_byte < self.input.len() {
            let value = *self
                .input
                .get(self.next_byte)
                .ok_or_else(invalid_code_block)?;
            if !crate::refinement::ht_forward_stuffing_valid(stuffed, value) {
                return Err(DecodeError::malformed(
                    self.next_byte as u64,
                    MalformedKind::InvalidBitStuffing,
                ));
            }
            self.value = value;
            self.current_is_physical = true;
            self.next_byte = self
                .next_byte
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        } else {
            self.value = crate::refinement::ht_magsgn_fill_value();
            self.current_is_physical = false;
        }
        self.next_bit = 0;
        self.last_bit = crate::refinement::ht_forward_data_bits(stuffed) - 1;
        self.has_byte = true;
        self.previous_was_ff = self.value == 0xff;
        Ok(())
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtMelBitReader<'a> {
    input: &'a [u8],
    next_byte: usize,
    current_byte: usize,
    value: u8,
    next_bit: i8,
    previous_was_ff: bool,
    bits_read: u64,
    maximum_work_units: u64,
}

impl<'a> HtMelBitReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if input.is_empty() || input.len() > MAX_HT_SCUP - 1 {
            return Err(invalid_code_block());
        }
        let mut reader = Self {
            input,
            next_byte: 0,
            current_byte: 0,
            value: 0,
            next_bit: -1,
            previous_was_ff: false,
            bits_read: 0,
            maximum_work_units: limits.maximum_work_units(),
        };
        reader.load_byte()?;
        Ok(reader)
    }

    pub fn next_position(&self) -> Option<HtBitPosition> {
        if self.next_bit < 0 {
            None
        } else {
            Some(HtBitPosition {
                byte: u16::try_from(self.current_byte).ok()?,
                bit: u8::try_from(self.next_bit).ok()?,
            })
        }
    }

    pub const fn bits_read(&self) -> u64 {
        self.bits_read
    }

    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        if self.next_bit < 0 {
            self.load_byte()?;
        }
        if self.next_bit < 0 {
            return Err(invalid_code_block());
        }
        let bit_index = u8::try_from(self.next_bit).map_err(|_| arithmetic_overflow())?;
        if bit_index >= 8 {
            return Err(invalid_code_block());
        }
        let bit = (self.value >> bit_index) & 1 != 0;
        self.next_bit -= 1;
        self.bits_read = self
            .bits_read
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.bits_read > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.bits_read,
            ));
        }
        Ok(bit)
    }

    fn load_byte(&mut self) -> Result<(), DecodeError> {
        if self.next_byte >= self.input.len() {
            self.next_bit = -1;
            return Ok(());
        }
        let index = self.next_byte;
        let mut value = *self.input.get(index).ok_or_else(invalid_code_block)?;
        if index + 1 == self.input.len() {
            value |= 0x0f;
        }
        if !crate::refinement::ht_mel_stuffing_valid(self.previous_was_ff, value) {
            return Err(DecodeError::malformed(
                index as u64,
                MalformedKind::InvalidBitStuffing,
            ));
        }
        self.current_byte = index;
        self.value = value;
        self.next_bit = if self.previous_was_ff { 6 } else { 7 };
        self.previous_was_ff = value == 0xff;
        self.next_byte = self
            .next_byte
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtReverseVlcReader<'a> {
    input: &'a [u8],
    current_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    later_byte_requires_unstuffing: bool,
    bits_read: u64,
    maximum_work_units: u64,
}

impl<'a> HtReverseVlcReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if input.len() < 2 || input.len() > MAX_HT_SCUP {
            return Err(invalid_code_block());
        }
        let current_byte = input.len().checked_sub(2).ok_or_else(arithmetic_overflow)?;
        let value = *input.get(current_byte).ok_or_else(invalid_code_block)?;
        let nibble = value >> 4;
        Ok(Self {
            input,
            current_byte,
            value,
            next_bit: 4,
            last_bit: if nibble & 0x07 == 0x07 { 6 } else { 7 },
            has_byte: true,
            later_byte_requires_unstuffing: value | 0x0f > 0x8f,
            bits_read: 0,
            maximum_work_units: limits.maximum_work_units(),
        })
    }

    pub fn next_position(&self) -> Option<HtBitPosition> {
        if !self.has_byte {
            None
        } else {
            Some(HtBitPosition {
                byte: u16::try_from(self.current_byte).ok()?,
                bit: self.next_bit,
            })
        }
    }

    pub const fn bits_read(&self) -> u64 {
        self.bits_read
    }

    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        if !self.has_byte || self.next_bit >= 8 {
            return Err(invalid_code_block());
        }
        let bit = (self.value >> self.next_bit) & 1 != 0;
        self.next_bit = self
            .next_bit
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        self.bits_read = self
            .bits_read
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.bits_read > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.bits_read,
            ));
        }
        if self.next_bit > self.last_bit {
            self.load_previous_byte()?;
        }
        Ok(bit)
    }

    fn load_previous_byte(&mut self) -> Result<(), DecodeError> {
        if self.current_byte == 0 {
            self.has_byte = false;
            return Ok(());
        }
        self.current_byte = self
            .current_byte
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        self.value = *self
            .input
            .get(self.current_byte)
            .ok_or_else(invalid_code_block)?;
        self.next_bit = 0;
        self.last_bit = crate::refinement::ht_reverse_data_bits(
            self.later_byte_requires_unstuffing,
            self.value,
        ) - 1;
        self.later_byte_requires_unstuffing = self.value > 0x8f;
        Ok(())
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtQuadMetadata {
    pub x: u16,
    pub y: u16,
    pub context: u8,
    pub initial_row: bool,
    pub significance: u8,
    /// Values of the embedded leading bits (e_1), one flag per sample.
    pub embedded_magnitude: u8,
    /// Flags selecting omitted leading bits (e_k), one flag per sample.
    pub embedded_bit_mask: u8,
    pub u_offset: bool,
    pub u_base: u8,
    pub codeword_bits: u8,
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, Eq, PartialEq))]
pub struct HtCleanupMetadata {
    pub width: u16,
    pub height: u16,
    pub quads: Vec<HtQuadMetadata>,
    pub significant_samples: u16,
    pub mel_bits: u32,
    pub vlc_bits: u32,
    pub mel_events: u32,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtRefinementSegment<'a> {
    encoded: &'a [u8],
    significance_propagation: HtSubstreamView<'a>,
    magnitude_refinement: HtSubstreamView<'a>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtForwardRefinementReader<'a> {
    input: &'a [u8],
    next_byte: usize,
    current_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    previous_was_ff: bool,
    physical_bits_read: u64,
    fill_bits_read: u64,
    maximum_work_units: u64,
}

impl<'a> HtForwardRefinementReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if input.len() > MAX_HT_REFINEMENT_BYTES {
            return Err(invalid_code_block());
        }
        Ok(Self {
            input,
            next_byte: 0,
            current_byte: 0,
            value: 0,
            next_bit: 0,
            last_bit: 0,
            has_byte: false,
            previous_was_ff: false,
            physical_bits_read: 0,
            fill_bits_read: 0,
            maximum_work_units: limits.maximum_work_units(),
        })
    }

    pub const fn physical_bits_read(&self) -> u64 {
        self.physical_bits_read
    }

    pub const fn fill_bits_read(&self) -> u64 {
        self.fill_bits_read
    }

    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        self.read_positioned_bit().map(|(bit, _)| bit)
    }

    fn read_positioned_bit(&mut self) -> Result<(bool, Option<HtBitPosition>), DecodeError> {
        if !self.has_byte || self.next_bit > self.last_bit {
            self.load_byte()?;
        }
        if !self.has_byte || self.next_bit > self.last_bit || self.next_bit >= 8 {
            return Err(invalid_code_block());
        }
        let position = if self.current_byte < self.input.len() {
            Some(HtBitPosition {
                byte: self.current_byte as u16,
                bit: self.next_bit,
            })
        } else {
            None
        };
        let bit = self.value >> self.next_bit & 1 != 0;
        self.next_bit = self
            .next_bit
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if position.is_some() {
            self.physical_bits_read = self
                .physical_bits_read
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        } else {
            self.fill_bits_read = self
                .fill_bits_read
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        let work = self
            .physical_bits_read
            .checked_add(self.fill_bits_read)
            .ok_or_else(arithmetic_overflow)?;
        if work > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                work,
            ));
        }
        Ok((bit, position))
    }

    fn load_byte(&mut self) -> Result<(), DecodeError> {
        let stuffed = self.previous_was_ff;
        if self.next_byte < self.input.len() {
            let value = *self
                .input
                .get(self.next_byte)
                .ok_or_else(invalid_code_block)?;
            if stuffed && value & 0x80 != 0 {
                return Err(DecodeError::malformed(
                    self.next_byte as u64,
                    MalformedKind::InvalidBitStuffing,
                ));
            }
            self.current_byte = self.next_byte;
            self.value = value;
            self.next_byte = self
                .next_byte
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        } else {
            self.current_byte = self.input.len();
            self.value = 0;
        }
        self.next_bit = 0;
        self.last_bit = if stuffed { 6 } else { 7 };
        self.has_byte = true;
        self.previous_was_ff = self.value == 0xff;
        Ok(())
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtReverseRefinementReader<'a> {
    input: &'a [u8],
    current_byte: usize,
    value: u8,
    next_bit: u8,
    last_bit: u8,
    has_byte: bool,
    later_requires_unstuffing: bool,
    physical_bits_read: u64,
    fill_bits_read: u64,
    maximum_work_units: u64,
}

impl<'a> HtReverseRefinementReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if input.len() > MAX_HT_REFINEMENT_BYTES {
            return Err(invalid_code_block());
        }
        let mut reader = Self {
            input,
            current_byte: input.len(),
            value: 0,
            next_bit: 0,
            last_bit: 7,
            has_byte: false,
            later_requires_unstuffing: true,
            physical_bits_read: 0,
            fill_bits_read: 0,
            maximum_work_units: limits.maximum_work_units(),
        };
        reader.load_previous_byte()?;
        Ok(reader)
    }

    pub const fn physical_bits_read(&self) -> u64 {
        self.physical_bits_read
    }

    pub const fn fill_bits_read(&self) -> u64 {
        self.fill_bits_read
    }

    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        self.read_positioned_bit().map(|(bit, _)| bit)
    }

    fn read_positioned_bit(&mut self) -> Result<(bool, Option<HtBitPosition>), DecodeError> {
        if !self.has_byte || self.next_bit > self.last_bit {
            self.load_previous_byte()?;
        }
        if self.has_byte && self.next_bit >= 8 {
            return Err(invalid_code_block());
        }
        let position = if self.has_byte {
            Some(HtBitPosition {
                byte: self.current_byte as u16,
                bit: self.next_bit,
            })
        } else {
            None
        };
        let bit = if self.has_byte {
            self.value >> self.next_bit & 1 != 0
        } else {
            false
        };
        if self.has_byte {
            self.next_bit = self
                .next_bit
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            self.physical_bits_read = self
                .physical_bits_read
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        } else {
            self.fill_bits_read = self
                .fill_bits_read
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        let work = self
            .physical_bits_read
            .checked_add(self.fill_bits_read)
            .ok_or_else(arithmetic_overflow)?;
        if work > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                work,
            ));
        }
        Ok((bit, position))
    }

    fn load_previous_byte(&mut self) -> Result<(), DecodeError> {
        if self.current_byte == 0 {
            self.has_byte = false;
            self.value = 0;
            self.next_bit = 0;
            self.last_bit = 7;
            return Ok(());
        }
        self.current_byte = self
            .current_byte
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        self.value = *self
            .input
            .get(self.current_byte)
            .ok_or_else(invalid_code_block)?;
        self.next_bit = 0;
        self.last_bit = if self.later_requires_unstuffing && self.value & 0x7f == 0x7f {
            6
        } else {
            7
        };
        self.later_requires_unstuffing = self.value > 0x8f;
        self.has_byte = true;
        Ok(())
    }
}

struct HtRefinementReaders<'a> {
    forward: HtForwardRefinementReader<'a>,
    reverse: Option<HtReverseRefinementReader<'a>>,
    claimed: Vec<u8>,
    stuffed: Vec<u8>,
}

impl<'a> HtRefinementReaders<'a> {
    fn new(
        segment: HtRefinementSegment<'a>,
        has_magnitude_refinement: bool,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        Ok(Self {
            forward: HtForwardRefinementReader::new(
                segment.significance_propagation().bytes(),
                limits,
            )?,
            reverse: if has_magnitude_refinement {
                Some(HtReverseRefinementReader::new(
                    segment.magnitude_refinement().bytes(),
                    limits,
                )?)
            } else {
                None
            },
            claimed: vec![0; segment.encoded().len()],
            stuffed: vec![0; segment.encoded().len()],
        })
    }

    fn claim(&mut self, position: Option<HtBitPosition>) -> Result<(), DecodeError> {
        let Some(position) = position else {
            return Ok(());
        };
        if position.bit >= 8 {
            return Err(invalid_code_block());
        }
        let byte = usize::from(position.byte);
        let mask = 1_u8 << position.bit;
        let claimed = self.claimed.get_mut(byte).ok_or_else(invalid_code_block)?;
        if !crate::refinement::ht_claim_available(*claimed & mask != 0) {
            return Err(invalid_code_block());
        }
        *claimed |= mask;
        Ok(())
    }

    fn read_forward(&mut self) -> Result<bool, DecodeError> {
        let (bit, position) = self.forward.read_positioned_bit()?;
        self.claim(position)?;
        Ok(bit)
    }

    fn read_reverse(&mut self) -> Result<bool, DecodeError> {
        let reverse = self.reverse.as_mut().ok_or_else(invalid_code_block)?;
        let (bit, position) = reverse.read_positioned_bit()?;
        if reverse.has_byte && reverse.last_bit == 6 {
            let stuffed = self
                .stuffed
                .get_mut(reverse.current_byte)
                .ok_or_else(invalid_code_block)?;
            *stuffed |= 0x80;
        }
        self.claim(position)?;
        Ok(bit)
    }

    fn finish(&self, encoded: &[u8]) -> Result<(), DecodeError> {
        if self.claimed.len() != encoded.len() || self.stuffed.len() != encoded.len() {
            return Err(invalid_code_block());
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= encoded.len(),
                decreases encoded.len() - index,
            )
        )]
        while index < encoded.len() {
            let value = *encoded.get(index).ok_or_else(invalid_code_block)?;
            let claimed = *self.claimed.get(index).ok_or_else(invalid_code_block)?;
            let stuffed = *self.stuffed.get(index).ok_or_else(invalid_code_block)?;
            if value & !(claimed | stuffed) != 0 {
                return Err(invalid_code_block());
            }
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(())
    }
}

impl<'a> HtRefinementSegment<'a> {
    pub fn encoded(&self) -> &'a [u8] {
        self.encoded
    }

    pub const fn significance_propagation(&self) -> HtSubstreamView<'a> {
        self.significance_propagation
    }

    pub const fn magnitude_refinement(&self) -> HtSubstreamView<'a> {
        self.magnitude_refinement
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct HtBlockSegments<'a> {
    cleanup: HtCleanupSegment<'a>,
    refinement: Option<HtRefinementSegment<'a>>,
    bytes: u32,
}

impl<'a> HtBlockSegments<'a> {
    pub const fn cleanup(&self) -> HtCleanupSegment<'a> {
        self.cleanup
    }

    pub const fn refinement(&self) -> Option<HtRefinementSegment<'a>> {
        self.refinement
    }

    pub const fn bytes(&self) -> u32 {
        self.bytes
    }
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1CodingStyle {
    pub block_coding: Tier1BlockCoding,
    pub force_high_throughput: bool,
    pub selective_arithmetic_coding_bypass: bool,
    pub reset_contexts: bool,
    pub terminate_all_passes: bool,
    pub vertical_causal_context: bool,
    pub predictable_termination: bool,
    pub segmentation_symbols: bool,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Tier1BlockCoding {
    #[default]
    Legacy,
    HighThroughput,
    Mixed,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum Tier1CodingMode {
    Mq,
    Raw,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1PassPlan {
    pub kind: Tier1PassKind,
    pub coding_mode: Tier1CodingMode,
    pub terminates_segment: bool,
    pub reset_contexts_after_pass: bool,
    pub validate_predictable_termination: bool,
    pub expect_segmentation_symbol: bool,
}

impl Tier1CodingStyle {
    pub fn from_code_block_style(value: u8) -> Result<Self, DecodeError> {
        let block_coding = Tier1BlockCoding::from_code_block_style(value)?;
        Ok(Self {
            block_coding,
            force_high_throughput: matches!(block_coding, Tier1BlockCoding::HighThroughput),
            selective_arithmetic_coding_bypass: value & 0x01 != 0,
            reset_contexts: value & 0x02 != 0,
            terminate_all_passes: value & 0x04 != 0,
            vertical_causal_context: value & 0x08 != 0,
            predictable_termination: value & 0x10 != 0,
            segmentation_symbols: value & 0x20 != 0,
        })
    }

    pub fn set_force_high_throughput(&mut self, required: bool) {
        self.force_high_throughput = required;
    }

    pub fn uses_raw_bypass(self, pass_index: u32) -> bool {
        self.selective_arithmetic_coding_bypass
            && pass_index >= 10
            && !matches!(pass_kind(pass_index), Tier1PassKind::Cleanup)
    }

    pub fn pass_plan(self, pass_index: u32) -> Tier1PassPlan {
        let kind = pass_kind(pass_index);
        let coding_mode = if self.uses_raw_bypass(pass_index) {
            Tier1CodingMode::Raw
        } else {
            Tier1CodingMode::Mq
        };
        let bypass_boundary = self.selective_arithmetic_coding_bypass
            && (pass_index == 9
                || (pass_index >= 10 && !matches!(kind, Tier1PassKind::SignificancePropagation)));
        let terminates_segment = self.terminate_all_passes || bypass_boundary;
        Tier1PassPlan {
            kind,
            coding_mode,
            terminates_segment,
            reset_contexts_after_pass: self.reset_contexts,
            validate_predictable_termination: self.predictable_termination
                && terminates_segment
                && matches!(coding_mode, Tier1CodingMode::Mq),
            expect_segmentation_symbol: self.segmentation_symbols
                && matches!(kind, Tier1PassKind::Cleanup),
        }
    }

    pub fn segment_passes(self, first_pass: u32, available_passes: u32) -> u32 {
        if available_passes == 0 {
            return 0;
        }
        if self.terminate_all_passes {
            return 1;
        }
        if !self.selective_arithmetic_coding_bypass {
            return available_passes;
        }
        if first_pass < 10 {
            return available_passes.min(10 - first_pass);
        }
        match pass_kind(first_pass) {
            Tier1PassKind::SignificancePropagation => available_passes.min(2),
            Tier1PassKind::MagnitudeRefinement | Tier1PassKind::Cleanup => 1,
        }
    }
}

impl Tier1BlockCoding {
    pub fn from_code_block_style(value: u8) -> Result<Self, DecodeError> {
        match value >> 6 {
            0 => Ok(Self::Legacy),
            1 if value & 0x37 == 0 => Ok(Self::HighThroughput),
            1 | 2 => Err(invalid_code_block()),
            3 if value & 0x05 == 0 => Ok(Self::Mixed),
            3 => Err(invalid_code_block()),
            _ => Err(invalid_code_block()),
        }
    }

    pub const fn uses_high_throughput(self) -> bool {
        !matches!(self, Self::Legacy)
    }

    pub const fn selects_high_throughput(self, first_contribution_passes: u8) -> bool {
        match self {
            Self::Legacy => false,
            Self::HighThroughput => true,
            Self::Mixed => first_contribution_passes <= 3,
        }
    }
}

pub const fn pass_kind(pass_index: u32) -> Tier1PassKind {
    match crate::refinement::tier1_pass_code(pass_index) {
        0 => Tier1PassKind::SignificancePropagation,
        1 => Tier1PassKind::MagnitudeRefinement,
        _ => Tier1PassKind::Cleanup,
    }
}

pub fn parse_ht_block_segments<'a>(
    cleanup: &'a [u8],
    refinement: Option<&'a [u8]>,
    limits: &ResourceLimits,
) -> Result<HtBlockSegments<'a>, DecodeError> {
    if cleanup.len() < 2 || cleanup.len() > MAX_HT_CLEANUP_BYTES {
        return Err(invalid_code_block());
    }
    let cleanup_bytes = cleanup.len() as u64;
    let refinement_bytes = match refinement {
        Some(bytes) => bytes.len() as u64,
        None => 0_u64,
    };
    if refinement_bytes > MAX_HT_REFINEMENT_BYTES as u64 {
        return Err(invalid_code_block());
    }
    let total_bytes = cleanup_bytes
        .checked_add(refinement_bytes)
        .ok_or_else(arithmetic_overflow)?;
    if total_bytes > limits.maximum_code_block_bytes() {
        return Err(DecodeError::limit(
            Resource::CodeBlockBytes,
            limits.maximum_code_block_bytes(),
            total_bytes,
        ));
    }

    let penultimate = *cleanup
        .get(cleanup.len() - 2)
        .ok_or_else(invalid_code_block)?;
    let last = *cleanup.last().ok_or_else(invalid_code_block)?;
    let scup = crate::refinement::ht_scup(penultimate, last);
    if scup < 2 {
        return Err(invalid_code_block());
    }
    if scup > MAX_HT_SCUP || scup > cleanup.len() {
        return Err(invalid_code_block());
    }
    let mag_sgn_end = crate::refinement::ht_magsgn_end(cleanup.len(), scup);
    let mel_end = cleanup
        .len()
        .checked_sub(1)
        .ok_or_else(arithmetic_overflow)?;
    if mag_sgn_end > mel_end || mel_end > cleanup.len() {
        return Err(invalid_code_block());
    }
    let mag_sgn_bytes = cleanup.get(..mag_sgn_end).ok_or_else(invalid_code_block)?;
    let mel_vlc_bytes = cleanup.get(mag_sgn_end..).ok_or_else(invalid_code_block)?;
    let mel_bytes = cleanup
        .get(mag_sgn_end..mel_end)
        .ok_or_else(invalid_code_block)?;
    let mag_sgn_offset = 0_u32;
    let mel_vlc_offset = u32::try_from(mag_sgn_end).map_err(|_| arithmetic_overflow())?;
    let cleanup_segment = HtCleanupSegment {
        encoded: cleanup,
        scup: u16::try_from(scup).map_err(|_| arithmetic_overflow())?,
        mag_sgn: HtSubstreamView {
            bytes: mag_sgn_bytes,
            offset: mag_sgn_offset,
            direction: HtStreamDirection::Forward,
        },
        mel_vlc: HtSubstreamView {
            bytes: mel_vlc_bytes,
            offset: mel_vlc_offset,
            direction: HtStreamDirection::Forward,
        },
        mel: HtSubstreamView {
            bytes: mel_bytes,
            offset: mel_vlc_offset,
            direction: HtStreamDirection::Forward,
        },
        vlc: HtSubstreamView {
            bytes: mel_vlc_bytes,
            offset: mel_vlc_offset,
            direction: HtStreamDirection::Reverse,
        },
    };
    let refinement_segment = match refinement {
        Some(encoded) => Some(HtRefinementSegment {
            encoded,
            significance_propagation: HtSubstreamView {
                bytes: encoded,
                offset: u32::try_from(cleanup.len()).map_err(|_| arithmetic_overflow())?,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: encoded,
                offset: u32::try_from(cleanup.len()).map_err(|_| arithmetic_overflow())?,
                direction: HtStreamDirection::Reverse,
            },
        }),
        None => None,
    };
    Ok(HtBlockSegments {
        cleanup: cleanup_segment,
        refinement: refinement_segment,
        bytes: u32::try_from(total_bytes).map_err(|_| arithmetic_overflow())?,
    })
}

struct HtCleanupReaders<'a> {
    mel: HtMelBitReader<'a>,
    vlc: HtReverseVlcReader<'a>,
    mel_last_byte: Option<u16>,
    vlc_last_byte: Option<u16>,
    terminal_byte: u16,
    mel_state: u8,
    mel_zero_events: u8,
    mel_terminating_one: bool,
    mel_events: u32,
    work_units: u64,
    maximum_work_units: u64,
}

impl<'a> HtCleanupReaders<'a> {
    fn new(segment: HtCleanupSegment<'a>, limits: &ResourceLimits) -> Result<Self, DecodeError> {
        Ok(Self {
            mel: HtMelBitReader::new(segment.mel().bytes(), limits)?,
            vlc: HtReverseVlcReader::new(segment.vlc().bytes(), limits)?,
            mel_last_byte: None,
            vlc_last_byte: None,
            terminal_byte: u16::try_from(
                segment
                    .vlc()
                    .bytes()
                    .len()
                    .checked_sub(2)
                    .ok_or_else(invalid_code_block)?,
            )
            .map_err(|_| arithmetic_overflow())?,
            mel_state: 0,
            mel_zero_events: 0,
            mel_terminating_one: false,
            mel_events: 0,
            work_units: 0,
            maximum_work_units: limits.maximum_work_units(),
        })
    }

    fn tick(&mut self) -> Result<(), DecodeError> {
        self.work_units = self
            .work_units
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.work_units > self.maximum_work_units {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.work_units,
            ));
        }
        Ok(())
    }

    fn can_claim_byte(&self, direction: HtStreamDirection, byte: u16) -> bool {
        let value = match self.vlc.input.get(usize::from(byte)) {
            Some(value) => *value,
            None => return false,
        };
        match direction {
            HtStreamDirection::Forward => match self.vlc_last_byte {
                Some(vlc) => crate::refinement::ht_cleanup_byte_claims_valid(
                    byte,
                    vlc,
                    self.terminal_byte,
                    value,
                ),
                None => byte <= self.terminal_byte,
            },
            HtStreamDirection::Reverse => match self.mel_last_byte {
                Some(mel) => crate::refinement::ht_cleanup_byte_claims_valid(
                    mel,
                    byte,
                    self.terminal_byte,
                    value,
                ),
                None => byte <= self.terminal_byte,
            },
        }
    }

    fn read_mel_bit(&mut self) -> Result<bool, DecodeError> {
        if self.mel.next_position().is_none() {
            self.mel.load_byte()?;
        }
        let position = self.mel.next_position().ok_or_else(invalid_code_block)?;
        if !self.can_claim_byte(HtStreamDirection::Forward, position.byte) {
            return Err(invalid_code_block());
        }
        let bit = self.mel.read_bit()?;
        self.mel_last_byte = Some(position.byte);
        self.tick()?;
        Ok(bit)
    }

    fn read_vlc_bit(&mut self) -> Result<bool, DecodeError> {
        let position = self.vlc.next_position().ok_or_else(invalid_code_block)?;
        if !self.can_claim_byte(HtStreamDirection::Reverse, position.byte) {
            return Err(invalid_code_block());
        }
        let bit = self.vlc.read_bit()?;
        self.vlc_last_byte = Some(position.byte);
        self.tick()?;
        Ok(bit)
    }

    fn peek_vlc(&self, count: u8) -> u16 {
        let mut copy = self.vlc;
        let mut value = 0_u16;
        let mut bit = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant bit <= count,
                decreases count - bit,
            )
        )]
        while bit < count {
            let available = match copy.next_position() {
                Some(vlc) => self.can_claim_byte(HtStreamDirection::Reverse, vlc.byte),
                None => false,
            };
            if !available {
                break;
            }
            let Ok(decoded) = copy.read_bit() else {
                break;
            };
            if decoded {
                if bit >= 16 {
                    break;
                }
                value |= 1_u16 << bit;
            }
            bit += 1;
        }
        value
    }

    fn advance_vlc(&mut self, count: u8) -> Result<(), DecodeError> {
        let mut consumed = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant consumed <= count,
                decreases count - consumed,
            )
        )]
        while consumed < count {
            let _ = self.read_vlc_bit()?;
            consumed = consumed.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(())
    }

    fn mel_event(&mut self) -> Result<bool, DecodeError> {
        if self.mel_zero_events > 0 {
            self.mel_zero_events = self
                .mel_zero_events
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
            self.mel_events = self
                .mel_events
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            return Ok(false);
        }
        if self.mel_terminating_one {
            self.mel_terminating_one = false;
            self.mel_events = self
                .mel_events
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            return Ok(true);
        }

        if self.mel_state > 12 {
            return Err(invalid_code_block());
        }
        let exponent = crate::refinement::ht_mel_exponent(self.mel_state);
        if self.read_mel_bit()? {
            self.mel_zero_events = 1_u8 << exponent;
            self.mel_state = crate::refinement::ht_mel_next_state(self.mel_state, true);
        } else {
            let mut suffix = 0_u8;
            let mut decoded = 0_u8;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant decoded <= exponent,
                    decreases exponent - decoded,
                )
            )]
            while decoded < exponent {
                suffix <<= 1;
                if self.read_mel_bit()? {
                    suffix |= 1;
                }
                decoded = decoded.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            self.mel_zero_events = suffix;
            self.mel_terminating_one = true;
            self.mel_state = crate::refinement::ht_mel_next_state(self.mel_state, false);
        }
        if self.mel_zero_events > 0 {
            self.mel_zero_events = self
                .mel_zero_events
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
            self.mel_events = self
                .mel_events
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            Ok(false)
        } else {
            self.mel_terminating_one = false;
            self.mel_events = self
                .mel_events
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            Ok(true)
        }
    }

    fn decode_quad_word(&mut self, initial: bool, context: u8) -> Result<u16, DecodeError> {
        if context > 7 {
            return Err(invalid_code_block());
        }
        let lookahead = usize::from(self.peek_vlc(7) & 0x7f);
        let index = crate::refinement::ht_vlc_table_index(context, lookahead as u8);
        let table = if initial {
            &HT_VLC_INITIAL
        } else {
            &HT_VLC_NON_INITIAL
        };
        let mut word = *table.get(index).ok_or_else(invalid_code_block)?;
        if context == 0 && !self.mel_event()? {
            word = 0;
        }
        let length = (word & 0x07) as u8;
        if !crate::refinement::ht_vlc_word_valid(word, length) {
            return Err(invalid_code_block());
        }
        self.advance_vlc(length)?;
        self.tick()?;
        Ok(word)
    }

    fn read_prefix(&mut self) -> Result<(u8, u8, u8), DecodeError> {
        if self.read_vlc_bit()? {
            return Ok((1, 0, 1));
        }
        if self.read_vlc_bit()? {
            return Ok((2, 0, 2));
        }
        if self.read_vlc_bit()? {
            Ok((3, 1, 3))
        } else {
            Ok((5, 5, 3))
        }
    }

    fn read_suffix(&mut self, length: u8) -> Result<u8, DecodeError> {
        let mut value = 0_u8;
        let mut bit = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant bit <= length,
                decreases length - bit,
            )
        )]
        while bit < length {
            if self.read_vlc_bit()? {
                if bit >= 8 {
                    return Err(invalid_code_block());
                }
                value |= 1_u8 << bit;
            }
            bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(value)
    }

    fn prefix_value(&mut self) -> Result<(u8, u8), DecodeError> {
        let (base, suffix_length, prefix_length) = self.read_prefix()?;
        let suffix = self.read_suffix(suffix_length)?;
        let value = base.checked_add(suffix).ok_or_else(arithmetic_overflow)?;
        Ok((value, prefix_length))
    }

    fn decode_initial_u(&mut self, mode: u8) -> Result<[u8; 2], DecodeError> {
        let mut values = [1_u8, 1_u8];
        match mode {
            0 => {}
            1 | 2 => {
                let (value, _) = self.prefix_value()?;
                values[if mode == 1 { 0 } else { 1 }] =
                    value.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            3 => {
                let (base_0, suffix_0, prefix_0) = self.read_prefix()?;
                if prefix_0 > 2 {
                    values[1] = u8::from(self.read_vlc_bit()?)
                        .checked_add(2)
                        .ok_or_else(arithmetic_overflow)?;
                    values[0] = base_0
                        .checked_add(self.read_suffix(suffix_0)?)
                        .and_then(|value| value.checked_add(1))
                        .ok_or_else(arithmetic_overflow)?;
                } else {
                    let (base_1, suffix_1, _) = self.read_prefix()?;
                    values[0] = base_0
                        .checked_add(self.read_suffix(suffix_0)?)
                        .and_then(|value| value.checked_add(1))
                        .ok_or_else(arithmetic_overflow)?;
                    values[1] = base_1
                        .checked_add(self.read_suffix(suffix_1)?)
                        .and_then(|value| value.checked_add(1))
                        .ok_or_else(arithmetic_overflow)?;
                }
            }
            4 => {
                let (base_0, suffix_0, _) = self.read_prefix()?;
                let (base_1, suffix_1, _) = self.read_prefix()?;
                values[0] = u8::try_from(crate::refinement::ht_uvlc_value(
                    base_0,
                    self.read_suffix(suffix_0)?,
                    3,
                ))
                .map_err(|_| arithmetic_overflow())?;
                values[1] = u8::try_from(crate::refinement::ht_uvlc_value(
                    base_1,
                    self.read_suffix(suffix_1)?,
                    3,
                ))
                .map_err(|_| arithmetic_overflow())?;
            }
            _ => return Err(invalid_code_block()),
        }
        Ok(values)
    }

    fn decode_non_initial_u(&mut self, mode: u8) -> Result<[u8; 2], DecodeError> {
        let mut values = [1_u8, 1_u8];
        match mode {
            0 => {}
            1 | 2 => {
                let (value, _) = self.prefix_value()?;
                values[if mode == 1 { 0 } else { 1 }] =
                    value.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            3 => {
                let (base_0, suffix_0, _) = self.read_prefix()?;
                let (base_1, suffix_1, _) = self.read_prefix()?;
                values[0] = u8::try_from(crate::refinement::ht_uvlc_value(
                    base_0,
                    self.read_suffix(suffix_0)?,
                    1,
                ))
                .map_err(|_| arithmetic_overflow())?;
                values[1] = u8::try_from(crate::refinement::ht_uvlc_value(
                    base_1,
                    self.read_suffix(suffix_1)?,
                    1,
                ))
                .map_err(|_| arithmetic_overflow())?;
            }
            _ => return Err(invalid_code_block()),
        }
        Ok(values)
    }

    fn finish(&self) -> Result<(), DecodeError> {
        match (self.mel_last_byte, self.vlc_last_byte) {
            (Some(mel), Some(vlc)) => {
                let value = *self
                    .vlc
                    .input
                    .get(usize::from(mel))
                    .ok_or_else(invalid_code_block)?;
                if crate::refinement::ht_cleanup_byte_claims_valid(
                    mel,
                    vlc,
                    self.terminal_byte,
                    value,
                ) {
                    Ok(())
                } else {
                    Err(invalid_code_block())
                }
            }
            _ => Ok(()),
        }
    }
}

pub fn decode_ht_cleanup_metadata(
    cleanup: &[u8],
    width: u16,
    height: u16,
    maximum_u: u8,
    limits: &ResourceLimits,
) -> Result<HtCleanupMetadata, DecodeError> {
    let segments = parse_ht_block_segments(cleanup, None, limits)?;
    decode_ht_cleanup_segment_metadata(segments.cleanup(), width, height, maximum_u, limits)
}

fn decode_ht_cleanup_segment_metadata(
    cleanup: HtCleanupSegment<'_>,
    width: u16,
    height: u16,
    maximum_u: u8,
    limits: &ResourceLimits,
) -> Result<HtCleanupMetadata, DecodeError> {
    if width == 0 || height == 0 || maximum_u == 0 || maximum_u > MAX_HT_MAGNITUDE_BITS {
        return Err(invalid_code_block());
    }
    let samples = u32::from(width)
        .checked_mul(u32::from(height))
        .ok_or_else(arithmetic_overflow)?;
    if samples > 4_096 {
        return Err(invalid_code_block());
    }
    let quads_per_row = usize::from(width)
        .checked_add(1)
        .and_then(|value| value.checked_div(2))
        .ok_or_else(arithmetic_overflow)?;
    let quad_rows = usize::from(height)
        .checked_add(1)
        .and_then(|value| value.checked_div(2))
        .ok_or_else(arithmetic_overflow)?;
    let quad_count = quads_per_row
        .checked_mul(quad_rows)
        .ok_or_else(arithmetic_overflow)?;
    let mut readers = HtCleanupReaders::new(cleanup, limits)?;
    let mut quads = Vec::with_capacity(quad_count);
    let mut previous_patterns = vec![0_u8; quads_per_row];
    let mut significant_samples = 0_u16;
    let mut quad_row = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant quad_row <= quad_rows,
            decreases quad_rows - quad_row,
        )
    )]
    while quad_row < quad_rows {
        let initial = quad_row == 0;
        let mut current_patterns = vec![0_u8; quads_per_row];
        let mut left_context = 0_u8;
        let mut pair = 0_usize;
        let mut pair_passes = quads_per_row
            .checked_add(1)
            .and_then(|value| value.checked_div(2))
            .ok_or_else(arithmetic_overflow)?;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases pair_passes,)
        )]
        while pair < quads_per_row {
            let mut words = [0_u16; 2];
            let mut contexts = [0_u8; 2];
            let mut member = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant member <= 2,
                    decreases 2 - member,
                )
            )]
            while member < 2 {
                let quad_index = pair.checked_add(member).ok_or_else(arithmetic_overflow)?;
                if quad_index >= quads_per_row {
                    break;
                }
                let context = if initial {
                    left_context
                } else {
                    let north_pattern = *previous_patterns
                        .get(quad_index)
                        .ok_or_else(invalid_code_block)?;
                    let north_west_pattern = match quad_index.checked_sub(1) {
                        Some(index) => *previous_patterns
                            .get(index)
                            .ok_or_else(invalid_code_block)?,
                        None => 0,
                    };
                    let north_east_index =
                        quad_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
                    let north_east_pattern = match previous_patterns.get(north_east_index) {
                        Some(pattern) => *pattern,
                        None => 0,
                    };
                    crate::refinement::ht_noninitial_vlc_context(
                        left_context,
                        north_west_pattern,
                        north_pattern,
                        north_east_pattern,
                    )
                };
                let word = readers.decode_quad_word(initial, context)?;
                let significance = ((word >> 4) & 0x0f) as u8;
                *words.get_mut(member).ok_or_else(invalid_code_block)? = word;
                *contexts.get_mut(member).ok_or_else(invalid_code_block)? = context;
                *current_patterns
                    .get_mut(quad_index)
                    .ok_or_else(invalid_code_block)? = significance;
                left_context = if initial {
                    (significance & 0x01) | ((significance & 0x0e) >> 1)
                } else if significance & 0x0c != 0 {
                    2
                } else {
                    0
                };
                member = member.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }

            let mut mode = u8::from(words[0] & 0x08 != 0);
            mode |= u8::from(words[1] & 0x08 != 0) << 1;
            if initial && mode == 3 && readers.mel_event()? {
                mode = 4;
            }
            let u_values = if initial {
                readers.decode_initial_u(mode)?
            } else {
                readers.decode_non_initial_u(mode)?
            };

            member = 0;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant member <= 2,
                    decreases 2 - member,
                )
            )]
            while member < 2 {
                let quad_index = pair.checked_add(member).ok_or_else(arithmetic_overflow)?;
                if quad_index >= quads_per_row {
                    break;
                }
                let word = *words.get(member).ok_or_else(invalid_code_block)?;
                let significance = *current_patterns
                    .get(quad_index)
                    .ok_or_else(invalid_code_block)?;
                let u_value = *u_values.get(member).ok_or_else(invalid_code_block)?;
                if u_value > maximum_u {
                    return Err(invalid_code_block());
                }
                let x = u16::try_from(quad_index.checked_mul(2).ok_or_else(arithmetic_overflow)?)
                    .map_err(|_| arithmetic_overflow())?;
                let y = u16::try_from(quad_row.checked_mul(2).ok_or_else(arithmetic_overflow)?)
                    .map_err(|_| arithmetic_overflow())?;
                if !crate::refinement::ht_quad_origin_valid(x, y, width, height) {
                    return Err(invalid_code_block());
                }
                let mut sample = 0_u8;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant sample <= 4,
                        decreases 4 - sample,
                    )
                )]
                while sample < 4 {
                    if significance & (1_u8 << sample) != 0 {
                        let sample_x = x
                            .checked_add(u16::from(sample >> 1))
                            .ok_or_else(arithmetic_overflow)?;
                        let sample_y = y
                            .checked_add(u16::from(sample & 1))
                            .ok_or_else(arithmetic_overflow)?;
                        if !crate::refinement::ht_quad_sample_in_bounds(x, y, sample, width, height)
                            || sample_x >= width
                            || sample_y >= height
                        {
                            return Err(invalid_code_block());
                        }
                        significant_samples = significant_samples
                            .checked_add(1)
                            .ok_or_else(arithmetic_overflow)?;
                    }
                    sample = sample.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                quads.push(HtQuadMetadata {
                    x,
                    y,
                    context: *contexts.get(member).ok_or_else(invalid_code_block)?,
                    initial_row: initial,
                    significance,
                    embedded_magnitude: ((word >> 8) & 0x0f) as u8,
                    embedded_bit_mask: ((word >> 12) & 0x0f) as u8,
                    u_offset: word & 0x08 != 0,
                    u_base: u_value,
                    codeword_bits: (word & 0x07) as u8,
                });
                readers.tick()?;
                member = member.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            pair = pair.checked_add(2).ok_or_else(arithmetic_overflow)?;
            pair_passes = pair_passes.checked_sub(1).ok_or_else(arithmetic_overflow)?;
        }
        previous_patterns = current_patterns;
        quad_row = quad_row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    readers.finish()?;
    Ok(HtCleanupMetadata {
        width,
        height,
        quads,
        significant_samples,
        mel_bits: u32::try_from(readers.mel.bits_read()).map_err(|_| arithmetic_overflow())?,
        vlc_bits: u32::try_from(readers.vlc.bits_read()).map_err(|_| arithmetic_overflow())?,
        mel_events: readers.mel_events,
    })
}

pub fn complete_ht_kappa(
    u_base: u8,
    significance: u8,
    north_west_exponent: u8,
    north_east_exponent: u8,
    maximum_u: u8,
) -> Result<u8, DecodeError> {
    if u_base == 0
        || significance & 0xf0 != 0
        || maximum_u == 0
        || maximum_u > MAX_HT_MAGNITUDE_BITS
    {
        return Err(invalid_code_block());
    }
    let gamma = significance & significance.wrapping_sub(1) != 0;
    let exponent = north_west_exponent.max(north_east_exponent);
    if u_base > u8::MAX - exponent {
        return Err(arithmetic_overflow());
    }
    let completed = crate::refinement::ht_kappa_completion(u_base, gamma, exponent);
    if completed > maximum_u {
        return Err(invalid_code_block());
    }
    Ok(completed)
}

fn reconstruct_ht_magnitude(
    reader: &mut HtForwardMagSgnReader<'_>,
    completed_u: u8,
    embedded_bit: bool,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Result<(Magnitude, bool, u8), DecodeError> {
    if completed_u == 0
        || completed_u > MAX_HT_MAGNITUDE_BITS
        || decoded_bitplanes == 0
        || decoded_bitplanes > MAX_TIER1_BITPLANES
    {
        return Err(invalid_code_block());
    }
    let magnitude_bits = crate::refinement::ht_magnitude_payload_bits(completed_u, embedded_bit);
    let mut bin_center = Magnitude::ZERO;
    let mut negative = false;
    let mut exponent = 0_u8;
    let mut bit = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= magnitude_bits,
            decreases magnitude_bits - bit,
        )
    )]
    while bit < magnitude_bits {
        if reader.read_bit()? {
            if crate::refinement::ht_magnitude_sign(bit, true) {
                negative = true;
            }
            bin_center = bin_center.checked_add(Magnitude::single_bit(u16::from(bit))?)?;
            exponent = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    if embedded_value {
        bin_center = bin_center.checked_add(Magnitude::single_bit(u16::from(magnitude_bits))?)?;
        exponent = magnitude_bits
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    if crate::refinement::ht_bin_center_odd(bin_center.low_u64()) != bin_center.low_u64() {
        bin_center = bin_center.checked_add(Magnitude::from_u64(1))?;
        exponent = exponent.max(1);
    }
    let centered = bin_center.checked_add(Magnitude::from_u64(2))?;
    let shift = decoded_bitplanes - 1;
    let magnitude = centered.checked_shl(shift)?.shift_right(1);
    if magnitude.is_zero() {
        return Err(invalid_code_block());
    }
    Ok((magnitude, negative, exponent))
}

fn reconstruct_ht_cleanup_plane(
    plane: &CodeBlockPlane,
    cleanup: HtCleanupSegment<'_>,
    metadata: &HtCleanupMetadata,
    maximum_u: u8,
    decoded_bitplanes: u16,
    limits: &ResourceLimits,
) -> Result<(CodeBlockPlane, Tier1PassStatistics), DecodeError> {
    if metadata.width == 0 {
        return Err(invalid_code_block());
    }
    let mut output = CodeBlockPlane::new(plane.width(), plane.height())?;
    let mut reader = HtForwardMagSgnReader::new(cleanup.mag_sgn().bytes(), limits)?;
    let quads_per_row = usize::from(metadata.width)
        .checked_add(1)
        .and_then(|value| value.checked_div(2))
        .ok_or_else(arithmetic_overflow)?;
    if quads_per_row == 0 {
        return Err(invalid_code_block());
    }
    let exponent_count = quads_per_row
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let mut previous_exponents = vec![0_u8; exponent_count];
    let mut current_exponents = vec![0_u8; exponent_count];
    let mut statistics = Tier1PassStatistics::default();
    let mut quad_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant quad_index <= metadata.quads.len(),
            decreases metadata.quads.len() - quad_index,
        )
    )]
    while quad_index < metadata.quads.len() {
        let quad = *metadata
            .quads
            .get(quad_index)
            .ok_or_else(invalid_code_block)?;
        let column = quad_index
            .checked_rem(quads_per_row)
            .ok_or_else(arithmetic_overflow)?;
        if column == 0 {
            let mut exponent_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant exponent_index <= current_exponents.len(),
                    decreases current_exponents.len() - exponent_index,
                )
            )]
            while exponent_index < current_exponents.len() {
                *current_exponents
                    .get_mut(exponent_index)
                    .ok_or_else(invalid_code_block)? = 0;
                exponent_index = exponent_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
        }
        let next_column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
        let completed_u = if quad.initial_row {
            if quad.u_base > maximum_u {
                return Err(invalid_code_block());
            }
            quad.u_base
        } else {
            complete_ht_kappa(
                quad.u_base,
                quad.significance,
                *previous_exponents
                    .get(column)
                    .ok_or_else(invalid_code_block)?,
                *previous_exponents
                    .get(next_column)
                    .ok_or_else(invalid_code_block)?,
                maximum_u,
            )?
        };
        let mut sample = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant sample <= 4,
                decreases 4 - sample,
            )
        )]
        while sample < 4 {
            if sample >= 8 {
                return Err(invalid_code_block());
            }
            let x = quad
                .x
                .checked_add(u16::from(sample >> 1))
                .ok_or_else(arithmetic_overflow)?;
            let y = quad
                .y
                .checked_add(u16::from(sample & 1))
                .ok_or_else(arithmetic_overflow)?;
            if x < metadata.width && y < metadata.height {
                statistics.scanned(1)?;
                if quad.significance & (1_u8 << sample) != 0 {
                    let embedded_bit = quad.embedded_bit_mask & (1_u8 << sample) != 0;
                    let embedded_value = quad.embedded_magnitude & (1_u8 << sample) != 0;
                    let (magnitude, negative, exponent) = reconstruct_ht_magnitude(
                        &mut reader,
                        completed_u,
                        embedded_bit,
                        embedded_value,
                        decoded_bitplanes,
                    )?;
                    output.mark_significant_magnitude(x, y, magnitude, negative)?;
                    statistics.decoded_symbols(1)?;
                    statistics.became_significant()?;
                    if sample == 1 {
                        let entry = current_exponents
                            .get_mut(column)
                            .ok_or_else(invalid_code_block)?;
                        *entry = (*entry).max(exponent);
                    } else if sample == 3 {
                        *current_exponents
                            .get_mut(next_column)
                            .ok_or_else(invalid_code_block)? = exponent;
                    }
                }
            }
            sample = sample.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        if next_column == quads_per_row {
            core::mem::swap(&mut previous_exponents, &mut current_exponents);
        }
        quad_index = quad_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    reader.finish()?;
    Ok((output, statistics))
}

fn ht_significance_magnitude(decoded_bitplanes: u16) -> Result<Magnitude, DecodeError> {
    if !(2..=MAX_TIER1_BITPLANES).contains(&decoded_bitplanes) {
        return Err(invalid_code_block());
    }
    Magnitude::from_u64(3)
        .checked_shl(decoded_bitplanes - 2)
        .map(|centered| centered.shift_right(1))
}

fn ht_refinement_delta(decoded_bitplanes: u16) -> Result<Magnitude, DecodeError> {
    if !(2..=MAX_TIER1_BITPLANES).contains(&decoded_bitplanes) {
        return Err(invalid_code_block());
    }
    if decoded_bitplanes == 2 {
        Ok(Magnitude::from_u64(1))
    } else {
        Magnitude::single_bit(decoded_bitplanes - 3)
    }
}

fn copy_ht_refinement_bytes(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    let mut output = Vec::with_capacity(input.len());
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= input.len(),
            decreases input.len() - index,
        )
    )]
    while index < input.len() {
        output.push(*input.get(index).ok_or_else(invalid_code_block)?);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(output)
}

fn decode_ht_refinement_plane(
    cleanup_plane: &CodeBlockPlane,
    segment: HtRefinementSegment<'_>,
    refinement_passes: u8,
    decoded_bitplanes: u16,
    vertical_causal_context: bool,
    limits: &ResourceLimits,
) -> Result<(CodeBlockPlane, Tier1PassStatistics), DecodeError> {
    if refinement_passes == 0 || refinement_passes > 2 || decoded_bitplanes < 2 {
        return Err(invalid_code_block());
    }
    let mut output = cleanup_plane.duplicate()?;
    let mut readers = HtRefinementReaders::new(segment, refinement_passes == 2, limits)?;
    let cleanup_significant: Vec<bool> = cleanup_plane
        .coefficients()
        .iter()
        .map(|coefficient| coefficient.significant)
        .collect();
    let mut statistics = Tier1PassStatistics::default();

    if refinement_passes == 2 {
        let delta = ht_refinement_delta(decoded_bitplanes)?;
        let output_height = output.height();
        let output_width = output.width();
        let mut stripe_y = 0_u16;
        let mut stripe_passes = output_height
            .checked_add(3)
            .and_then(|value| value.checked_div(4))
            .ok_or_else(arithmetic_overflow)?;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases stripe_passes,)
        )]
        while stripe_y < output_height {
            let stripe_rows = crate::refinement::ht_stripe_rows(output_height, stripe_y);
            let mut x = 0_u16;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(decreases output_width - x,)
            )]
            while x < output_width {
                let mut row = 0_u16;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(decreases stripe_rows - row,)
                )]
                while row < stripe_rows {
                    let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                    statistics.scanned(1)?;
                    let index = output.index(x, y)?;
                    if crate::refinement::ht_magref_eligible(
                        *cleanup_significant
                            .get(index)
                            .ok_or_else(invalid_code_block)?,
                    ) {
                        let bit = readers.read_reverse()?;
                        // The final upper half-bin truncates to the existing integer magnitude.
                        let adjustment = if decoded_bitplanes == 2 && bit {
                            Magnitude::ZERO
                        } else {
                            delta
                        };
                        output.apply_ht_refinement_decision(x, y, adjustment, bit)?;
                        statistics.decoded_symbols(1)?;
                        statistics.refined()?;
                    }
                    row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            stripe_y = stripe_y.checked_add(4).ok_or_else(arithmetic_overflow)?;
            stripe_passes = stripe_passes
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
        }
    }

    let significance_magnitude = ht_significance_magnitude(decoded_bitplanes)?;
    let mut significance_plane = output.duplicate()?;
    let output_height = output.height();
    let output_width = output.width();
    let mut stripe_y = 0_u16;
    let mut stripe_passes = output_height
        .checked_add(3)
        .and_then(|value| value.checked_div(4))
        .ok_or_else(arithmetic_overflow)?;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(decreases stripe_passes,)
    )]
    while stripe_y < output_height {
        let stripe_rows = crate::refinement::ht_stripe_rows(output_height, stripe_y);
        let mut patch_x = 0_u16;
        let mut patch_passes = output_width
            .checked_add(3)
            .and_then(|value| value.checked_div(4))
            .ok_or_else(arithmetic_overflow)?;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(decreases patch_passes,)
        )]
        while patch_x < output_width {
            let patch_end = crate::refinement::ht_patch_end(patch_x, output_width);
            let mut newly_significant = Vec::new();
            let mut x = patch_x;
            #[cfg_attr(verus_keep_ghost, verus_spec(decreases patch_end - x,))]
            while x < patch_end {
                let mut row = 0_u16;
                #[cfg_attr(verus_keep_ghost, verus_spec(decreases stripe_rows - row,))]
                while row < stripe_rows {
                    let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                    statistics.scanned(1)?;
                    if !significance_plane.coefficient(x, y)?.significant {
                        let summary = significance_plane.neighbor_summary_with_causality(
                            x,
                            y,
                            vertical_causal_context,
                        )?;
                        if crate::refinement::ht_sigprop_eligible(
                            false,
                            significant_neighbor_count(summary),
                        ) {
                            let significant = readers.read_forward()?;
                            statistics.decoded_symbols(1)?;
                            if significant {
                                significance_plane.mark_significant_magnitude(
                                    x,
                                    y,
                                    significance_magnitude,
                                    false,
                                )?;
                                newly_significant.push((x, y));
                            }
                        }
                    }
                    row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
                x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            let mut index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= newly_significant.len(),
                    decreases newly_significant.len() - index,
                )
            )]
            while index < newly_significant.len() {
                let (x, y) = *newly_significant
                    .get(index)
                    .ok_or_else(invalid_code_block)?;
                let negative = readers.read_forward()?;
                output.mark_significant_magnitude(x, y, significance_magnitude, negative)?;
                statistics.decoded_symbols(1)?;
                statistics.became_significant()?;
                index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            patch_x = patch_x.checked_add(4).ok_or_else(arithmetic_overflow)?;
            patch_passes = patch_passes
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        stripe_y = stripe_y.checked_add(4).ok_or_else(arithmetic_overflow)?;
        stripe_passes = stripe_passes
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    readers.finish(segment.encoded())?;
    Ok((output, statistics))
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockSegmentAccounting {
    maximum_passes: u32,
    maximum_bytes: u64,
    total_passes: u32,
    total_bytes: u64,
    segments: u32,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CoefficientState {
    /// Decoded magnitude bits; unfinished legacy passes retain a bit prefix.
    pub magnitude: u64,
    magnitude_high: [u64; 5],
    legacy_bitplane: Option<u16>,
    pub negative: bool,
    pub significant: bool,
    pub refined: bool,
}

impl CoefficientState {
    pub(crate) fn signed_magnitude(&self) -> Result<SignedMagnitude, DecodeError> {
        let mut magnitude = if self.significant {
            self.wide_magnitude()
        } else {
            Magnitude::ZERO
        };
        if let (true, Some(bitplane)) = (self.significant, self.legacy_bitplane) {
            let midpoint = if bitplane <= 64 {
                Magnitude::from_u64(crate::refinement::tier1_midpoint_delta(bitplane))
            } else {
                Magnitude::single_bit(bitplane - 1)?
            };
            magnitude = magnitude.checked_add(midpoint)?;
        }
        Ok(SignedMagnitude::new(
            magnitude,
            self.significant && self.negative,
        ))
    }
    pub fn magnitude_limb(&self, index: usize) -> Option<u64> {
        if index == 0 {
            Some(self.magnitude)
        } else {
            let high_index = index.checked_sub(1)?;
            if high_index < self.magnitude_high.len() {
                Some(self.magnitude_high[high_index])
            } else {
                None
            }
        }
    }

    pub fn wide_magnitude(&self) -> Magnitude {
        let mut limbs = [0_u64; 6];
        limbs[0] = self.magnitude;
        let mut index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.magnitude_high.len(),
                decreases self.magnitude_high.len() - index,
            )
        )]
        while index < self.magnitude_high.len() {
            limbs[index + 1] = self.magnitude_high[index];
            index += 1;
        }
        Magnitude::from_limbs(limbs)
    }

    fn from_magnitude(
        magnitude: Magnitude,
        negative: bool,
        significant: bool,
        refined: bool,
    ) -> Result<Self, DecodeError> {
        let mut output = Self {
            magnitude: magnitude.low_u64(),
            magnitude_high: [0; 5],
            legacy_bitplane: None,
            negative,
            significant,
            refined,
        };
        output.set_magnitude(magnitude)?;
        Ok(output)
    }

    fn set_magnitude(&mut self, magnitude: Magnitude) -> Result<(), DecodeError> {
        self.magnitude = magnitude.low_u64();
        let mut index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.magnitude_high.len(),
                decreases self.magnitude_high.len() - index,
            )
        )]
        while index < self.magnitude_high.len() {
            self.magnitude_high[index] =
                magnitude.limb(index + 1).ok_or_else(arithmetic_overflow)?;
            index += 1;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct NeighborSummary {
    pub horizontal_significant: u8,
    pub vertical_significant: u8,
    pub diagonal_significant: u8,
    pub horizontal_sign_balance: i8,
    pub vertical_sign_balance: i8,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum SubbandOrientation {
    Ll,
    Lh,
    Hl,
    Hh,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct SignContext {
    pub context: u8,
    pub predicted_negative: bool,
}

pub fn zero_coding_context(summary: NeighborSummary, orientation: SubbandOrientation) -> u8 {
    let (horizontal, vertical) = if matches!(orientation, SubbandOrientation::Hl) {
        (summary.vertical_significant, summary.horizontal_significant)
    } else {
        (summary.horizontal_significant, summary.vertical_significant)
    };
    let diagonal = summary.diagonal_significant;
    crate::refinement::tier1_zero_context(
        u16::from(horizontal),
        u16::from(vertical),
        u16::from(diagonal),
        matches!(orientation, SubbandOrientation::Hh),
    )
}

pub fn sign_context(summary: NeighborSummary) -> SignContext {
    let mut horizontal = signum_i8(summary.horizontal_sign_balance);
    let mut vertical = signum_i8(summary.vertical_sign_balance);
    if horizontal < 0 {
        horizontal = 1;
        vertical = if vertical < 0 {
            1
        } else if vertical > 0 {
            -1
        } else {
            0
        };
    }

    const fn signum_i8(value: i8) -> i8 {
        if value < 0 {
            -1
        } else if value > 0 {
            1
        } else {
            0
        }
    }
    let offset = crate::refinement::tier1_sign_offset(horizontal, vertical);
    let predicted_negative = crate::refinement::tier1_predicted_negative(
        summary.horizontal_sign_balance,
        summary.vertical_sign_balance,
    );
    SignContext {
        context: 9 + offset,
        predicted_negative,
    }
}

pub fn magnitude_refinement_context(coefficient: CoefficientState, summary: NeighborSummary) -> u8 {
    let neighbors = u16::from(summary.horizontal_significant)
        + u16::from(summary.vertical_significant)
        + u16::from(summary.diagonal_significant);
    crate::refinement::tier1_refinement_context(coefficient.refined, neighbors)
}

pub fn initialize_tier1_contexts(decoder: &mut MqDecoder<'_>) -> Result<(), DecodeError> {
    decoder.reset_contexts();
    decoder.set_context(0, 4, false)?;
    decoder.set_context(RUN_LENGTH_CONTEXT, 3, false)?;
    decoder.set_context(UNIFORM_CONTEXT, 46, false)?;
    Ok(())
}

pub fn reset_tier1_contexts_after_pass(
    decoder: &mut MqDecoder<'_>,
    style: Tier1CodingStyle,
) -> Result<(), DecodeError> {
    if style.reset_contexts {
        initialize_tier1_contexts(decoder)?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct SignificanceStep {
    pub zero_coding_context: u8,
    pub sign_context: Option<u8>,
    pub became_significant: bool,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1BitplaneState {
    width: u16,
    height: u16,
    bitplane: u16,
    significant_before: Vec<bool>,
    significance_visited: Vec<bool>,
    significance_propagation_complete: bool,
    magnitude_refinement_complete: bool,
    cleanup_complete: bool,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1PassStatistics {
    pub coefficients_scanned: u32,
    pub coding_symbols: u32,
    pub newly_significant: u32,
    pub refined_coefficients: u32,
    pub run_mode_columns: u32,
}

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct Tier1SegmentDecode {
    pub passes: u32,
    pub bytes: u32,
    pub statistics: Tier1PassStatistics,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
struct LegacySegmentState {
    plane: CodeBlockPlane,
    next_pass: u32,
    bitplane: u16,
    bitplane_state: Option<Tier1BitplaneState>,
    mq_context_state: Option<MqContextState>,
    reset_contexts_before_mq: bool,
    decoded_segments: u32,
    decoded_bytes: u64,
    input: Vec<u8>,
    passes: u32,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct Tier1CodeBlockDecoder {
    plane: CodeBlockPlane,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
    maximum_passes: u32,
    next_pass: u32,
    bitplane: u16,
    zero_bitplanes: Option<u16>,
    bitplane_state: Option<Tier1BitplaneState>,
    mq_context_state: Option<MqContextState>,
    reset_contexts_before_mq: bool,
    decoded_segments: u32,
    decoded_bytes: u64,
    legacy_segment: Option<LegacySegmentState>,
    legacy_decode_work: u64,
    ht_cleanup_plane: Option<CodeBlockPlane>,
    ht_refinement_data: Vec<u8>,
    ht_refinement_passes: u8,
    ht_decoded_bitplanes: u16,
    ht_current_set_has_cleanup: bool,
    ht_sets_seen: u16,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
}

impl Tier1PassStatistics {
    fn scanned(&mut self, count: u32) -> Result<(), DecodeError> {
        self.coefficients_scanned = self
            .coefficients_scanned
            .checked_add(count)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    fn decoded_symbols(&mut self, count: u32) -> Result<(), DecodeError> {
        self.coding_symbols = self
            .coding_symbols
            .checked_add(count)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    fn became_significant(&mut self) -> Result<(), DecodeError> {
        self.newly_significant = self
            .newly_significant
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    fn refined(&mut self) -> Result<(), DecodeError> {
        self.refined_coefficients = self
            .refined_coefficients
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    fn used_run_mode(&mut self) -> Result<(), DecodeError> {
        self.run_mode_columns = self
            .run_mode_columns
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    fn merge(&mut self, other: Self) -> Result<(), DecodeError> {
        self.scanned(other.coefficients_scanned)?;
        self.decoded_symbols(other.coding_symbols)?;
        self.newly_significant = self
            .newly_significant
            .checked_add(other.newly_significant)
            .ok_or_else(arithmetic_overflow)?;
        self.refined_coefficients = self
            .refined_coefficients
            .checked_add(other.refined_coefficients)
            .ok_or_else(arithmetic_overflow)?;
        self.run_mode_columns = self
            .run_mode_columns
            .checked_add(other.run_mode_columns)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }
}

impl Tier1CodeBlockDecoder {
    pub fn new(
        width: u16,
        height: u16,
        significant_bitplanes: u16,
        orientation: SubbandOrientation,
        style: Tier1CodingStyle,
    ) -> Result<Self, DecodeError> {
        if significant_bitplanes == 0 || significant_bitplanes > MAX_TIER1_BITPLANES {
            return Err(invalid_code_block());
        }
        let bitplane = significant_bitplanes
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        let maximum_passes = u32::from(significant_bitplanes)
            .checked_mul(3)
            .and_then(|passes| passes.checked_sub(2))
            .ok_or_else(arithmetic_overflow)?;
        Ok(Self {
            plane: CodeBlockPlane::new(width, height)?,
            orientation,
            style,
            maximum_passes,
            next_pass: 0,
            bitplane,
            zero_bitplanes: None,
            bitplane_state: None,
            mq_context_state: None,
            reset_contexts_before_mq: false,
            decoded_segments: 0,
            decoded_bytes: 0,
            legacy_segment: None,
            legacy_decode_work: 0,
            ht_cleanup_plane: None,
            ht_refinement_data: Vec::new(),
            ht_refinement_passes: 0,
            ht_decoded_bitplanes: 0,
            ht_current_set_has_cleanup: false,
            ht_sets_seen: 0,
            allow_multiple_ht_sets: false,
            ht_magnitude_bound: MAX_HT_MAGNITUDE_BITS,
        })
    }

    pub const fn plane(&self) -> &CodeBlockPlane {
        &self.plane
    }

    pub const fn block_coding(&self) -> Tier1BlockCoding {
        self.style.block_coding
    }

    pub const fn accepts_high_throughput_route(&self, high_throughput: bool) -> bool {
        !self.style.force_high_throughput || high_throughput
    }

    pub const fn next_pass(&self) -> u32 {
        self.next_pass
    }

    pub const fn maximum_passes(&self) -> u32 {
        self.maximum_passes
    }

    pub const fn decoded_segments(&self) -> u32 {
        self.decoded_segments
    }

    pub const fn decoded_bytes(&self) -> u64 {
        self.decoded_bytes
    }

    pub(crate) fn set_zero_bitplanes(&mut self, zero_bitplanes: u16) -> Result<(), DecodeError> {
        if let Some(previous) = self.zero_bitplanes {
            return if previous == zero_bitplanes {
                Ok(())
            } else {
                Err(invalid_code_block())
            };
        }
        if self.next_pass != 0 || self.decoded_segments != 0 || zero_bitplanes > self.bitplane {
            return Err(invalid_code_block());
        }
        let bitplane = self
            .bitplane
            .checked_sub(zero_bitplanes)
            .ok_or_else(invalid_code_block)?;
        let maximum_passes = u32::from(bitplane)
            .checked_mul(3)
            .and_then(|passes| passes.checked_add(1))
            .ok_or_else(arithmetic_overflow)?;
        self.bitplane = bitplane;
        self.maximum_passes = maximum_passes;
        self.zero_bitplanes = Some(zero_bitplanes);
        Ok(())
    }

    pub fn set_multiple_ht_sets_allowed(&mut self, allowed: bool) {
        self.allow_multiple_ht_sets = allowed;
    }

    pub fn set_ht_magnitude_bound(&mut self, bound: u8) -> Result<(), DecodeError> {
        if bound == 0 || bound > MAX_HT_MAGNITUDE_BITS {
            return Err(invalid_code_block());
        }
        self.ht_magnitude_bound = bound;
        Ok(())
    }

    pub const fn is_complete(&self) -> bool {
        if self.active_high_throughput() {
            self.next_pass > 0
        } else {
            self.next_pass == self.maximum_passes
        }
    }

    pub const fn active_high_throughput(&self) -> bool {
        matches!(self.style.block_coding, Tier1BlockCoding::HighThroughput)
            || (matches!(self.style.block_coding, Tier1BlockCoding::Mixed)
                && self.ht_cleanup_plane.is_some())
    }

    pub(crate) fn decode_legacy_contribution(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<(), DecodeError> {
        if passes == 0 {
            return Err(invalid_code_block());
        }
        let next_bytes = self
            .decoded_bytes
            .checked_add(input.len() as u64)
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockBytes,
                limits.maximum_code_block_bytes(),
                next_bytes,
            ));
        }
        let replay_passes = match &self.legacy_segment {
            Some(segment) => segment.passes,
            None => 0,
        }
        .checked_add(u32::from(passes))
        .ok_or_else(arithmetic_overflow)?;
        let work = (self.plane.coefficients().len() as u64)
            .checked_mul(u64::from(replay_passes))
            .and_then(|value| value.checked_add(next_bytes))
            .and_then(|value| value.checked_add(self.legacy_decode_work))
            .ok_or_else(arithmetic_overflow)?;
        if work > limits.maximum_work_units() {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                limits.maximum_work_units(),
                work,
            ));
        }
        self.legacy_decode_work = work;
        let next_pass = self
            .next_pass
            .checked_add(u32::from(passes))
            .ok_or_else(arithmetic_overflow)?;
        let last_pass = next_pass.checked_sub(1).ok_or_else(invalid_code_block)?;
        if self.legacy_segment.is_none()
            && (next_pass == self.maximum_passes
                || self.style.pass_plan(last_pass).terminates_segment)
        {
            self.decode_legacy_segment(input, u32::from(passes), limits)?;
            return Ok(());
        }
        let mut segment = match self.legacy_segment.take() {
            Some(segment) => segment,
            None => LegacySegmentState {
                plane: self.plane.clone(),
                next_pass: self.next_pass,
                bitplane: self.bitplane,
                bitplane_state: self.bitplane_state.clone(),
                mq_context_state: self.mq_context_state,
                reset_contexts_before_mq: self.reset_contexts_before_mq,
                decoded_segments: self.decoded_segments,
                decoded_bytes: self.decoded_bytes,
                input: Vec::new(),
                passes: 0,
            },
        };
        segment.input.extend_from_slice(input);
        segment.passes = replay_passes;
        self.plane = segment.plane.clone();
        self.next_pass = segment.next_pass;
        self.bitplane = segment.bitplane;
        self.bitplane_state = segment.bitplane_state.clone();
        self.mq_context_state = segment.mq_context_state;
        self.reset_contexts_before_mq = segment.reset_contexts_before_mq;
        self.decoded_segments = segment.decoded_segments;
        self.decoded_bytes = segment.decoded_bytes;
        // Layer boundaries can truncate an unterminated arithmetic segment.
        // Replay its bounded prefix so virtual end-fill is never resumed as real input.
        self.decode_legacy_segment(&segment.input, segment.passes, limits)?;
        let last_pass = self
            .next_pass
            .checked_sub(1)
            .ok_or_else(invalid_code_block)?;
        if self.next_pass < self.maximum_passes
            && !self.style.pass_plan(last_pass).terminates_segment
        {
            self.legacy_segment = Some(segment);
        }
        Ok(())
    }

    pub fn decode_segment(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        if input.is_empty() || passes == 0 {
            return Err(invalid_code_block());
        }
        if matches!(self.style.block_coding, Tier1BlockCoding::HighThroughput)
            || (matches!(self.style.block_coding, Tier1BlockCoding::Mixed)
                && self.ht_cleanup_plane.is_some())
        {
            let grouping = HtPassGroup::from_packet_passes(passes)?;
            if grouping.refinement_passes != 0 {
                return Err(invalid_code_block());
            }
            let mut staged = self.clone();
            let mut placeholder_passes = grouping.placeholder_passes;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(decreases placeholder_passes,)
            )]
            while placeholder_passes > 0 {
                staged.skip_high_throughput_segment(1, limits)?;
                staged.skip_high_throughput_segment(2, limits)?;
                placeholder_passes = placeholder_passes
                    .checked_sub(3)
                    .ok_or_else(arithmetic_overflow)?;
            }
            let decoded = staged.decode_high_throughput_segments(input, 1, None, 0, limits)?;
            *self = staged;
            return Ok(Tier1SegmentDecode {
                passes: u32::from(passes),
                ..decoded
            });
        }
        self.decode_legacy_segment(input, u32::from(passes), limits)
    }

    fn decode_legacy_segment(
        &mut self,
        input: &[u8],
        pass_count: u32,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        if input.is_empty() || pass_count == 0 {
            return Err(invalid_code_block());
        }
        let next_pass = self
            .next_pass
            .checked_add(pass_count)
            .ok_or_else(arithmetic_overflow)?;
        if next_pass > limits.maximum_code_block_passes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockPasses,
                u64::from(limits.maximum_code_block_passes()),
                u64::from(next_pass),
            ));
        }
        let next_bytes = self
            .decoded_bytes
            .checked_add(input.len() as u64)
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockBytes,
                limits.maximum_code_block_bytes(),
                next_bytes,
            ));
        }
        if next_pass > self.maximum_passes
            || self.style.segment_passes(self.next_pass, pass_count) != pass_count
        {
            return Err(invalid_code_block());
        }

        let coding_mode = self.style.pass_plan(self.next_pass).coding_mode;
        let mut statistics = Tier1PassStatistics::default();
        if matches!(coding_mode, Tier1CodingMode::Mq) {
            let mut decoder = MqDecoder::new(input, limits)?;
            if self.reset_contexts_before_mq || self.mq_context_state.is_none() {
                initialize_tier1_contexts(&mut decoder)?;
                self.reset_contexts_before_mq = false;
            } else if let Some(context_state) = self.mq_context_state {
                decoder.restore_context_state(context_state);
            }
            let mut decoded = 0_u32;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant decoded <= pass_count,
                    decreases pass_count - decoded,
                )
            )]
            while decoded < pass_count {
                let plan = self.style.pass_plan(self.next_pass);
                if !matches!(plan.coding_mode, Tier1CodingMode::Mq) {
                    return Err(invalid_code_block());
                }
                statistics.merge(self.decode_mq_pass(&mut decoder, plan.kind)?)?;
                self.advance_pass(plan.kind)?;
                reset_tier1_contexts_after_pass(&mut decoder, self.style)?;
                decoded = decoded.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            if self.style.predictable_termination {
                decoder.validate_predictable_termination()?;
            }
            self.mq_context_state = Some(decoder.context_state());
        } else {
            let mut reader = RawBitReader::new(input, limits)?;
            let mut decoded = 0_u32;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant decoded <= pass_count,
                    decreases pass_count - decoded,
                )
            )]
            while decoded < pass_count {
                let plan = self.style.pass_plan(self.next_pass);
                if !matches!(plan.coding_mode, Tier1CodingMode::Raw) {
                    return Err(invalid_code_block());
                }
                statistics.merge(self.decode_raw_pass(&mut reader, plan.kind)?)?;
                self.advance_pass(plan.kind)?;
                if self.style.reset_contexts {
                    self.reset_contexts_before_mq = true;
                }
                decoded = decoded.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            if self.style.predictable_termination {
                reader.validate_predictable_termination()?;
            }
        }

        self.decoded_segments = self
            .decoded_segments
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_bytes = self
            .decoded_bytes
            .checked_add(input.len() as u64)
            .ok_or_else(arithmetic_overflow)?;
        Ok(Tier1SegmentDecode {
            passes: pass_count,
            bytes: u32::try_from(input.len()).map_err(|_| arithmetic_overflow())?,
            statistics,
        })
    }

    pub fn decode_high_throughput_segments(
        &mut self,
        cleanup: &[u8],
        cleanup_passes: u8,
        refinement: Option<&[u8]>,
        refinement_passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        if !self.style.block_coding.uses_high_throughput()
            || !self.next_pass.is_multiple_of(3)
            || cleanup_passes != 1
            || refinement_passes > 2
            || (refinement_passes == 0) != refinement.is_none()
        {
            return Err(invalid_code_block());
        }
        if self.ht_sets_seen > 0 && !self.allow_multiple_ht_sets {
            return Err(invalid_code_block());
        }
        let pass_count = u32::from(cleanup_passes)
            .checked_add(u32::from(refinement_passes))
            .ok_or_else(arithmetic_overflow)?;
        let next_pass = self
            .next_pass
            .checked_add(pass_count)
            .ok_or_else(arithmetic_overflow)?;
        if next_pass > self.maximum_passes {
            return Err(invalid_code_block());
        }
        if next_pass > limits.maximum_code_block_passes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockPasses,
                u64::from(limits.maximum_code_block_passes()),
                u64::from(next_pass),
            ));
        }
        let significant_bitplanes = self
            .maximum_passes
            .checked_add(2)
            .and_then(|passes| passes.checked_div(3))
            .and_then(|value| u16::try_from(value).ok())
            .ok_or_else(arithmetic_overflow)?;
        if refinement_passes > 0 && significant_bitplanes < 2 {
            return Err(invalid_code_block());
        }
        let segments = parse_ht_block_segments(cleanup, refinement, limits)?;
        let next_bytes = self
            .decoded_bytes
            .checked_add(u64::from(segments.bytes()))
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockBytes,
                limits.maximum_code_block_bytes(),
                next_bytes,
            ));
        }
        let substantive_passes = u64::from(refinement_passes)
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        let coefficient_work = (self.plane.coefficients().len() as u64)
            .checked_mul(substantive_passes)
            .ok_or_else(arithmetic_overflow)?;
        let work = coefficient_work
            .checked_add(u64::from(segments.bytes()))
            .and_then(|value| value.checked_add(u64::from(pass_count)))
            .ok_or_else(arithmetic_overflow)?;
        if work > limits.maximum_work_units() {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                limits.maximum_work_units(),
                work,
            ));
        }
        let skipped_bitplanes =
            u16::try_from(self.next_pass / 3).map_err(|_| arithmetic_overflow())?;
        let missing_msbs = self.zero_bitplanes.unwrap_or(0);
        let maximum_u = crate::refinement::part15_cleanup_u_bound(
            missing_msbs,
            skipped_bitplanes,
            self.ht_magnitude_bound,
        );
        self.decode_ht_coefficient_symbols(
            segments,
            pass_count,
            maximum_u,
            skipped_bitplanes,
            limits,
        )
    }

    fn decode_ht_coefficient_symbols(
        &mut self,
        segments: HtBlockSegments<'_>,
        pass_count: u32,
        maximum_u: u8,
        skipped_bitplanes: u16,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        let metadata = decode_ht_cleanup_segment_metadata(
            segments.cleanup(),
            self.plane.width(),
            self.plane.height(),
            maximum_u,
            limits,
        )?;
        let significant_bitplanes = self
            .maximum_passes
            .checked_add(2)
            .and_then(|passes| passes.checked_div(3))
            .and_then(|value| u16::try_from(value).ok())
            .ok_or_else(arithmetic_overflow)?;
        let decoded_bitplanes = significant_bitplanes
            .checked_sub(skipped_bitplanes)
            .ok_or_else(arithmetic_overflow)?;
        let (plane, statistics) = reconstruct_ht_cleanup_plane(
            &self.plane,
            segments.cleanup(),
            &metadata,
            maximum_u,
            decoded_bitplanes,
            limits,
        )?;
        let cleanup_plane = plane.duplicate()?;
        let mut output = plane;
        let mut statistics = statistics;
        self.ht_refinement_data.clear();
        self.ht_refinement_passes = 0;
        if let Some(refinement) = segments.refinement() {
            let refinement_passes =
                u8::try_from(pass_count.saturating_sub(1)).map_err(|_| arithmetic_overflow())?;
            let (refined, refinement_statistics) = decode_ht_refinement_plane(
                &cleanup_plane,
                refinement,
                refinement_passes,
                decoded_bitplanes,
                self.style.vertical_causal_context,
                limits,
            )?;
            output = refined;
            statistics.merge(refinement_statistics)?;
            self.ht_refinement_data = copy_ht_refinement_bytes(refinement.encoded())?;
            self.ht_refinement_passes = refinement_passes;
        }
        self.plane = output;
        self.ht_cleanup_plane = Some(cleanup_plane);
        self.ht_current_set_has_cleanup = true;
        self.ht_decoded_bitplanes = decoded_bitplanes;
        self.ht_sets_seen = self
            .ht_sets_seen
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        self.next_pass = self
            .next_pass
            .checked_add(pass_count)
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_segments = self
            .decoded_segments
            .checked_add(if segments.refinement().is_some() {
                2
            } else {
                1
            })
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_bytes = self
            .decoded_bytes
            .checked_add(u64::from(segments.bytes()))
            .ok_or_else(arithmetic_overflow)?;
        Ok(Tier1SegmentDecode {
            passes: pass_count,
            bytes: segments.bytes(),
            statistics,
        })
    }

    pub fn skip_high_throughput_segment(
        &mut self,
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        if !self.style.block_coding.uses_high_throughput() || passes == 0 || passes > 2 {
            return Err(invalid_code_block());
        }
        let phase = self.next_pass % 3;
        if (phase == 0 && passes != 1)
            || (phase != 0 && u32::from(passes) > 3_u32.saturating_sub(phase))
        {
            return Err(invalid_code_block());
        }
        let next_pass = self
            .next_pass
            .checked_add(u32::from(passes))
            .ok_or_else(arithmetic_overflow)?;
        if next_pass > self.maximum_passes {
            return Err(invalid_code_block());
        }
        if next_pass > limits.maximum_code_block_passes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockPasses,
                u64::from(limits.maximum_code_block_passes()),
                u64::from(next_pass),
            ));
        }
        if phase == 0 {
            if !crate::refinement::ht_replacement_allowed(
                phase,
                self.ht_current_set_has_cleanup,
                true,
            ) {
                return Err(invalid_code_block());
            }
            if self.ht_sets_seen > 0 {
                if !crate::refinement::ht_multiple_set_allowed(
                    self.ht_sets_seen,
                    self.allow_multiple_ht_sets,
                ) {
                    return Err(invalid_code_block());
                }
                self.ht_sets_seen = self
                    .ht_sets_seen
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
            self.ht_current_set_has_cleanup = false;
            self.ht_refinement_data.clear();
            self.ht_refinement_passes = 0;
        } else if self.ht_current_set_has_cleanup {
            return Err(invalid_code_block());
        }
        self.next_pass = next_pass;
        self.decoded_segments = self
            .decoded_segments
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(Tier1SegmentDecode {
            passes: u32::from(passes),
            bytes: 0,
            statistics: Tier1PassStatistics::default(),
        })
    }

    pub const fn ht_current_set_has_cleanup(&self) -> bool {
        self.ht_current_set_has_cleanup
    }

    pub fn decode_high_throughput_refinement(
        &mut self,
        input: &[u8],
        passes: u8,
        limits: &ResourceLimits,
    ) -> Result<Tier1SegmentDecode, DecodeError> {
        if !self.style.block_coding.uses_high_throughput()
            || self.next_pass == 0
            || !self.ht_current_set_has_cleanup
            || self.next_pass.is_multiple_of(3)
            || passes == 0
            || match self.ht_refinement_passes.checked_add(passes) {
                Some(value) => value > 2,
                None => true,
            }
        {
            return Err(invalid_code_block());
        }
        let cleanup_plane = self
            .ht_cleanup_plane
            .as_ref()
            .ok_or_else(invalid_code_block)?;
        let next_bytes = self
            .decoded_bytes
            .checked_add(input.len() as u64)
            .ok_or_else(arithmetic_overflow)?;
        if next_bytes > limits.maximum_code_block_bytes() {
            return Err(DecodeError::limit(
                Resource::CodeBlockBytes,
                limits.maximum_code_block_bytes(),
                next_bytes,
            ));
        }
        let mut refinement_data = self.ht_refinement_data.clone();
        refinement_data.extend_from_slice(input);
        if refinement_data.len() > MAX_HT_REFINEMENT_BYTES {
            return Err(invalid_code_block());
        }
        let refinement_passes =
            crate::refinement::ht_refinement_pass_total(self.ht_refinement_passes, passes);
        if refinement_data.is_empty() {
            self.ht_refinement_passes = refinement_passes;
            self.next_pass = self
                .next_pass
                .checked_add(u32::from(passes))
                .ok_or_else(arithmetic_overflow)?;
            self.decoded_segments = self
                .decoded_segments
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            return Ok(Tier1SegmentDecode {
                passes: u32::from(passes),
                bytes: 0,
                statistics: Tier1PassStatistics::default(),
            });
        }
        let segment = HtRefinementSegment {
            encoded: &refinement_data,
            significance_propagation: HtSubstreamView {
                bytes: &refinement_data,
                offset: 0,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: &refinement_data,
                offset: 0,
                direction: HtStreamDirection::Reverse,
            },
        };
        let (plane, statistics) = decode_ht_refinement_plane(
            cleanup_plane,
            segment,
            refinement_passes,
            self.ht_decoded_bitplanes,
            self.style.vertical_causal_context,
            limits,
        )?;
        self.plane = plane;
        self.ht_refinement_data = refinement_data;
        self.ht_refinement_passes = refinement_passes;
        self.next_pass = self
            .next_pass
            .checked_add(u32::from(passes))
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_segments = self
            .decoded_segments
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        self.decoded_bytes = next_bytes;
        Ok(Tier1SegmentDecode {
            passes: u32::from(passes),
            bytes: u32::try_from(input.len()).map_err(|_| arithmetic_overflow())?,
            statistics,
        })
    }

    fn decode_mq_pass(
        &mut self,
        decoder: &mut MqDecoder<'_>,
        kind: Tier1PassKind,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        self.ensure_bitplane_state()?;
        let state = self
            .bitplane_state
            .as_mut()
            .ok_or_else(invalid_code_block)?;
        match kind {
            Tier1PassKind::SignificancePropagation => {
                decode_significance_propagation_pass_with_style(
                    &mut self.plane,
                    state,
                    decoder,
                    self.orientation,
                    self.style,
                )
            }
            Tier1PassKind::MagnitudeRefinement => decode_magnitude_refinement_pass_with_style(
                &mut self.plane,
                state,
                decoder,
                self.style,
            ),
            Tier1PassKind::Cleanup => decode_cleanup_pass_with_style(
                &mut self.plane,
                state,
                decoder,
                self.orientation,
                self.style,
            ),
        }
    }

    fn decode_raw_pass(
        &mut self,
        reader: &mut RawBitReader<'_>,
        kind: Tier1PassKind,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        self.ensure_bitplane_state()?;
        let state = self
            .bitplane_state
            .as_mut()
            .ok_or_else(invalid_code_block)?;
        match kind {
            Tier1PassKind::SignificancePropagation => decode_raw_significance_propagation_pass(
                &mut self.plane,
                state,
                reader,
                self.orientation,
                self.style,
            ),
            Tier1PassKind::MagnitudeRefinement => {
                decode_raw_magnitude_refinement_pass(&mut self.plane, state, reader, self.style)
            }
            Tier1PassKind::Cleanup => Err(invalid_code_block()),
        }
    }

    fn ensure_bitplane_state(&mut self) -> Result<(), DecodeError> {
        if self.bitplane_state.is_none() {
            self.bitplane_state = Some(Tier1BitplaneState::new_at_bitplane(
                &self.plane,
                self.bitplane,
            )?);
        }
        Ok(())
    }

    fn advance_pass(&mut self, kind: Tier1PassKind) -> Result<(), DecodeError> {
        self.next_pass = self
            .next_pass
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if matches!(kind, Tier1PassKind::Cleanup) {
            self.bitplane_state = None;
            if self.next_pass < self.maximum_passes {
                self.bitplane = self
                    .bitplane
                    .checked_sub(1)
                    .ok_or_else(invalid_code_block)?;
            }
        }
        Ok(())
    }
}

impl Tier1BitplaneState {
    pub fn new(plane: &CodeBlockPlane, bitplane_mask: u64) -> Result<Self, DecodeError> {
        if !is_bitplane_mask(bitplane_mask) {
            return Err(invalid_code_block());
        }
        let bitplane =
            u16::try_from(bitplane_mask.trailing_zeros()).map_err(|_| arithmetic_overflow())?;
        Self::new_at_bitplane(plane, bitplane)
    }

    pub fn new_at_bitplane(plane: &CodeBlockPlane, bitplane: u16) -> Result<Self, DecodeError> {
        if bitplane >= MAX_TIER1_BITPLANES {
            return Err(invalid_code_block());
        }
        let mut significant_before = Vec::with_capacity(plane.coefficients.len());
        let mut index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= plane.coefficients.len(),
                decreases plane.coefficients.len() - index,
            )
        )]
        while index < plane.coefficients.len() {
            significant_before.push(plane.coefficients[index].significant);
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(Self {
            width: plane.width,
            height: plane.height,
            bitplane,
            significance_visited: vec![false; significant_before.len()],
            significant_before,
            significance_propagation_complete: false,
            magnitude_refinement_complete: false,
            cleanup_complete: false,
        })
    }

    pub const fn bitplane_mask(&self) -> u64 {
        if self.bitplane < 64 {
            1_u64 << self.bitplane
        } else {
            0
        }
    }

    pub const fn bitplane(&self) -> u16 {
        self.bitplane
    }

    pub const fn significance_propagation_complete(&self) -> bool {
        self.significance_propagation_complete
    }

    pub const fn magnitude_refinement_complete(&self) -> bool {
        self.magnitude_refinement_complete
    }

    pub const fn cleanup_complete(&self) -> bool {
        self.cleanup_complete
    }

    pub fn was_visited_by_significance_propagation(
        &self,
        plane: &CodeBlockPlane,
        x: u16,
        y: u16,
    ) -> Result<bool, DecodeError> {
        self.validate_plane(plane)?;
        let index = plane.index(x, y)?;
        if index >= self.significance_visited.len() {
            return Err(invalid_code_block());
        }
        Ok(self.significance_visited[index])
    }

    fn validate_plane(&self, plane: &CodeBlockPlane) -> Result<(), DecodeError> {
        if self.width != plane.width
            || self.height != plane.height
            || self.significant_before.len() != plane.coefficients.len()
            || self.significance_visited.len() != plane.coefficients.len()
        {
            return Err(invalid_code_block());
        }
        Ok(())
    }
}

pub fn decode_significance_propagation_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_significance_propagation_pass_with_style(
        plane,
        state,
        decoder,
        orientation,
        Tier1CodingStyle::default(),
    )
}

pub fn decode_significance_propagation_pass_with_style(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    let mut symbol_decoder = Tier1SymbolDecoder::Mq(decoder);
    decode_significance_propagation(
        plane,
        state,
        &mut symbol_decoder,
        orientation,
        style.vertical_causal_context,
    )
}

pub fn decode_raw_significance_propagation_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    reader: &mut RawBitReader<'_>,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    let mut symbol_decoder = Tier1SymbolDecoder::Raw(reader);
    decode_significance_propagation(
        plane,
        state,
        &mut symbol_decoder,
        orientation,
        style.vertical_causal_context,
    )
}

fn decode_significance_propagation(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut Tier1SymbolDecoder<'_, '_>,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
) -> Result<Tier1PassStatistics, DecodeError> {
    state.validate_plane(plane)?;
    if state.significance_propagation_complete
        || state.magnitude_refinement_complete
        || state.cleanup_complete
    {
        return Err(invalid_code_block());
    }

    let mut statistics = Tier1PassStatistics::default();
    let height = plane.height;
    let width = plane.width;
    let mut stripe_y = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant stripe_y <= height,
            decreases height - stripe_y,
        )
    )]
    while stripe_y < height {
        let stripe_rows = crate::refinement::tier1_stripe_rows(height, stripe_y);
        let mut x = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= width,
                decreases width - x,
            )
        )]
        while x < width {
            let mut row = 0;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant row <= stripe_rows,
                    decreases stripe_rows - row,
                )
            )]
            while row < stripe_rows {
                let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                statistics.scanned(1)?;
                let index = plane.index(x, y)?;
                let coefficient = plane.coefficient(x, y)?;
                if !coefficient.significant {
                    let summary =
                        plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
                    let neighbors = significant_neighbor_count(summary);
                    if crate::refinement::tier1_sigprop_eligible(coefficient.significant, neighbors)
                    {
                        if index >= state.significance_visited.len() {
                            return Err(invalid_code_block());
                        }
                        let zero_context = zero_coding_context(summary, orientation);
                        let significant = decoder.decode(usize::from(zero_context))?;
                        state.significance_visited[index] = true;
                        statistics.decoded_symbols(1)?;
                        if significant {
                            decode_sign_and_mark(plane, decoder, x, y, state.bitplane, summary)?;
                            statistics.decoded_symbols(1)?;
                            statistics.became_significant()?;
                        }
                    }
                }
                row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        let next_stripe = stripe_y
            .checked_add(stripe_rows)
            .ok_or_else(arithmetic_overflow)?;
        if next_stripe <= stripe_y || next_stripe > height {
            return Err(invalid_code_block());
        }
        stripe_y = next_stripe;
    }
    state.significance_propagation_complete = crate::refinement::tier1_pass_complete(0) & 1 != 0;
    Ok(statistics)
}

pub fn decode_magnitude_refinement_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_magnitude_refinement_pass_with_style(plane, state, decoder, Tier1CodingStyle::default())
}

pub fn decode_magnitude_refinement_pass_with_style(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    let mut symbol_decoder = Tier1SymbolDecoder::Mq(decoder);
    decode_magnitude_refinement(
        plane,
        state,
        &mut symbol_decoder,
        style.vertical_causal_context,
    )
}

pub fn decode_raw_magnitude_refinement_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    reader: &mut RawBitReader<'_>,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    let mut symbol_decoder = Tier1SymbolDecoder::Raw(reader);
    decode_magnitude_refinement(
        plane,
        state,
        &mut symbol_decoder,
        style.vertical_causal_context,
    )
}

fn decode_magnitude_refinement(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut Tier1SymbolDecoder<'_, '_>,
    vertical_causal_context: bool,
) -> Result<Tier1PassStatistics, DecodeError> {
    state.validate_plane(plane)?;
    if !state.significance_propagation_complete
        || state.magnitude_refinement_complete
        || state.cleanup_complete
    {
        return Err(invalid_code_block());
    }

    let mut statistics = Tier1PassStatistics::default();
    let height = plane.height;
    let width = plane.width;
    let mut stripe_y = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant stripe_y <= height,
            decreases height - stripe_y,
        )
    )]
    while stripe_y < height {
        let stripe_rows = crate::refinement::tier1_stripe_rows(height, stripe_y);
        let mut x = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= width,
                decreases width - x,
            )
        )]
        while x < width {
            let mut row = 0;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant row <= stripe_rows,
                    decreases stripe_rows - row,
                )
            )]
            while row < stripe_rows {
                let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                statistics.scanned(1)?;
                let index = plane.index(x, y)?;
                if index >= state.significant_before.len() {
                    return Err(invalid_code_block());
                }
                if crate::refinement::tier1_magref_eligible(state.significant_before[index]) {
                    let coefficient = plane.coefficient(x, y)?;
                    let summary =
                        plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
                    let context = magnitude_refinement_context(coefficient, summary);
                    let refinement_bit = decoder.decode(usize::from(context))?;
                    statistics.decoded_symbols(1)?;
                    plane.apply_refinement_bit(x, y, state.bitplane, refinement_bit)?;
                    statistics.refined()?;
                }
                row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        let next_stripe = stripe_y
            .checked_add(stripe_rows)
            .ok_or_else(arithmetic_overflow)?;
        if next_stripe <= stripe_y || next_stripe > height {
            return Err(invalid_code_block());
        }
        stripe_y = next_stripe;
    }
    state.magnitude_refinement_complete = crate::refinement::tier1_pass_complete(1) & 2 != 0;
    Ok(statistics)
}

pub fn decode_cleanup_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_cleanup_pass_with_style(
        plane,
        state,
        decoder,
        orientation,
        Tier1CodingStyle::default(),
    )
}

pub fn decode_cleanup_pass_with_style(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    let mut symbol_decoder = Tier1SymbolDecoder::Mq(decoder);
    decode_cleanup(
        plane,
        state,
        &mut symbol_decoder,
        orientation,
        style.vertical_causal_context,
        style.segmentation_symbols,
    )
}

fn decode_cleanup(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut Tier1SymbolDecoder<'_, '_>,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
    segmentation_symbols: bool,
) -> Result<Tier1PassStatistics, DecodeError> {
    state.validate_plane(plane)?;
    if state.cleanup_complete
        || state.significance_propagation_complete != state.magnitude_refinement_complete
    {
        return Err(invalid_code_block());
    }

    let mut statistics = Tier1PassStatistics::default();
    let height = plane.height;
    let width = plane.width;
    let mut stripe_y = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant stripe_y <= height,
            decreases height - stripe_y,
        )
    )]
    while stripe_y < height {
        let stripe_rows = crate::refinement::tier1_stripe_rows(height, stripe_y);
        let mut x = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= width,
                decreases width - x,
            )
        )]
        while x < width {
            let stripe_y_1 = stripe_y.checked_add(1).ok_or_else(arithmetic_overflow)?;
            let stripe_y_2 = stripe_y.checked_add(2).ok_or_else(arithmetic_overflow)?;
            let stripe_y_3 = stripe_y.checked_add(3).ok_or_else(arithmetic_overflow)?;
            if stripe_rows == 4
                && cleanup_run_candidate(plane, state, x, stripe_y, vertical_causal_context)?
                && cleanup_run_candidate(plane, state, x, stripe_y_1, vertical_causal_context)?
                && cleanup_run_candidate(plane, state, x, stripe_y_2, vertical_causal_context)?
                && cleanup_run_candidate(plane, state, x, stripe_y_3, vertical_causal_context)?
            {
                statistics.scanned(4)?;
                statistics.used_run_mode()?;
                let interrupted = decoder.decode(RUN_LENGTH_CONTEXT)?;
                statistics.decoded_symbols(1)?;
                if interrupted {
                    let run_high = decoder.decode(UNIFORM_CONTEXT)?;
                    let run_low = decoder.decode(UNIFORM_CONTEXT)?;
                    statistics.decoded_symbols(2)?;
                    let run_length = if run_high {
                        if run_low { 3 } else { 2 }
                    } else if run_low {
                        1
                    } else {
                        0
                    };
                    let y = stripe_y
                        .checked_add(run_length)
                        .ok_or_else(arithmetic_overflow)?;
                    let summary =
                        plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
                    decode_sign_and_mark(plane, decoder, x, y, state.bitplane, summary)?;
                    statistics.decoded_symbols(1)?;
                    statistics.became_significant()?;

                    let mut row = run_length.checked_add(1).ok_or_else(arithmetic_overflow)?;
                    #[cfg_attr(
                        verus_keep_ghost,
                        verus_spec(decreases 4int - row as int,)
                    )]
                    while row < 4 {
                        let remaining_y =
                            stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                        decode_cleanup_coefficient(
                            plane,
                            state,
                            decoder,
                            orientation,
                            vertical_causal_context,
                            (x, remaining_y),
                            &mut statistics,
                        )?;
                        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
                    }
                }
            } else {
                let mut row = 0;
                #[cfg_attr(
                    verus_keep_ghost,
                    verus_spec(
                        invariant row <= stripe_rows,
                        decreases stripe_rows - row,
                    )
                )]
                while row < stripe_rows {
                    let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                    statistics.scanned(1)?;
                    decode_cleanup_coefficient(
                        plane,
                        state,
                        decoder,
                        orientation,
                        vertical_causal_context,
                        (x, y),
                        &mut statistics,
                    )?;
                    row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
                }
            }
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        let next_stripe = stripe_y
            .checked_add(stripe_rows)
            .ok_or_else(arithmetic_overflow)?;
        if next_stripe <= stripe_y || next_stripe > height {
            return Err(invalid_code_block());
        }
        stripe_y = next_stripe;
    }
    if segmentation_symbols {
        let first = decoder.decode(UNIFORM_CONTEXT)?;
        let second = decoder.decode(UNIFORM_CONTEXT)?;
        let third = decoder.decode(UNIFORM_CONTEXT)?;
        let fourth = decoder.decode(UNIFORM_CONTEXT)?;
        statistics.decoded_symbols(4)?;
        if !first || second || !third || fourth {
            return Err(invalid_code_block());
        }
    }
    state.cleanup_complete = crate::refinement::tier1_pass_complete(2) & 4 != 0;
    Ok(statistics)
}

fn decode_cleanup_coefficient(
    plane: &mut CodeBlockPlane,
    state: &Tier1BitplaneState,
    decoder: &mut Tier1SymbolDecoder<'_, '_>,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
    coordinate: (u16, u16),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    let (x, y) = coordinate;
    let index = plane.index(x, y)?;
    if index >= state.significance_visited.len() {
        return Err(invalid_code_block());
    }
    let coefficient = plane.coefficient(x, y)?;
    if !crate::refinement::tier1_cleanup_eligible(
        coefficient.significant,
        state.significance_visited[index],
    ) {
        return Ok(());
    }
    let summary = plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
    let zero_context = zero_coding_context(summary, orientation);
    let significant = decoder.decode(usize::from(zero_context))?;
    statistics.decoded_symbols(1)?;
    if significant {
        decode_sign_and_mark(plane, decoder, x, y, state.bitplane, summary)?;
        statistics.decoded_symbols(1)?;
        statistics.became_significant()?;
    }
    Ok(())
}

fn decode_sign_and_mark(
    plane: &mut CodeBlockPlane,
    decoder: &mut Tier1SymbolDecoder<'_, '_>,
    x: u16,
    y: u16,
    bitplane: u16,
    summary: NeighborSummary,
) -> Result<(), DecodeError> {
    let sign = sign_context(summary);
    let raw = matches!(decoder, Tier1SymbolDecoder::Raw(_));
    let decoded_sign = decoder.decode(usize::from(sign.context))?;
    plane.mark_significant_at_bitplane(
        x,
        y,
        bitplane,
        crate::refinement::tier1_decoded_sign(decoded_sign, sign.predicted_negative, raw),
    )
}

fn cleanup_run_candidate(
    plane: &CodeBlockPlane,
    state: &Tier1BitplaneState,
    x: u16,
    y: u16,
    vertical_causal_context: bool,
) -> Result<bool, DecodeError> {
    let index = plane.index(x, y)?;
    if index >= state.significance_visited.len() {
        return Err(invalid_code_block());
    }
    Ok(!plane.coefficient(x, y)?.significant
        && !state.significance_visited[index]
        && significant_neighbor_count(plane.neighbor_summary_with_causality(
            x,
            y,
            vertical_causal_context,
        )?) == 0)
}

enum Tier1SymbolDecoder<'decoder, 'input> {
    Mq(&'decoder mut MqDecoder<'input>),
    Raw(&'decoder mut RawBitReader<'input>),
}

impl Tier1SymbolDecoder<'_, '_> {
    fn decode(&mut self, context: usize) -> Result<bool, DecodeError> {
        match self {
            Self::Mq(decoder) => decoder.decode(context),
            Self::Raw(reader) => reader.read_bit(),
        }
    }
}

fn significant_neighbor_count(summary: NeighborSummary) -> u16 {
    u16::from(summary.horizontal_significant)
        + u16::from(summary.vertical_significant)
        + u16::from(summary.diagonal_significant)
}

const fn is_bitplane_mask(bitplane_mask: u64) -> bool {
    bitplane_mask != 0 && bitplane_mask & (bitplane_mask - 1) == 0
}

fn invalid_code_block() -> DecodeError {
    DecodeError::malformed(0, MalformedKind::InvalidCodeBlock)
}

fn arithmetic_overflow() -> DecodeError {
    DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
}

pub fn apply_significance_decision(
    plane: &mut CodeBlockPlane,
    x: u16,
    y: u16,
    bitplane_mask: u64,
    orientation: SubbandOrientation,
    significant: bool,
    decoded_sign: bool,
) -> Result<SignificanceStep, DecodeError> {
    if bitplane_mask == 0 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
    }
    let summary = plane.neighbor_summary(x, y)?;
    let zero_context = zero_coding_context(summary, orientation);
    if !significant {
        return Ok(SignificanceStep {
            zero_coding_context: zero_context,
            sign_context: None,
            became_significant: false,
        });
    }
    let sign = sign_context(summary);
    plane.mark_significant(x, y, bitplane_mask, decoded_sign ^ sign.predicted_negative)?;
    Ok(SignificanceStep {
        zero_coding_context: zero_context,
        sign_context: Some(sign.context),
        became_significant: true,
    })
}

#[derive(Clone, Copy)]
enum NeighborKind {
    Horizontal,
    Vertical,
    Diagonal,
}

#[derive(Clone)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct CodeBlockPlane {
    width: u16,
    height: u16,
    coefficients: Vec<CoefficientState>,
}

impl CodeBlockPlane {
    pub fn new(width: u16, height: u16) -> Result<Self, DecodeError> {
        if width == 0 || height == 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        let samples = usize::from(width)
            .checked_mul(usize::from(height))
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if samples > 4096 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        Ok(Self {
            width,
            height,
            coefficients: vec![CoefficientState::default(); samples],
        })
    }

    fn duplicate(&self) -> Result<Self, DecodeError> {
        let mut output = Self::new(self.width, self.height)?;
        if output.coefficients.len() != self.coefficients.len() {
            return Err(invalid_code_block());
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.coefficients.len(),
                decreases self.coefficients.len() - index,
            )
        )]
        while index < self.coefficients.len() {
            *output
                .coefficients
                .get_mut(index)
                .ok_or_else(invalid_code_block)? = *self
                .coefficients
                .get(index)
                .ok_or_else(invalid_code_block)?;
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(output)
    }

    pub const fn width(&self) -> u16 {
        self.width
    }

    pub const fn height(&self) -> u16 {
        self.height
    }

    pub fn coefficient(&self, x: u16, y: u16) -> Result<CoefficientState, DecodeError> {
        let index = self.index(x, y)?;
        if index >= self.coefficients.len() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        Ok(self.coefficients[index])
    }

    pub fn coefficients(&self) -> &[CoefficientState] {
        &self.coefficients
    }

    /// Returns the reconstructed integer coefficient, including any legacy
    /// truncation midpoint; `coefficient` retains the decoded magnitude bits.
    pub fn signed_coefficient(&self, x: u16, y: u16) -> Result<i64, DecodeError> {
        let coefficient = self.coefficient(x, y)?;
        if !coefficient.significant {
            return Ok(0);
        }
        let magnitude = coefficient
            .signed_magnitude()?
            .magnitude
            .to_u64()
            .and_then(|value| i64::try_from(value).ok())
            .ok_or_else(arithmetic_overflow)?;
        if coefficient.negative {
            if magnitude == i64::MIN {
                Err(arithmetic_overflow())
            } else {
                Ok(-magnitude)
            }
        } else {
            Ok(magnitude)
        }
    }

    pub fn mark_significant(
        &mut self,
        x: u16,
        y: u16,
        magnitude: u64,
        negative: bool,
    ) -> Result<(), DecodeError> {
        self.mark_significant_magnitude(x, y, Magnitude::from_u64(magnitude), negative)
    }

    fn mark_significant_at_bitplane(
        &mut self,
        x: u16,
        y: u16,
        bitplane: u16,
        negative: bool,
    ) -> Result<(), DecodeError> {
        self.mark_significant_magnitude(x, y, Magnitude::single_bit(bitplane)?, negative)?;
        let index = self.index(x, y)?;
        self.coefficients
            .get_mut(index)
            .ok_or_else(invalid_code_block)?
            .legacy_bitplane = Some(bitplane);
        Ok(())
    }

    fn mark_significant_magnitude(
        &mut self,
        x: u16,
        y: u16,
        magnitude: Magnitude,
        negative: bool,
    ) -> Result<(), DecodeError> {
        if magnitude.is_zero() {
            return Err(invalid_code_block());
        }
        let index = self.index(x, y)?;
        if index >= self.coefficients.len() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        if self.coefficients[index].significant {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        self.coefficients[index] =
            CoefficientState::from_magnitude(magnitude, negative, true, false)?;
        Ok(())
    }

    pub fn refine(&mut self, x: u16, y: u16, bitplane_mask: u64) -> Result<(), DecodeError> {
        self.apply_refinement_decision(x, y, bitplane_mask, true)
    }

    pub fn apply_refinement_decision(
        &mut self,
        x: u16,
        y: u16,
        bitplane_mask: u64,
        refinement_bit: bool,
    ) -> Result<(), DecodeError> {
        if !is_bitplane_mask(bitplane_mask) {
            return Err(invalid_code_block());
        }
        let bitplane =
            u16::try_from(bitplane_mask.trailing_zeros()).map_err(|_| arithmetic_overflow())?;
        self.apply_refinement_bit(x, y, bitplane, refinement_bit)
    }

    fn apply_refinement_bit(
        &mut self,
        x: u16,
        y: u16,
        bitplane: u16,
        refinement_bit: bool,
    ) -> Result<(), DecodeError> {
        if bitplane >= MAX_TIER1_BITPLANES {
            return Err(invalid_code_block());
        }
        let index = self.index(x, y)?;
        if index >= self.coefficients.len() {
            return Err(invalid_code_block());
        }
        let coefficient = self.coefficients[index];
        if !coefficient.significant {
            return Err(invalid_code_block());
        }
        if refinement_bit {
            let current = coefficient.wide_magnitude();
            let delta = Magnitude::single_bit(bitplane)?;
            let magnitude = match (current.to_u64(), delta.to_u64()) {
                (Some(current), Some(delta)) if current <= u64::MAX - delta => Magnitude::from_u64(
                    crate::refinement::tier1_refined_magnitude(current, delta, true),
                ),
                _ => current.checked_add(delta)?,
            };
            self.coefficients[index].set_magnitude(magnitude)?;
        }
        self.coefficients[index].refined = true;
        if coefficient.legacy_bitplane.is_some() {
            self.coefficients[index].legacy_bitplane = Some(bitplane);
        }
        Ok(())
    }

    fn apply_ht_refinement_decision(
        &mut self,
        x: u16,
        y: u16,
        delta: Magnitude,
        refinement_bit: bool,
    ) -> Result<(), DecodeError> {
        if delta.is_zero() && !refinement_bit {
            return Err(invalid_code_block());
        }
        let index = self.index(x, y)?;
        let coefficient = *self
            .coefficients
            .get(index)
            .ok_or_else(invalid_code_block)?;
        if !coefficient.significant {
            return Err(invalid_code_block());
        }
        let magnitude = if refinement_bit {
            coefficient.wide_magnitude().checked_add(delta)?
        } else {
            coefficient
                .wide_magnitude()
                .checked_sub(delta)
                .map_err(|_| invalid_code_block())?
        };
        if magnitude.is_zero() {
            return Err(invalid_code_block());
        }
        let output = self
            .coefficients
            .get_mut(index)
            .ok_or_else(invalid_code_block)?;
        output.set_magnitude(magnitude)?;
        output.refined = true;
        Ok(())
    }

    pub fn neighbor_summary(&self, x: u16, y: u16) -> Result<NeighborSummary, DecodeError> {
        self.neighbor_summary_with_causality(x, y, false)
    }

    fn neighbor_summary_with_causality(
        &self,
        x: u16,
        y: u16,
        vertical_causal_context: bool,
    ) -> Result<NeighborSummary, DecodeError> {
        self.index(x, y)?;
        let mut summary = NeighborSummary::default();
        self.accumulate_neighbor(x, y, (-1, 0), NeighborKind::Horizontal, &mut summary)?;
        self.accumulate_neighbor(x, y, (1, 0), NeighborKind::Horizontal, &mut summary)?;
        self.accumulate_neighbor(x, y, (0, -1), NeighborKind::Vertical, &mut summary)?;
        self.accumulate_neighbor(x, y, (-1, -1), NeighborKind::Diagonal, &mut summary)?;
        self.accumulate_neighbor(x, y, (1, -1), NeighborKind::Diagonal, &mut summary)?;
        if !vertical_causal_context || y % 4 != 3 {
            self.accumulate_neighbor(x, y, (0, 1), NeighborKind::Vertical, &mut summary)?;
            self.accumulate_neighbor(x, y, (-1, 1), NeighborKind::Diagonal, &mut summary)?;
            self.accumulate_neighbor(x, y, (1, 1), NeighborKind::Diagonal, &mut summary)?;
        }
        Ok(summary)
    }

    fn index(&self, x: u16, y: u16) -> Result<usize, DecodeError> {
        if x >= self.width || y >= self.height {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        let index = usize::from(y)
            .checked_mul(usize::from(self.width))
            .and_then(|row| row.checked_add(usize::from(x)))
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if index >= self.coefficients.len() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        Ok(index)
    }

    // Specialize the fixed offsets and neighbor kinds in the hot context traversal.
    #[inline(always)]
    fn accumulate_neighbor(
        &self,
        x: u16,
        y: u16,
        delta: (i8, i8),
        kind: NeighborKind,
        summary: &mut NeighborSummary,
    ) -> Result<(), DecodeError> {
        let neighbor_x = i32::from(x) + i32::from(delta.0);
        let neighbor_y = i32::from(y) + i32::from(delta.1);
        if neighbor_x < 0
            || neighbor_y < 0
            || neighbor_x >= i32::from(self.width)
            || neighbor_y >= i32::from(self.height)
        {
            return Ok(());
        }
        let coefficient = self.coefficient(
            u16::try_from(neighbor_x)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            u16::try_from(neighbor_y)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        )?;
        if !coefficient.significant {
            return Ok(());
        }
        let sign = if coefficient.negative { -1 } else { 1 };
        if matches!(kind, NeighborKind::Horizontal) {
            summary.horizontal_significant = summary
                .horizontal_significant
                .checked_add(1)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            summary.horizontal_sign_balance = summary
                .horizontal_sign_balance
                .checked_add(sign)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        } else if matches!(kind, NeighborKind::Vertical) {
            summary.vertical_significant = summary
                .vertical_significant
                .checked_add(1)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            summary.vertical_sign_balance = summary
                .vertical_sign_balance
                .checked_add(sign)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        } else {
            summary.diagonal_significant = summary
                .diagonal_significant
                .checked_add(1)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        }
        Ok(())
    }
}

impl CodeBlockSegmentAccounting {
    pub fn new(maximum_passes: u32, limits: &ResourceLimits) -> Result<Self, DecodeError> {
        if maximum_passes == 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        Ok(Self {
            maximum_passes,
            maximum_bytes: limits.maximum_input_bytes(),
            total_passes: 0,
            total_bytes: 0,
            segments: 0,
        })
    }

    pub fn add_segment(&mut self, passes: u32, bytes: u32) -> Result<Tier1PassKind, DecodeError> {
        if passes == 0 || bytes == 0 {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        let next_passes = self
            .total_passes
            .checked_add(passes)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let next_bytes = self
            .total_bytes
            .checked_add(u64::from(bytes))
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let next_segments = self
            .segments
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        if next_passes > self.maximum_passes {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
        }
        if next_bytes > self.maximum_bytes {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.maximum_bytes,
                next_bytes,
            ));
        }
        let first_pass = pass_kind(self.total_passes);
        self.total_passes = next_passes;
        self.total_bytes = next_bytes;
        self.segments = next_segments;
        Ok(first_pass)
    }

    pub const fn total_passes(&self) -> u32 {
        self.total_passes
    }

    pub const fn total_bytes(&self) -> u64 {
        self.total_bytes
    }

    pub const fn segments(&self) -> u32 {
        self.segments
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ht_cleanup_u_bound_includes_packet_msbs_and_placeholders() {
        assert_eq!(crate::refinement::part15_cleanup_u_bound(0, 0, 74), 2);
        assert_eq!(crate::refinement::part15_cleanup_u_bound(6, 0, 8), 8);
        assert_eq!(crate::refinement::part15_cleanup_u_bound(6, 1, 74), 9);
        assert_eq!(crate::refinement::part15_cleanup_u_bound(6, 1, 8), 8);
        assert_eq!(
            crate::refinement::part15_cleanup_u_bound(u16::MAX, u16::MAX, 74),
            74
        );
    }

    #[test]
    fn leading_zero_bitplanes_are_configured_once_before_coding() {
        let mut decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            5,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .unwrap();
        assert!(decoder.set_zero_bitplanes(5).is_err());
        assert_eq!(decoder.maximum_passes(), 13);
        decoder.set_zero_bitplanes(2).unwrap();
        assert_eq!(decoder.bitplane, 2);
        assert_eq!(decoder.maximum_passes(), 7);
        decoder.set_zero_bitplanes(2).unwrap();
        assert!(decoder.set_zero_bitplanes(1).is_err());
        assert_eq!(decoder.bitplane, 2);
        assert_eq!(decoder.maximum_passes(), 7);
    }

    #[test]
    fn raw_reader_applies_seven_bit_stuffing_after_ff() {
        let mut reader = RawBitReader::new(&[0xff, 0x7f], &ResourceLimits::default()).unwrap();
        for _ in 0..8 {
            assert!(reader.read_bit().unwrap());
        }
        let mut second_byte = Vec::new();
        for _ in 0..7 {
            second_byte.push(reader.read_bit().unwrap());
        }
        assert_eq!(second_byte, [true; 7]);
        assert_eq!(reader.bytes_consumed(), 2);
    }

    #[test]
    fn raw_reader_stops_at_marker_without_reading_past_input() {
        let mut reader = RawBitReader::new(&[0xff, 0x90], &ResourceLimits::default()).unwrap();
        for _ in 0..16 {
            assert!(reader.read_bit().unwrap());
        }
        assert_eq!(reader.bytes_consumed(), 1);
        assert!(reader.marker_padding_count() > 0);
    }

    #[test]
    fn validates_raw_predictable_termination_fill() {
        let limits = ResourceLimits::default();
        let mut valid = RawBitReader::new(&[0xaa], &limits).unwrap();
        assert!(valid.read_bit().unwrap());
        valid.validate_predictable_termination().unwrap();

        let mut invalid = RawBitReader::new(&[0xab], &limits).unwrap();
        assert!(invalid.read_bit().unwrap());
        assert!(invalid.validate_predictable_termination().is_err());
    }

    #[test]
    fn tier_one_pass_schedule_repeats_normative_cycle() {
        assert_eq!(pass_kind(0), Tier1PassKind::Cleanup);
        assert_eq!(pass_kind(1), Tier1PassKind::SignificancePropagation);
        assert_eq!(pass_kind(2), Tier1PassKind::MagnitudeRefinement);
        assert_eq!(pass_kind(3), Tier1PassKind::Cleanup);
        assert_eq!(pass_kind(4), Tier1PassKind::SignificancePropagation);
    }

    #[test]
    fn validates_code_block_style_and_raw_bypass_schedule() {
        let style = Tier1CodingStyle::from_code_block_style(0x3f).unwrap();
        assert!(style.selective_arithmetic_coding_bypass);
        assert!(style.reset_contexts);
        assert!(style.terminate_all_passes);
        assert!(style.vertical_causal_context);
        assert!(style.predictable_termination);
        assert!(style.segmentation_symbols);
        assert!(!style.uses_raw_bypass(9));
        assert!(style.uses_raw_bypass(10));
        assert!(style.uses_raw_bypass(11));
        assert!(!style.uses_raw_bypass(12));
        let ht = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
        assert_eq!(ht.block_coding, Tier1BlockCoding::HighThroughput);
        let mut ht_decoder =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, ht).unwrap();
        let decoded = ht_decoder
            .decode_high_throughput_segments(
                &[0x00, 0x63, 0x00],
                1,
                None,
                0,
                &ResourceLimits::default(),
            )
            .unwrap();
        assert_eq!(decoded.passes, 1);
        assert_eq!(decoded.statistics.newly_significant, 1);
        assert_eq!(ht_decoder.next_pass(), 1);
        assert_eq!(ht_decoder.plane().signed_coefficient(0, 0).unwrap(), -1);
        let mixed = Tier1CodingStyle::from_code_block_style(0xc0).unwrap();
        assert_eq!(mixed.block_coding, Tier1BlockCoding::Mixed);
        assert!(mixed.block_coding.selects_high_throughput(3));
        assert!(!mixed.block_coding.selects_high_throughput(4));
        assert!(Tier1CodingStyle::from_code_block_style(0x80).is_err());
        assert!(Tier1CodingStyle::from_code_block_style(0x41).is_err());

        let cleanup = style.pass_plan(12);
        assert_eq!(cleanup.kind, Tier1PassKind::Cleanup);
        assert_eq!(cleanup.coding_mode, Tier1CodingMode::Mq);
        assert!(cleanup.terminates_segment);
        assert!(cleanup.reset_contexts_after_pass);
        assert!(cleanup.validate_predictable_termination);
        assert!(cleanup.expect_segmentation_symbol);

        let bypass = Tier1CodingStyle::from_code_block_style(0x01).unwrap();
        assert_eq!(bypass.segment_passes(0, 20), 10);
        assert_eq!(bypass.segment_passes(8, 20), 2);
        assert_eq!(bypass.segment_passes(10, 20), 2);
        assert_eq!(bypass.segment_passes(11, 20), 1);
        assert_eq!(bypass.segment_passes(12, 20), 1);
        assert_eq!(bypass.segment_passes(12, 0), 0);

        let default_style = Tier1CodingStyle::default();
        assert_eq!(default_style.segment_passes(0, 20), 20);
        assert!(!default_style.pass_plan(0).terminates_segment);
    }

    #[test]
    fn groups_ht_packet_passes_and_retains_bounded_stream_views() {
        assert_eq!(
            HtPassGroup::from_packet_passes(1).unwrap(),
            HtPassGroup {
                cleanup_passes: 1,
                refinement_passes: 0,
                placeholder_passes: 0,
                skipped_bitplanes: 0,
            }
        );
        assert_eq!(
            HtPassGroup::from_packet_passes(3).unwrap(),
            HtPassGroup {
                cleanup_passes: 1,
                refinement_passes: 2,
                placeholder_passes: 0,
                skipped_bitplanes: 0,
            }
        );
        assert!(HtPassGroup::from_packet_passes(0).is_err());
        assert!(HtPassGroup::from_packet_passes(165).is_err());
        assert_eq!(
            HtPassGroup::from_packet_passes(4).unwrap(),
            HtPassGroup {
                cleanup_passes: 4,
                refinement_passes: 0,
                placeholder_passes: 3,
                skipped_bitplanes: 1,
            }
        );

        let cleanup = [0xaa, 0xbb, 0x03, 0x00];
        let refinement = [0x11, 0x22];
        let segments =
            parse_ht_block_segments(&cleanup, Some(&refinement), &ResourceLimits::default())
                .unwrap();
        assert_eq!(segments.bytes(), 6);
        assert_eq!(segments.cleanup().scup(), 3);
        assert_eq!(segments.cleanup().mag_sgn().bytes(), &[0xaa]);
        assert_eq!(segments.cleanup().mel_vlc().bytes(), &[0xbb, 0x03, 0x00]);
        assert_eq!(segments.cleanup().mel().bytes(), &[0xbb, 0x03]);
        assert_eq!(
            segments.cleanup().vlc().direction(),
            HtStreamDirection::Reverse
        );
        let retained = segments.refinement().unwrap();
        assert_eq!(retained.encoded(), &refinement);
        assert_eq!(
            retained.significance_propagation().direction(),
            HtStreamDirection::Forward
        );
        assert_eq!(
            retained.magnitude_refinement().direction(),
            HtStreamDirection::Reverse
        );
        assert_eq!(retained.significance_propagation().offset(), 4);
    }

    #[test]
    fn decodes_bounded_ht_cleanup_quad_metadata() {
        let limits = ResourceLimits::default();
        let metadata = decode_ht_cleanup_metadata(&[0x00, 0x63, 0x00], 1, 1, 1, &limits).unwrap();
        assert_eq!(metadata.width, 1);
        assert_eq!(metadata.height, 1);
        assert_eq!(metadata.significant_samples, 1);
        assert_eq!(metadata.mel_events, 1);
        assert_eq!(metadata.quads.len(), 1);
        assert_eq!(
            metadata.quads[0],
            HtQuadMetadata {
                x: 0,
                y: 0,
                context: 0,
                initial_row: true,
                significance: 1,
                embedded_magnitude: 0,
                embedded_bit_mask: 0,
                u_offset: false,
                u_base: 1,
                codeword_bits: 4,
            }
        );
        assert_eq!(metadata.mel_bits, 1);
        assert_eq!(metadata.vlc_bits, 4);
    }

    #[test]
    fn ht_readers_apply_directional_stuffing_and_reject_bad_mel_sequences() {
        let limits = ResourceLimits::default();
        let mut mel = HtMelBitReader::new(&[0xff, 0x8f], &limits).unwrap();
        for _ in 0..8 {
            let _ = mel.read_bit().unwrap();
        }
        let _ = mel.read_bit().unwrap();
        assert_eq!(mel.next_position().unwrap().bit, 5);
        let mut malformed = HtMelBitReader::new(&[0xff, 0x90], &limits).unwrap();
        for _ in 0..8 {
            assert!(malformed.read_bit().unwrap());
        }
        assert!(malformed.read_bit().is_err());

        let mut reverse = HtReverseVlcReader::new(&[0x7f, 0x90, 0x00], &limits).unwrap();
        for _ in 0..4 {
            let _ = reverse.read_bit().unwrap();
        }
        assert_eq!(
            reverse.next_position(),
            Some(HtBitPosition { byte: 0, bit: 0 })
        );
        for _ in 0..7 {
            let _ = reverse.read_bit().unwrap();
        }
        assert_eq!(reverse.bits_read(), 11);
        assert!(reverse.next_position().is_none());
    }

    #[test]
    fn ht_magsgn_reader_is_bounded_stuffed_and_termination_checked() {
        let limits = ResourceLimits::default();
        let mut reader = HtForwardMagSgnReader::new(&[0xff, 0x7f], &limits).unwrap();
        assert_eq!(reader.read_bits(15).unwrap(), 0x7fff);
        assert_eq!(reader.physical_bits_read(), 15);
        assert_eq!(reader.fill_bits_read(), 0);
        assert_eq!(reader.read_bits(3).unwrap(), 7);
        assert_eq!(reader.fill_bits_read(), 3);
        reader.finish().unwrap();

        let mut bad_stuffing = HtForwardMagSgnReader::new(&[0xff, 0x80], &limits).unwrap();
        assert_eq!(bad_stuffing.read_bits(8).unwrap(), 0xff);
        assert!(matches!(
            bad_stuffing.read_bits(1),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidBitStuffing,
                ..
            })
        ));

        let mut bad_termination = HtForwardMagSgnReader::new(&[0xfc], &limits).unwrap();
        assert_eq!(bad_termination.read_bits(1).unwrap(), 0);
        assert!(bad_termination.finish().is_err());
    }

    #[test]
    fn ht_refinement_readers_are_stuffed_bounded_and_collision_checked() {
        let limits = ResourceLimits::default();
        let mut forward = HtForwardRefinementReader::new(&[0xff, 0x7f], &limits).unwrap();
        for _ in 0..15 {
            assert!(forward.read_bit().unwrap());
        }
        assert_eq!(forward.physical_bits_read(), 15);
        assert!(!forward.read_bit().unwrap());
        assert_eq!(forward.fill_bits_read(), 1);

        let mut malformed = HtForwardRefinementReader::new(&[0xff, 0x80], &limits).unwrap();
        for _ in 0..8 {
            let _ = malformed.read_bit().unwrap();
        }
        assert!(matches!(
            malformed.read_bit(),
            Err(DecodeError::MalformedInput {
                kind: MalformedKind::InvalidBitStuffing,
                ..
            })
        ));

        let segment = HtRefinementSegment {
            encoded: &[1],
            significance_propagation: HtSubstreamView {
                bytes: &[1],
                offset: 0,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: &[1],
                offset: 0,
                direction: HtStreamDirection::Reverse,
            },
        };
        let mut readers = HtRefinementReaders::new(segment, true, &limits).unwrap();
        assert!(readers.read_forward().unwrap());
        assert!(readers.read_reverse().is_err());
    }

    #[test]
    fn ht_refinement_applies_new_signs_and_magnitude_bits_transactionally() {
        let limits = ResourceLimits::default();
        let mut cleanup = CodeBlockPlane::new(2, 1).unwrap();
        cleanup.mark_significant(0, 0, 3, false).unwrap();

        let spp_bytes = [0x01];
        let spp = HtRefinementSegment {
            encoded: &spp_bytes,
            significance_propagation: HtSubstreamView {
                bytes: &spp_bytes,
                offset: 0,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: &spp_bytes,
                offset: 0,
                direction: HtStreamDirection::Reverse,
            },
        };
        let (spp_plane, statistics) =
            decode_ht_refinement_plane(&cleanup, spp, 1, 2, false, &limits).unwrap();
        assert_eq!(statistics.newly_significant, 1);
        assert_eq!(spp_plane.signed_coefficient(1, 0).unwrap(), 1);

        let both_bytes = [0x01, 0x01];
        let both = HtRefinementSegment {
            encoded: &both_bytes,
            significance_propagation: HtSubstreamView {
                bytes: &both_bytes,
                offset: 0,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: &both_bytes,
                offset: 0,
                direction: HtStreamDirection::Reverse,
            },
        };
        let (both_plane, statistics) =
            decode_ht_refinement_plane(&cleanup, both, 2, 2, false, &limits).unwrap();
        assert_eq!(statistics.refined_coefficients, 1);
        assert_eq!(statistics.newly_significant, 1);
        assert_eq!(both_plane.signed_coefficient(0, 0).unwrap(), 3);
        assert_eq!(both_plane.signed_coefficient(1, 0).unwrap(), 1);

        let bad_bytes = [0xff];
        let bad = HtRefinementSegment {
            encoded: &bad_bytes,
            significance_propagation: HtSubstreamView {
                bytes: &bad_bytes,
                offset: 0,
                direction: HtStreamDirection::Forward,
            },
            magnitude_refinement: HtSubstreamView {
                bytes: &bad_bytes,
                offset: 0,
                direction: HtStreamDirection::Reverse,
            },
        };
        assert!(decode_ht_refinement_plane(&cleanup, bad, 2, 2, false, &limits).is_err());
        assert_eq!(cleanup.signed_coefficient(0, 0).unwrap(), 3);
        assert_eq!(cleanup.signed_coefficient(1, 0).unwrap(), 0);
    }

    #[test]
    fn completes_non_initial_ht_kappa_from_north_exponents() {
        assert_eq!(complete_ht_kappa(2, 0x1, 7, 3, 8).unwrap(), 2);
        assert_eq!(complete_ht_kappa(2, 0x3, 7, 3, 8).unwrap(), 7);
        assert!(complete_ht_kappa(2, 0x3, 9, 3, 8).is_err());
        assert!(complete_ht_kappa(0, 0x3, 1, 1, 8).is_err());
    }

    #[test]
    fn reconstructs_positive_ht_cleanup_magnitude_from_physical_bits() {
        let limits = ResourceLimits::default();
        let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 1, SubbandOrientation::Ll, style).unwrap();
        let decoded = decoder
            .decode_high_throughput_segments(&[0xfe, 0x00, 0x63, 0x00], 1, None, 0, &limits)
            .unwrap();
        assert_eq!(decoded.statistics.coefficients_scanned, 1);
        assert_eq!(decoded.statistics.coding_symbols, 1);
        assert_eq!(decoded.statistics.newly_significant, 1);
        assert_eq!(decoder.plane().signed_coefficient(0, 0).unwrap(), 1);
        assert!(decoder.is_complete());
        assert_eq!(decoder.decoded_segments(), 1);
        assert_eq!(decoder.decoded_bytes(), 4);
    }

    #[test]
    fn ht_embedded_zero_bit_still_reduces_payload_precision() {
        let mut reader = HtForwardMagSgnReader::new(&[0x04], &ResourceLimits::default()).unwrap();
        let (magnitude, negative, exponent) =
            reconstruct_ht_magnitude(&mut reader, 3, true, false, 1).unwrap();
        assert_eq!(magnitude.to_u64(), Some(1));
        assert!(!negative);
        assert_eq!(exponent, 1);
        assert_eq!(reader.physical_bits_read(), 2);
    }

    #[test]
    fn reconstructs_capability_b74_magnitude_without_narrowing() {
        let bytes = [0_u8; 10];
        let mut reader = HtForwardMagSgnReader::new(&bytes, &ResourceLimits::default()).unwrap();
        let (magnitude, negative, exponent) =
            reconstruct_ht_magnitude(&mut reader, 74, false, false, 1).unwrap();
        assert!(!negative);
        assert_eq!(exponent, 1);
        assert_eq!(magnitude.to_u64(), Some(1));
        assert_eq!(reader.physical_bits_read(), 74);
    }

    #[test]
    fn ht_noninitial_context_uses_the_northern_boundary_stencil() {
        assert_eq!(crate::refinement::ht_noninitial_vlc_context(2, 0, 0, 0), 2);
        assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 8, 0, 0), 1);
        assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 2, 0), 1);
        assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 8, 0), 4);
        assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 0, 2), 4);
        assert_eq!(
            crate::refinement::ht_noninitial_vlc_context(2, 15, 15, 15),
            7
        );
        assert_eq!(crate::refinement::ht_noninitial_vlc_context(0, 0, 5, 0), 0);
    }

    #[test]
    fn ht_cleanup_context_preserves_both_northern_columns() {
        let metadata = decode_ht_cleanup_metadata(
            &[0x00, 0x00, 0xd5, 0xb4, 0x00],
            2,
            4,
            8,
            &ResourceLimits::default(),
        )
        .unwrap();
        assert_eq!(metadata.significant_samples, 8, "{metadata:?}");
        assert_eq!(metadata.quads[0].significance, 15);
        assert_eq!(metadata.quads[1].context, 5);
        assert_eq!(metadata.quads[1].significance, 15);
    }

    #[test]
    fn ht_cleanup_accepts_fused_mel_vlc_final_byte() {
        let metadata = decode_ht_cleanup_metadata(
            &[0xf0, 0x0c, 0xe3, 0x00],
            4,
            1,
            8,
            &ResourceLimits::default(),
        )
        .unwrap();
        assert_eq!(metadata.quads.len(), 2);
        assert_eq!(metadata.quads[0].significance, 5);
        assert_eq!(metadata.quads[1].significance, 5);
    }

    #[test]
    fn ht_cleanup_fusion_does_not_cross_bytes() {
        let limits = ResourceLimits::default();
        let segments = parse_ht_block_segments(&[0x00, 0x00, 0x04, 0x00], None, &limits).unwrap();
        let mut readers = HtCleanupReaders::new(segments.cleanup(), &limits).unwrap();
        for _ in 0..4 {
            readers.read_vlc_bit().unwrap();
        }
        for _ in 0..8 {
            readers.read_mel_bit().unwrap();
        }
        for _ in 0..8 {
            readers.read_vlc_bit().unwrap();
        }
        for _ in 0..8 {
            readers.read_mel_bit().unwrap();
        }
        readers.finish().unwrap();
        assert!(readers.read_mel_bit().is_err());
        assert!(readers.read_vlc_bit().is_err());
    }

    #[test]
    fn ht_cleanup_fusion_excludes_ff() {
        let limits = ResourceLimits::default();
        let segments = parse_ht_block_segments(&[0x00, 0xff, 0x04, 0x00], None, &limits).unwrap();
        let mut readers = HtCleanupReaders::new(segments.cleanup(), &limits).unwrap();
        for _ in 0..4 {
            readers.read_vlc_bit().unwrap();
        }
        for _ in 0..8 {
            readers.read_mel_bit().unwrap();
        }
        readers.read_vlc_bit().unwrap();
        assert!(readers.read_mel_bit().is_err());
    }

    #[test]
    fn legacy_partial_quality_reconstructs_signed_midpoints_without_changing_prefixes() {
        for negative in [false, true] {
            let mut plane = CodeBlockPlane::new(1, 1).unwrap();
            plane
                .mark_significant_at_bitplane(0, 0, 4, negative)
                .unwrap();
            assert_eq!(plane.coefficient(0, 0).unwrap().magnitude, 16);
            let sign = if negative { -1 } else { 1 };
            assert_eq!(plane.signed_coefficient(0, 0).unwrap(), sign * 24);
            for (bitplane, bit, expected) in
                [(3, false, 20), (2, true, 22), (1, true, 23), (0, true, 23)]
            {
                plane.apply_refinement_bit(0, 0, bitplane, bit).unwrap();
                assert_eq!(plane.signed_coefficient(0, 0).unwrap(), sign * expected);
            }
            assert_eq!(plane.coefficient(0, 0).unwrap().magnitude, 23);
        }
    }

    #[test]
    fn legacy_partial_pass_midpoints_are_coefficient_local() {
        let mut plane = CodeBlockPlane::new(2, 1).unwrap();
        plane.mark_significant_at_bitplane(0, 0, 3, false).unwrap();
        plane.mark_significant_at_bitplane(1, 0, 2, false).unwrap();
        assert_eq!(plane.signed_coefficient(0, 0).unwrap(), 12);
        assert_eq!(plane.signed_coefficient(1, 0).unwrap(), 6);
        plane.apply_refinement_bit(0, 0, 2, false).unwrap();
        assert_eq!(plane.signed_coefficient(0, 0).unwrap(), 10);
        assert_eq!(plane.signed_coefficient(1, 0).unwrap(), 6);
    }

    #[test]
    fn legacy_midpoint_reconstruction_preserves_wide_magnitudes() {
        for (bitplane, low, high) in [(64, 1_u64 << 63, 1), (65, 0, 3), (74, 0, 1536)] {
            let mut plane = CodeBlockPlane::new(1, 1).unwrap();
            plane
                .mark_significant_at_bitplane(0, 0, bitplane, false)
                .unwrap();
            let reconstructed = plane.coefficient(0, 0).unwrap().signed_magnitude().unwrap();
            assert_eq!(reconstructed.magnitude.limb(0), Some(low));
            assert_eq!(reconstructed.magnitude.limb(1), Some(high));
        }
    }

    #[test]
    fn ht_cleanup_rejects_cursor_collision_and_out_of_bounds_significance() {
        let limits = ResourceLimits::default();
        assert!(decode_ht_cleanup_metadata(&[0x02, 0x00], 1, 1, 1, &limits).is_err());
        assert!(decode_ht_cleanup_metadata(&[0x00, 0x03, 0x00], 1, 1, 1, &limits).is_err());
        let work_limited = limits.with_maximum_work_units(4).unwrap();
        assert!(matches!(
            decode_ht_cleanup_metadata(&[0x00, 0x63, 0x00], 1, 1, 1, &work_limited),
            Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                ..
            })
        ));
    }

    #[test]
    fn rejects_invalid_ht_cleanup_termination_and_limits() {
        let limits = ResourceLimits::default();
        assert!(parse_ht_block_segments(&[0x01], None, &limits).is_err());
        assert!(parse_ht_block_segments(&[0x01, 0x00], None, &limits).is_err());
        assert!(parse_ht_block_segments(&[0xff, 0xff], None, &limits).is_err());
        let byte_limited = limits.with_maximum_code_block_bytes(2).unwrap();
        assert!(matches!(
            parse_ht_block_segments(&[0x02, 0x00], Some(&[0]), &byte_limited),
            Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockBytes,
                limit: 2,
                actual: 3,
            })
        ));

        let ht = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
        let mut pass_limited_decoder =
            Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Ll, ht).unwrap();
        let pass_limited = limits.with_maximum_code_block_passes(1).unwrap();
        assert!(matches!(
            pass_limited_decoder.decode_high_throughput_segments(
                &[0x02, 0x00],
                1,
                Some(&[]),
                1,
                &pass_limited,
            ),
            Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlockPasses,
                ..
            })
        ));
        let mut work_limited_decoder =
            Tier1CodeBlockDecoder::new(2, 2, 1, SubbandOrientation::Ll, ht).unwrap();
        let work_limited = limits.with_maximum_work_units(1).unwrap();
        assert!(matches!(
            work_limited_decoder.decode_high_throughput_segments(
                &[0x02, 0x00],
                1,
                None,
                0,
                &work_limited,
            ),
            Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                ..
            })
        ));
    }

    #[test]
    fn segment_accounting_is_failure_atomic() {
        let mut accounting =
            CodeBlockSegmentAccounting::new(4, &ResourceLimits::default()).unwrap();
        assert_eq!(
            accounting.add_segment(1, 5).unwrap(),
            Tier1PassKind::Cleanup
        );
        assert_eq!(
            accounting.add_segment(2, 7).unwrap(),
            Tier1PassKind::SignificancePropagation
        );
        let previous = accounting;
        assert!(accounting.add_segment(2, 1).is_err());
        assert_eq!(accounting, previous);
        assert_eq!(accounting.total_passes(), 3);
        assert_eq!(accounting.total_bytes(), 12);
        assert_eq!(accounting.segments(), 2);
    }

    #[test]
    fn coefficient_state_and_neighbor_access_are_bounded() {
        let mut plane = CodeBlockPlane::new(3, 3).unwrap();
        plane.mark_significant(0, 1, 8, false).unwrap();
        plane.mark_significant(1, 0, 8, true).unwrap();
        plane.mark_significant(2, 2, 8, false).unwrap();
        let summary = plane.neighbor_summary(1, 1).unwrap();
        assert_eq!(summary.horizontal_significant, 1);
        assert_eq!(summary.vertical_significant, 1);
        assert_eq!(summary.diagonal_significant, 1);
        assert_eq!(summary.horizontal_sign_balance, 1);
        assert_eq!(summary.vertical_sign_balance, -1);

        plane.refine(0, 1, 4).unwrap();
        assert_eq!(plane.coefficient(0, 1).unwrap().magnitude, 12);
        assert!(plane.coefficient(0, 1).unwrap().refined);
        assert!(plane.coefficient(3, 0).is_err());
    }

    #[test]
    fn neighbor_summaries_match_all_local_sign_states_and_stripe_boundaries() {
        let mut patterns_checked = 0;
        for (width, height, x, y) in [
            (1_u16, 1_u16, 0_u16, 0_u16),
            (1, 5, 0, 3),
            (5, 1, 3, 0),
            (3, 5, 0, 0),
            (3, 5, 2, 4),
            (3, 5, 0, 3),
            (3, 5, 2, 3),
            (3, 5, 1, 2),
            (3, 5, 1, 3),
        ] {
            let mut neighbors = Vec::new();
            for dy in -1..=1 {
                for dx in -1..=1 {
                    if dx == 0 && dy == 0 {
                        continue;
                    }
                    let nx = i32::from(x) + dx;
                    let ny = i32::from(y) + dy;
                    if (0..i32::from(width)).contains(&nx) && (0..i32::from(height)).contains(&ny) {
                        neighbors.push((
                            u16::try_from(nx).unwrap(),
                            u16::try_from(ny).unwrap(),
                            dx,
                            dy,
                        ));
                    }
                }
            }
            let patterns = 3_u32.pow(u32::try_from(neighbors.len()).unwrap());
            for pattern in 0..patterns {
                patterns_checked += 1;
                let mut plane = CodeBlockPlane::new(width, height).unwrap();
                let mut remaining = pattern;
                let mut full = NeighborSummary::default();
                let mut causal = NeighborSummary::default();
                for &(nx, ny, dx, dy) in &neighbors {
                    let state = remaining % 3;
                    remaining /= 3;
                    if state == 0 {
                        continue;
                    }
                    let negative = state == 2;
                    plane.mark_significant(nx, ny, 1, negative).unwrap();
                    for (vertical_causal, summary) in [(false, &mut full), (true, &mut causal)] {
                        if vertical_causal && y % 4 == 3 && dy == 1 {
                            continue;
                        }
                        let sign = if negative { -1 } else { 1 };
                        if dy == 0 {
                            summary.horizontal_significant += 1;
                            summary.horizontal_sign_balance += sign;
                        } else if dx == 0 {
                            summary.vertical_significant += 1;
                            summary.vertical_sign_balance += sign;
                        } else {
                            summary.diagonal_significant += 1;
                        }
                    }
                }
                assert_eq!(plane.neighbor_summary(x, y).unwrap(), full);
                assert_eq!(
                    plane.neighbor_summary_with_causality(x, y, true).unwrap(),
                    causal,
                );
            }
        }
        assert_eq!(patterns_checked, 13_681);
    }

    #[test]
    fn forms_tier_one_contexts_from_neighbors() {
        let summary = NeighborSummary {
            horizontal_significant: 1,
            vertical_significant: 0,
            diagonal_significant: 1,
            horizontal_sign_balance: -1,
            vertical_sign_balance: 1,
        };
        assert_eq!(zero_coding_context(summary, SubbandOrientation::Lh), 6);
        assert_eq!(zero_coding_context(summary, SubbandOrientation::Hl), 3);
        assert_eq!(zero_coding_context(summary, SubbandOrientation::Hh), 4);
        assert_eq!(
            sign_context(summary),
            SignContext {
                context: 11,
                predicted_negative: true,
            }
        );
        assert_eq!(
            magnitude_refinement_context(CoefficientState::default(), summary),
            15
        );
        assert_eq!(
            magnitude_refinement_context(
                CoefficientState {
                    refined: true,
                    ..CoefficientState::default()
                },
                NeighborSummary::default(),
            ),
            16
        );
    }

    #[test]
    fn applies_significance_and_predicted_sign_atomically() {
        let mut plane = CodeBlockPlane::new(2, 1).unwrap();
        plane.mark_significant(0, 0, 8, true).unwrap();
        let step =
            apply_significance_decision(&mut plane, 1, 0, 4, SubbandOrientation::Lh, true, false)
                .unwrap();
        assert!(step.became_significant);
        assert_eq!(step.sign_context, Some(12));
        assert!(plane.coefficient(1, 0).unwrap().negative);
        let previous = plane.coefficient(1, 0).unwrap();
        assert!(
            apply_significance_decision(&mut plane, 1, 0, 2, SubbandOrientation::Lh, true, false,)
                .is_err()
        );
        assert_eq!(plane.coefficient(1, 0).unwrap(), previous);
    }

    #[test]
    fn refinement_records_zero_decisions_without_changing_magnitude() {
        let mut plane = CodeBlockPlane::new(1, 1).unwrap();
        plane.mark_significant(0, 0, 8, false).unwrap();
        plane.apply_refinement_decision(0, 0, 4, false).unwrap();
        assert_eq!(
            plane.coefficient(0, 0).unwrap(),
            CoefficientState {
                magnitude: 8,
                magnitude_high: [0; 5],
                legacy_bitplane: None,
                negative: false,
                significant: true,
                refined: true,
            }
        );
        assert!(plane.apply_refinement_decision(0, 0, 3, true).is_err());
    }

    #[test]
    fn tier_one_context_initialization_sets_normative_nonzero_states() {
        let limits = ResourceLimits::default();
        let baseline = MqDecoder::new(&[0], &limits).unwrap();
        let mut initialized = MqDecoder::new(&[0], &limits).unwrap();
        initialize_tier1_contexts(&mut initialized).unwrap();
        assert_ne!(
            initialized.context(0).unwrap(),
            baseline.context(0).unwrap()
        );
        assert_ne!(
            initialized.context(RUN_LENGTH_CONTEXT).unwrap(),
            baseline.context(RUN_LENGTH_CONTEXT).unwrap()
        );
        assert_ne!(
            initialized.context(UNIFORM_CONTEXT).unwrap(),
            baseline.context(UNIFORM_CONTEXT).unwrap()
        );
        assert_eq!(
            initialized.context(1).unwrap(),
            baseline.context(1).unwrap()
        );

        let expected_zero = initialized.context(0).unwrap();
        let expected_run = initialized.context(RUN_LENGTH_CONTEXT).unwrap();
        let _ = initialized.decode(0).unwrap();
        reset_tier1_contexts_after_pass(
            &mut initialized,
            Tier1CodingStyle::from_code_block_style(0x02).unwrap(),
        )
        .unwrap();
        assert_eq!(initialized.context(0).unwrap(), expected_zero);
        assert_eq!(
            initialized.context(RUN_LENGTH_CONTEXT).unwrap(),
            expected_run
        );
    }

    #[test]
    fn vertical_causal_context_ignores_the_next_stripe() {
        let mut plane = CodeBlockPlane::new(1, 5).unwrap();
        plane.mark_significant(0, 3, 8, false).unwrap();
        plane.mark_significant(0, 4, 8, false).unwrap();
        assert_eq!(
            plane
                .neighbor_summary_with_causality(0, 3, false)
                .unwrap()
                .vertical_significant,
            1
        );
        assert_eq!(
            plane
                .neighbor_summary_with_causality(0, 3, true)
                .unwrap()
                .vertical_significant,
            0
        );
        assert_eq!(
            plane
                .neighbor_summary_with_causality(0, 2, true)
                .unwrap()
                .vertical_significant,
            1
        );
    }

    #[test]
    fn raw_bypass_sign_bits_do_not_use_mq_sign_prediction() {
        let limits = ResourceLimits::default();
        for neighbor_negative in [false, true] {
            for negative in [false, true] {
                let mut plane = CodeBlockPlane::new(2, 1).unwrap();
                plane.mark_significant(0, 0, 8, neighbor_negative).unwrap();
                let mut state = Tier1BitplaneState::new(&plane, 4).unwrap();
                let bytes = [if negative { 0xc0 } else { 0x80 }];
                let mut reader = RawBitReader::new(&bytes, &limits).unwrap();
                decode_raw_significance_propagation_pass(
                    &mut plane,
                    &mut state,
                    &mut reader,
                    SubbandOrientation::Ll,
                    Tier1CodingStyle::from_code_block_style(0x01).unwrap(),
                )
                .unwrap();
                assert_eq!(plane.coefficient(1, 0).unwrap().negative, negative);
            }
        }
    }

    #[test]
    fn raw_bypass_decodes_significance_and_refinement_passes() {
        let limits = ResourceLimits::default();
        let style = Tier1CodingStyle::from_code_block_style(0x01).unwrap();
        let mut plane = CodeBlockPlane::new(2, 1).unwrap();
        plane.mark_significant(0, 0, 8, false).unwrap();
        let mut state = Tier1BitplaneState::new(&plane, 4).unwrap();
        let mut reader = RawBitReader::new(&[0x80], &limits).unwrap();

        let significance = decode_raw_significance_propagation_pass(
            &mut plane,
            &mut state,
            &mut reader,
            SubbandOrientation::Ll,
            style,
        )
        .unwrap();
        assert_eq!(significance.coefficients_scanned, 2);
        assert_eq!(significance.coding_symbols, 2);
        assert_eq!(significance.newly_significant, 1);

        let refinement =
            decode_raw_magnitude_refinement_pass(&mut plane, &mut state, &mut reader, style)
                .unwrap();
        assert_eq!(refinement.coefficients_scanned, 2);
        assert_eq!(refinement.coding_symbols, 1);
        assert_eq!(refinement.refined_coefficients, 1);
        assert_eq!(plane.coefficient(0, 0).unwrap().magnitude, 8);
        assert!(plane.coefficient(0, 0).unwrap().refined);
        assert_eq!(plane.coefficient(1, 0).unwrap().magnitude, 4);
        assert_eq!(reader.bytes_consumed(), 1);
    }

    #[test]
    fn traverses_all_three_passes_and_preserves_bitplane_eligibility() {
        let limits = ResourceLimits::default();
        let mut plane = CodeBlockPlane::new(3, 2).unwrap();
        plane.mark_significant(0, 0, 8, false).unwrap();
        let mut state = Tier1BitplaneState::new(&plane, 4).unwrap();
        let mut decoder = MqDecoder::new(&[0, 0, 0, 0], &limits).unwrap();
        initialize_tier1_contexts(&mut decoder).unwrap();

        let significance = decode_significance_propagation_pass(
            &mut plane,
            &mut state,
            &mut decoder,
            SubbandOrientation::Lh,
        )
        .unwrap();
        assert_eq!(significance.coefficients_scanned, 6);
        assert!(state.significance_propagation_complete());
        assert!(
            state
                .was_visited_by_significance_propagation(&plane, 1, 0)
                .unwrap()
        );

        let refinement =
            decode_magnitude_refinement_pass(&mut plane, &mut state, &mut decoder).unwrap();
        assert_eq!(refinement.coefficients_scanned, 6);
        assert_eq!(refinement.refined_coefficients, 1);
        assert!(plane.coefficient(0, 0).unwrap().refined);
        assert!(state.magnitude_refinement_complete());

        let cleanup =
            decode_cleanup_pass(&mut plane, &mut state, &mut decoder, SubbandOrientation::Lh)
                .unwrap();
        assert_eq!(cleanup.coefficients_scanned, 6);
        assert!(state.cleanup_complete());
        assert!(
            decode_cleanup_pass(&mut plane, &mut state, &mut decoder, SubbandOrientation::Lh,)
                .is_err()
        );
    }

    #[test]
    fn cleanup_uses_run_mode_only_for_complete_four_row_stripes() {
        let limits = ResourceLimits::default();
        let mut plane = CodeBlockPlane::new(1, 5).unwrap();
        let mut state = Tier1BitplaneState::new(&plane, 8).unwrap();
        let mut decoder = MqDecoder::new(&[0, 0, 0, 0], &limits).unwrap();
        initialize_tier1_contexts(&mut decoder).unwrap();

        let cleanup =
            decode_cleanup_pass(&mut plane, &mut state, &mut decoder, SubbandOrientation::Ll)
                .unwrap();
        assert_eq!(cleanup.coefficients_scanned, 5);
        assert_eq!(cleanup.run_mode_columns, 1);
        assert!(cleanup.coding_symbols >= 2);
        assert!(state.cleanup_complete());
        assert!(
            decode_significance_propagation_pass(
                &mut plane,
                &mut state,
                &mut decoder,
                SubbandOrientation::Ll,
            )
            .is_err()
        );
    }

    #[test]
    fn bitplane_state_rejects_invalid_masks_and_mismatched_planes() {
        let plane = CodeBlockPlane::new(2, 2).unwrap();
        assert!(Tier1BitplaneState::new(&plane, 0).is_err());
        assert!(Tier1BitplaneState::new(&plane, 3).is_err());

        let state = Tier1BitplaneState::new(&plane, 4).unwrap();
        let other_plane = CodeBlockPlane::new(1, 4).unwrap();
        assert!(
            state
                .was_visited_by_significance_propagation(&other_plane, 0, 0)
                .is_err()
        );
    }

    #[test]
    fn cleanup_validates_segmentation_symbols() {
        let limits = ResourceLimits::default();
        let style = Tier1CodingStyle::from_code_block_style(0x20).unwrap();
        let mut valid_plane = CodeBlockPlane::new(1, 1).unwrap();
        let mut valid_state = Tier1BitplaneState::new(&valid_plane, 8).unwrap();
        let mut valid_decoder = MqDecoder::new(&[0x01, 0xae], &limits).unwrap();
        initialize_tier1_contexts(&mut valid_decoder).unwrap();
        let statistics = decode_cleanup_pass_with_style(
            &mut valid_plane,
            &mut valid_state,
            &mut valid_decoder,
            SubbandOrientation::Ll,
            style,
        )
        .unwrap();
        assert!(statistics.coding_symbols >= 5);
        assert!(valid_state.cleanup_complete());

        let mut invalid_plane = CodeBlockPlane::new(1, 1).unwrap();
        let mut invalid_state = Tier1BitplaneState::new(&invalid_plane, 8).unwrap();
        let mut invalid_decoder = MqDecoder::new(&[0, 0], &limits).unwrap();
        initialize_tier1_contexts(&mut invalid_decoder).unwrap();
        assert!(
            decode_cleanup_pass_with_style(
                &mut invalid_plane,
                &mut invalid_state,
                &mut invalid_decoder,
                SubbandOrientation::Ll,
                style,
            )
            .is_err()
        );
        assert!(!invalid_state.cleanup_complete());
    }

    #[test]
    fn reconstructs_code_block_across_mq_and_raw_segments() {
        let limits = ResourceLimits::default();
        let style = Tier1CodingStyle::from_code_block_style(0x01).unwrap();
        let mut decoder =
            Tier1CodeBlockDecoder::new(1, 1, 5, SubbandOrientation::Ll, style).unwrap();

        let mq = decoder.decode_segment(&[0; 16], 10, &limits).unwrap();
        assert_eq!(mq.passes, 10);
        assert_eq!(decoder.next_pass(), 10);
        assert_eq!(decoder.decoded_segments(), 1);

        let raw = decoder.decode_segment(&[0], 2, &limits).unwrap();
        assert_eq!(raw.passes, 2);
        assert_eq!(decoder.next_pass(), 12);

        decoder.decode_segment(&[0; 4], 1, &limits).unwrap();
        assert!(decoder.is_complete());
        assert_eq!(decoder.maximum_passes(), 13);
        assert_eq!(decoder.decoded_segments(), 3);
        assert_eq!(decoder.decoded_bytes(), 21);
        assert_eq!(decoder.plane().coefficients().len(), 1);
        let coefficient = decoder.plane().coefficient(0, 0).unwrap();
        assert_eq!(
            decoder.plane().signed_coefficient(0, 0).unwrap(),
            if coefficient.negative {
                -(coefficient.magnitude as i64)
            } else {
                coefficient.magnitude as i64
            }
        );
        assert!(decoder.decode_segment(&[0], 1, &limits).is_err());
    }

    #[test]
    fn supports_sample_and_roi_adjusted_coefficient_bitplanes() {
        let decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            38,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .unwrap();
        assert_eq!(decoder.maximum_passes(), 112);
        assert_eq!(decoder.bitplane, 37);

        let roi_decoder = Tier1CodeBlockDecoder::new(
            1,
            1,
            292,
            SubbandOrientation::Ll,
            Tier1CodingStyle::default(),
        )
        .unwrap();
        assert_eq!(roi_decoder.maximum_passes(), 874);
        assert_eq!(roi_decoder.bitplane, 291);
        assert!(
            Tier1CodeBlockDecoder::new(
                1,
                1,
                293,
                SubbandOrientation::Ll,
                Tier1CodingStyle::default(),
            )
            .is_err()
        );

        let mut plane = CodeBlockPlane::new(1, 1).unwrap();
        plane
            .mark_significant_magnitude(0, 0, Magnitude::single_bit(291).unwrap(), false)
            .unwrap();
        assert_eq!(
            plane.coefficient(0, 0).unwrap().magnitude_limb(4),
            Some(1_u64 << 35)
        );
        plane.apply_refinement_bit(0, 0, 255, true).unwrap();
        assert_eq!(
            plane.coefficient(0, 0).unwrap().magnitude_limb(3),
            Some(1_u64 << 63)
        );
    }
}
