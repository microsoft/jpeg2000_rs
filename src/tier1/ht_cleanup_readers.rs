use super::ht_vlc_tables::{HT_VLC_INITIAL, HT_VLC_NON_INITIAL};
use super::state::{arithmetic_overflow, invalid_code_block};
use super::{
    HtBitPosition, HtCleanupReaders, HtForwardMagSgnReader, HtMelBitReader, HtReverseVlcReader,
    HtStreamDirection, MAX_HT_CLEANUP_BYTES, MAX_HT_SCUP,
};
#[cfg(verus_keep_ghost)]
use super::{
    ht_cleanup_readers_outcome, ht_cleanup_readers_view, ht_direction_forward, ht_magsgn_outcome,
    ht_magsgn_view, ht_mel_outcome, ht_mel_view, ht_position_view, ht_reverse_vlc_outcome,
    ht_reverse_vlc_view, ht_vlc_table_view,
};
use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures ht_magsgn_outcome(result) == crate::specs::ht_magsgn_initial(input@, maximum_work_units),
    )
)]
pub(super) fn ht_magsgn_from_input(
    input: &[u8],
    maximum_work_units: u64,
) -> Result<HtForwardMagSgnReader<'_>, DecodeError> {
    if input.len() > MAX_HT_CLEANUP_BYTES {
        return Err(invalid_code_block());
    }
    Ok(HtForwardMagSgnReader {
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
        maximum_work_units,
    })
}

impl<'a> HtForwardMagSgnReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        ht_magsgn_from_input(input, limits.maximum_work_units())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == ht_magsgn_view(self).physical_bits_read,))]
    pub const fn physical_bits_read(&self) -> u64 {
        self.physical_bits_read
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == ht_magsgn_view(self).fill_bits_read,))]
    pub const fn fill_bits_read(&self) -> u64 {
        self.fill_bits_read
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_magsgn_view(final(self))) == crate::specs::ht_magsgn_read_bits(ht_magsgn_view(old(self)), count),
        )
    )]
    pub fn read_bits(&mut self, count: u8) -> Result<u64, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_magsgn_view(self); }
        if count > 39 {
            return Err(invalid_code_block());
        }
        let mut value = 0_u64;
        let mut bit = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant bit <= count, count <= 39,
                    initial == ht_magsgn_view(old(self)),
                    crate::specs::ht_magsgn_read_bits(initial, count)
                        == crate::specs::ht_magsgn_word_run(ht_magsgn_view(self), (count - bit) as nat, bit as nat, value),
                decreases count - bit,
            )
        )]
        while bit < count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_magsgn_word_unfold(
                    ht_magsgn_view(self), (count - bit) as nat, bit as nat, value,
                );
            }
            if bit >= 64 {
                return Err(invalid_code_block());
            }
            if self.read_bit()? {
                value |= 1_u64 << bit;
            }
            bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_magsgn_word_unfold(ht_magsgn_view(self), 0, bit as nat, value);
        }
        Ok(value)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_magsgn_view(final(self))) == crate::specs::ht_magsgn_finish(ht_magsgn_view(old(self))),
        )
    )]
    pub fn finish(&mut self) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_magsgn_view(self); }
        let mut remaining_bits = self
            .input
            .len()
            .checked_mul(8)
            .ok_or_else(arithmetic_overflow)?;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant initial == ht_magsgn_view(old(self)),
                    crate::specs::ht_magsgn_finish(initial)
                    == crate::specs::ht_magsgn_finish_run(ht_magsgn_view(self), remaining_bits as nat),
                decreases remaining_bits,
            )
        )]
        while self.has_pending_physical_bits() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_magsgn_finish_unfold(ht_magsgn_view(self), remaining_bits as nat);
            }
            if remaining_bits == 0 {
                return Err(invalid_code_block());
            }
            remaining_bits -= 1;
            if !self.read_bit()? {
                return Err(invalid_code_block());
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_magsgn_finish_unfold(ht_magsgn_view(self), remaining_bits as nat);
        }
        Ok(())
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result => ensures result == crate::specs::ht_magsgn_pending(ht_magsgn_view(self)),)
    )]
    fn has_pending_physical_bits(&self) -> bool {
        (self.has_byte && self.current_is_physical && self.next_bit <= self.last_bit)
            || self.next_byte < self.input.len()
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_magsgn_view(final(self))) == crate::specs::ht_magsgn_read(ht_magsgn_view(old(self))),
        )
    )]
    #[inline(always)]
    pub(super) fn read_bit(&mut self) -> Result<bool, DecodeError> {
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
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.maximum_work_units,
                actual: self.work_units,
            });
        }
        Ok(bit)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_magsgn_view(final(self))) == crate::specs::ht_magsgn_load(ht_magsgn_view(old(self))),
        )
    )]
    fn load_byte(&mut self) -> Result<(), DecodeError> {
        let stuffed = self.previous_was_ff;
        if self.next_byte < self.input.len() {
            let value = *self
                .input
                .get(self.next_byte)
                .ok_or_else(invalid_code_block)?;
            if !crate::refinement::ht_forward_stuffing_valid(stuffed, value) {
                return Err(DecodeError::MalformedInput {
                    offset: self.next_byte as u64,
                    kind: MalformedKind::InvalidBitStuffing,
                });
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

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures ht_mel_outcome(result) == crate::specs::ht_mel_initial(input@, maximum_work_units),
    )
)]
fn ht_mel_from_input(
    input: &[u8],
    maximum_work_units: u64,
) -> Result<HtMelBitReader<'_>, DecodeError> {
    if input.is_empty() || input.len() > MAX_HT_SCUP - 1 {
        return Err(invalid_code_block());
    }
    let mut reader = HtMelBitReader {
        input,
        next_byte: 0,
        current_byte: 0,
        value: 0,
        next_bit: -1,
        previous_was_ff: false,
        bits_read: 0,
        maximum_work_units,
    };
    reader.load_byte()?;
    Ok(reader)
}

impl<'a> HtMelBitReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        ht_mel_from_input(input, limits.maximum_work_units())
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures ht_position_view(result) == crate::specs::ht_mel_position(ht_mel_view(self)),
        )
    )]
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result => ensures result == ht_mel_view(self).bits_read,)
    )]
    pub const fn bits_read(&self) -> u64 {
        self.bits_read
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_mel_view(final(self))) == crate::specs::ht_mel_read(ht_mel_view(old(self))),
        )
    )]
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
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.maximum_work_units,
                actual: self.bits_read,
            });
        }
        Ok(bit)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_mel_view(final(self))) == crate::specs::ht_mel_load(ht_mel_view(old(self))),
        )
    )]
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
            return Err(DecodeError::MalformedInput {
                offset: index as u64,
                kind: MalformedKind::InvalidBitStuffing,
            });
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

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures ht_reverse_vlc_outcome(result) == crate::specs::ht_reverse_vlc_initial(input@, maximum_work_units),
    )
)]
fn ht_reverse_vlc_from_input(
    input: &[u8],
    maximum_work_units: u64,
) -> Result<HtReverseVlcReader<'_>, DecodeError> {
    if input.len() < 2 || input.len() > MAX_HT_SCUP {
        return Err(invalid_code_block());
    }
    let current_byte = input.len().checked_sub(2).ok_or_else(arithmetic_overflow)?;
    let value = *input.get(current_byte).ok_or_else(invalid_code_block)?;
    let nibble = value >> 4;
    Ok(HtReverseVlcReader {
        input,
        current_byte,
        value,
        next_bit: 4,
        last_bit: if nibble & 0x07 == 0x07 { 6 } else { 7 },
        has_byte: true,
        later_byte_requires_unstuffing: value | 0x0f > 0x8f,
        bits_read: 0,
        maximum_work_units,
    })
}

impl<'a> HtReverseVlcReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        ht_reverse_vlc_from_input(input, limits.maximum_work_units())
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures ht_position_view(result) == crate::specs::ht_reverse_vlc_position(ht_reverse_vlc_view(self)),
        )
    )]
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result => ensures result == ht_reverse_vlc_view(self).bits_read,)
    )]
    pub const fn bits_read(&self) -> u64 {
        self.bits_read
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_reverse_vlc_view(final(self)))
                == crate::specs::ht_reverse_vlc_read(ht_reverse_vlc_view(old(self))),
        )
    )]
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
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.maximum_work_units,
                actual: self.bits_read,
            });
        }
        if self.next_bit > self.last_bit {
            self.load_previous_byte()?;
        }
        Ok(bit)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_reverse_vlc_view(final(self)))
                == crate::specs::ht_reverse_vlc_load(ht_reverse_vlc_view(old(self))),
        )
    )]
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

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures ht_cleanup_readers_outcome(result) == crate::specs::ht_cleanup_readers_initial(
            mel_input@, vlc_input@, maximum_work_units,
        ),
    )
)]
pub(super) fn ht_cleanup_readers_from_inputs<'a>(
    mel_input: &'a [u8],
    vlc_input: &'a [u8],
    maximum_work_units: u64,
) -> Result<HtCleanupReaders<'a>, DecodeError> {
    Ok(HtCleanupReaders {
        mel: ht_mel_from_input(mel_input, maximum_work_units)?,
        vlc: ht_reverse_vlc_from_input(vlc_input, maximum_work_units)?,
        mel_last_byte: None,
        vlc_last_byte: None,
        terminal_byte: u16::try_from(
            vlc_input
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
        maximum_work_units,
    })
}

impl<'a> HtCleanupReaders<'a> {
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_cleanup_reader_tick(ht_cleanup_readers_view(old(self))),
        )
    )]
    pub(super) fn tick(&mut self) -> Result<(), DecodeError> {
        self.work_units = self
            .work_units
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        if self.work_units > self.maximum_work_units {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.maximum_work_units,
                actual: self.work_units,
            });
        }
        Ok(())
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures result == crate::specs::ht_cleanup_reader_can_claim(
                ht_cleanup_readers_view(self), ht_direction_forward(direction), byte,
            ),
        )
    )]
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_cleanup_reader_read_mel(ht_cleanup_readers_view(old(self))),
        )
    )]
    pub(super) fn read_mel_bit(&mut self) -> Result<bool, DecodeError> {
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_cleanup_reader_read_vlc(ht_cleanup_readers_view(old(self))),
        )
    )]
    pub(super) fn read_vlc_bit(&mut self) -> Result<bool, DecodeError> {
        let position = self.vlc.next_position().ok_or_else(invalid_code_block)?;
        if !self.can_claim_byte(HtStreamDirection::Reverse, position.byte) {
            return Err(invalid_code_block());
        }
        let bit = self.vlc.read_bit()?;
        self.vlc_last_byte = Some(position.byte);
        self.tick()?;
        Ok(bit)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures result == crate::specs::ht_cleanup_peek_vlc(ht_cleanup_readers_view(self), count),
        )
    )]
    pub(super) fn peek_vlc(&self, count: u8) -> u16 {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
        let mut copy = self.vlc;
        let mut value = 0_u16;
        let mut bit = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_cleanup_peek_unfold(initial, ht_reverse_vlc_view(&copy), 0, 0, value);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant bit <= count,
                    initial == ht_cleanup_readers_view(self),
                invariant_except_break
                    crate::specs::ht_cleanup_peek_vlc(initial, count)
                        == crate::specs::ht_cleanup_peek_run(initial, ht_reverse_vlc_view(&copy), (count - bit) as nat, bit as nat, value),
                    crate::specs::ht_cleanup_peek_run(initial, ht_reverse_vlc_view(&copy), 0, bit as nat, value) == value,
                ensures value == crate::specs::ht_cleanup_peek_vlc(initial, count),
                decreases count - bit,
            )
        )]
        while bit < count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_cleanup_peek_unfold(
                    initial, ht_reverse_vlc_view(&copy), (count - bit) as nat, bit as nat, value,
                );
            }
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
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_cleanup_peek_unfold(initial, ht_reverse_vlc_view(&copy), 0, bit as nat, value);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if bit == count {
                crate::proofs::production_impl::production_ht_cleanup_peek_unfold(initial, ht_reverse_vlc_view(&copy), 0, bit as nat, value);
            }
        }
        value
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_cleanup_advance_vlc(ht_cleanup_readers_view(old(self)), count as nat),
        )
    )]
    pub(super) fn advance_vlc(&mut self, count: u8) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
        let mut consumed = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant consumed <= count, initial == ht_cleanup_readers_view(old(self)),
                    crate::specs::ht_cleanup_advance_vlc(initial, count as nat)
                        == crate::specs::ht_cleanup_advance_vlc(ht_cleanup_readers_view(self), (count - consumed) as nat),
                decreases count - consumed,
            )
        )]
        while consumed < count {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_cleanup_advance_unfold(
                    ht_cleanup_readers_view(self), (count - consumed) as nat,
                );
            }
            let _ = self.read_vlc_bit()?;
            consumed = consumed.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_cleanup_advance_unfold(ht_cleanup_readers_view(self), 0);
        }
        Ok(())
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_cleanup_mel_event(ht_cleanup_readers_view(old(self))),
        )
    )]
    pub(super) fn mel_event(&mut self) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
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
                    invariant decoded <= exponent, exponent <= 5,
                        initial == ht_cleanup_readers_view(old(self)),
                        crate::specs::ht_cleanup_mel_event(initial)
                            == crate::specs::ht_cleanup_mel_complete_suffix(
                                crate::specs::ht_cleanup_mel_suffix(ht_cleanup_readers_view(self), (exponent - decoded) as nat, suffix)),
                    decreases exponent - decoded,
                )
            )]
            while decoded < exponent {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_ht_cleanup_mel_suffix_unfold(
                        ht_cleanup_readers_view(self), (exponent - decoded) as nat, suffix,
                    );
                }
                suffix <<= 1;
                if self.read_mel_bit()? {
                    suffix |= 1;
                }
                decoded = decoded.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_cleanup_mel_suffix_unfold(
                    ht_cleanup_readers_view(self), 0, suffix,
                );
            }
            self.mel_zero_events = suffix;
            self.mel_terminating_one = true;
            self.mel_state = crate::refinement::ht_mel_next_state(self.mel_state, false);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::ht_cleanup_mel_event(initial)
                == crate::specs::ht_cleanup_mel_emit(ht_cleanup_readers_view(self)));
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self))) == crate::specs::ht_cleanup_quad_word(
                ht_cleanup_readers_view(old(self)), ht_vlc_table_view(initial), context,
            ),
        )
    )]
    pub(super) fn decode_quad_word(
        &mut self,
        initial: bool,
        context: u8,
    ) -> Result<u16, DecodeError> {
        if context > 7 {
            return Err(invalid_code_block());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let word = crate::specs::ht_cleanup_peek_vlc(ht_cleanup_readers_view(self), 7);
            assert(word & 0x7fu16 <= 127) by (bit_vector);
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_uvlc_prefix(ht_cleanup_readers_view(old(self))),
        )
    )]
    pub(super) fn read_prefix(&mut self) -> Result<(u8, u8, u8), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_uvlc_prefix); }
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_uvlc_suffix(ht_cleanup_readers_view(old(self)), length),
        )
    )]
    pub(super) fn read_suffix(&mut self, length: u8) -> Result<u8, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
        let mut value = 0_u8;
        let mut bit = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant bit <= length, initial == ht_cleanup_readers_view(old(self)),
                    crate::specs::ht_uvlc_suffix(initial, length)
                        == crate::specs::ht_uvlc_suffix_run(ht_cleanup_readers_view(self), (length - bit) as nat, bit as nat, value),
                decreases length - bit,
            )
        )]
        while bit < length {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_uvlc_suffix_unfold(
                    ht_cleanup_readers_view(self), (length - bit) as nat, bit as nat, value,
                );
            }
            if self.read_vlc_bit()? {
                if bit >= 8 {
                    return Err(invalid_code_block());
                }
                value |= 1_u8 << bit;
            }
            bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_uvlc_suffix_unfold(ht_cleanup_readers_view(self), 0, bit as nat, value);
        }
        Ok(value)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_uvlc_prefix_value(ht_cleanup_readers_view(old(self))),
        )
    )]
    pub(super) fn prefix_value(&mut self) -> Result<(u8, u8), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_uvlc_prefix_value); }
        let (base, suffix_length, prefix_length) = self.read_prefix()?;
        let suffix = self.read_suffix(suffix_length)?;
        let value = base.checked_add(suffix).ok_or_else(arithmetic_overflow)?;
        Ok((value, prefix_length))
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_uvlc_initial(ht_cleanup_readers_view(old(self)), mode),
        )
    )]
    pub(super) fn decode_initial_u(&mut self, mode: u8) -> Result<[u8; 2], DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
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
                    values[1] = (if self.read_vlc_bit()? { 1_u8 } else { 0_u8 })
                        .checked_add(2)
                        .ok_or_else(arithmetic_overflow)?;
                    values[0] = base_0
                        .checked_add(self.read_suffix(suffix_0)?)
                        .ok_or_else(arithmetic_overflow)?
                        .checked_add(1)
                        .ok_or_else(arithmetic_overflow)?;
                } else {
                    let (base_1, suffix_1, _) = self.read_prefix()?;
                    values[0] = base_0
                        .checked_add(self.read_suffix(suffix_0)?)
                        .ok_or_else(arithmetic_overflow)?
                        .checked_add(1)
                        .ok_or_else(arithmetic_overflow)?;
                    values[1] = base_1
                        .checked_add(self.read_suffix(suffix_1)?)
                        .ok_or_else(arithmetic_overflow)?
                        .checked_add(1)
                        .ok_or_else(arithmetic_overflow)?;
                }
            }
            4 => {
                let (base_0, suffix_0, _) = self.read_prefix()?;
                let (base_1, suffix_1, _) = self.read_prefix()?;
                values[0] = ht_uvlc_byte(base_0, self.read_suffix(suffix_0)?, 3)?;
                values[1] = ht_uvlc_byte(base_1, self.read_suffix(suffix_1)?, 3)?;
            }
            _ => return Err(invalid_code_block()),
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let expected = crate::specs::ht_uvlc_initial(initial, mode);
            assert(expected.0.is_ok());
            assert(expected.1 == ht_cleanup_readers_view(self));
            match expected.0 {
                Ok(expected_values) => {
                    assert(values@ =~= expected_values@);
                    vstd::array::axiom_array_ext_equal(values, expected_values);
                    assert(values =~= expected_values);
                },
                Err(_) => { assert(false); },
            }
        }
        Ok(values)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_uvlc_non_initial(ht_cleanup_readers_view(old(self)), mode),
        )
    )]
    pub(super) fn decode_non_initial_u(&mut self, mode: u8) -> Result<[u8; 2], DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
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
                values[0] = ht_uvlc_byte(base_0, self.read_suffix(suffix_0)?, 1)?;
                values[1] = ht_uvlc_byte(base_1, self.read_suffix(suffix_1)?, 1)?;
            }
            _ => return Err(invalid_code_block()),
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let expected = crate::specs::ht_uvlc_non_initial(initial, mode);
            assert(expected.0.is_ok());
            assert(expected.1 == ht_cleanup_readers_view(self));
            match expected.0 {
                Ok(expected_values) => {
                    assert(values@ =~= expected_values@);
                    vstd::array::axiom_array_ext_equal(values, expected_values);
                    assert(values =~= expected_values);
                },
                Err(_) => { assert(false); },
            }
        }
        Ok(values)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures result == crate::specs::ht_cleanup_readers_finish(ht_cleanup_readers_view(self)),
        )
    )]
    pub(super) fn finish(&self) -> Result<(), DecodeError> {
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

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::ht_uvlc_byte(base, suffix, bias),)
)]
pub(super) fn ht_uvlc_byte(base: u8, suffix: u8, bias: u8) -> Result<u8, DecodeError> {
    match u8::try_from(crate::refinement::ht_uvlc_value(base, suffix, bias)) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}
