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

#[cfg(verus_keep_ghost)]
verus! {
    use crate::specs::{HtCleanupReaderState, HtMagSgnState, HtReverseVlcState};

    pub(super) open spec fn magsgn_resident(state: HtMagSgnState, width: u8) -> bool {
        state.has_byte && state.current_is_physical
            && state.next_bit as int + width <= state.last_bit as int + 1 <= 8
            && state.work_units as int + width <= state.maximum_work_units
            && state.physical_bits_read as int + width <= u64::MAX
    }

    pub(super) open spec fn magsgn_field(state: HtMagSgnState, width: u8) -> u8 {
        (((state.value >> state.next_bit) as u16) & (0xffu16 >> ((8 - width) as u8))) as u8
    }

    pub(super) open spec fn magsgn_consumed(state: HtMagSgnState, width: u8) -> HtMagSgnState {
        HtMagSgnState {
            next_bit: (state.next_bit + width) as u8,
            physical_bits_read: (state.physical_bits_read + width) as u64,
            work_units: (state.work_units + width) as u64,
            ..state
        }
    }

    spec fn vlc_resident_byte(owner: HtCleanupReaderState, copy: HtReverseVlcState, width: u8) -> bool {
        copy.has_byte
            && copy.current_byte <= u16::MAX
            && copy.current_byte <= copy.input.len()
            && copy.next_bit as int + width <= copy.last_bit as int + 1 <= 8
            && copy.bits_read as int + width <= copy.maximum_work_units
            && crate::specs::ht_cleanup_reader_can_claim(owner, false, copy.current_byte as u16)
    }

    spec fn vlc_resident_field(copy: HtReverseVlcState, width: u8) -> u16 {
        ((copy.value >> copy.next_bit) as u16) & (0xffu16 >> ((8 - width) as u8))
    }

    spec fn vlc_after_resident(copy: HtReverseVlcState, width: u8) -> HtReverseVlcState {
        let advanced = HtReverseVlcState {
            next_bit: (copy.next_bit + width) as u8,
            bits_read: (copy.bits_read + width) as u64,
            ..copy
        };
        if width > 0 && advanced.next_bit > copy.last_bit {
            crate::specs::ht_reverse_vlc_load(advanced).1
        } else {
            advanced
        }
    }

    proof fn vlc_peek_resident_equivalence(
        owner: HtCleanupReaderState,
        copy: HtReverseVlcState,
        remaining: nat,
        index: u8,
        value: u16,
        width: u8,
    )
        requires
            vlc_resident_byte(owner, copy, width),
            width <= remaining,
            index as int + remaining <= 16,
        ensures
            crate::specs::ht_cleanup_peek_run(owner, copy, remaining, index as nat, value)
                == crate::specs::ht_cleanup_peek_run(
                    owner,
                    vlc_after_resident(copy, width),
                    (remaining - width) as nat,
                    (index + width) as nat,
                    value | (vlc_resident_field(copy, width) << index),
                ),
        decreases width,
    {
        if width == 0 {
            let shifted = (copy.value >> copy.next_bit) as u16;
            let field = vlc_resident_field(copy, 0);
            assert(field == 0 && (value | (field << index)) == value) by (bit_vector)
                requires field == (shifted & (0xffu16 >> 8u8)), index <= 16;
        } else {
            crate::proofs::production_impl::production_ht_cleanup_peek_unfold(
                owner, copy, remaining, index as nat, value,
            );
            let read = crate::specs::ht_reverse_vlc_read(copy);
            let bit = ((copy.value >> copy.next_bit) & 1u8) != 0;
            let next_val = if bit { value | (1u16 << index) } else { value };
            let field = vlc_resident_field(copy, width);
            if width == 1 {
                assert(read == (Ok::<bool, DecodeError>(bit), vlc_after_resident(copy, 1)));
                let bval = copy.value;
                let pos = copy.next_bit;
                assert(next_val == (value | (field << index))) by (bit_vector)
                    requires
                        pos < 8,
                        index < 16,
                        bit == (((bval >> pos) & 1u8) != 0),
                        field == (((bval >> pos) as u16) & (0xffu16 >> 7u8)),
                        next_val == if bit { value | (1u16 << index) } else { value };
            } else {
                let next_copy = HtReverseVlcState {
                    next_bit: (copy.next_bit + 1) as u8,
                    bits_read: (copy.bits_read + 1) as u64,
                    ..copy
                };
                assert(read == (Ok::<bool, DecodeError>(bit), next_copy));
                let rest = (width - 1) as u8;
                vlc_peek_resident_equivalence(
                    owner,
                    next_copy,
                    (remaining - 1) as nat,
                    (index + 1) as u8,
                    next_val,
                    rest,
                );
                let tail = vlc_resident_field(next_copy, rest);
                let bval = copy.value;
                let pos = copy.next_bit;
                let pos1 = next_copy.next_bit;
                let idx1 = (index + 1) as u8;
                assert((next_val | (tail << idx1)) == (value | (field << index))) by (bit_vector)
                    requires
                        1 < width <= 8,
                        rest == sub(width, 1u8),
                        pos < 7,
                        pos1 == add(pos, 1u8),
                        index < 15,
                        idx1 == add(index, 1u8),
                        bit == (((bval >> pos) & 1u8) != 0),
                        field == (((bval >> pos) as u16) & (0xffu16 >> sub(8u8, width))),
                        tail == (((bval >> pos1) as u16) & (0xffu16 >> sub(8u8, rest))),
                        next_val == if bit { value | (1u16 << index) } else { value };
                assert(vlc_after_resident(next_copy, rest) == vlc_after_resident(copy, width));
            }
        }
    }

    proof fn vlc_advance_resident_equivalence(
        state: HtCleanupReaderState,
        count: nat,
        width: u8,
    )
        requires
            width <= count,
            vlc_resident_byte(state, state.vlc, width),
            state.work_units as int + width <= state.maximum_work_units,
        ensures
            crate::specs::ht_cleanup_advance_vlc(state, count)
                == crate::specs::ht_cleanup_advance_vlc(
                    HtCleanupReaderState {
                        vlc: vlc_after_resident(state.vlc, width),
                        vlc_last_byte: if width > 0 {
                            Some(state.vlc.current_byte as u16)
                        } else {
                            state.vlc_last_byte
                        },
                        work_units: (state.work_units + width) as u64,
                        ..state
                    },
                    (count - width) as nat,
                ),
        decreases width,
    {
        if width > 0 {
            crate::proofs::production_impl::production_ht_cleanup_advance_unfold(state, count);
            let read = crate::specs::ht_cleanup_reader_read_vlc(state);
            let next_vlc = if width == 1 {
                vlc_after_resident(state.vlc, 1)
            } else {
                HtReverseVlcState {
                    next_bit: (state.vlc.next_bit + 1) as u8,
                    bits_read: (state.vlc.bits_read + 1) as u64,
                    ..state.vlc
                }
            };
            let next_state = HtCleanupReaderState {
                vlc: next_vlc,
                vlc_last_byte: Some(state.vlc.current_byte as u16),
                work_units: (state.work_units + 1) as u64,
                ..state
            };
            assert(read.0.is_ok() && read.1 == next_state);
            if width > 1 {
                let rest = (width - 1) as u8;
                vlc_advance_resident_equivalence(next_state, (count - 1) as nat, rest);
                assert(vlc_after_resident(next_vlc, rest) == vlc_after_resident(state.vlc, width));
            }
        }
    }

    proof fn vlc_suffix_resident_equivalence(
        state: HtCleanupReaderState,
        remaining: nat,
        index: u8,
        value: u8,
        width: u8,
    )
        requires
            width <= remaining,
            index as int + remaining <= 8,
            vlc_resident_byte(state, state.vlc, width),
            state.work_units as int + width <= state.maximum_work_units,
        ensures
            crate::specs::ht_uvlc_suffix_run(state, remaining, index as nat, value)
                == crate::specs::ht_uvlc_suffix_run(
                    HtCleanupReaderState {
                        vlc: vlc_after_resident(state.vlc, width),
                        vlc_last_byte: if width > 0 {
                            Some(state.vlc.current_byte as u16)
                        } else {
                            state.vlc_last_byte
                        },
                        work_units: (state.work_units + width) as u64,
                        ..state
                    },
                    (remaining - width) as nat,
                    (index + width) as nat,
                    value | ((vlc_resident_field(state.vlc, width) as u8) << index),
                ),
        decreases width,
    {
        if width == 0 {
            let shifted = (state.vlc.value >> state.vlc.next_bit) as u16;
            let field = vlc_resident_field(state.vlc, 0) as u8;
            assert(field == 0 && (value | (field << index)) == value) by (bit_vector)
                requires field == ((shifted & (0xffu16 >> 8u8)) as u8), index <= 8;
        } else {
            crate::proofs::production_impl::production_ht_uvlc_suffix_unfold(
                state, remaining, index as nat, value,
            );
            let read = crate::specs::ht_cleanup_reader_read_vlc(state);
            let bit = ((state.vlc.value >> state.vlc.next_bit) & 1u8) != 0;
            let next_val = if bit { value | (1u8 << index) } else { value };
            let field = vlc_resident_field(state.vlc, width) as u8;
            if width == 1 {
                let next_state = HtCleanupReaderState {
                    vlc: vlc_after_resident(state.vlc, 1),
                    vlc_last_byte: Some(state.vlc.current_byte as u16),
                    work_units: (state.work_units + 1) as u64,
                    ..state
                };
                assert(read == (Ok::<bool, DecodeError>(bit), next_state));
                let bval = state.vlc.value;
                let pos = state.vlc.next_bit;
                assert(next_val == (value | (field << index))) by (bit_vector)
                    requires
                        pos < 8,
                        index < 8,
                        bit == (((bval >> pos) & 1u8) != 0),
                        field == ((((bval >> pos) as u16) & (0xffu16 >> 7u8)) as u8),
                        next_val == if bit { value | (1u8 << index) } else { value };
            } else {
                let next_vlc = HtReverseVlcState {
                    next_bit: (state.vlc.next_bit + 1) as u8,
                    bits_read: (state.vlc.bits_read + 1) as u64,
                    ..state.vlc
                };
                let next_state = HtCleanupReaderState {
                    vlc: next_vlc,
                    vlc_last_byte: Some(state.vlc.current_byte as u16),
                    work_units: (state.work_units + 1) as u64,
                    ..state
                };
                assert(read == (Ok::<bool, DecodeError>(bit), next_state));
                let rest = (width - 1) as u8;
                vlc_suffix_resident_equivalence(
                    next_state,
                    (remaining - 1) as nat,
                    (index + 1) as u8,
                    next_val,
                    rest,
                );
                let tail = vlc_resident_field(next_vlc, rest) as u8;
                let bval = state.vlc.value;
                let pos = state.vlc.next_bit;
                let pos1 = next_vlc.next_bit;
                let idx1 = (index + 1) as u8;
                assert((next_val | (tail << idx1)) == (value | (field << index))) by (bit_vector)
                    requires
                        1 < width <= 8,
                        rest == sub(width, 1u8),
                        pos < 7,
                        pos1 == add(pos, 1u8),
                        index < 7,
                        idx1 == add(index, 1u8),
                        bit == (((bval >> pos) & 1u8) != 0),
                        field == ((((bval >> pos) as u16) & (0xffu16 >> sub(8u8, width))) as u8),
                        tail == ((((bval >> pos1) as u16) & (0xffu16 >> sub(8u8, rest))) as u8),
                        next_val == if bit { value | (1u8 << index) } else { value };
                assert(vlc_after_resident(next_vlc, rest) == vlc_after_resident(state.vlc, width));
            }
        }
    }
}

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
            ensures (result, ht_magsgn_view(final(self))) == (
                if !ht_magsgn_view(old(self)).has_byte || ht_magsgn_view(old(self)).next_bit > ht_magsgn_view(old(self)).last_bit {
                    crate::specs::ht_magsgn_load(ht_magsgn_view(old(self)))
                } else {
                    (Ok(()), ht_magsgn_view(old(self)))
                }
            ),
        )
    )]
    #[inline(always)]
    pub(super) fn ensure_byte(&mut self) -> Result<(), DecodeError> {
        if !self.has_byte || self.next_bit > self.last_bit {
            self.load_byte()?;
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result {
            None => ht_magsgn_view(final(self)) == ht_magsgn_view(old(self)),
            Some((width, field)) => {
                let start = ht_magsgn_view(old(self));
                1 <= width <= remaining && width <= 8
                    && magsgn_resident(start, width) && field == magsgn_field(start, width)
                    && ht_magsgn_view(final(self)) == magsgn_consumed(start, width)
            },
        },
    ))]
    #[inline(always)]
    pub(super) fn take_resident_physical(&mut self, remaining: u8) -> Option<(u8, u8)> {
        if !self.has_byte
            || !self.current_is_physical
            || self.last_bit >= 8
            || self.next_bit > self.last_bit
        {
            return None;
        }
        let width = remaining.min(self.last_bit - self.next_bit + 1);
        if width == 0 {
            return None;
        }
        // Do not take a shorter partial batch on budget/overflow failure:
        // the checked bit path must commit exactly the original error prefix.
        let work = self.work_units.checked_add(u64::from(width))?;
        if work > self.maximum_work_units {
            return None;
        }
        let physical = self.physical_bits_read.checked_add(u64::from(width))?;
        let field = (u16::from(self.value >> self.next_bit) & (0xff_u16 >> (8 - width))) as u8;
        self.next_bit += width;
        self.physical_bits_read = physical;
        self.work_units = work;
        Some((width, field))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires 1 <= remaining <= 16,
        ensures match result {
            None => ht_magsgn_view(final(self)) == ht_magsgn_view(old(self)),
            Some((w1, f1, w2, f2)) => {
                let start = ht_magsgn_view(old(self));
                let after1 = magsgn_consumed(start, w1);
                let loaded = crate::specs::ht_magsgn_load(after1);
                1 <= w1 <= 8 && 1 <= w2 <= 8 && w1 + w2 == remaining
                    && magsgn_resident(start, w1) && f1 == magsgn_field(start, w1)
                    && (!after1.has_byte || after1.next_bit > after1.last_bit)
                    && loaded.0.is_ok()
                    && magsgn_resident(loaded.1, w2) && f2 == magsgn_field(loaded.1, w2)
                    && ht_magsgn_view(final(self)) == magsgn_consumed(loaded.1, w2)
            },
        },
    ))]
    #[inline(always)]
    pub(super) fn take_resident_physical_two(&mut self, remaining: u8) -> Option<(u8, u8, u8, u8)> {
        if !self.has_byte
            || !self.current_is_physical
            || self.last_bit >= 8
            || self.next_bit > self.last_bit
            || self.previous_was_ff
            || self.next_byte >= self.input.len()
        {
            return None;
        }
        let w1 = self.last_bit - self.next_bit + 1;
        if remaining <= w1 {
            return None;
        }
        let w2 = remaining - w1;
        if w2 > 8 {
            return None;
        }
        let next_index = self.next_byte.checked_add(1)?;
        let work = self.work_units.checked_add(u64::from(remaining))?;
        if work > self.maximum_work_units {
            return None;
        }
        let physical = self.physical_bits_read.checked_add(u64::from(remaining))?;
        let f1 = (u16::from(self.value >> self.next_bit) & (0xff_u16 >> (8 - w1))) as u8;
        let b1 = self.input[self.next_byte];
        let f2 = (u16::from(b1) & (0xff_u16 >> (8 - w2))) as u8;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((((b1 >> 0u8) as u16) & (0xffu16 >> sub(8u8, w2))) == ((b1 as u16) & (0xffu16 >> sub(8u8, w2)))) by (bit_vector)
                requires 1 <= w2 <= 8;
        }
        self.value = b1;
        self.next_byte = next_index;
        self.next_bit = w2;
        self.last_bit = 7;
        self.previous_was_ff = b1 == 0xff;
        self.physical_bits_read = physical;
        self.work_units = work;
        Some((w1, f1, w2, f2))
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline(always)]
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
    #[inline(always)]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub(super) fn peek_vlc(&self, count: u8) -> u16 {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
        if count > 0
            && count <= 8
            && self.vlc.has_byte
            && self.vlc.last_bit < 8
            && self.vlc.next_bit <= self.vlc.last_bit
            && self.vlc.current_byte <= usize::from(u16::MAX)
            && self.vlc.current_byte <= self.vlc.input.len()
            && self.vlc.bits_read <= self.vlc.maximum_work_units
            && u64::from(count) <= self.vlc.maximum_work_units - self.vlc.bits_read
        {
            let byte = self.vlc.current_byte as u16;
            if self.can_claim_byte(HtStreamDirection::Reverse, byte) {
                let avail = self.vlc.last_bit - self.vlc.next_bit + 1;
                if avail >= count {
                    let value =
                        u16::from(self.vlc.value >> self.vlc.next_bit) & (0xff_u16 >> (8 - count));
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        vlc_peek_resident_equivalence(initial, initial.vlc, count as nat, 0, 0, count);
                        crate::proofs::production_impl::production_ht_cleanup_peek_unfold(
                            initial, vlc_after_resident(initial.vlc, count), 0, count as nat, value,
                        );
                        assert((0u16 | (value << 0u8)) == value) by (bit_vector);
                    }
                    return value;
                } else if self.vlc.current_byte > 0 {
                    let prev_idx = self.vlc.current_byte - 1;
                    if prev_idx < self.vlc.input.len()
                        && self.can_claim_byte(HtStreamDirection::Reverse, prev_idx as u16)
                    {
                        let prev_val = self.vlc.input[prev_idx];
                        let prev_bits = crate::refinement::ht_reverse_data_bits(
                            self.vlc.later_byte_requires_unstuffing,
                            prev_val,
                        );
                        let rem = count - avail;
                        if rem <= prev_bits {
                            let low = u16::from(self.vlc.value >> self.vlc.next_bit)
                                & (0xff_u16 >> (8 - avail));
                            let high = u16::from(prev_val) & (0xff_u16 >> (8 - rem));
                            let value = low | (high << avail);
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                vlc_peek_resident_equivalence(initial, initial.vlc, count as nat, 0, 0, avail);
                                assert((0u16 | (low << 0u8)) == low) by (bit_vector);
                                let mid = vlc_after_resident(initial.vlc, avail);
                                assert(mid.has_byte && mid.current_byte == prev_idx && mid.value == prev_val
                                    && mid.next_bit == 0 && mid.last_bit == prev_bits - 1);
                                assert(vlc_resident_field(mid, rem) == high) by (bit_vector)
                                    requires
                                        1 <= rem <= 8,
                                        high == ((prev_val as u16) & (0xffu16 >> sub(8u8, rem))),
                                        vlc_resident_field(mid, rem) == (((prev_val >> 0u8) as u16) & (0xffu16 >> sub(8u8, rem)));
                                vlc_peek_resident_equivalence(initial, mid, rem as nat, avail, low, rem);
                                crate::proofs::production_impl::production_ht_cleanup_peek_unfold(
                                    initial, vlc_after_resident(mid, rem), 0, count as nat, value,
                                );
                            }
                            return value;
                        }
                    }
                }
            }
        }
        self.peek_vlc_slow(count)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures result == crate::specs::ht_cleanup_peek_vlc(ht_cleanup_readers_view(self), count),
        )
    )]
    #[cold]
    #[inline(never)]
    fn peek_vlc_slow(&self, count: u8) -> u16 {
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
    #[inline]
    pub(super) fn advance_vlc(&mut self, count: u8) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
        if count > 0
            && count <= 8
            && self.vlc.has_byte
            && self.vlc.last_bit < 8
            && self.vlc.next_bit <= self.vlc.last_bit
            && self.vlc.current_byte <= usize::from(u16::MAX)
            && self.vlc.current_byte <= self.vlc.input.len()
            && self.vlc.bits_read <= self.vlc.maximum_work_units
            && u64::from(count) <= self.vlc.maximum_work_units - self.vlc.bits_read
            && self.work_units <= self.maximum_work_units
            && u64::from(count) <= self.maximum_work_units - self.work_units
        {
            let end_vlc_bits = self.vlc.bits_read + u64::from(count);
            let end_work = self.work_units + u64::from(count);
            let byte = self.vlc.current_byte as u16;
            let avail = self.vlc.last_bit - self.vlc.next_bit + 1;
            if count <= avail && self.can_claim_byte(HtStreamDirection::Reverse, byte) {
                self.vlc.next_bit += count;
                self.vlc.bits_read = end_vlc_bits;
                self.work_units = end_work;
                self.vlc_last_byte = Some(byte);
                if self.vlc.next_bit > self.vlc.last_bit {
                    self.vlc.load_previous_byte()?;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    vlc_advance_resident_equivalence(initial, count as nat, count);
                    crate::proofs::production_impl::production_ht_cleanup_advance_unfold(
                        ht_cleanup_readers_view(self), 0,
                    );
                }
                return Ok(());
            } else if count > avail && self.vlc.current_byte > 0 {
                let prev_idx = self.vlc.current_byte - 1;
                if prev_idx < self.vlc.input.len()
                    && self.can_claim_byte(HtStreamDirection::Reverse, byte)
                    && self.can_claim_byte(HtStreamDirection::Reverse, prev_idx as u16)
                {
                    let prev_val = self.vlc.input[prev_idx];
                    let prev_bits = crate::refinement::ht_reverse_data_bits(
                        self.vlc.later_byte_requires_unstuffing,
                        prev_val,
                    );
                    let rem = count - avail;
                    if rem <= prev_bits {
                        self.vlc.current_byte = prev_idx;
                        self.vlc.value = prev_val;
                        self.vlc.next_bit = rem;
                        self.vlc.last_bit = prev_bits - 1;
                        self.vlc.later_byte_requires_unstuffing = prev_val > 0x8f;
                        self.vlc.bits_read = end_vlc_bits;
                        self.work_units = end_work;
                        self.vlc_last_byte = Some(prev_idx as u16);
                        if self.vlc.next_bit > self.vlc.last_bit {
                            self.vlc.load_previous_byte()?;
                        }
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            vlc_advance_resident_equivalence(initial, count as nat, avail);
                            let mid_state = HtCleanupReaderState {
                                vlc: vlc_after_resident(initial.vlc, avail),
                                vlc_last_byte: Some(byte),
                                work_units: (initial.work_units + avail) as u64,
                                ..initial
                            };
                            vlc_advance_resident_equivalence(mid_state, rem as nat, rem);
                            crate::proofs::production_impl::production_ht_cleanup_advance_unfold(
                                ht_cleanup_readers_view(self), 0,
                            );
                        }
                        return Ok(());
                    }
                }
            }
        }
        self.advance_vlc_slow(count)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_cleanup_readers_view(final(self)))
                == crate::specs::ht_cleanup_advance_vlc(ht_cleanup_readers_view(old(self)), count as nat),
        )
    )]
    #[cold]
    #[inline(never)]
    fn advance_vlc_slow(&mut self, count: u8) -> Result<(), DecodeError> {
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
    #[inline]
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
    #[inline]
    pub(super) fn decode_quad_word(
        &mut self,
        initial: bool,
        context: u8,
    ) -> Result<u16, DecodeError> {
        if context > 7 {
            return Err(invalid_code_block());
        }
        if context == 0 && self.mel_zero_events > 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                let word = crate::specs::ht_cleanup_peek_vlc(ht_cleanup_readers_view(self), 7);
                assert(word & 0x7fu16 <= 127) by (bit_vector);
            }
            let _ = self.mel_event()?;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_cleanup_advance_unfold(
                    ht_cleanup_readers_view(self), 0,
                );
            }
            self.tick()?;
            return Ok(0);
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
    #[inline]
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
    #[inline]
    pub(super) fn read_suffix(&mut self, length: u8) -> Result<u8, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_cleanup_readers_view(self); }
        if length == 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_ht_uvlc_suffix_unfold(initial, 0, 0, 0);
            }
            return Ok(0);
        }
        if length <= 8
            && self.vlc.has_byte
            && self.vlc.last_bit < 8
            && self.vlc.next_bit <= self.vlc.last_bit
            && self.vlc.current_byte <= usize::from(u16::MAX)
            && self.vlc.current_byte <= self.vlc.input.len()
            && self.vlc.bits_read <= self.vlc.maximum_work_units
            && u64::from(length) <= self.vlc.maximum_work_units - self.vlc.bits_read
            && self.work_units <= self.maximum_work_units
            && u64::from(length) <= self.maximum_work_units - self.work_units
        {
            let avail = self.vlc.last_bit - self.vlc.next_bit + 1;
            let byte = self.vlc.current_byte as u16;
            if length <= avail && self.can_claim_byte(HtStreamDirection::Reverse, byte) {
                let value = (u16::from(self.vlc.value >> self.vlc.next_bit)
                    & (0xff_u16 >> (8 - length))) as u8;
                self.vlc.next_bit += length;
                self.vlc.bits_read += u64::from(length);
                self.work_units += u64::from(length);
                self.vlc_last_byte = Some(byte);
                if self.vlc.next_bit > self.vlc.last_bit {
                    self.vlc.load_previous_byte()?;
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    vlc_suffix_resident_equivalence(initial, length as nat, 0, 0, length);
                    assert((0u8 | (value << 0u8)) == value) by (bit_vector);
                    crate::proofs::production_impl::production_ht_uvlc_suffix_unfold(
                        ht_cleanup_readers_view(self), 0, length as nat, value,
                    );
                }
                return Ok(value);
            }
        }
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
