use super::state::{arithmetic_overflow, invalid_code_block};
use super::{
    HtBitPosition, HtForwardRefinementReader, HtRefinementReaders, HtReverseRefinementReader,
    MAX_HT_REFINEMENT_BYTES,
};
#[cfg(verus_keep_ghost)]
use super::{
    ht_forward_refinement_outcome, ht_forward_refinement_view, ht_refinement_readers_outcome,
    ht_refinement_readers_view, ht_reverse_refinement_outcome, ht_reverse_refinement_view,
};
use crate::{DecodeError, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures ht_forward_refinement_outcome(result)
            == crate::specs::ht_forward_refinement_initial(input@, maximum_work_units),
    )
)]
fn ht_forward_refinement_from_input(
    input: &[u8],
    maximum_work_units: u64,
) -> Result<HtForwardRefinementReader<'_>, DecodeError> {
    if input.len() > MAX_HT_REFINEMENT_BYTES {
        return Err(invalid_code_block());
    }
    Ok(HtForwardRefinementReader {
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
        maximum_work_units,
    })
}

impl<'a> HtForwardRefinementReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        ht_forward_refinement_from_input(input, limits.maximum_work_units())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == ht_forward_refinement_view(self).physical_bits_read,))]
    pub const fn physical_bits_read(&self) -> u64 {
        self.physical_bits_read
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == ht_forward_refinement_view(self).fill_bits_read,))]
    pub const fn fill_bits_read(&self) -> u64 {
        self.fill_bits_read
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_forward_refinement_view(final(self)))
                == crate::specs::ht_forward_refinement_read(ht_forward_refinement_view(old(self))),
        )
    )]
    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        match self.read_positioned_bit() {
            Ok((bit, _)) => Ok(bit),
            Err(error) => Err(error),
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_forward_refinement_view(final(self)))
                == crate::specs::ht_forward_refinement_positioned(ht_forward_refinement_view(old(self))),
        )
    )]
    pub(super) fn read_positioned_bit(
        &mut self,
    ) -> Result<(bool, Option<HtBitPosition>), DecodeError> {
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
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.maximum_work_units,
                actual: work,
            });
        }
        Ok((bit, position))
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_forward_refinement_view(final(self)))
                == crate::specs::ht_forward_refinement_load(ht_forward_refinement_view(old(self))),
        )
    )]
    fn load_byte(&mut self) -> Result<(), DecodeError> {
        let stuffed = self.previous_was_ff;
        if self.next_byte < self.input.len() {
            let value = *self
                .input
                .get(self.next_byte)
                .ok_or_else(invalid_code_block)?;
            if stuffed && value & 0x80 != 0 {
                return Err(DecodeError::MalformedInput {
                    offset: self.next_byte as u64,
                    kind: MalformedKind::InvalidBitStuffing,
                });
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

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures ht_reverse_refinement_outcome(result)
            == crate::specs::ht_reverse_refinement_initial(input@, maximum_work_units),
    )
)]
fn ht_reverse_refinement_from_input(
    input: &[u8],
    maximum_work_units: u64,
) -> Result<HtReverseRefinementReader<'_>, DecodeError> {
    if input.len() > MAX_HT_REFINEMENT_BYTES {
        return Err(invalid_code_block());
    }
    let mut reader = HtReverseRefinementReader {
        input,
        current_byte: input.len(),
        value: 0,
        next_bit: 0,
        last_bit: 7,
        has_byte: false,
        later_requires_unstuffing: true,
        physical_bits_read: 0,
        fill_bits_read: 0,
        maximum_work_units,
    };
    reader.load_previous_byte()?;
    Ok(reader)
}

impl<'a> HtReverseRefinementReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        ht_reverse_refinement_from_input(input, limits.maximum_work_units())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == ht_reverse_refinement_view(self).physical_bits_read,))]
    pub const fn physical_bits_read(&self) -> u64 {
        self.physical_bits_read
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == ht_reverse_refinement_view(self).fill_bits_read,))]
    pub const fn fill_bits_read(&self) -> u64 {
        self.fill_bits_read
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_reverse_refinement_view(final(self)))
                == crate::specs::ht_reverse_refinement_read(ht_reverse_refinement_view(old(self))),
        )
    )]
    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        match self.read_positioned_bit() {
            Ok((bit, _)) => Ok(bit),
            Err(error) => Err(error),
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_reverse_refinement_view(final(self)))
                == crate::specs::ht_reverse_refinement_positioned(ht_reverse_refinement_view(old(self))),
        )
    )]
    pub(super) fn read_positioned_bit(
        &mut self,
    ) -> Result<(bool, Option<HtBitPosition>), DecodeError> {
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
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.maximum_work_units,
                actual: work,
            });
        }
        Ok((bit, position))
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_reverse_refinement_view(final(self)))
                == crate::specs::ht_reverse_refinement_load(ht_reverse_refinement_view(old(self))),
        )
    )]
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

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::specs::part2_ht_scratch_result(forward_input@,reverse_input@,bytes,has_reverse,maximum_work_units,ht_refinement_readers_outcome(result)),
            ht_refinement_readers_outcome(result)!=Err(DecodeError::AllocationFailed) ==> ht_refinement_readers_outcome(result) == crate::specs::ht_refinement_readers_initial(
            forward_input@, reverse_input@, bytes, has_reverse, maximum_work_units,
        ),
    )
)]
pub(super) fn ht_refinement_readers_from_inputs<'a>(
    forward_input: &'a [u8],
    reverse_input: &'a [u8],
    bytes: usize,
    has_reverse: bool,
    maximum_work_units: u64,
) -> Result<HtRefinementReaders<'a>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_ht_scratch_normal(forward_input@,reverse_input@,bytes,has_reverse,maximum_work_units);}
    let forward = ht_forward_refinement_from_input(forward_input, maximum_work_units)?;
    let reverse = if has_reverse {
        Some(ht_reverse_refinement_from_input(
            reverse_input,
            maximum_work_units,
        )?)
    } else {
        None
    };
    let allocated = crate::allocation::filled_values(0_u8, bytes);
    #[cfg(verus_keep_ghost)]
    proof! {
        let result=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_ht_scratch_capacity_observed(crate::specs::part2_ht_scratch_context(forward_input@,reverse_input@,bytes,has_reverse,maximum_work_units,false),false,result);
        if let Err(error)=allocated{crate::specs::part2_ht_scratch_first_error(forward_input@,reverse_input@,bytes,has_reverse,maximum_work_units,error);}
    }
    let claimed = allocated?;
    let allocated = crate::allocation::filled_values(0_u8, bytes);
    #[cfg(verus_keep_ghost)]
    proof! {
        let context=crate::specs::part2_ht_scratch_context(forward_input@,reverse_input@,bytes,has_reverse,maximum_work_units,true);
        assert(context.claimed==Some(claimed@));
        let result=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_ht_scratch_capacity_observed(context,true,result);
        crate::specs::part2_ht_scratch_second_observed(forward_input@,reverse_input@,bytes,has_reverse,maximum_work_units,result);
    }
    let stuffed = allocated?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(claimed@ =~= Seq::new(bytes as nat, |i: int| 0u8));
        assert(stuffed@ =~= Seq::new(bytes as nat, |i: int| 0u8));
    }
    Ok(HtRefinementReaders {
        forward,
        reverse,
        claimed,
        stuffed,
    })
}

impl<'a> HtRefinementReaders<'a> {
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_refinement_readers_view(final(self)))
                == crate::specs::ht_refinement_claim(ht_refinement_readers_view(old(self)), position),
        )
    )]
    pub(super) fn claim(&mut self, position: Option<HtBitPosition>) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = ht_refinement_readers_view(self); }
        let Some(position) = position else {
            return Ok(());
        };
        if position.bit >= 8 {
            return Err(invalid_code_block());
        }
        let byte = usize::from(position.byte);
        let mask = 1_u8 << position.bit;
        let result = {
            let claimed = self.claimed.get_mut(byte).ok_or_else(invalid_code_block)?;
            if !crate::refinement::ht_claim_available(*claimed & mask != 0) {
                Err(invalid_code_block())
            } else {
                *claimed |= mask;
                Ok(())
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            if result.is_err() {
                assert(self.claimed@ =~= initial.claimed);
            } else {
                assert(self.claimed@ =~= initial.claimed.update(byte as int, initial.claimed[byte as int] | mask));
            }
            assert(ht_refinement_readers_view(self).forward == initial.forward);
            assert(ht_refinement_readers_view(self).reverse == initial.reverse);
            assert(ht_refinement_readers_view(self).stuffed == initial.stuffed);
        }
        result
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_refinement_readers_view(final(self)))
                == crate::specs::ht_refinement_read_forward(ht_refinement_readers_view(old(self))),
        )
    )]
    pub(super) fn read_forward(&mut self) -> Result<bool, DecodeError> {
        let (bit, position) = self.forward.read_positioned_bit()?;
        self.claim(position)?;
        Ok(bit)
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures (result, ht_refinement_readers_view(final(self)))
                == crate::specs::ht_refinement_read_reverse(ht_refinement_readers_view(old(self))),
        )
    )]
    pub(super) fn read_reverse(&mut self) -> Result<bool, DecodeError> {
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

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures result == crate::specs::ht_refinement_finish(ht_refinement_readers_view(self), encoded@),
        )
    )]
    pub(super) fn finish(&self, encoded: &[u8]) -> Result<(), DecodeError> {
        if self.claimed.len() != encoded.len() || self.stuffed.len() != encoded.len() {
            return Err(invalid_code_block());
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= encoded.len(),
                    self.claimed.len() == encoded.len(), self.stuffed.len() == encoded.len(),
                    forall |i: int| 0 <= i < index ==> encoded@[i] & !(self.claimed@[i] | self.stuffed@[i]) == 0,
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
