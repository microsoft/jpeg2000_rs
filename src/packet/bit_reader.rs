use super::errors::{packet_reader_error, packet_reader_limit};
use super::{DecodeError, MalformedKind, PacketBitReader, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use super::{packet_bit_reader_view, packet_reader_outcome};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_bit_reader_view(&result) == crate::specs::part1_packet_reader_prefix(input@, header_limit, work_limit),
))]
pub(crate) fn packet_reader_prefix_from_input(
    input: &[u8],
    header_limit: u64,
    work_limit: u64,
) -> PacketBitReader<'_> {
    PacketBitReader {
        input,
        byte_index: 0,
        current_byte: 0,
        bits_remaining: 0,
        previous_byte_was_ff: false,
        bits_read: 0,
        maximum_work_units: work_limit,
        maximum_header_bytes: header_limit,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_reader_outcome(result) == crate::specs::part1_packet_reader_initial(input@, header_limit, work_limit),
))]
pub(crate) fn packet_reader_from_input(
    input: &[u8],
    header_limit: u64,
    work_limit: u64,
) -> Result<PacketBitReader<'_>, DecodeError> {
    let input_length = input.len() as u64;
    if input_length > header_limit {
        return Err(packet_reader_limit(
            Resource::PacketHeaderBytes,
            header_limit,
            input_length,
        ));
    }
    Ok(packet_reader_prefix_from_input(
        input,
        header_limit,
        work_limit,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_reader_outcome(result) == crate::specs::part1_packet_reader_initial(
        input@, crate::limits::resource_packet_header_byte_limit(limits), crate::limits::resource_work_limit(limits)),
))]
pub(crate) fn packet_reader_new<'a>(
    input: &'a [u8],
    limits: &ResourceLimits,
) -> Result<PacketBitReader<'a>, DecodeError> {
    packet_reader_from_input(
        input,
        limits.maximum_packet_header_bytes(),
        limits.maximum_work_units(),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_bit_reader_view(&result) == crate::specs::part1_packet_reader_prefix(
        input@, crate::limits::resource_packet_header_byte_limit(limits), crate::limits::resource_work_limit(limits)),
))]
pub(crate) fn packet_reader_prefix<'a>(
    input: &'a [u8],
    limits: &ResourceLimits,
) -> PacketBitReader<'a> {
    packet_reader_prefix_from_input(
        input,
        limits.maximum_packet_header_bytes(),
        limits.maximum_work_units(),
    )
}

impl<'a> PacketBitReader<'a> {
    pub fn new(input: &'a [u8], limits: &ResourceLimits) -> Result<Self, DecodeError> {
        packet_reader_new(input, limits)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == packet_bit_reader_view(self).bits_read,))]
    pub const fn bits_read(&self) -> u64 {
        self.bits_read
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == packet_bit_reader_view(self).byte_index,))]
    pub const fn bytes_consumed(&self) -> usize {
        self.byte_index
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (packet_bit_reader_view(self).bits_remaining == 0),))]
    pub const fn is_byte_aligned(&self) -> bool {
        self.bits_remaining == 0
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures packet_bit_reader_view(final(self)) == (crate::specs::Part1PacketReaderState {
            bits_remaining: 0, ..packet_bit_reader_view(old(self))
        }),
    ))]
    pub fn align_to_byte(&mut self) {
        self.bits_remaining = 0;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, packet_bit_reader_view(final(self))) == crate::specs::part1_packet_reader_finish(packet_bit_reader_view(old(self))),
    ))]
    pub(crate) fn finish_packet_header(&mut self) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_reader_finish); }
        if self.previous_byte_was_ff {
            self.load_byte()?;
        }
        self.align_to_byte();
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, packet_bit_reader_view(final(self))) == crate::specs::part1_packet_reader_read(packet_bit_reader_view(old(self))),
    ))]
    pub fn read_bit(&mut self) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_reader_read); }
        if self.bits_remaining == 0 {
            self.load_byte()?;
        }
        if self.bits_remaining == 0 || self.bits_remaining > 8 {
            return Err(packet_reader_error(
                self.byte_index,
                MalformedKind::InvalidBitStuffing,
            ));
        }
        self.bits_remaining = match self.bits_remaining.checked_sub(1) {
            Some(count) => count,
            None => {
                return Err(packet_reader_error(
                    self.byte_index,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        let bit = crate::refinement::packet_bit(self.current_byte, self.bits_remaining);
        self.bits_read = match self.bits_read.checked_add(1) {
            Some(count) => count,
            None => {
                return Err(packet_reader_error(
                    self.byte_index,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        if self.bits_read > self.maximum_work_units {
            return Err(packet_reader_limit(
                Resource::WorkUnits,
                self.maximum_work_units,
                self.bits_read,
            ));
        }
        Ok(bit)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, packet_bit_reader_view(final(self))) == crate::specs::part1_packet_reader_read_bits(packet_bit_reader_view(old(self)), count),
    ))]
    pub fn read_bits(&mut self, count: u8) -> Result<u32, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial = packet_bit_reader_view(self); }
        if count > 32 {
            return Err(packet_reader_error(
                self.byte_index,
                MalformedKind::InvalidMarkerLength,
            ));
        }
        let mut value = 0_u32;
        let mut read = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant read <= count,
                    count <= 32, initial == packet_bit_reader_view(old(self)),
                    crate::specs::part1_packet_reader_read_bits(initial, count)
                        == crate::specs::part1_packet_reader_word(packet_bit_reader_view(self), (count - read) as nat, value),
                decreases count - read,
            )
        )]
        while read < count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_packet_reader_word); }
            value <<= 1;
            #[cfg(verus_keep_ghost)]
            proof! { assert(value | 0u32 == value) by(bit_vector); }
            if self.read_bit()? {
                value |= 1;
            }
            read = match read.checked_add(1) {
                Some(count) => count,
                None => {
                    return Err(packet_reader_error(
                        self.byte_index,
                        MalformedKind::ArithmeticOverflow,
                    ));
                }
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_reader_word); }
        Ok(value)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, packet_bit_reader_view(final(self))) == crate::specs::part1_packet_reader_load(packet_bit_reader_view(old(self))),
    ))]
    fn load_byte(&mut self) -> Result<(), DecodeError> {
        if self.byte_index as u64 >= self.maximum_header_bytes {
            let actual = match (self.byte_index as u64).checked_add(1) {
                Some(actual) => actual,
                None => {
                    return Err(packet_reader_error(
                        self.byte_index,
                        MalformedKind::ArithmeticOverflow,
                    ));
                }
            };
            return Err(packet_reader_limit(
                Resource::PacketHeaderBytes,
                self.maximum_header_bytes,
                actual,
            ));
        }
        if self.byte_index >= self.input.len() {
            return Err(packet_reader_error(
                self.byte_index,
                MalformedKind::Truncated,
            ));
        }
        let byte = self.input[self.byte_index];
        if self.previous_byte_was_ff && byte & 0x80 != 0 {
            return Err(packet_reader_error(
                self.byte_index,
                MalformedKind::InvalidBitStuffing,
            ));
        }
        self.byte_index = match self.byte_index.checked_add(1) {
            Some(index) => index,
            None => {
                return Err(packet_reader_error(
                    self.byte_index,
                    MalformedKind::ArithmeticOverflow,
                ));
            }
        };
        self.current_byte = byte;
        self.bits_remaining = crate::refinement::packet_data_bits(self.previous_byte_was_ff);
        self.previous_byte_was_ff = byte == 0xff;
        Ok(())
    }
}
