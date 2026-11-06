//! As-implemented raw palette value traversal; normative palette HOLD is unchanged.

use super::*;

verus! {

pub open spec fn part2_palette_arithmetic_error(offset: u64) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::ArithmeticOverflow }
}

#[verifier::opaque]
pub open spec fn part2_palette_word_prefix(bytes: Seq<u8>, offset: u64, count: nat)
    -> Result<u64, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(0) }
    else {
        match part2_palette_word_prefix(bytes, offset, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(raw) => {
                let next = raw as nat * 256 + bytes[count - 1] as nat;
                if next > u64::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
                else { Ok(next as u64) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_palette_modulus_prefix(offset: u64, bits: nat) -> Result<u64, crate::DecodeError>
    decreases bits,
{
    if bits == 0 { Ok(1) }
    else {
        match part2_palette_modulus_prefix(offset, (bits - 1) as nat) {
            Err(error) => Err(error),
            Ok(value) => {
                let next = value as nat * 2;
                if next > u64::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
                else { Ok(next as u64) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_parse_palette_value(bytes: Seq<u8>, precision: u8, signed: bool, offset: u64)
    -> Result<i64, crate::DecodeError>
{
    if precision == 0 || precision > 38 || bytes.len() == 0 || bytes.len() > 5 {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxContents })
    } else {
        match part2_palette_word_prefix(bytes, offset, bytes.len()) {
            Err(error) => Err(error),
            Ok(raw) => match part2_palette_modulus_prefix(offset, precision as nat) {
                Err(error) => Err(error),
                Ok(modulus) => {
                    if modulus == 0 { Err(part2_palette_arithmetic_error(offset)) }
                    else {
                        let value = raw & ((modulus - 1) as u64);
                        if signed && value & (modulus >> 1u64) != 0 {
                            if value > modulus || modulus as int - value as int > i64::MAX as int {
                                Err(part2_palette_arithmetic_error(offset))
                            } else { Ok((-(modulus as int - value as int)) as i64) }
                        } else {
                            if value > i64::MAX as u64 { Err(part2_palette_arithmetic_error(offset)) }
                            else { Ok(value as i64) }
                        }
                    }
                },
            },
        }
    }
}

pub(crate) proof fn part2_palette_word_step(bytes: Seq<u8>, offset: u64, count: nat)
    ensures part2_palette_word_prefix(bytes, offset, count + 1)
        == match part2_palette_word_prefix(bytes, offset, count) {
            Err(error) => Err(error),
            Ok(raw) => {
                let next = raw as nat * 256 + bytes[count as int] as nat;
                if next > u64::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
                else { Ok(next as u64) }
            },
        },
{
    reveal(part2_palette_word_prefix);
}

pub(crate) proof fn part2_palette_word_error(bytes: Seq<u8>, offset: u64, count: nat, total: nat)
    requires count <= total,
    ensures match part2_palette_word_prefix(bytes, offset, count) {
        Err(error) => part2_palette_word_prefix(bytes, offset, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_palette_word_prefix);
    if count < total { part2_palette_word_error(bytes, offset, count, (total - 1) as nat); }
}

pub(crate) proof fn part2_palette_modulus_step(offset: u64, bits: nat)
    ensures part2_palette_modulus_prefix(offset, bits + 1) == match part2_palette_modulus_prefix(offset, bits) {
        Err(error) => Err(error),
        Ok(value) => if value as nat * 2 > u64::MAX as nat { Err(part2_palette_arithmetic_error(offset)) }
            else { Ok((value as nat * 2) as u64) },
    },
{
    reveal(part2_palette_modulus_prefix);
}

pub(crate) proof fn part2_palette_modulus_error(offset: u64, bits: nat, total: nat)
    requires bits <= total,
    ensures match part2_palette_modulus_prefix(offset, bits) {
        Err(error) => part2_palette_modulus_prefix(offset, total) == Err(error), Ok(_) => true,
    },
    decreases total - bits,
{
    reveal(part2_palette_modulus_prefix);
    if bits < total { part2_palette_modulus_error(offset, bits, (total - 1) as nat); }
}

pub type Part2PaletteDescriptors = (Seq<crate::jp2::PaletteColumn>, usize);
pub type Part2PaletteValues = (Seq<i64>, usize);

pub open spec fn part2_palette_descriptor_step(
    input: Part2BoxReference, base: u64, index: nat, previous: Part2PaletteDescriptors,
) -> Result<Part2PaletteDescriptors, crate::DecodeError> {
    if 3 + index >= input.1.len() {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else {
        match part2_container_bit_depth(input.1[3 + index as int], base) {
            Err(error) => Err(error),
            Ok(crate::jp2::ComponentBitDepth::Variable) =>
                Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents)),
            Ok(crate::jp2::ComponentBitDepth::Uniform { bits, signed }) => {
                let size = (bits as nat + 7) / 8;
                let total = previous.1 as nat + size;
                if total > usize::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                else { Ok((previous.0.push(crate::jp2::PaletteColumn { precision: bits, signed }), total as usize)) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_palette_descriptors(input: Part2BoxReference, base: u64, count: nat)
    -> Result<Part2PaletteDescriptors, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), 0)) }
    else {
        match part2_palette_descriptors(input, base, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_palette_descriptor_step(input, base, (count - 1) as nat, previous),
        }
    }
}

pub open spec fn part2_palette_value_step(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>, index: nat, previous: Part2PaletteValues,
) -> Result<Part2PaletteValues, crate::DecodeError> {
    if index >= columns.len() {
        Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::InvalidBoxContents })
    } else {
        let descriptor = columns[index as int];
        let size = (descriptor.precision as nat + 7) / 8;
        let end = previous.1 as nat + size;
        if end > usize::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
        else if end > input.1.len() {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
        } else {
            match part2_parse_palette_value(input.1.subrange(previous.1 as int, end as int),
                descriptor.precision, descriptor.signed, base) {
                Err(error) => Err(error), Ok(value) => Ok((previous.0.push(value), end as usize)),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_palette_row(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>,
    initial: Part2PaletteValues, count: nat,
) -> Result<Part2PaletteValues, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) }
    else {
        match part2_palette_row(input, base, columns, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_palette_value_step(input, base, columns, (count - 1) as nat, previous),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_palette_rows(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>, count: nat,
) -> Result<Part2PaletteValues, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), (3 + input.1[2] as nat) as usize)) }
    else {
        match part2_palette_rows(input, base, columns, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(initial) => part2_palette_row(input, base, columns, initial, columns.len()),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_parse_palette(input: Part2BoxReference, base: u64)
    -> Result<Part2PaletteModel, crate::DecodeError>
{
    let payload = input.1;
    if payload.len() < 3 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
    else {
        let entries = part2_box_u16([payload[0], payload[1]]);
        let count = payload[2] as nat;
        let descriptor_end = 3 + count;
        if entries == 0 || count == 0 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else if descriptor_end > usize::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
        else if descriptor_end > payload.len() {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
        } else {
            match part2_palette_descriptors(input, base, count) {
                Err(error) => Err(error),
                Ok(descriptors) => {
                    let sample_bytes = entries as nat * descriptors.1 as nat;
                    let expected = descriptor_end + sample_bytes;
                    let value_count = entries as nat * descriptors.0.len();
                    if sample_bytes > usize::MAX as nat || expected > usize::MAX as nat {
                        Err(part2_palette_arithmetic_error(base))
                    } else if payload.len() != expected {
                        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
                    } else if value_count > usize::MAX as nat { Err(part2_palette_arithmetic_error(base)) }
                    else {
                        match part2_palette_rows(input, base, descriptors.0, entries as nat) {
                            Err(error) => Err(error),
                            Ok(values) => if values.1 != payload.len() || values.0.len() != value_count {
                                Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
                            } else { Ok((entries, descriptors.0, values.0)) },
                        }
                    }
                },
            }
        }
    }
}

pub(crate) proof fn part2_palette_descriptors_step(input: Part2BoxReference, base: u64, count: nat)
    ensures part2_palette_descriptors(input, base, count + 1)
        == match part2_palette_descriptors(input, base, count) {
            Err(error) => Err(error),
            Ok(previous) => part2_palette_descriptor_step(input, base, count, previous),
        },
{
    reveal(part2_palette_descriptors);
}

pub(crate) proof fn part2_palette_descriptors_error(input: Part2BoxReference, base: u64, count: nat, total: nat)
    requires count <= total,
    ensures match part2_palette_descriptors(input, base, count) {
        Err(error) => part2_palette_descriptors(input, base, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_palette_descriptors);
    if count < total { part2_palette_descriptors_error(input, base, count, (total - 1) as nat); }
}

pub(crate) proof fn part2_palette_row_step(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>,
    initial: Part2PaletteValues, count: nat,
)
    ensures part2_palette_row(input, base, columns, initial, count + 1)
        == match part2_palette_row(input, base, columns, initial, count) {
            Err(error) => Err(error),
            Ok(previous) => part2_palette_value_step(input, base, columns, count, previous),
        },
{
    reveal(part2_palette_row);
}

pub(crate) proof fn part2_palette_row_error(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>,
    initial: Part2PaletteValues, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_palette_row(input, base, columns, initial, count) {
        Err(error) => part2_palette_row(input, base, columns, initial, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_palette_row);
    if count < total { part2_palette_row_error(input, base, columns, initial, count, (total - 1) as nat); }
}

pub(crate) proof fn part2_palette_rows_step(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>, count: nat,
)
    ensures part2_palette_rows(input, base, columns, count + 1)
        == match part2_palette_rows(input, base, columns, count) {
            Err(error) => Err(error),
            Ok(initial) => part2_palette_row(input, base, columns, initial, columns.len()),
        },
{
    reveal(part2_palette_rows);
}

pub(crate) proof fn part2_palette_rows_error(
    input: Part2BoxReference, base: u64, columns: Seq<crate::jp2::PaletteColumn>, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_palette_rows(input, base, columns, count) {
        Err(error) => part2_palette_rows(input, base, columns, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_palette_rows);
    if count < total { part2_palette_rows_error(input, base, columns, count, (total - 1) as nat); }
}

}
