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

}
