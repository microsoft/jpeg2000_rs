use super::ht_cleanup_readers::ht_magsgn_from_input;
#[cfg(verus_keep_ghost)]
use super::ht_cleanup_readers::{magsgn_consumed, magsgn_field, magsgn_resident};
use super::ht_metadata::decode_ht_cleanup_segment_metadata;
use super::state::{
    arithmetic_overflow, code_block_plane_from_dimensions, ht_statistics_zero, invalid_code_block,
};
use super::{
    CodeBlockPlane, HtCleanupMetadata, HtCleanupPlaneReconstruction, HtCleanupSegment,
    HtForwardMagSgnReader, HtQuadMetadata, MAX_HT_MAGSGN_BITS, MAX_TIER1_BITPLANES,
    Tier1PassStatistics,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_view, ht_cleanup_metadata_view, ht_cleanup_prepare_outcome,
    ht_cleanup_segment_view, ht_magsgn_view, ht_numeric_magnitude_outcome, ht_plane_outcome,
    ht_plane_view,
};
use crate::magnitude::Magnitude;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    spec fn ht_payload_word_outcome(result: Result<(u64, bool, u8), DecodeError>)
        -> Result<(nat, bool, u8), DecodeError> {
        match result { Err(error) => Err(error), Ok((word, negative, exponent)) =>
            Ok((word as nat, negative, exponent)) }
    }

    spec fn field_bits(field: u8) -> nat {
        (8 - vstd::std_specs::bits::u8_leading_zeros(field)) as nat
    }

    proof fn field_halves(field: u8)
        ensures
            field as nat == 2 * (field >> 1u8) as nat + (field & 1) as nat,
            field_bits(field) == if field >> 1u8 != 0 {
                field_bits(field >> 1u8) + 1
            } else { (field & 1) as nat },
    {
        use vstd::std_specs::bits::axiom_u8_leading_zeros;
        let tail = field >> 1u8;
        let low = field & 1u8;
        let quotient = (field / 2) as u8;
        let remainder = (field % 2) as u8;
        assert(field >> 1u8 == quotient && field & 1u8 == remainder) by (bit_vector)
            requires quotient == field / 2u8, remainder == field % 2u8;
        assert(field as nat == 2 * tail as nat + low as nat);
        axiom_u8_leading_zeros(field);
        axiom_u8_leading_zeros(tail);
        let top = field_bits(field) as u8;
        let rest = field_bits(tail) as u8;
        if tail == 0 {
            assert(field == low);
            assert(field != 0 && top > 0 && field == 1 && (field >> sub(top, 1)) & 1 != 0
                ==> top == 1) by (bit_vector);
        } else {
            assert(field != 0);
            assert(top > 0);
            assert(field >> top == 0);
            assert(top > 1) by (bit_vector)
                requires top > 0, tail == field >> 1u8, tail != 0, field >> top == 0;
            assert(top == add(rest, 1)) by (bit_vector)
                requires 1 < top <= 8, 0 < rest <= 8, tail == field >> 1u8,
                    field >> top == 0, tail >> rest == 0,
                    (field >> sub(top, 1)) & 1 != 0, (tail >> sub(rest, 1)) & 1 != 0;
        }
    }

    proof fn resident_payload_equivalence(
        start: crate::specs::HtMagSgnState, width: u8, remaining: nat, index: nat,
        word: nat, negative: bool, exponent: u8,
    )
        requires
            magsgn_resident(start, width), width <= remaining, index + remaining <= 64,
            word < vstd::arithmetic::power2::pow2(index),
            crate::specs::part1_magnitude_capacity() > u64::MAX,
        ensures ({
            let field = magsgn_field(start, width);
            let scale = vstd::arithmetic::power2::pow2(index);
            let combined = word + field as nat * scale;
            &&& combined < vstd::arithmetic::power2::pow2(index + width as nat)
            &&& field_bits(field) <= width
            &&& crate::specs::ht_numeric_payload(start, remaining, index, word, negative, exponent)
                == crate::specs::ht_numeric_payload(magsgn_consumed(start, width),
                    (remaining - width) as nat, index + width as nat, combined,
                    negative || (index == 0 && field & 1 != 0),
                    if field == 0 { exponent } else { (index + field_bits(field)) as u8 })
        }),
        decreases width,
    {
        use crate::specs::{ht_magsgn_read, ht_numeric_payload};
        use vstd::arithmetic::power2::{pow2, lemma_pow2_adds, lemma_pow2_pos,
            lemma_pow2_strictly_increases};
        let field = magsgn_field(start, width);
        if width == 0 {
            let shifted = (start.value >> start.next_bit) as u16;
            assert(field == 0) by (bit_vector) requires field == (shifted & (0xffu16 >> 8u8)) as u8;
            vstd::std_specs::bits::axiom_u8_leading_zeros(field);
        } else {
            let next = magsgn_consumed(start, 1);
            let rest = (width - 1) as u8;
            let bit = field & 1 != 0;
            let value = start.value;
            let pos = start.next_bit;
            let pos1 = next.next_bit;
            let tail = magsgn_field(next, rest);
            assert(bit == ((value >> pos) & 1 != 0) && tail == field >> 1u8) by (bit_vector)
                requires 0 < width <= 8, pos < 8, pos1 == pos + 1u8, rest == width - 1u8,
                    bit == (field & 1 != 0),
                    field == (((value >> pos) as u16) & (0xffu16 >> sub(8u8, width))) as u8,
                    tail == (((value >> pos1) as u16) & (0xffu16 >> sub(8u8, rest))) as u8;
            assert(ht_magsgn_read(start) == (Ok(bit), next));
            let scale = pow2(index);
            let prefix = word + if bit { scale } else { 0 };
            lemma_pow2_pos(index);
            lemma_pow2_adds(index, 1);
            vstd::arithmetic::power2::lemma2_to64();
            if index + 1 < 64 { lemma_pow2_strictly_increases(index + 1, 64); }
            assert(prefix < pow2(index + 1) && prefix <= u64::MAX);
            assert(word <= u64::MAX);
            let sign = negative || (index == 0 && bit);
            let exp = if bit { (index + 1) as u8 } else { exponent };
            crate::proofs::production_impl::production_ht_numeric_payload_unfold(
                start, remaining, index, word, negative, exponent);
            assert(ht_numeric_payload(start, remaining, index, word, negative, exponent)
                == ht_numeric_payload(next, (remaining - 1) as nat, index + 1, prefix, sign, exp));
            resident_payload_equivalence(next, rest, (remaining - 1) as nat,
                index + 1, prefix, sign, exp);
            field_halves(field);
            let low = field & 1u8;
            assert(low <= 1) by (bit_vector) requires low == field & 1u8;
            assert(low as nat == if bit { 1nat } else { 0 });
            assert(magsgn_consumed(next, rest) == magsgn_consumed(start, width));
            assert(word + field as nat * scale == prefix + tail as nat * pow2(index + 1))
                by (nonlinear_arith)
                requires pow2(index + 1) == 2 * scale,
                    prefix == word + if bit { scale } else { 0 },
                    field as nat == 2 * tail as nat + if bit { 1nat } else { 0 };
        }
    }

    #[verifier::spinoff_prover]
    proof fn resident_payload_two_equivalence(
        start: crate::specs::HtMagSgnState, w1: u8, f1: u8, w2: u8, f2: u8,
        bit: u8, word: u64, negative: bool, exponent: u8,
    )
        requires
            1 <= w1 <= 8, 1 <= w2 <= 8, (bit as nat) + (w1 as nat) + (w2 as nat) <= 64,
            (word as nat) < vstd::arithmetic::power2::pow2(bit as nat),
            crate::specs::part1_magnitude_capacity() > u64::MAX,
            magsgn_resident(start, w1), f1 == magsgn_field(start, w1),
            ({
                let after1 = magsgn_consumed(start, w1);
                let loaded2 = crate::specs::ht_magsgn_load(after1);
                (!after1.has_byte || after1.next_bit > after1.last_bit)
                    && loaded2.0.is_ok()
                    && magsgn_resident(loaded2.1, w2)
                    && f2 == magsgn_field(loaded2.1, w2)
            }),
        ensures ({
            let after1 = magsgn_consumed(start, w1);
            let loaded2 = crate::specs::ht_magsgn_load(after1).1;
            let after2 = magsgn_consumed(loaded2, w2);
            let bit1 = (bit + w1) as u8;
            let shift1 = (f1 as u64) << bit;
            let word1 = (word as nat) + (shift1 as nat);
            let shift2 = (f2 as u64) << bit1;
            let word2 = word1 + (shift2 as nat);
            let neg = negative || (bit == 0 && (f1 & 1) != 0);
            let exp1 = if f1 != 0 { (bit as nat + field_bits(f1)) as u8 } else { exponent };
            let exp2 = if f2 != 0 { (bit1 as nat + field_bits(f2)) as u8 } else { exp1 };
            &&& word1 <= u64::MAX
            &&& word2 <= u64::MAX
            &&& field_bits(f1) <= w1
            &&& field_bits(f2) <= w2
            &&& crate::specs::ht_numeric_payload(start, (w1 + w2) as nat, bit as nat, word as nat, negative, exponent)
                == (Ok((word2, neg, exp2)), after2)
        }),
    {
        use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2_strictly_increases};
        lemma2_to64();
        let after1 = magsgn_consumed(start, w1);
        let loaded2 = crate::specs::ht_magsgn_load(after1).1;
        let after2 = magsgn_consumed(loaded2, w2);
        let bit1 = (bit + w1) as u8;
        resident_payload_equivalence(start, w1, (w1 + w2) as nat, bit as nat, word as nat, negative, exponent);
        if bit + w1 < 64 { lemma_pow2_strictly_increases((bit + w1) as nat, 64); }
        vstd::bits::lemma_u64_shl_is_mul(f1 as u64, bit as u64);
        assert((f1 as u64) << bit == (f1 as u64) << (bit as u64)) by (bit_vector);
        let word1 = (word as nat) + ((f1 as u64) << bit) as nat;
        let neg1 = negative || (bit == 0 && (f1 & 1) != 0);
        let exp1 = if f1 != 0 { (bit as nat + field_bits(f1)) as u8 } else { exponent };
        crate::proofs::production_impl::production_ht_numeric_payload_unfold(
            after1, w2 as nat, bit1 as nat, word1, neg1, exp1);
        crate::proofs::production_impl::production_ht_numeric_payload_unfold(
            loaded2, w2 as nat, bit1 as nat, word1, neg1, exp1);
        resident_payload_equivalence(loaded2, w2, w2 as nat, bit1 as nat, word1, neg1, exp1);
        if bit1 + w2 < 64 { lemma_pow2_strictly_increases((bit1 + w2) as nat, 64); }
        vstd::bits::lemma_u64_shl_is_mul(f2 as u64, bit1 as u64);
        assert((f2 as u64) << bit1 == (f2 as u64) << (bit1 as u64)) by (bit_vector);
        let word2 = word1 + ((f2 as u64) << bit1) as nat;
        let exp2 = if f2 != 0 { (bit1 as nat + field_bits(f2)) as u8 } else { exp1 };
        crate::proofs::production_impl::production_ht_numeric_payload_unfold(
            after2, 0, (bit1 + w2) as nat, word2, neg1, exp2);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::ht_complete_kappa(
        u_base, significance, north_west_exponent, north_east_exponent, maximum_u),
))]
#[inline(always)]
pub fn complete_ht_kappa(
    u_base: u8,
    significance: u8,
    north_west_exponent: u8,
    north_east_exponent: u8,
    maximum_u: u8,
) -> Result<u8, DecodeError> {
    if u_base == 0 || significance & 0xf0 != 0 || maximum_u == 0 || maximum_u > MAX_HT_MAGSGN_BITS {
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

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires magnitude_bits <= 64,
    ensures (ht_payload_word_outcome(result), ht_magsgn_view(final(reader)))
        == crate::specs::ht_numeric_payload(ht_magsgn_view(old(reader)), magnitude_bits as nat,
            0, 0, false, 0),
))]
#[inline(always)]
fn read_ht_payload_word(
    reader: &mut HtForwardMagSgnReader<'_>,
    magnitude_bits: u8,
) -> Result<(u64, bool, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_magsgn_view(reader); }
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(64, 384);
    }
    let mut word = 0_u64;
    let mut negative = false;
    let mut exponent = 0_u8;
    let mut bit = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant bit <= magnitude_bits <= 64,
            vstd::arithmetic::power2::pow2(0) == 1,
            vstd::arithmetic::power2::pow2(1) == 2,
            vstd::arithmetic::power2::pow2(64) == 18446744073709551616,
            (word as nat) < vstd::arithmetic::power2::pow2(bit as nat),
            crate::specs::part1_magnitude_capacity() > u64::MAX,
            start == ht_magsgn_view(old(reader)),
            crate::specs::ht_numeric_payload(start, magnitude_bits as nat, 0, 0, false, 0)
                == crate::specs::ht_numeric_payload(ht_magsgn_view(reader),
                    (magnitude_bits - bit) as nat, bit as nat, word as nat, negative, exponent),
        decreases magnitude_bits - bit,
    ))]
    while bit < magnitude_bits {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before_load = ht_magsgn_view(reader); }
        let loaded = reader.ensure_byte();
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_numeric_payload_unfold(
                before_load, (magnitude_bits - bit) as nat, bit as nat,
                word as nat, negative, exponent);
            if loaded.is_ok() {
                crate::proofs::production_impl::production_ht_numeric_payload_unfold(
                    ht_magsgn_view(reader), (magnitude_bits - bit) as nat, bit as nat,
                    word as nat, negative, exponent);
            }
        }
        loaded?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost old_reader = ht_magsgn_view(reader); }
        let rem = magnitude_bits - bit;
        let two_bytes = if rem <= 16 {
            reader.take_resident_physical_two(rem)
        } else {
            None
        };
        if let Some((w1, f1, w2, f2)) = two_bytes {
            #[cfg(verus_keep_ghost)]
            proof! {
                resident_payload_two_equivalence(old_reader, w1, f1, w2, f2, bit, word, negative, exponent);
                vstd::std_specs::bits::axiom_u8_leading_zeros(f1);
                vstd::std_specs::bits::axiom_u8_leading_zeros(f2);
            }
            let _ = w2;
            word += u64::from(f1) << bit;
            negative |= bit == 0 && f1 & 1 != 0;
            if f1 != 0 {
                exponent = bit + (8 - f1.leading_zeros()) as u8;
            }
            let bit1 = bit + w1;
            word += u64::from(f2) << bit1;
            if f2 != 0 {
                exponent = bit1 + (8 - f2.leading_zeros()) as u8;
            }
            return Ok((word, negative, exponent));
        }
        if let Some((width, field)) = reader.take_resident_physical(rem) {
            #[cfg(verus_keep_ghost)]
            proof! {
                use vstd::arithmetic::power2::{pow2, lemma_pow2_strictly_increases};
                resident_payload_equivalence(old_reader, width, (magnitude_bits - bit) as nat,
                    bit as nat, word as nat, negative, exponent);
                if bit + width < 64 { lemma_pow2_strictly_increases((bit + width) as nat, 64); }
                vstd::bits::lemma_u64_shl_is_mul(field as u64, bit as u64);
                assert((field as u64) << bit == (field as u64) << (bit as u64)) by (bit_vector);
                vstd::std_specs::bits::axiom_u8_leading_zeros(field);
            }
            word += u64::from(field) << bit;
            negative |= bit == 0 && field & 1 != 0;
            if field != 0 {
                exponent = bit + (8 - field.leading_zeros()) as u8;
            }
            bit += width;
            continue;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_numeric_payload_unfold(
                ht_magsgn_view(reader), (magnitude_bits - bit) as nat, bit as nat,
                word as nat, negative, exponent);
            vstd::bits::lemma_u64_pow2_no_overflow(bit as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, bit as u64);
            assert((1u64 << bit) == (1u64 << (bit as u64))) by(bit_vector)
                requires bit < 64;
            vstd::arithmetic::power2::lemma_pow2_adds(bit as nat, 1);
            vstd::arithmetic::power2::lemma2_to64_rest();
            if bit < 63 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(bit as nat + 1, 64);
            }
        }
        let set = reader.read_bit()?;
        let digit = if set { 1_u64 << bit } else { 0 };
        word += digit;
        negative |= crate::refinement::ht_magnitude_sign(bit, set);
        if set {
            exponent = bit + 1;
        }
        bit += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_ht_numeric_payload_unfold(
            ht_magsgn_view(reader), 0, bit as nat, word as nat, negative, exponent);
    }
    Ok((word, negative, exponent))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires magnitude_bits <= 75, 1 <= decoded_bitplanes <= 292,
    ensures match result {
        None => true,
        Some((value, sign, exp)) =>
            crate::specs::ht_numeric_center(base as nat, negative, initial_exponent,
                magnitude_bits, embedded_value, decoded_bitplanes)
                    == Ok((value as nat, sign, exp))
            && value > 0
            && (value as nat) < crate::specs::part1_magnitude_capacity(),
    },
))]
#[inline(always)]
fn try_center_ht_u64(
    base: u64,
    negative: bool,
    initial_exponent: u8,
    magnitude_bits: u8,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Option<(u64, bool, u8)> {
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::arithmetic::power2::lemma2_to64();
        vstd::arithmetic::power2::lemma2_to64_rest();
        vstd::arithmetic::power2::lemma_pow2_strictly_increases(64, 384);
    }
    let mut word = base;
    let mut exponent = initial_exponent;
    if embedded_value {
        if magnitude_bits >= 64 {
            return None;
        }
        let embedded = 1_u64 << magnitude_bits;
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::bits::lemma_u64_pow2_no_overflow(magnitude_bits as nat);
            vstd::bits::lemma_u64_shl_is_mul(1, magnitude_bits as u64);
            assert((1u64 << magnitude_bits) == (1u64 << (magnitude_bits as u64))) by(bit_vector)
                requires magnitude_bits < 64;
        }
        word = word.checked_add(embedded)?;
        exponent = magnitude_bits.checked_add(1)?;
    }
    if crate::refinement::ht_bin_center_odd(word) != word {
        word = word.checked_add(1)?;
        exponent = exponent.max(1);
    }
    let centered = word.checked_add(2)?;
    let shift = decoded_bitplanes - 1;
    if shift >= 64 {
        return None;
    }
    let scale = 1_u64 << shift;
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::bits::lemma_u64_pow2_no_overflow(shift as nat);
        vstd::bits::lemma_u64_shl_is_mul(1, shift as u64);
        assert((1u64 << shift) == (1u64 << (shift as u64))) by(bit_vector)
            requires shift < 64;
    }
    let scaled = centered.checked_mul(scale)?;
    let value = scaled / 2;
    if value == 0 {
        return None;
    }
    Some((value, negative, exponent))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires magnitude_bits <= 75, 1 <= decoded_bitplanes <= 292,
    ensures match result {
        None => true,
        Some((value, sign, exp)) =>
            crate::specs::ht_numeric_center(base as nat, negative, initial_exponent,
                magnitude_bits, embedded_value, decoded_bitplanes)
                    == Ok((crate::magnitude::magnitude_value(value), sign, exp))
            && crate::magnitude::magnitude_value(value) > 0
            && crate::magnitude::magnitude_value(value) < crate::specs::part1_magnitude_capacity()
            && crate::magnitude::magnitude_limbs(value)
                == crate::specs::tier1_value_limbs(crate::magnitude::magnitude_value(value)),
    },
))]
#[inline]
fn try_center_ht_word(
    base: u64,
    negative: bool,
    initial_exponent: u8,
    magnitude_bits: u8,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Option<(Magnitude, bool, u8)> {
    let (value, sign, exponent) = try_center_ht_u64(
        base,
        negative,
        initial_exponent,
        magnitude_bits,
        embedded_value,
        decoded_bitplanes,
    )?;
    let magnitude = crate::magnitude::magnitude_from_u64(value);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude);
        crate::proofs::production_impl::production_tier1_value_limbs(crate::magnitude::magnitude_limbs(magnitude));
    }
    Some((magnitude, sign, exponent))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires magnitude_bits <= 75, 1 <= decoded_bitplanes <= 292,
        ensures ht_numeric_magnitude_outcome(result) == crate::specs::ht_numeric_center(
            crate::magnitude::magnitude_value(bin), negative, initial_exponent,
            magnitude_bits, embedded_value, decoded_bitplanes),
            match result {
                Ok((value, _, _)) => crate::magnitude::magnitude_limbs(value)
                    == crate::specs::tier1_value_limbs(crate::magnitude::magnitude_value(value))
                    && crate::magnitude::magnitude_value(value) > 0
                    && crate::magnitude::magnitude_value(value) < crate::specs::part1_magnitude_capacity(),
                Err(_) => true,
            },
    )
)]
pub(super) fn center_ht_numeric_magnitude(
    bin: Magnitude,
    negative: bool,
    initial_exponent: u8,
    magnitude_bits: u8,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Result<(Magnitude, bool, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { vstd::arithmetic::power2::lemma2_to64(); }
    let mut bin_center = bin;
    let mut exponent = initial_exponent;
    if embedded_value {
        bin_center = bin_center.checked_add(crate::magnitude::magnitude_single_bit(u16::from(
            magnitude_bits,
        ))?)?;
        exponent = magnitude_bits
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    let low = bin_center.low_u64();
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_ht_low_word_parity(crate::magnitude::magnitude_value(bin_center));
        assert((low as nat % 2) == crate::magnitude::magnitude_value(bin_center) % 2);
    }
    if crate::refinement::ht_bin_center_odd(low) != low {
        bin_center = bin_center.checked_add(crate::magnitude::magnitude_from_u64(1))?;
        exponent = exponent.max(1);
    }
    let centered = bin_center.checked_add(crate::magnitude::magnitude_from_u64(2))?;
    let shift = decoded_bitplanes - 1;
    let magnitude = centered.checked_shl(shift)?.shift_right(1);
    if magnitude.is_zero() {
        return Err(invalid_code_block());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude);
        crate::proofs::production_impl::production_tier1_value_limbs(crate::magnitude::magnitude_limbs(magnitude));
    }
    Ok((magnitude, negative, exponent))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (ht_numeric_magnitude_outcome(result), ht_magsgn_view(final(reader)))
            == crate::specs::ht_reconstruct_numeric_magnitude(ht_magsgn_view(old(reader)),
                completed_u, embedded_bit, embedded_value, decoded_bitplanes),
            match result {
                Ok((value, _, _)) => crate::magnitude::magnitude_limbs(value)
                    == crate::specs::tier1_value_limbs(crate::magnitude::magnitude_value(value))
                    && crate::magnitude::magnitude_value(value) > 0
                    && crate::magnitude::magnitude_value(value) < crate::specs::part1_magnitude_capacity(),
                Err(_) => true,
            },
    )
)]
pub(super) fn reconstruct_ht_magnitude(
    reader: &mut HtForwardMagSgnReader<'_>,
    completed_u: u8,
    embedded_bit: bool,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Result<(Magnitude, bool, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_magsgn_view(reader); }
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::arithmetic::power2::lemma_pow2_pos(384);
        vstd::arithmetic::power2::lemma2_to64();
    }
    if completed_u == 0
        || completed_u > MAX_HT_MAGSGN_BITS
        || decoded_bitplanes == 0
        || decoded_bitplanes > MAX_TIER1_BITPLANES
    {
        return Err(invalid_code_block());
    }
    let magnitude_bits = crate::refinement::ht_magnitude_payload_bits(completed_u, embedded_bit);
    if magnitude_bits <= 64 {
        let (word, negative, exponent) = read_ht_payload_word(reader, magnitude_bits)?;
        if let Some(centered) = try_center_ht_word(
            word,
            negative,
            exponent,
            magnitude_bits,
            embedded_value,
            decoded_bitplanes,
        ) {
            return Ok(centered);
        }
        return center_ht_numeric_magnitude(
            crate::magnitude::magnitude_from_u64(word),
            negative,
            exponent,
            magnitude_bits,
            embedded_value,
            decoded_bitplanes,
        );
    }
    let mut bin_center = crate::magnitude::magnitude_zero();
    let mut negative = false;
    let mut exponent = 0_u8;
    let mut bit = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= magnitude_bits, magnitude_bits <= 75,
                1 <= completed_u <= 75, 1 <= decoded_bitplanes <= 292,
                start == ht_magsgn_view(old(reader)),
                magnitude_bits as nat == crate::specs::ht_magnitude_payload_bits(completed_u as nat, embedded_bit),
                crate::magnitude::magnitude_value(bin_center) < crate::specs::part1_magnitude_capacity(),
                vstd::arithmetic::power2::pow2(1) == 2,
                crate::specs::ht_reconstruct_numeric_magnitude(start, completed_u, embedded_bit, embedded_value, decoded_bitplanes)
                    == crate::specs::ht_numeric_finish(
                        crate::specs::ht_numeric_payload(ht_magsgn_view(reader), (magnitude_bits - bit) as nat,
                            bit as nat, crate::magnitude::magnitude_value(bin_center), negative, exponent),
                        magnitude_bits, embedded_value, decoded_bitplanes),
            decreases magnitude_bits - bit,
        )
    )]
    while bit < magnitude_bits {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_numeric_payload_unfold(
                ht_magsgn_view(reader), (magnitude_bits - bit) as nat, bit as nat,
                crate::magnitude::magnitude_value(bin_center), negative, exponent,
            );
        }
        if reader.read_bit()? {
            if crate::refinement::ht_magnitude_sign(bit, true) {
                negative = true;
            }
            bin_center =
                bin_center.checked_add(crate::magnitude::magnitude_single_bit(u16::from(bit))?)?;
            exponent = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit == magnitude_bits);
        crate::proofs::production_impl::production_ht_numeric_payload_unfold(
            ht_magsgn_view(reader), 0, bit as nat,
            crate::magnitude::magnitude_value(bin_center), negative, exponent,
        );
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost final_value = crate::magnitude::magnitude_value(bin_center);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::ht_reconstruct_numeric_magnitude(start, completed_u, embedded_bit, embedded_value, decoded_bitplanes)
            == (crate::specs::ht_numeric_center(final_value, negative, exponent, magnitude_bits, embedded_value, decoded_bitplanes),
                ht_magsgn_view(reader)));
    }
    center_ht_numeric_magnitude(
        bin_center,
        negative,
        exponent,
        magnitude_bits,
        embedded_value,
        decoded_bitplanes,
    )
}

impl HtCleanupPlaneReconstruction<'_> {
    #[allow(
        clippy::too_many_arguments,
        reason = "The actual sample transition consumes these independent metadata and geometry fields."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires sample < 4, column + 1 < old(self).current_exponents.len(),
        ensures (result, ht_plane_view(final(self))) == crate::specs::ht_plane_sample(
            ht_plane_view(old(self)), quad, width, height, column as nat, completed_u, decoded_bitplanes, sample),
            final(self).current_exponents.len() == old(self).current_exponents.len(),
            final(self).previous_exponents@ == old(self).previous_exponents@,
            result == Ok(()) || result.is_err(),
    ))]
    #[inline(always)]
    pub(super) fn sample(
        &mut self,
        quad: HtQuadMetadata,
        width: u16,
        height: u16,
        column: usize,
        completed_u: u8,
        decoded_bitplanes: u16,
        sample: u8,
    ) -> Result<(), DecodeError> {
        let next_column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
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
        if x < width && y < height {
            self.statistics.scanned(1)?;
            if quad.significance & (1_u8 << sample) != 0 {
                let embedded_bit = quad.embedded_bit_mask & (1_u8 << sample) != 0;
                let embedded_value = quad.embedded_magnitude & (1_u8 << sample) != 0;
                let embedded_sub = if embedded_bit { 1_u8 } else { 0_u8 };
                let exponent = if completed_u > 0
                    && completed_u <= MAX_HT_MAGSGN_BITS
                    && decoded_bitplanes > 0
                    && decoded_bitplanes <= MAX_TIER1_BITPLANES
                    && completed_u - embedded_sub <= 64
                {
                    let magnitude_bits = completed_u - embedded_sub;
                    let (word, negative, raw_exponent) =
                        read_ht_payload_word(&mut self.reader, magnitude_bits)?;
                    if let Some((value, sign, exp)) = try_center_ht_u64(
                        word,
                        negative,
                        raw_exponent,
                        magnitude_bits,
                        embedded_value,
                        decoded_bitplanes,
                    ) {
                        self.output.mark_significant_u64(x, y, value, sign)?;
                        exp
                    } else {
                        let (magnitude, sign, exp) = center_ht_numeric_magnitude(
                            crate::magnitude::magnitude_from_u64(word),
                            negative,
                            raw_exponent,
                            magnitude_bits,
                            embedded_value,
                            decoded_bitplanes,
                        )?;
                        self.output
                            .mark_significant_magnitude(x, y, magnitude, sign)?;
                        exp
                    }
                } else {
                    let (magnitude, negative, exp) = reconstruct_ht_magnitude(
                        &mut self.reader,
                        completed_u,
                        embedded_bit,
                        embedded_value,
                        decoded_bitplanes,
                    )?;
                    self.output
                        .mark_significant_magnitude(x, y, magnitude, negative)?;
                    exp
                };
                self.statistics.decoded_symbols(1)?;
                self.statistics.became_significant()?;
                if sample == 1 {
                    let entry = self
                        .current_exponents
                        .get_mut(column)
                        .ok_or_else(invalid_code_block)?;
                    *entry = (*entry).max(exponent);
                } else if sample == 3 {
                    *self
                        .current_exponents
                        .get_mut(next_column)
                        .ok_or_else(invalid_code_block)? = exponent;
                }
            }
        }
        Ok(())
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "The shared quad stage preserves the real caller's metadata and traversal inputs."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires 0 < quads_per_row <= 32768,
            old(self).current_exponents.len() == quads_per_row + 1,
            old(self).previous_exponents.len() == quads_per_row + 1,
        ensures (result, ht_plane_view(final(self))) == crate::specs::ht_plane_quad(
            ht_plane_view(old(self)), quad, width, height, maximum_u, decoded_bitplanes,
            quads_per_row as nat, quad_index as nat),
            final(self).current_exponents.len() == quads_per_row + 1,
            final(self).previous_exponents.len() == quads_per_row + 1,
            result == Ok(()) || result.is_err(),
    ))]
    #[inline]
    pub(super) fn quad(
        &mut self,
        quad: HtQuadMetadata,
        width: u16,
        height: u16,
        maximum_u: u8,
        decoded_bitplanes: u16,
        quads_per_row: usize,
        quad_index: usize,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost start = ht_plane_view(self); }
        let column = if quad_index < quads_per_row {
            #[cfg(verus_keep_ghost)]
            proof! {
                vstd::arithmetic::div_mod::lemma_small_mod(quad_index as nat, quads_per_row as nat);
            }
            quad_index
        } else {
            quad_index
                .checked_rem(quads_per_row)
                .ok_or_else(arithmetic_overflow)?
        };
        if column == 0 {
            let mut exponent_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant exponent_index <= self.current_exponents.len(),
                        self.current_exponents.len() == quads_per_row + 1,
                        start.current.len() == quads_per_row + 1,
                        start == ht_plane_view(old(self)),
                        self.previous_exponents@ == start.previous,
                        code_block_plane_view(&self.output) == start.output,
                        ht_magsgn_view(&self.reader) == start.reader, self.statistics == start.statistics,
                        forall |i: int| 0 <= i < self.current_exponents.len() ==>
                            self.current_exponents@[i] == if i < exponent_index { 0u8 } else { start.current[i] },
                    decreases self.current_exponents.len() - exponent_index,
                )
            )]
            while exponent_index < self.current_exponents.len() {
                self.current_exponents[exponent_index] = 0;
                exponent_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { assert(self.current_exponents@ =~= Seq::new(start.current.len(), |i: int| 0u8)); }
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
                *self
                    .previous_exponents
                    .get(column)
                    .ok_or_else(invalid_code_block)?,
                *self
                    .previous_exponents
                    .get(next_column)
                    .ok_or_else(invalid_code_block)?,
                maximum_u,
            )?
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost samples_start = ht_plane_view(self); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_plane_samples); }
        if quad.significance == 0
            && width > 0
            && height > 0
            && quad.x < width - 1
            && quad.y < height - 1
            && self.statistics.coefficients_scanned <= u32::MAX - 4
        {
            self.statistics.scanned(4)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((0u8 & (1u8 << 0u8)) == 0 && (0u8 & (1u8 << 1u8)) == 0
                    && (0u8 & (1u8 << 2u8)) == 0 && (0u8 & (1u8 << 3u8)) == 0) by (bit_vector);
                assert((Ok::<(), DecodeError>(()), ht_plane_view(self)) == crate::specs::ht_plane_samples(
                    samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, 4));
            }
        } else {
            let mut sample = 0_u8;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant sample <= 4, column < quads_per_row, next_column == column + 1,
                        samples_start.current.len() == quads_per_row + 1,
                        self.current_exponents.len() == quads_per_row + 1,
                        self.previous_exponents.len() == quads_per_row + 1,
                        crate::specs::ht_plane_quad(ht_plane_view(old(self)), quad, width, height,
                            maximum_u, decoded_bitplanes, quads_per_row as nat, quad_index as nat)
                            == crate::specs::ht_plane_quad_finish(crate::specs::ht_plane_samples(
                                samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, 4),
                                quads_per_row as nat, column as nat),
                        (Ok::<(), DecodeError>(()), ht_plane_view(self)) == crate::specs::ht_plane_samples(
                            samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, sample as nat),
                    decreases 4 - sample,
                )
            )]
            while sample < 4 {
                let result = self.sample(
                    quad,
                    width,
                    height,
                    column,
                    completed_u,
                    decoded_bitplanes,
                    sample,
                );
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::ht_plane_samples);
                    assert((result, ht_plane_view(self)) == crate::specs::ht_plane_samples(
                        samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, sample as nat + 1));
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    if result.is_err() {
                        crate::proofs::production_impl::production_ht_plane_samples_error(
                            samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, sample as nat + 1, 4);
                    }
                }
                result?;
                sample += 1;
            }
        }
        if next_column == quads_per_row {
            core::mem::swap(&mut self.previous_exponents, &mut self.current_exponents);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, ht_plane_view(final(self))) == crate::specs::ht_plane_finish(ht_plane_view(old(self))),
    ))]
    pub(super) fn finish(&mut self) -> Result<(), DecodeError> {
        self.reader.finish()
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_cleanup_result(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),
        maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits),ht_plane_outcome(result)),
        ht_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==> ht_plane_outcome(result) == crate::specs::ht_cleanup_plane(
        code_block_plane_view(plane), ht_cleanup_segment_view(&cleanup), ht_cleanup_metadata_view(metadata),
        maximum_u, decoded_bitplanes, crate::limits::resource_work_limit(limits)),
))]
#[inline(never)]
pub(super) fn reconstruct_ht_cleanup_plane(
    plane: &CodeBlockPlane,
    cleanup: HtCleanupSegment<'_>,
    metadata: &HtCleanupMetadata,
    maximum_u: u8,
    decoded_bitplanes: u16,
    limits: &ResourceLimits,
) -> Result<(CodeBlockPlane, Tier1PassStatistics), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost source=code_block_plane_view(plane);let ghost segment=ht_cleanup_segment_view(&cleanup);let ghost rows=ht_cleanup_metadata_view(metadata);
        let ghost work=crate::limits::resource_work_limit(limits);
    }
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_cleanup_normal(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits));}
    if metadata.width == 0 {
        return Err(invalid_code_block());
    }
    let output_result = code_block_plane_from_dimensions(
        plane.width(),
        plane.height(),
        super::CoefficientStorageRole::CleanupOutput,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=output_result {crate::specs::part2_plane_cleanup_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),
    maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits),error);}}
    let output = output_result?;
    let reader = ht_magsgn_from_input(cleanup.mag_sgn().bytes(), limits.maximum_work_units())?;
    let doubled_quads = usize::from(metadata.width)
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let quads_per_row = doubled_quads
        .checked_div(2)
        .ok_or_else(arithmetic_overflow)?;
    if quads_per_row == 0 {
        return Err(invalid_code_block());
    }
    let exponent_count = quads_per_row
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let mut state = HtCleanupPlaneReconstruction {
        output,
        reader,
        previous_exponents: {
            let filled = crate::allocation::filled_values(0_u8, exponent_count);
            #[cfg(verus_keep_ghost)]
            proof! {
                let result=match filled{Err(error)=>Err(error),Ok(_)=>Ok(())};
                crate::specs::part2_ht_exponent_capacity_observed(crate::specs::part2_ht_exponent_context(source,segment,rows,maximum_u,decoded_bitplanes,work,false),false,result);
                if let Err(error)=filled{crate::specs::part2_ht_exponent_first_error(source,segment,rows,maximum_u,decoded_bitplanes,work,error);}
            }
            filled?
        },
        current_exponents: {
            let filled = crate::allocation::filled_values(0_u8, exponent_count);
            #[cfg(verus_keep_ghost)]
            proof! {
                let result=match filled{Err(error)=>Err(error),Ok(_)=>Ok(())};
                crate::specs::part2_ht_exponent_capacity_observed(crate::specs::part2_ht_exponent_context(source,segment,rows,maximum_u,decoded_bitplanes,work,true),true,result);
                crate::specs::part2_ht_exponent_current_observed(source,segment,rows,maximum_u,decoded_bitplanes,work,result);
            }
            filled?
        },
        statistics: ht_statistics_zero(),
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_plane_view(&state); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.previous_exponents@ =~= Seq::new(quads_per_row as nat + 1, |i: int| 0u8));
        assert(state.current_exponents@ =~= Seq::new(quads_per_row as nat + 1, |i: int| 0u8));
        reveal(crate::specs::ht_plane_quads);
    }
    let mut quad_index = 0_usize;
    let mut column = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant quad_index <= metadata.quads.len(), 0 < quads_per_row <= 32768,
            column == (quad_index as nat) % (quads_per_row as nat),
            column < quads_per_row,
            crate::specs::part2_plane_cleanup_result(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),
                maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits),
                crate::specs::ht_cleanup_plane(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits))),
            start.current.len() == quads_per_row + 1,
            start.previous.len() == quads_per_row + 1,
            state.current_exponents.len() == quads_per_row + 1,
            state.previous_exponents.len() == quads_per_row + 1,
            crate::specs::ht_cleanup_plane(code_block_plane_view(plane), ht_cleanup_segment_view(&cleanup),
                ht_cleanup_metadata_view(metadata), maximum_u, decoded_bitplanes, crate::limits::resource_work_limit(limits))
                == crate::specs::ht_plane_output(crate::specs::ht_plane_quads(
                    start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                    decoded_bitplanes, quads_per_row as nat, metadata.quads@.len())),
            (Ok::<(), DecodeError>(()), ht_plane_view(&state)) == crate::specs::ht_plane_quads(
                start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                decoded_bitplanes, quads_per_row as nat, quad_index as nat),
        decreases metadata.quads.len() - quad_index,
    ))]
    while quad_index < metadata.quads.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(quad_index)?;
        let quad = *metadata
            .quads
            .get(quad_index)
            .ok_or_else(invalid_code_block)?;
        let result = state.quad(
            quad,
            metadata.width,
            metadata.height,
            maximum_u,
            decoded_bitplanes,
            quads_per_row,
            column,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::div_mod::lemma_small_mod(column as nat, quads_per_row as nat);
            reveal(crate::specs::ht_plane_quads);
            assert((result, ht_plane_view(&state)) == crate::specs::ht_plane_quads(
                start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                decoded_bitplanes, quads_per_row as nat, quad_index as nat + 1));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if result.is_err() {
                crate::proofs::production_impl::production_ht_plane_quads_error(
                    start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                    decoded_bitplanes, quads_per_row as nat, quad_index as nat + 1, metadata.quads@.len());
            }
        }
        result?;
        quad_index = quad_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost prev_column = column; }
        column += 1;
        if column == quads_per_row {
            column = 0;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let q = quads_per_row as int;
            let idx = (quad_index - 1) as int;
            vstd::arithmetic::div_mod::lemma_add_mod_noop(idx, 1, q);
            if quads_per_row == 1 {
                vstd::arithmetic::div_mod::lemma_mod_self_zero(1);
                assert(column == 0 && (quad_index as nat) % 1nat == 0);
            } else {
                vstd::arithmetic::div_mod::lemma_small_mod(1nat, quads_per_row as nat);
                if prev_column + 1 < quads_per_row {
                    vstd::arithmetic::div_mod::lemma_small_mod((prev_column + 1) as nat, quads_per_row as nat);
                } else {
                    vstd::arithmetic::div_mod::lemma_mod_self_zero(q);
                }
            }
        }
    }
    state.finish()?;
    Ok((state.output, state.statistics))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_prepare_result(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,
        crate::limits::resource_work_limit(limits),private_plan,ht_cleanup_prepare_outcome(result)),
        ht_cleanup_prepare_outcome(result)!=Err(DecodeError::AllocationFailed) ==> ht_cleanup_prepare_outcome(result) == crate::specs::ht_cleanup_prepare(
        code_block_plane_view(plane), ht_cleanup_segment_view(&cleanup), maximum_passes,
        maximum_u, skipped_bitplanes, crate::limits::resource_work_limit(limits)),
))]
pub(super) fn prepare_ht_cleanup_symbols(
    plane: &CodeBlockPlane,
    cleanup: HtCleanupSegment<'_>,
    maximum_passes: u32,
    maximum_u: u8,
    skipped_bitplanes: u16,
    limits: &ResourceLimits,
    private_plan: bool,
) -> Result<
    (
        CodeBlockPlane,
        super::ht_checkpoint::HtCleanupCheckpoint,
        Tier1PassStatistics,
        u16,
    ),
    DecodeError,
> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_prepare_normal(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,crate::limits::resource_work_limit(limits),private_plan);}
    let metadata_result = decode_ht_cleanup_segment_metadata(
        cleanup,
        plane.width(),
        plane.height(),
        maximum_u,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=metadata_result{crate::specs::part2_plane_prepare_metadata_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),
    maximum_passes,maximum_u,skipped_bitplanes,crate::limits::resource_work_limit(limits),private_plan,error);}}
    let metadata = metadata_result?;
    let significant_bitplanes = ht_significant_bitplanes(maximum_passes)?;
    let decoded_bitplanes = significant_bitplanes
        .checked_sub(skipped_bitplanes)
        .ok_or_else(arithmetic_overflow)?;
    let reconstructed = reconstruct_ht_cleanup_plane(
        plane,
        cleanup,
        &metadata,
        maximum_u,
        decoded_bitplanes,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=reconstructed {crate::specs::part2_plane_prepare_cleanup_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,
    crate::limits::resource_work_limit(limits),private_plan,(ht_cleanup_metadata_view(&metadata),decoded_bitplanes),error);}}
    let (output, statistics) = reconstructed?;
    let duplicated = super::ht_checkpoint::retain_ht_cleanup(&output, private_plan);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=duplicated {crate::specs::part2_plane_prepare_duplicate_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,
    crate::limits::resource_work_limit(limits),private_plan,(ht_cleanup_metadata_view(&metadata),decoded_bitplanes),(code_block_plane_view(&output),statistics),error);}}
    let duplicate = duplicated?;
    Ok((output, duplicate, statistics, decoded_bitplanes))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::ht_significant_bitplanes(maximum_passes),
))]
pub(super) fn ht_significant_bitplanes(maximum_passes: u32) -> Result<u16, DecodeError> {
    let rounded_passes = maximum_passes
        .checked_add(2)
        .ok_or_else(arithmetic_overflow)?;
    let significant = rounded_passes
        .checked_div(3)
        .ok_or_else(arithmetic_overflow)?;
    if significant > u32::from(u16::MAX) {
        return Err(arithmetic_overflow());
    }
    Ok(significant as u16)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_word_centering_matches_wide_arithmetic_and_declines_overflow() {
        let cases: &[(u64, u8, bool, u16, bool)] = &[
            (0, 0, false, 1, true),
            (0, 0, true, 1, true),
            (u64::MAX - 2, 64, false, 1, true),
            (u64::MAX, 64, false, 1, false),
            (0, 64, true, 1, false),
            (1, 1, false, 64, false),
            (1, 1, false, 65, false),
            (u64::MAX, 75, false, 292, false),
            (0, 75, true, 292, false),
        ];
        for &(base, bits, embedded, planes, fits) in cases {
            let actual = try_center_ht_word(base, true, 255, bits, embedded, planes);
            assert_eq!(actual.is_some(), fits);
            let expected = center_ht_numeric_magnitude(
                Magnitude::from_u64(base),
                true,
                255,
                bits,
                embedded,
                planes,
            )
            .unwrap();
            if let Some(actual) = actual {
                assert_eq!(actual, expected);
            }
        }
    }

    #[test]
    fn ht_payload_word_and_wide_paths_preserve_bits_and_work_errors() {
        let bytes = [0x55; 16];
        let limits = ResourceLimits::default();
        let pattern = 0x5555_5555_5555_5555_u64;
        for bits in [0_u8, 1, 39, 63, 64] {
            let mut reader = HtForwardMagSgnReader::new(&bytes, &limits).unwrap();
            let word = pattern
                & if bits == 64 {
                    u64::MAX
                } else {
                    (1_u64 << bits) - 1
                };
            assert_eq!(
                read_ht_payload_word(&mut reader, bits).unwrap(),
                (word, bits > 0, (64 - word.leading_zeros()) as u8)
            );
            assert_eq!(reader.physical_bits_read(), u64::from(bits));
            assert_eq!(reader.fill_bits_read(), 0);
        }
        for bits in [1_u8, 39, 63, 64, 65, 75] {
            let low = pattern
                & if bits >= 64 {
                    u64::MAX
                } else {
                    (1_u64 << bits) - 1
                };
            let high = if bits > 64 {
                pattern & ((1_u64 << (bits - 64)) - 1)
            } else {
                0
            };
            let base = Magnitude::from_limbs([low, high, 0, 0, 0, 0]);
            let exponent = if bits % 2 == 1 { bits } else { bits - 1 };
            for planes in [1_u16, 17, 292] {
                let mut reader = HtForwardMagSgnReader::new(&bytes, &limits).unwrap();
                let actual =
                    reconstruct_ht_magnitude(&mut reader, bits, false, false, planes).unwrap();
                let expected =
                    center_ht_numeric_magnitude(base, true, exponent, bits, false, planes).unwrap();
                assert_eq!(actual, expected);
                assert_eq!(reader.physical_bits_read(), u64::from(bits));
            }
        }
        let limited = limits.with_maximum_work_units(1).unwrap();
        let mut reader = HtForwardMagSgnReader::new(&bytes, &limited).unwrap();
        assert!(matches!(
            reconstruct_ht_magnitude(&mut reader, 64, false, false, 1),
            Err(DecodeError::LimitExceeded {
                resource: crate::Resource::WorkUnits,
                ..
            })
        ));
    }

    #[test]
    fn resident_payload_matches_checked_bits_and_state_at_each_frontier() {
        for data in [&[0xff, 0x42, 0xa0][..], &[0xff, 0x80][..], &[][..]] {
            for limit in [4, 8, 9, 15, 17, 128] {
                let limits = ResourceLimits::default()
                    .with_maximum_work_units(limit)
                    .unwrap();
                for prefix in [0, 1, 6, 7, 8] {
                    let mut reader = HtForwardMagSgnReader::new(data, &limits).unwrap();
                    if (0..prefix)
                        .try_for_each(|_| reader.read_bit().map(|_| ()))
                        .is_err()
                    {
                        continue;
                    }
                    for width in [0, 1, 2, 3, 6, 7, 8, 13, 63, 64] {
                        let mut actual = reader;
                        let mut checked = reader;
                        let expected = (|| {
                            let mut word = 0_u64;
                            for bit in 0..width {
                                if checked.read_bit()? {
                                    word |= 1_u64 << bit;
                                }
                            }
                            Ok((word, word & 1 != 0, (64 - word.leading_zeros()) as u8))
                        })();
                        assert_eq!(read_ht_payload_word(&mut actual, width), expected);
                        assert_eq!(
                            actual, checked,
                            "{data:?} limit={limit} prefix={prefix} width={width}"
                        );
                        assert_eq!(actual.read_bit(), checked.read_bit());
                        assert_eq!(actual, checked);
                    }
                }
            }
        }
    }

    #[test]
    fn resident_payload_never_batches_a_physical_counter_overflow() {
        let limits = ResourceLimits::default();
        let mut reader = HtForwardMagSgnReader::new(&[0xfe], &limits).unwrap();
        assert_eq!(reader.read_bit(), Ok(false));
        reader.physical_bits_read = u64::MAX - 1;
        assert_eq!(
            read_ht_payload_word(&mut reader, 6),
            Err(arithmetic_overflow())
        );
        // The second read advances the cursor but cannot charge either counter.
        assert_eq!(
            (
                reader.next_byte,
                reader.next_bit,
                reader.physical_bits_read(),
                reader.work_units
            ),
            (1, 3, u64::MAX, 2)
        );
    }
}
