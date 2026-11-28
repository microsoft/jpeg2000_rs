#[cfg(test)]
use super::state::sign_context;
#[cfg(test)]
use super::state::significant_neighbor_count;
use super::state::{ht_statistics_zero, invalid_code_block};
use super::{
    CoefficientState, NeighborSummary, RUN_LENGTH_CONTEXT, SignContext, SubbandOrientation,
    Tier1BitplaneState, Tier1BlockCoding, Tier1CodeBlockDecoder, Tier1PassKind,
    Tier1PassStatistics, UNIFORM_CONTEXT,
};
use crate::mq::MqDecoder;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const MAG: u64 = u32::MAX as u64;
const BP_SHIFT: u32 = 32;
const BP_MASK: u64 = 63 << BP_SHIFT;
const EMPTY: u64 = BP_MASK;
const SIG: u64 = 1 << 38;
const NEG: u64 = 1 << 39;
const REFINED: u64 = 1 << 40;
const SIG_NEIGHBORS: u32 = 41;
const NEG_NEIGHBORS: u32 = 49;
const DIRECTIONS: [(i32, i32); 8] = [
    (-1, -1),
    (0, -1),
    (1, -1),
    (-1, 0),
    (1, 0),
    (-1, 1),
    (0, 1),
    (1, 1),
];

const ZERO_NORMAL: [u8; 256] = [
    0, 1, 3, 3, 1, 2, 3, 3, 5, 6, 7, 7, 6, 6, 7, 7, 5, 6, 7, 7, 6, 6, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    1, 2, 3, 3, 2, 2, 3, 3, 6, 6, 7, 7, 6, 6, 7, 7, 6, 6, 7, 7, 6, 6, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    3, 3, 4, 4, 3, 3, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    3, 3, 4, 4, 3, 3, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    1, 2, 3, 3, 2, 2, 3, 3, 6, 6, 7, 7, 6, 6, 7, 7, 6, 6, 7, 7, 6, 6, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    2, 2, 3, 3, 2, 2, 3, 3, 6, 6, 7, 7, 6, 6, 7, 7, 6, 6, 7, 7, 6, 6, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    3, 3, 4, 4, 3, 3, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
    3, 3, 4, 4, 3, 3, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8,
];
const ZERO_HL: [u8; 256] = [
    0, 1, 5, 6, 1, 2, 6, 6, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 4, 4, 7, 7, 4, 4, 7, 7,
    1, 2, 6, 6, 2, 2, 6, 6, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 4, 4, 7, 7, 4, 4, 7, 7,
    5, 6, 8, 8, 6, 6, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8,
    6, 6, 8, 8, 6, 6, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8,
    1, 2, 6, 6, 2, 2, 6, 6, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 4, 4, 7, 7, 4, 4, 7, 7,
    2, 2, 6, 6, 2, 2, 6, 6, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 3, 3, 7, 7, 4, 4, 7, 7, 4, 4, 7, 7,
    6, 6, 8, 8, 6, 6, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8,
    6, 6, 8, 8, 6, 6, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8, 7, 7, 8, 8,
];
const ZERO_HH: [u8; 256] = [
    0, 3, 1, 4, 3, 6, 4, 7, 1, 4, 2, 5, 4, 7, 5, 7, 1, 4, 2, 5, 4, 7, 5, 7, 2, 5, 2, 5, 5, 7, 5, 7,
    3, 6, 4, 7, 6, 8, 7, 8, 4, 7, 5, 7, 7, 8, 7, 8, 4, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8,
    1, 4, 2, 5, 4, 7, 5, 7, 2, 5, 2, 5, 5, 7, 5, 7, 2, 5, 2, 5, 5, 7, 5, 7, 2, 5, 2, 5, 5, 7, 5, 7,
    4, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8,
    3, 6, 4, 7, 6, 8, 7, 8, 4, 7, 5, 7, 7, 8, 7, 8, 4, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8,
    6, 8, 7, 8, 8, 8, 8, 8, 7, 8, 7, 8, 8, 8, 8, 8, 7, 8, 7, 8, 8, 8, 8, 8, 7, 8, 7, 8, 8, 8, 8, 8,
    4, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8, 5, 7, 5, 7, 7, 8, 7, 8,
    7, 8, 7, 8, 8, 8, 8, 8, 7, 8, 7, 8, 8, 8, 8, 8, 7, 8, 7, 8, 8, 8, 8, 8, 7, 8, 7, 8, 8, 8, 8, 8,
];
const SIGN_TABLE: [u8; 256] = [
    18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 20, 21, 20, 21, 20, 21, 20, 21,
    20, 21, 20, 21, 20, 21, 20, 21, 24, 24, 25, 25, 24, 24, 25, 25, 24, 24, 25, 25, 24, 24, 25, 25,
    26, 22, 23, 27, 26, 22, 23, 27, 26, 22, 23, 27, 26, 22, 23, 27, 24, 24, 24, 24, 25, 25, 25, 25,
    24, 24, 24, 24, 25, 25, 25, 25, 26, 22, 26, 22, 23, 27, 23, 27, 26, 22, 26, 22, 23, 27, 23, 27,
    24, 24, 18, 18, 18, 18, 25, 25, 24, 24, 18, 18, 18, 18, 25, 25, 26, 22, 20, 21, 20, 21, 23, 27,
    26, 22, 20, 21, 20, 21, 23, 27, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21,
    20, 18, 20, 18, 20, 18, 20, 18, 18, 21, 18, 21, 18, 21, 18, 21, 26, 26, 23, 23, 26, 26, 23, 23,
    22, 22, 27, 27, 22, 22, 27, 27, 26, 24, 23, 25, 26, 24, 23, 25, 24, 22, 25, 27, 24, 22, 25, 27,
    26, 26, 26, 26, 23, 23, 23, 23, 22, 22, 22, 22, 27, 27, 27, 27, 26, 24, 26, 24, 23, 25, 23, 25,
    24, 22, 24, 22, 25, 27, 25, 27, 26, 26, 20, 20, 20, 20, 23, 23, 22, 22, 21, 21, 21, 21, 27, 27,
    26, 24, 20, 18, 20, 18, 23, 25, 24, 22, 18, 21, 18, 21, 25, 27,
];

#[cfg(verus_keep_ghost)]
verus! {
    proof fn u8_bits_to_arith(x: u8)
        ensures
            (x & 1u8) == (x % 2u8),
            ((x >> 1u8) & 1u8) == ((x / 2u8) % 2u8),
            ((x >> 2u8) & 1u8) == ((x / 4u8) % 2u8),
            ((x >> 3u8) & 1u8) == ((x / 8u8) % 2u8),
            ((x >> 4u8) & 1u8) == ((x / 16u8) % 2u8),
            ((x >> 5u8) & 1u8) == ((x / 32u8) % 2u8),
            ((x >> 6u8) & 1u8) == ((x / 64u8) % 2u8),
            ((x >> 7u8) & 1u8) == ((x / 128u8) % 2u8),
            (0u8 & x) == 0u8,
    {
        assert(
            (x & 1u8) == (x % 2u8)
            && ((x >> 1u8) & 1u8) == ((x / 2u8) % 2u8)
            && ((x >> 2u8) & 1u8) == ((x / 4u8) % 2u8)
            && ((x >> 3u8) & 1u8) == ((x / 8u8) % 2u8)
            && ((x >> 4u8) & 1u8) == ((x / 16u8) % 2u8)
            && ((x >> 5u8) & 1u8) == ((x / 32u8) % 2u8)
            && ((x >> 6u8) & 1u8) == ((x / 64u8) % 2u8)
            && ((x >> 7u8) & 1u8) == ((x / 128u8) % 2u8)
            && (0u8 & x) == 0u8
        ) by (bit_vector);
    }

    spec fn zero_lut_spec(sig: u8, orientation: SubbandOrientation) -> u8 {
        crate::specs::part1_legacy_zero_context(
            crate::specs::compact_flag_summary(sig, 0), orientation)
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_normal_q0(sig: u8)
        requires 0 <= sig, sig < 64,
        ensures ZERO_NORMAL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Ll),
    {
        u8_bits_to_arith(sig);
        assert(sig == 0u8 || sig == 1u8 || sig == 2u8 || sig == 3u8 || sig == 4u8 || sig == 5u8 || sig == 6u8 || sig == 7u8 || sig == 8u8 || sig == 9u8 || sig == 10u8 || sig == 11u8 || sig == 12u8 || sig == 13u8 || sig == 14u8 || sig == 15u8 || sig == 16u8 || sig == 17u8 || sig == 18u8 || sig == 19u8 || sig == 20u8 || sig == 21u8 || sig == 22u8 || sig == 23u8 || sig == 24u8 || sig == 25u8 || sig == 26u8 || sig == 27u8 || sig == 28u8 || sig == 29u8 || sig == 30u8 || sig == 31u8 || sig == 32u8 || sig == 33u8 || sig == 34u8 || sig == 35u8 || sig == 36u8 || sig == 37u8 || sig == 38u8 || sig == 39u8 || sig == 40u8 || sig == 41u8 || sig == 42u8 || sig == 43u8 || sig == 44u8 || sig == 45u8 || sig == 46u8 || sig == 47u8 || sig == 48u8 || sig == 49u8 || sig == 50u8 || sig == 51u8 || sig == 52u8 || sig == 53u8 || sig == 54u8 || sig == 55u8 || sig == 56u8 || sig == 57u8 || sig == 58u8 || sig == 59u8 || sig == 60u8 || sig == 61u8 || sig == 62u8 || sig == 63u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_normal_q1(sig: u8)
        requires 64 <= sig, sig < 128,
        ensures ZERO_NORMAL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Ll),
    {
        u8_bits_to_arith(sig);
        assert(sig == 64u8 || sig == 65u8 || sig == 66u8 || sig == 67u8 || sig == 68u8 || sig == 69u8 || sig == 70u8 || sig == 71u8 || sig == 72u8 || sig == 73u8 || sig == 74u8 || sig == 75u8 || sig == 76u8 || sig == 77u8 || sig == 78u8 || sig == 79u8 || sig == 80u8 || sig == 81u8 || sig == 82u8 || sig == 83u8 || sig == 84u8 || sig == 85u8 || sig == 86u8 || sig == 87u8 || sig == 88u8 || sig == 89u8 || sig == 90u8 || sig == 91u8 || sig == 92u8 || sig == 93u8 || sig == 94u8 || sig == 95u8 || sig == 96u8 || sig == 97u8 || sig == 98u8 || sig == 99u8 || sig == 100u8 || sig == 101u8 || sig == 102u8 || sig == 103u8 || sig == 104u8 || sig == 105u8 || sig == 106u8 || sig == 107u8 || sig == 108u8 || sig == 109u8 || sig == 110u8 || sig == 111u8 || sig == 112u8 || sig == 113u8 || sig == 114u8 || sig == 115u8 || sig == 116u8 || sig == 117u8 || sig == 118u8 || sig == 119u8 || sig == 120u8 || sig == 121u8 || sig == 122u8 || sig == 123u8 || sig == 124u8 || sig == 125u8 || sig == 126u8 || sig == 127u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_normal_q2(sig: u8)
        requires 128 <= sig, sig < 192,
        ensures ZERO_NORMAL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Ll),
    {
        u8_bits_to_arith(sig);
        assert(sig == 128u8 || sig == 129u8 || sig == 130u8 || sig == 131u8 || sig == 132u8 || sig == 133u8 || sig == 134u8 || sig == 135u8 || sig == 136u8 || sig == 137u8 || sig == 138u8 || sig == 139u8 || sig == 140u8 || sig == 141u8 || sig == 142u8 || sig == 143u8 || sig == 144u8 || sig == 145u8 || sig == 146u8 || sig == 147u8 || sig == 148u8 || sig == 149u8 || sig == 150u8 || sig == 151u8 || sig == 152u8 || sig == 153u8 || sig == 154u8 || sig == 155u8 || sig == 156u8 || sig == 157u8 || sig == 158u8 || sig == 159u8 || sig == 160u8 || sig == 161u8 || sig == 162u8 || sig == 163u8 || sig == 164u8 || sig == 165u8 || sig == 166u8 || sig == 167u8 || sig == 168u8 || sig == 169u8 || sig == 170u8 || sig == 171u8 || sig == 172u8 || sig == 173u8 || sig == 174u8 || sig == 175u8 || sig == 176u8 || sig == 177u8 || sig == 178u8 || sig == 179u8 || sig == 180u8 || sig == 181u8 || sig == 182u8 || sig == 183u8 || sig == 184u8 || sig == 185u8 || sig == 186u8 || sig == 187u8 || sig == 188u8 || sig == 189u8 || sig == 190u8 || sig == 191u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_normal_q3(sig: u8)
        requires 192 <= sig, sig < 256,
        ensures ZERO_NORMAL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Ll),
    {
        u8_bits_to_arith(sig);
        assert(sig == 192u8 || sig == 193u8 || sig == 194u8 || sig == 195u8 || sig == 196u8 || sig == 197u8 || sig == 198u8 || sig == 199u8 || sig == 200u8 || sig == 201u8 || sig == 202u8 || sig == 203u8 || sig == 204u8 || sig == 205u8 || sig == 206u8 || sig == 207u8 || sig == 208u8 || sig == 209u8 || sig == 210u8 || sig == 211u8 || sig == 212u8 || sig == 213u8 || sig == 214u8 || sig == 215u8 || sig == 216u8 || sig == 217u8 || sig == 218u8 || sig == 219u8 || sig == 220u8 || sig == 221u8 || sig == 222u8 || sig == 223u8 || sig == 224u8 || sig == 225u8 || sig == 226u8 || sig == 227u8 || sig == 228u8 || sig == 229u8 || sig == 230u8 || sig == 231u8 || sig == 232u8 || sig == 233u8 || sig == 234u8 || sig == 235u8 || sig == 236u8 || sig == 237u8 || sig == 238u8 || sig == 239u8 || sig == 240u8 || sig == 241u8 || sig == 242u8 || sig == 243u8 || sig == 244u8 || sig == 245u8 || sig == 246u8 || sig == 247u8 || sig == 248u8 || sig == 249u8 || sig == 250u8 || sig == 251u8 || sig == 252u8 || sig == 253u8 || sig == 254u8 || sig == 255u8);
    }

    proof fn zero_lut_normal(sig: u8)
        ensures ZERO_NORMAL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Ll),
    {
        if sig < 64 { zero_lut_normal_q0(sig); }
        else if sig < 128 { zero_lut_normal_q1(sig); }
        else if sig < 192 { zero_lut_normal_q2(sig); }
        else { zero_lut_normal_q3(sig); }
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hl_q0(sig: u8)
        requires 0 <= sig, sig < 64,
        ensures ZERO_HL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hl),
    {
        u8_bits_to_arith(sig);
        assert(sig == 0u8 || sig == 1u8 || sig == 2u8 || sig == 3u8 || sig == 4u8 || sig == 5u8 || sig == 6u8 || sig == 7u8 || sig == 8u8 || sig == 9u8 || sig == 10u8 || sig == 11u8 || sig == 12u8 || sig == 13u8 || sig == 14u8 || sig == 15u8 || sig == 16u8 || sig == 17u8 || sig == 18u8 || sig == 19u8 || sig == 20u8 || sig == 21u8 || sig == 22u8 || sig == 23u8 || sig == 24u8 || sig == 25u8 || sig == 26u8 || sig == 27u8 || sig == 28u8 || sig == 29u8 || sig == 30u8 || sig == 31u8 || sig == 32u8 || sig == 33u8 || sig == 34u8 || sig == 35u8 || sig == 36u8 || sig == 37u8 || sig == 38u8 || sig == 39u8 || sig == 40u8 || sig == 41u8 || sig == 42u8 || sig == 43u8 || sig == 44u8 || sig == 45u8 || sig == 46u8 || sig == 47u8 || sig == 48u8 || sig == 49u8 || sig == 50u8 || sig == 51u8 || sig == 52u8 || sig == 53u8 || sig == 54u8 || sig == 55u8 || sig == 56u8 || sig == 57u8 || sig == 58u8 || sig == 59u8 || sig == 60u8 || sig == 61u8 || sig == 62u8 || sig == 63u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hl_q1(sig: u8)
        requires 64 <= sig, sig < 128,
        ensures ZERO_HL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hl),
    {
        u8_bits_to_arith(sig);
        assert(sig == 64u8 || sig == 65u8 || sig == 66u8 || sig == 67u8 || sig == 68u8 || sig == 69u8 || sig == 70u8 || sig == 71u8 || sig == 72u8 || sig == 73u8 || sig == 74u8 || sig == 75u8 || sig == 76u8 || sig == 77u8 || sig == 78u8 || sig == 79u8 || sig == 80u8 || sig == 81u8 || sig == 82u8 || sig == 83u8 || sig == 84u8 || sig == 85u8 || sig == 86u8 || sig == 87u8 || sig == 88u8 || sig == 89u8 || sig == 90u8 || sig == 91u8 || sig == 92u8 || sig == 93u8 || sig == 94u8 || sig == 95u8 || sig == 96u8 || sig == 97u8 || sig == 98u8 || sig == 99u8 || sig == 100u8 || sig == 101u8 || sig == 102u8 || sig == 103u8 || sig == 104u8 || sig == 105u8 || sig == 106u8 || sig == 107u8 || sig == 108u8 || sig == 109u8 || sig == 110u8 || sig == 111u8 || sig == 112u8 || sig == 113u8 || sig == 114u8 || sig == 115u8 || sig == 116u8 || sig == 117u8 || sig == 118u8 || sig == 119u8 || sig == 120u8 || sig == 121u8 || sig == 122u8 || sig == 123u8 || sig == 124u8 || sig == 125u8 || sig == 126u8 || sig == 127u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hl_q2(sig: u8)
        requires 128 <= sig, sig < 192,
        ensures ZERO_HL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hl),
    {
        u8_bits_to_arith(sig);
        assert(sig == 128u8 || sig == 129u8 || sig == 130u8 || sig == 131u8 || sig == 132u8 || sig == 133u8 || sig == 134u8 || sig == 135u8 || sig == 136u8 || sig == 137u8 || sig == 138u8 || sig == 139u8 || sig == 140u8 || sig == 141u8 || sig == 142u8 || sig == 143u8 || sig == 144u8 || sig == 145u8 || sig == 146u8 || sig == 147u8 || sig == 148u8 || sig == 149u8 || sig == 150u8 || sig == 151u8 || sig == 152u8 || sig == 153u8 || sig == 154u8 || sig == 155u8 || sig == 156u8 || sig == 157u8 || sig == 158u8 || sig == 159u8 || sig == 160u8 || sig == 161u8 || sig == 162u8 || sig == 163u8 || sig == 164u8 || sig == 165u8 || sig == 166u8 || sig == 167u8 || sig == 168u8 || sig == 169u8 || sig == 170u8 || sig == 171u8 || sig == 172u8 || sig == 173u8 || sig == 174u8 || sig == 175u8 || sig == 176u8 || sig == 177u8 || sig == 178u8 || sig == 179u8 || sig == 180u8 || sig == 181u8 || sig == 182u8 || sig == 183u8 || sig == 184u8 || sig == 185u8 || sig == 186u8 || sig == 187u8 || sig == 188u8 || sig == 189u8 || sig == 190u8 || sig == 191u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hl_q3(sig: u8)
        requires 192 <= sig, sig < 256,
        ensures ZERO_HL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hl),
    {
        u8_bits_to_arith(sig);
        assert(sig == 192u8 || sig == 193u8 || sig == 194u8 || sig == 195u8 || sig == 196u8 || sig == 197u8 || sig == 198u8 || sig == 199u8 || sig == 200u8 || sig == 201u8 || sig == 202u8 || sig == 203u8 || sig == 204u8 || sig == 205u8 || sig == 206u8 || sig == 207u8 || sig == 208u8 || sig == 209u8 || sig == 210u8 || sig == 211u8 || sig == 212u8 || sig == 213u8 || sig == 214u8 || sig == 215u8 || sig == 216u8 || sig == 217u8 || sig == 218u8 || sig == 219u8 || sig == 220u8 || sig == 221u8 || sig == 222u8 || sig == 223u8 || sig == 224u8 || sig == 225u8 || sig == 226u8 || sig == 227u8 || sig == 228u8 || sig == 229u8 || sig == 230u8 || sig == 231u8 || sig == 232u8 || sig == 233u8 || sig == 234u8 || sig == 235u8 || sig == 236u8 || sig == 237u8 || sig == 238u8 || sig == 239u8 || sig == 240u8 || sig == 241u8 || sig == 242u8 || sig == 243u8 || sig == 244u8 || sig == 245u8 || sig == 246u8 || sig == 247u8 || sig == 248u8 || sig == 249u8 || sig == 250u8 || sig == 251u8 || sig == 252u8 || sig == 253u8 || sig == 254u8 || sig == 255u8);
    }

    proof fn zero_lut_hl(sig: u8)
        ensures ZERO_HL@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hl),
    {
        if sig < 64 { zero_lut_hl_q0(sig); }
        else if sig < 128 { zero_lut_hl_q1(sig); }
        else if sig < 192 { zero_lut_hl_q2(sig); }
        else { zero_lut_hl_q3(sig); }
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hh_q0(sig: u8)
        requires 0 <= sig, sig < 64,
        ensures ZERO_HH@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hh),
    {
        u8_bits_to_arith(sig);
        assert(sig == 0u8 || sig == 1u8 || sig == 2u8 || sig == 3u8 || sig == 4u8 || sig == 5u8 || sig == 6u8 || sig == 7u8 || sig == 8u8 || sig == 9u8 || sig == 10u8 || sig == 11u8 || sig == 12u8 || sig == 13u8 || sig == 14u8 || sig == 15u8 || sig == 16u8 || sig == 17u8 || sig == 18u8 || sig == 19u8 || sig == 20u8 || sig == 21u8 || sig == 22u8 || sig == 23u8 || sig == 24u8 || sig == 25u8 || sig == 26u8 || sig == 27u8 || sig == 28u8 || sig == 29u8 || sig == 30u8 || sig == 31u8 || sig == 32u8 || sig == 33u8 || sig == 34u8 || sig == 35u8 || sig == 36u8 || sig == 37u8 || sig == 38u8 || sig == 39u8 || sig == 40u8 || sig == 41u8 || sig == 42u8 || sig == 43u8 || sig == 44u8 || sig == 45u8 || sig == 46u8 || sig == 47u8 || sig == 48u8 || sig == 49u8 || sig == 50u8 || sig == 51u8 || sig == 52u8 || sig == 53u8 || sig == 54u8 || sig == 55u8 || sig == 56u8 || sig == 57u8 || sig == 58u8 || sig == 59u8 || sig == 60u8 || sig == 61u8 || sig == 62u8 || sig == 63u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hh_q1(sig: u8)
        requires 64 <= sig, sig < 128,
        ensures ZERO_HH@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hh),
    {
        u8_bits_to_arith(sig);
        assert(sig == 64u8 || sig == 65u8 || sig == 66u8 || sig == 67u8 || sig == 68u8 || sig == 69u8 || sig == 70u8 || sig == 71u8 || sig == 72u8 || sig == 73u8 || sig == 74u8 || sig == 75u8 || sig == 76u8 || sig == 77u8 || sig == 78u8 || sig == 79u8 || sig == 80u8 || sig == 81u8 || sig == 82u8 || sig == 83u8 || sig == 84u8 || sig == 85u8 || sig == 86u8 || sig == 87u8 || sig == 88u8 || sig == 89u8 || sig == 90u8 || sig == 91u8 || sig == 92u8 || sig == 93u8 || sig == 94u8 || sig == 95u8 || sig == 96u8 || sig == 97u8 || sig == 98u8 || sig == 99u8 || sig == 100u8 || sig == 101u8 || sig == 102u8 || sig == 103u8 || sig == 104u8 || sig == 105u8 || sig == 106u8 || sig == 107u8 || sig == 108u8 || sig == 109u8 || sig == 110u8 || sig == 111u8 || sig == 112u8 || sig == 113u8 || sig == 114u8 || sig == 115u8 || sig == 116u8 || sig == 117u8 || sig == 118u8 || sig == 119u8 || sig == 120u8 || sig == 121u8 || sig == 122u8 || sig == 123u8 || sig == 124u8 || sig == 125u8 || sig == 126u8 || sig == 127u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hh_q2(sig: u8)
        requires 128 <= sig, sig < 192,
        ensures ZERO_HH@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hh),
    {
        u8_bits_to_arith(sig);
        assert(sig == 128u8 || sig == 129u8 || sig == 130u8 || sig == 131u8 || sig == 132u8 || sig == 133u8 || sig == 134u8 || sig == 135u8 || sig == 136u8 || sig == 137u8 || sig == 138u8 || sig == 139u8 || sig == 140u8 || sig == 141u8 || sig == 142u8 || sig == 143u8 || sig == 144u8 || sig == 145u8 || sig == 146u8 || sig == 147u8 || sig == 148u8 || sig == 149u8 || sig == 150u8 || sig == 151u8 || sig == 152u8 || sig == 153u8 || sig == 154u8 || sig == 155u8 || sig == 156u8 || sig == 157u8 || sig == 158u8 || sig == 159u8 || sig == 160u8 || sig == 161u8 || sig == 162u8 || sig == 163u8 || sig == 164u8 || sig == 165u8 || sig == 166u8 || sig == 167u8 || sig == 168u8 || sig == 169u8 || sig == 170u8 || sig == 171u8 || sig == 172u8 || sig == 173u8 || sig == 174u8 || sig == 175u8 || sig == 176u8 || sig == 177u8 || sig == 178u8 || sig == 179u8 || sig == 180u8 || sig == 181u8 || sig == 182u8 || sig == 183u8 || sig == 184u8 || sig == 185u8 || sig == 186u8 || sig == 187u8 || sig == 188u8 || sig == 189u8 || sig == 190u8 || sig == 191u8);
    }

    #[verifier::spinoff_prover]
    proof fn zero_lut_hh_q3(sig: u8)
        requires 192 <= sig, sig < 256,
        ensures ZERO_HH@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hh),
    {
        u8_bits_to_arith(sig);
        assert(sig == 192u8 || sig == 193u8 || sig == 194u8 || sig == 195u8 || sig == 196u8 || sig == 197u8 || sig == 198u8 || sig == 199u8 || sig == 200u8 || sig == 201u8 || sig == 202u8 || sig == 203u8 || sig == 204u8 || sig == 205u8 || sig == 206u8 || sig == 207u8 || sig == 208u8 || sig == 209u8 || sig == 210u8 || sig == 211u8 || sig == 212u8 || sig == 213u8 || sig == 214u8 || sig == 215u8 || sig == 216u8 || sig == 217u8 || sig == 218u8 || sig == 219u8 || sig == 220u8 || sig == 221u8 || sig == 222u8 || sig == 223u8 || sig == 224u8 || sig == 225u8 || sig == 226u8 || sig == 227u8 || sig == 228u8 || sig == 229u8 || sig == 230u8 || sig == 231u8 || sig == 232u8 || sig == 233u8 || sig == 234u8 || sig == 235u8 || sig == 236u8 || sig == 237u8 || sig == 238u8 || sig == 239u8 || sig == 240u8 || sig == 241u8 || sig == 242u8 || sig == 243u8 || sig == 244u8 || sig == 245u8 || sig == 246u8 || sig == 247u8 || sig == 248u8 || sig == 249u8 || sig == 250u8 || sig == 251u8 || sig == 252u8 || sig == 253u8 || sig == 254u8 || sig == 255u8);
    }

    proof fn zero_lut_hh(sig: u8)
        ensures ZERO_HH@[sig as int] == zero_lut_spec(sig, SubbandOrientation::Hh),
    {
        if sig < 64 { zero_lut_hh_q0(sig); }
        else if sig < 128 { zero_lut_hh_q1(sig); }
        else if sig < 192 { zero_lut_hh_q2(sig); }
        else { zero_lut_hh_q3(sig); }
    }

    spec fn sign_lut_entry_spec(idx: u8) -> u8 {
        let s1 = (idx / 16u8) % 2u8;
        let s3 = (idx / 32u8) % 2u8;
        let s4 = (idx / 64u8) % 2u8;
        let s6 = (idx / 128u8) % 2u8;
        let n1 = if s1 == 1u8 { idx % 2u8 } else { 0u8 };
        let n3 = if s3 == 1u8 { (idx / 2u8) % 2u8 } else { 0u8 };
        let n4 = if s4 == 1u8 { (idx / 4u8) % 2u8 } else { 0u8 };
        let n6 = if s6 == 1u8 { (idx / 8u8) % 2u8 } else { 0u8 };
        let summary = NeighborSummary {
            horizontal_significant: (s3 + s4) as u8,
            vertical_significant: (s1 + s6) as u8,
            diagonal_significant: 0u8,
            horizontal_sign_balance: ((s3 as int + s4 as int) - 2 * (n3 as int + n4 as int)) as i8,
            vertical_sign_balance: ((s1 as int + s6 as int) - 2 * (n1 as int + n6 as int)) as i8,
        };
        let sc = crate::specs::part1_legacy_sign_context(summary);
        ((sc.context as int) * 2 + if sc.predicted_negative { 1int } else { 0int }) as u8
    }

    #[verifier::spinoff_prover]
    proof fn sign_lut_q0(idx: u8)
        requires 0 <= idx, idx < 64,
        ensures SIGN_TABLE@[idx as int] == sign_lut_entry_spec(idx),
    {
        assert(idx == 0u8 || idx == 1u8 || idx == 2u8 || idx == 3u8 || idx == 4u8 || idx == 5u8 || idx == 6u8 || idx == 7u8 || idx == 8u8 || idx == 9u8 || idx == 10u8 || idx == 11u8 || idx == 12u8 || idx == 13u8 || idx == 14u8 || idx == 15u8 || idx == 16u8 || idx == 17u8 || idx == 18u8 || idx == 19u8 || idx == 20u8 || idx == 21u8 || idx == 22u8 || idx == 23u8 || idx == 24u8 || idx == 25u8 || idx == 26u8 || idx == 27u8 || idx == 28u8 || idx == 29u8 || idx == 30u8 || idx == 31u8 || idx == 32u8 || idx == 33u8 || idx == 34u8 || idx == 35u8 || idx == 36u8 || idx == 37u8 || idx == 38u8 || idx == 39u8 || idx == 40u8 || idx == 41u8 || idx == 42u8 || idx == 43u8 || idx == 44u8 || idx == 45u8 || idx == 46u8 || idx == 47u8 || idx == 48u8 || idx == 49u8 || idx == 50u8 || idx == 51u8 || idx == 52u8 || idx == 53u8 || idx == 54u8 || idx == 55u8 || idx == 56u8 || idx == 57u8 || idx == 58u8 || idx == 59u8 || idx == 60u8 || idx == 61u8 || idx == 62u8 || idx == 63u8);
    }

    #[verifier::spinoff_prover]
    proof fn sign_lut_q1(idx: u8)
        requires 64 <= idx, idx < 128,
        ensures SIGN_TABLE@[idx as int] == sign_lut_entry_spec(idx),
    {
        assert(idx == 64u8 || idx == 65u8 || idx == 66u8 || idx == 67u8 || idx == 68u8 || idx == 69u8 || idx == 70u8 || idx == 71u8 || idx == 72u8 || idx == 73u8 || idx == 74u8 || idx == 75u8 || idx == 76u8 || idx == 77u8 || idx == 78u8 || idx == 79u8 || idx == 80u8 || idx == 81u8 || idx == 82u8 || idx == 83u8 || idx == 84u8 || idx == 85u8 || idx == 86u8 || idx == 87u8 || idx == 88u8 || idx == 89u8 || idx == 90u8 || idx == 91u8 || idx == 92u8 || idx == 93u8 || idx == 94u8 || idx == 95u8 || idx == 96u8 || idx == 97u8 || idx == 98u8 || idx == 99u8 || idx == 100u8 || idx == 101u8 || idx == 102u8 || idx == 103u8 || idx == 104u8 || idx == 105u8 || idx == 106u8 || idx == 107u8 || idx == 108u8 || idx == 109u8 || idx == 110u8 || idx == 111u8 || idx == 112u8 || idx == 113u8 || idx == 114u8 || idx == 115u8 || idx == 116u8 || idx == 117u8 || idx == 118u8 || idx == 119u8 || idx == 120u8 || idx == 121u8 || idx == 122u8 || idx == 123u8 || idx == 124u8 || idx == 125u8 || idx == 126u8 || idx == 127u8);
    }

    #[verifier::spinoff_prover]
    proof fn sign_lut_q2(idx: u8)
        requires 128 <= idx, idx < 192,
        ensures SIGN_TABLE@[idx as int] == sign_lut_entry_spec(idx),
    {
        assert(idx == 128u8 || idx == 129u8 || idx == 130u8 || idx == 131u8 || idx == 132u8 || idx == 133u8 || idx == 134u8 || idx == 135u8 || idx == 136u8 || idx == 137u8 || idx == 138u8 || idx == 139u8 || idx == 140u8 || idx == 141u8 || idx == 142u8 || idx == 143u8 || idx == 144u8 || idx == 145u8 || idx == 146u8 || idx == 147u8 || idx == 148u8 || idx == 149u8 || idx == 150u8 || idx == 151u8 || idx == 152u8 || idx == 153u8 || idx == 154u8 || idx == 155u8 || idx == 156u8 || idx == 157u8 || idx == 158u8 || idx == 159u8 || idx == 160u8 || idx == 161u8 || idx == 162u8 || idx == 163u8 || idx == 164u8 || idx == 165u8 || idx == 166u8 || idx == 167u8 || idx == 168u8 || idx == 169u8 || idx == 170u8 || idx == 171u8 || idx == 172u8 || idx == 173u8 || idx == 174u8 || idx == 175u8 || idx == 176u8 || idx == 177u8 || idx == 178u8 || idx == 179u8 || idx == 180u8 || idx == 181u8 || idx == 182u8 || idx == 183u8 || idx == 184u8 || idx == 185u8 || idx == 186u8 || idx == 187u8 || idx == 188u8 || idx == 189u8 || idx == 190u8 || idx == 191u8);
    }

    #[verifier::spinoff_prover]
    proof fn sign_lut_q3(idx: u8)
        requires 192 <= idx, idx < 256,
        ensures SIGN_TABLE@[idx as int] == sign_lut_entry_spec(idx),
    {
        assert(idx == 192u8 || idx == 193u8 || idx == 194u8 || idx == 195u8 || idx == 196u8 || idx == 197u8 || idx == 198u8 || idx == 199u8 || idx == 200u8 || idx == 201u8 || idx == 202u8 || idx == 203u8 || idx == 204u8 || idx == 205u8 || idx == 206u8 || idx == 207u8 || idx == 208u8 || idx == 209u8 || idx == 210u8 || idx == 211u8 || idx == 212u8 || idx == 213u8 || idx == 214u8 || idx == 215u8 || idx == 216u8 || idx == 217u8 || idx == 218u8 || idx == 219u8 || idx == 220u8 || idx == 221u8 || idx == 222u8 || idx == 223u8 || idx == 224u8 || idx == 225u8 || idx == 226u8 || idx == 227u8 || idx == 228u8 || idx == 229u8 || idx == 230u8 || idx == 231u8 || idx == 232u8 || idx == 233u8 || idx == 234u8 || idx == 235u8 || idx == 236u8 || idx == 237u8 || idx == 238u8 || idx == 239u8 || idx == 240u8 || idx == 241u8 || idx == 242u8 || idx == 243u8 || idx == 244u8 || idx == 245u8 || idx == 246u8 || idx == 247u8 || idx == 248u8 || idx == 249u8 || idx == 250u8 || idx == 251u8 || idx == 252u8 || idx == 253u8 || idx == 254u8 || idx == 255u8);
    }

    proof fn sign_lut(idx: u8)
        ensures SIGN_TABLE@[idx as int] == sign_lut_entry_spec(idx),
    {
        if idx < 64 { sign_lut_q0(idx); }
        else if idx < 128 { sign_lut_q1(idx); }
        else if idx < 192 { sign_lut_q2(idx); }
        else { sign_lut_q3(idx); }
    }

    proof fn sign_index_bits(sig: u8, neg: u8, cs: u8, cn: u8, idx: u8, masked: u8)
        requires
            cs == (((sig >> 1u8) & 1u8) | ((sig >> 2u8) & 6u8) | ((sig >> 3u8) & 8u8)),
            cn == (((neg >> 1u8) & 1u8) | ((neg >> 2u8) & 6u8) | ((neg >> 3u8) & 8u8)),
            idx == ((cs << 4u8) | cn),
            masked == (neg & sig),
        ensures
            ((sig >> 1u8) & 1u8) == ((idx / 16u8) % 2u8),
            ((sig >> 3u8) & 1u8) == ((idx / 32u8) % 2u8),
            ((sig >> 4u8) & 1u8) == ((idx / 64u8) % 2u8),
            ((sig >> 6u8) & 1u8) == ((idx / 128u8) % 2u8),
            ((masked >> 1u8) & 1u8) == (if ((idx / 16u8) % 2u8) == 1u8 { idx % 2u8 } else { 0u8 }),
            ((masked >> 3u8) & 1u8) == (if ((idx / 32u8) % 2u8) == 1u8 { (idx / 2u8) % 2u8 } else { 0u8 }),
            ((masked >> 4u8) & 1u8) == (if ((idx / 64u8) % 2u8) == 1u8 { (idx / 4u8) % 2u8 } else { 0u8 }),
            ((masked >> 6u8) & 1u8) == (if ((idx / 128u8) % 2u8) == 1u8 { (idx / 8u8) % 2u8 } else { 0u8 }),
    {
        assert(
            ((sig >> 1u8) & 1u8) == ((idx / 16u8) % 2u8)
            && ((sig >> 3u8) & 1u8) == ((idx / 32u8) % 2u8)
            && ((sig >> 4u8) & 1u8) == ((idx / 64u8) % 2u8)
            && ((sig >> 6u8) & 1u8) == ((idx / 128u8) % 2u8)
            && ((masked >> 1u8) & 1u8) == (if ((idx / 16u8) % 2u8) == 1u8 { idx % 2u8 } else { 0u8 })
            && ((masked >> 3u8) & 1u8) == (if ((idx / 32u8) % 2u8) == 1u8 { (idx / 2u8) % 2u8 } else { 0u8 })
            && ((masked >> 4u8) & 1u8) == (if ((idx / 64u8) % 2u8) == 1u8 { (idx / 4u8) % 2u8 } else { 0u8 })
            && ((masked >> 6u8) & 1u8) == (if ((idx / 128u8) % 2u8) == 1u8 { (idx / 8u8) % 2u8 } else { 0u8 })
        ) by (bit_vector)
            requires
                cs == (((sig >> 1u8) & 1u8) | ((sig >> 2u8) & 6u8) | ((sig >> 3u8) & 8u8)),
                cn == (((neg >> 1u8) & 1u8) | ((neg >> 2u8) & 6u8) | ((neg >> 3u8) & 8u8)),
                idx == ((cs << 4u8) | cn),
                masked == (neg & sig);
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_zero_context(
        crate::specs::compact_flag_summary(sig, 0), orientation),
))]
#[inline(always)]
fn cached_zero_context(sig: u8, orientation: SubbandOrientation) -> u8 {
    match orientation {
        SubbandOrientation::Hl => {
            #[cfg(verus_keep_ghost)]
            proof! { zero_lut_hl(sig); }
            ZERO_HL[usize::from(sig)]
        }
        SubbandOrientation::Hh => {
            #[cfg(verus_keep_ghost)]
            proof! { zero_lut_hh(sig); }
            ZERO_HH[usize::from(sig)]
        }
        SubbandOrientation::Ll | SubbandOrientation::Lh => {
            #[cfg(verus_keep_ghost)]
            proof! { zero_lut_normal(sig); }
            ZERO_NORMAL[usize::from(sig)]
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_sign_context(
        crate::specs::compact_flag_summary(sig, neg)),
))]
#[inline(always)]
fn cached_sign_context(sig: u8, neg: u8) -> SignContext {
    let cs = ((sig >> 1) & 1) | ((sig >> 2) & 6) | ((sig >> 3) & 8);
    let cn = ((neg >> 1) & 1) | ((neg >> 2) & 6) | ((neg >> 3) & 8);
    let idx = (cs << 4) | cn;
    let entry = SIGN_TABLE[usize::from(idx)];
    let context = entry >> 1;
    let predicted_negative = (entry & 1) != 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        sign_index_bits(sig, neg, cs, cn, idx, neg & sig);
        sign_lut(idx);
        let sc = crate::specs::part1_legacy_sign_context(crate::specs::compact_flag_summary(sig, neg));
        assert(sc.context <= 13);
        assert(entry == ((sc.context as int) * 2 + if sc.predicted_negative { 1int } else { 0int }) as u8);
        assert((entry >> 1u8) == (entry / 2u8) && ((entry & 1u8) != 0) == ((entry % 2u8) != 0)) by (bit_vector);
        assert(context == sc.context && predicted_negative == sc.predicted_negative);
    }
    SignContext {
        context,
        predicted_negative,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == ((value >> 41) as u8) & if causal && y % 4 == 3 { 0x1fu8 } else { 0xffu8 },
))]
#[inline(always)]
fn significance_mask(value: u64, y: usize, causal: bool) -> u8 {
    ((value >> SIG_NEIGHBORS) as u8) & if causal && y % 4 == 3 { 0x1f } else { 0xff }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == ((value >> 49) as u8) & if causal && y % 4 == 3 { 0x1fu8 } else { 0xffu8 },
))]
#[inline(always)]
fn negative_mask(value: u64, y: usize, causal: bool) -> u8 {
    ((value >> NEG_NEIGHBORS) as u8) & if causal && y % 4 == 3 { 0x1f } else { 0xff }
}

#[cfg(test)]
mod cached_context_tests {
    use super::*;
    use crate::tier1::state::zero_coding_context;

    #[test]
    fn direct_contexts_match_every_cached_mask_orientation_sign_and_vsc_edge() {
        for sig in 0..=u8::MAX {
            for neg in [0, sig, u8::MAX] {
                for y in [0, 3] {
                    for causal in [false, true] {
                        let word = 17
                            | SIG
                            | REFINED
                            | (u64::from(sig) << SIG_NEIGHBORS)
                            | (u64::from(neg) << NEG_NEIGHBORS);
                        let mask = significance_mask(word, y, causal);
                        let signs = negative_mask(word, y, causal);
                        let summary = word_flag_summary(mask, signs);
                        assert_eq!(mask == 0, significant_neighbor_count(summary) == 0);
                        assert_eq!(cached_sign_context(mask, signs), sign_context(summary));
                        for orientation in [
                            SubbandOrientation::Ll,
                            SubbandOrientation::Hl,
                            SubbandOrientation::Lh,
                            SubbandOrientation::Hh,
                        ] {
                            let table = match orientation {
                                SubbandOrientation::Hl => &ZERO_HL,
                                SubbandOrientation::Hh => &ZERO_HH,
                                _ => &ZERO_NORMAL,
                            };
                            assert_eq!(
                                cached_zero_context(mask, orientation),
                                table[usize::from(mask)]
                            );
                            assert_eq!(
                                cached_zero_context(mask, orientation),
                                zero_coding_context(summary, orientation),
                            );
                        }
                    }
                }
            }
        }
    }
}

struct CompactPlane {
    width: usize,
    height: usize,
    entries: Vec<u64>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl CompactPlane {
    closed spec fn view(&self)->crate::specs::Tier1RawPlane {
        crate::specs::compact_plane(self.width,self.height,self.entries@)
    }
    closed spec fn shape(&self)->bool {
        crate::specs::compact_shape(self.width,self.height,self.entries@)
    }
    closed spec fn ready(&self,state:&Tier1BitplaneState)->bool {
        self.shape() && crate::specs::compact_membership(self.width,self.height,self.entries@,super::legacy_bitplane_view(state))
    }
    closed spec fn frame(&self,state:&Tier1BitplaneState,decoder:&MqDecoder<'_>,statistics:Tier1PassStatistics)->crate::specs::Part1LegacyFrame {
        crate::specs::Part1LegacyFrame {
            plane:self.view(),state:super::legacy_bitplane_view(state),
            symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics,
        }
    }
}
impl Tier1CodeBlockDecoder {
    closed spec fn compact_view(&self,packed:&CompactPlane)->crate::specs::Tier1DecoderState {
        crate::specs::Tier1DecoderState {plane:packed.view(),..super::tier1_decoder_state(self)}
    }
    closed spec fn compact_run(&self,packed:&CompactPlane,decoder:&MqDecoder<'_>,statistics:Tier1PassStatistics)->crate::specs::Part1LegacySegmentRun {
        crate::specs::Part1LegacySegmentRun {
            decoder:self.compact_view(packed),symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics,
        }
    }
    proof fn compact_metadata(&self)
        ensures super::tier1_decoder_state(self).plane==super::code_block_plane_view(&self.plane),
            super::tier1_decoder_state(self).next_pass==self.next_pass,
            super::tier1_decoder_state(self).bitplane==self.bitplane,
            super::tier1_decoder_state(self).maximum_passes==self.maximum_passes,
            super::tier1_decoder_state(self).style==self.style,
            super::tier1_decoder_state(self).orientation==self.orientation,
            super::tier1_decoder_state(self).bitplane_state==super::legacy_bitplane_option_view(&self.bitplane_state),
    {reveal(super::tier1_decoder_state);reveal(super::legacy_bitplane_option_view);}
    proof fn compact_views(&self,packed:&CompactPlane,decoder:&MqDecoder<'_>,statistics:Tier1PassStatistics)
        ensures self.compact_view(packed)==crate::specs::compact_substitute_plane(super::tier1_decoder_state(self),packed.view()),
            self.compact_run(packed,decoder,statistics)==(crate::specs::Part1LegacySegmentRun {
                decoder:self.compact_view(packed),symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics}),
    {}
    proof fn compact_native_store(before:Self,after:Self)
        requires after==(Self {next_pass:after.next_pass,bitplane:after.bitplane,bitplane_state:after.bitplane_state,..before}),
        ensures super::tier1_decoder_state(&after)==(crate::specs::Tier1DecoderState {
            next_pass:after.next_pass,bitplane:after.bitplane,
            bitplane_state:super::legacy_bitplane_option_view(&after.bitplane_state),
            ..super::tier1_decoder_state(&before)
        }),
    {reveal(super::tier1_decoder_state);}
}
pub(super) closed spec fn compact_plane_outcome(result:Result<CompactPlane,DecodeError>)->Result<(usize,usize,Seq<u64>),DecodeError> {
    match result{Err(error)=>Err(error),Ok(plane)=>Ok((plane.width,plane.height,plane.entries@)),}
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires 0<width<=4096,0<height<=4096,width*height<=4096,
        ensures crate::specs::compact_initial_result(width,height,compact_plane_outcome(result)),
            crate::specs::compact_capacity_result(width,height,match result{Err(error)=>Err(error),Ok(_)=>Ok(())}),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>
                value.width==width && value.height==height && value.entries@==Seq::new(width as nat*height as nat,|_:int|EMPTY)
                    && crate::specs::compact_cache(width,height,value.entries@)
                    && forall|i:int|0<=i<value.entries.len() ==> crate::specs::compact_precision_word(value.entries@[i])},
    ))]
fn new_compact_plane(width: usize, height: usize) -> Result<CompactPlane, DecodeError> {
    let count = width * height;
    let allocated = crate::allocation::empty_with_capacity(count);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(width*height>0) by(nonlinear_arith) requires width>0,height>0;
        crate::specs::compact_capacity_observed(width,height,match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())});
        crate::specs::compact_initial_observed(width,height,match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())});
    }
    let mut entries = allocated?;
    entries.resize(count, EMPTY);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int|0<=i<count implies entries@[i]==EMPTY by{
            assert(vstd::pervasive::cloned::<u64>(EMPTY,entries@[i]));
        }
        assert(entries@ =~= Seq::new(count as nat,|_:int|EMPTY));
        assert(EMPTY==0x3f_0000_0000u64) by(compute);
        crate::specs::compact_empty_cache(width,height,entries@);
        assert(crate::specs::compact_precision_word(EMPTY)) by(compute);
    }
    Ok(CompactPlane {
        width,
        height,
        entries,
    })
}

impl CompactPlane {
    #[cfg_attr(verus_keep_ghost, verus_spec(_result =>
        requires self.shape(),wide.width==self.width,wide.height==self.height,
            wide.coefficients.len()==self.entries.len(),
        ensures ((),super::code_block_plane_view(final(wide)))==crate::specs::compact_bulk_commit(
                super::code_block_plane_view(old(wide)),self.entries@),
            super::code_block_plane_view(final(wide))==self.view(),
    ))]
    fn commit(&self, wide: &mut super::CodeBlockPlane) {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=self.entries.len(),
                wide.width==self.width,wide.height==self.height,
                wide.coefficients.len()==self.entries.len(),
                forall|i:int|0<=i<index ==> super::coefficient_raw_view(wide.coefficients@[i])==crate::specs::compact_coefficient(self.entries@[i]),
            decreases self.entries.len()-index,
        ))]
        while index < self.entries.len() {
            wide.coefficients[index] = unpack_word(self.entries[index]);
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {assert(super::code_block_plane_view(wide).coefficients =~= self.view().coefficients);}
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::coefficient_raw_view(result)==crate::specs::compact_coefficient(value),
))]
pub(super) fn unpack_word(value: u64) -> CoefficientState {
    let bp = (value & BP_MASK) >> BP_SHIFT;
    let coefficient = CoefficientState {
        magnitude: value & MAG,
        magnitude_high: [0; 5],
        legacy_bitplane: if bp == 63 { None } else { Some(bp as u16) },
        significant: value & SIG != 0,
        negative: value & NEG != 0,
        refined: value & REFINED != 0,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::coefficient_raw_view);
        assert(bp==((value>>32)&63) && bp<=63) by(bit_vector)
            requires bp==(value & (63u64<<32))>>32;
        assert(super::coefficient_raw_view(coefficient).limbs =~= crate::specs::compact_coefficient(value).limbs);
    }
    coefficient
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::compact_packable_coefficient(super::coefficient_raw_view(coefficient)),
))]
pub(super) fn packable(coefficient: CoefficientState) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(super::coefficient_raw_view); }
    coefficient.magnitude <= MAG
        && coefficient.magnitude_high[0] == 0
        && coefficient.magnitude_high[1] == 0
        && coefficient.magnitude_high[2] == 0
        && coefficient.magnitude_high[3] == 0
        && coefficient.magnitude_high[4] == 0
        && match coefficient.legacy_bitplane {
            None => true,
            Some(bp) => bp < 63,
        }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires crate::specs::compact_packable_coefficient(super::coefficient_raw_view(coefficient)),
    ensures crate::specs::compact_coefficient(result) == super::coefficient_raw_view(coefficient),
))]
pub(super) fn pack_word(coefficient: CoefficientState) -> u64 {
    let bp = match coefficient.legacy_bitplane {
        Some(value) => u64::from(value),
        None => 63,
    };
    let mag = coefficient.magnitude;
    let significant = coefficient.significant;
    let negative = coefficient.negative;
    let is_refined = coefficient.refined;
    let sig = if significant { SIG } else { 0 };
    let neg = if negative { NEG } else { 0 };
    let refined = if is_refined { REFINED } else { 0 };
    let word = mag | (bp << BP_SHIFT) | sig | neg | refined;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::coefficient_raw_view);
        assert(mag <= 0xffff_ffff && bp <= 63);
        assert(SIG==1u64<<38 && NEG==1u64<<39 && REFINED==1u64<<40) by(compute);
        assert(sig == if significant { 1u64 << 38 } else { 0 });
        assert(neg == if negative { 1u64 << 39 } else { 0 });
        assert(refined == if is_refined { 1u64 << 40 } else { 0 });
        assert(word & 0xffff_ffffu64 == mag
            && ((word >> 32) & 63) == bp
            && ((word & (1u64 << 38)) != 0) == significant
            && ((word & (1u64 << 39)) != 0) == negative
            && ((word & (1u64 << 40)) != 0) == is_refined) by(bit_vector)
            requires mag <= 0xffff_ffff, bp <= 63,
                sig == (if significant { 1u64 << 38 } else { 0 }),
                neg == (if negative { 1u64 << 39 } else { 0 }),
                refined == (if is_refined { 1u64 << 40 } else { 0 }),
                word == mag | (bp << 32) | sig | neg | refined;
        assert(crate::specs::compact_coefficient(word).limbs =~= super::coefficient_raw_view(coefficient).limbs);
        let packed = crate::specs::compact_coefficient(word);
        let raw = super::coefficient_raw_view(coefficient);
        match coefficient.legacy_bitplane {
            None => {
                assert(bp==63);
                assert(packed.legacy_bitplane.is_none());
            },
            Some(index) => {
                assert(index<63 && bp as u16==index);
                assert(packed.legacy_bitplane==Some(index));
            },
        }
        assert(packed.legacy_bitplane==raw.legacy_bitplane);
        assert(packed.significant==raw.significant);
        assert(packed.negative==raw.negative);
        assert(packed.refined==raw.refined);
    }
    word
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires bp<31,
    ensures result==crate::specs::compact_mark_word(value,bp,negative),
        crate::specs::compact_coefficient(result).significant,
        crate::specs::compact_coefficient(result).negative==negative,
        !crate::specs::compact_coefficient(result).refined,
        crate::specs::compact_coefficient(result).legacy_bitplane==Some(bp),
        crate::specs::compact_coefficient(result).limbs[0]==1u64<<bp,
        result>>41==value>>41,
        crate::specs::compact_precision_word(result),
))]
#[inline(always)]
fn mark_word(value: u64, bp: u16, negative: bool) -> u64 {
    let marked = (value & !(MAG | BP_MASK | NEG | REFINED))
        | (1u64 << bp)
        | ((u64::from(bp)) << BP_SHIFT)
        | SIG
        | if negative { NEG } else { 0 };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::compact_precision_mark(value,bp,negative);
        assert(marked==crate::specs::compact_mark_word(value,bp,negative)) by(bit_vector)
            requires bp<31,
                marked==(value & !(0xffff_ffffu64 | (63u64<<32) | (1u64<<39) | (1u64<<40)))
                    | (1u64<<bp) | ((bp as u64)<<32) | (1u64<<38) | if negative{1u64<<39}else{0u64};
        assert(marked>>41==value>>41
            && marked & (1u64<<38)!=0
            && (marked & (1u64<<39)!=0)==negative
            && marked & (1u64<<40)==0
            && ((marked>>32)&63)==bp as u64
            && marked & 0xffff_ffff==1u64<<bp) by(bit_vector)
            requires bp<31,marked==crate::specs::compact_mark_word(value,bp,negative);
    }
    marked
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires direction<8,
    ensures result==crate::specs::compact_add_neighbor(value,direction,negative),
        result==value | (1u64<<(41+direction)) | if negative{1u64<<(49+direction)}else{0u64},
        crate::specs::compact_coefficient(result)==crate::specs::compact_coefficient(value),
        result & 0x1ff_ffff_ffffu64==value & 0x1ff_ffff_ffffu64,
        crate::specs::compact_precision_word(result)==crate::specs::compact_precision_word(value),
))]
#[inline(always)]
fn cache_word(value: u64, direction: u32, negative: bool) -> u64 {
    let updated = value
        | (1u64 << (SIG_NEIGHBORS + direction))
        | if negative {
            1u64 << (NEG_NEIGHBORS + direction)
        } else {
            0
        };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(updated & 0x1ff_ffff_ffffu64==value & 0x1ff_ffff_ffffu64) by(bit_vector)
            requires direction<8,updated==value | (1u64<<(41+direction)) | if negative{1u64<<(49+direction)}else{0u64};
        crate::specs::compact_precision_lower_frame(updated,value);
        assert(updated & 0xffff_ffffu64==value & 0xffff_ffffu64
            && ((updated>>32)&63)==((value>>32)&63)
            && updated & (1u64<<38)==value & (1u64<<38)
            && updated & (1u64<<39)==value & (1u64<<39)
            && updated & (1u64<<40)==value & (1u64<<40)) by(bit_vector)
            requires updated & 0x1ff_ffff_ffffu64==value & 0x1ff_ffff_ffffu64;
    }
    updated
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires bp<31,value & MAG<1u64<<31,
        value & (((1u64<<((bp+1) as u16))-1) as u64)==0,
    ensures result==crate::specs::compact_refine_word(value,bp,bit),
        crate::specs::compact_coefficient(result).limbs[0]==(value & MAG)+if bit{1u64<<bp}else{0u64},
        crate::specs::compact_coefficient(result).legacy_bitplane==Some(bp),
        crate::specs::compact_coefficient(result).refined,
        crate::specs::compact_coefficient(result).significant==crate::specs::compact_coefficient(value).significant,
        crate::specs::compact_coefficient(result).negative==crate::specs::compact_coefficient(value).negative,
        result>>41==value>>41,result & MAG<1u64<<31,
        crate::specs::compact_refinement_frontier(value,bp) ==> crate::specs::compact_precision_word(result),
))]
#[inline(always)]
fn refine_word(value: u64, bp: u16, bit: bool) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(value<=u64::MAX-(1u64<<bp)) by(bit_vector)
            requires bp<31,value & 0xffff_ffffu64<1u64<<31,value & (((1u64<<((bp+1) as u16))-1) as u64)==0;
    }
    let next = if bit { value + (1u64 << bp) } else { value };
    let refined = (next & !BP_MASK) | ((u64::from(bp)) << BP_SHIFT) | REFINED;
    #[cfg(verus_keep_ghost)]
    proof! {
        if crate::specs::compact_refinement_frontier(value,bp){crate::specs::compact_precision_refine(value,bp,bit);}
        assert(refined & 0xffff_ffffu64==(value & 0xffff_ffffu64)+if bit{1u64<<bp}else{0u64}
            && refined & 0xffff_ffffu64<1u64<<31
            && ((refined>>32)&63)==bp as u64
            && refined & (1u64<<40)!=0
            && refined & (1u64<<38)==value & (1u64<<38)
            && refined & (1u64<<39)==value & (1u64<<39)
            && refined>>41==value>>41) by(bit_vector)
            requires bp<31,value & 0xffff_ffffu64<1u64<<31,value & (((1u64<<((bp+1) as u16))-1) as u64)==0,
                next==if bit{(value+(1u64<<bp)) as u64}else{value},
                refined==(next & !(63u64<<32)) | ((bp as u64)<<32) | (1u64<<40);
    }
    refined
}

#[cfg_attr(not(test), allow(dead_code))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::compact_flag_summary(sig,neg),
        result.horizontal_significant<=2,result.vertical_significant<=2,result.diagonal_significant<=4,
        -2<=result.horizontal_sign_balance<=2,-2<=result.vertical_sign_balance<=2,
))]
fn word_flag_summary(sig: u8, neg: u8) -> NeighborSummary {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost original_neg=neg;}
    let neg = neg & sig;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((sig&1)<=1 && ((sig>>1)&1)<=1 && ((sig>>2)&1)<=1 && ((sig>>3)&1)<=1
            && ((sig>>4)&1)<=1 && ((sig>>5)&1)<=1 && ((sig>>6)&1)<=1 && ((sig>>7)&1)<=1
            && ((neg>>1)&1)<=1 && ((neg>>3)&1)<=1 && ((neg>>4)&1)<=1 && ((neg>>6)&1)<=1) by(bit_vector);
        assert(((neg>>1)&1)<=((sig>>1)&1) && ((neg>>3)&1)<=((sig>>3)&1)
            && ((neg>>4)&1)<=((sig>>4)&1) && ((neg>>6)&1)<=((sig>>6)&1)) by(bit_vector)
            requires neg==original_neg & sig;
    }
    let h = ((sig >> 3) & 1) + ((sig >> 4) & 1);
    let v = ((sig >> 1) & 1) + ((sig >> 6) & 1);
    NeighborSummary {
        horizontal_significant: h,
        vertical_significant: v,
        diagonal_significant: (sig & 1) + ((sig >> 2) & 1) + ((sig >> 5) & 1) + ((sig >> 7) & 1),
        horizontal_sign_balance: h as i8 - 2 * (((neg >> 3) & 1) + ((neg >> 4) & 1)) as i8,
        vertical_sign_balance: v as i8 - 2 * (((neg >> 1) & 1) + ((neg >> 6) & 1)) as i8,
    }
}

impl CompactPlane {
    #[cfg_attr(not(test), allow(dead_code))]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.shape(),x<self.width,y<self.height,
            crate::specs::compact_cache(self.width,self.height,self.entries@),
        ensures result==crate::specs::compact_flag_summary(
            ((self.entries@[y*self.width+x]>>41) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8},
            ((self.entries@[y*self.width+x]>>49) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8}),
            crate::specs::ht_neighbors(self.view(),x as u16,y as u16,causal)==Ok(result),
    ))]
    fn summary(&self, x: usize, y: usize, causal: bool) -> NeighborSummary {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
        }
        let value = self.entries[y * self.width + x];
        let sig = (value >> SIG_NEIGHBORS) as u8;
        let neg = (value >> NEG_NEIGHBORS) as u8;
        let mask = if causal && y % 4 == 3 { 0x1f } else { 0xff };
        word_flag_summary(sig & mask, neg & mask)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).shape(),x<old(self).width,y<old(self).height,bp<31,
            crate::specs::compact_cache(old(self).width,old(self).height,old(self).entries@),
            forall|i:int|0<=i<old(self).entries.len() ==> crate::specs::compact_precision_word(old(self).entries@[i]),
            old(self).entries@[(y*old(self).width+x) as int] & SIG==0,
        ensures final(self).shape(),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_cache(final(self).width,final(self).height,final(self).entries@),
            forall|i:int|0<=i<final(self).entries.len() ==> crate::specs::compact_precision_word(final(self).entries@[i]),
            forall|i:int|0<=i<final(self).entries.len() && i!=(y*old(self).width+x) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            match result{Err(_)=>final(self).entries@==old(self).entries@,Ok(())=>
                crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).significant
                    && crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).legacy_bitplane==Some(bp)},
            (result,final(self).view(),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                ==crate::specs::part1_legacy_sign_mark(old(self).view(),
                    crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),x as u16,y as u16,bp,
                    crate::specs::compact_flag_summary(
                        ((old(self).entries@[(y*old(self).width+x) as int]>>41) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8},
                        ((old(self).entries@[(y*old(self).width+x) as int]>>49) as u8) & if causal && y%4==3{0x1fu8}else{0xffu8})),
    ))]
    #[inline]
    fn sign_and_mark(
        &mut self,
        x: usize,
        y: usize,
        bp: u16,
        causal: bool,
        decoder: &mut MqDecoder<'_>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_sign_mark);
            reveal(crate::specs::part1_legacy_symbol);
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
        }
        let word = self.entries[y * self.width + x];
        let sig = significance_mask(word, y, causal);
        let neg = negative_mask(word, y, causal);
        let sign = cached_sign_context(sig, neg);
        let bit = decoder.decode(usize::from(sign.context))?;
        let negative = crate::refinement::tier1_decoded_sign(bit, sign.predicted_negative, false);
        self.mark(x, y, bp, negative);
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).shape(), x < old(self).width, y < old(self).height, d < 8,
            target < old(self).entries.len(),
            crate::specs::compact_neighbor_index(old(self).width, old(self).height, x as int, y as int, d) == Some(target as int),
            crate::specs::compact_pending_cache(old(self).width, old(self).height, old(self).entries@, x as int, y as int, d),
            crate::specs::compact_coefficient(old(self).entries@[(y * old(self).width + x) as int]).significant,
            crate::specs::compact_coefficient(old(self).entries@[(y * old(self).width + x) as int]).negative == negative,
            forall|i:int| 0 <= i < old(self).entries.len() ==> crate::specs::compact_precision_word(old(self).entries@[i]),
        ensures final(self).shape(), final(self).width == old(self).width, final(self).height == old(self).height,
            final(self).view() == old(self).view(),
            crate::specs::compact_pending_cache(final(self).width, final(self).height, final(self).entries@, x as int, y as int, (d + 1) as u32),
            crate::specs::compact_coefficient(final(self).entries@[(y * old(self).width + x) as int]).significant,
            crate::specs::compact_coefficient(final(self).entries@[(y * old(self).width + x) as int]).negative == negative,
            forall|i:int| 0 <= i < final(self).entries.len() ==> crate::specs::compact_precision_word(final(self).entries@[i]),
            forall|i:int| 0 <= i < final(self).entries.len() ==>
                final(self).entries@[i] & 0x1ff_ffff_ffffu64 == old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    #[inline(always)]
    fn update_neighbor(
        &mut self,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] x: usize,
        #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] y: usize,
        target: usize,
        d: u32,
        negative: bool,
    ) {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width, self.height, self.entries@, x, y);
            crate::specs::compact_cache_mark_step(self.width, self.height, self.entries@, x, y, d, negative);
        }
        self.entries[target] = cache_word(self.entries[target], 7 - d, negative);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.view().coefficients =~= old(self).view().coefficients);
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).shape(),
            0 < x, x + 1 < old(self).width,
            0 < y, y + 1 < old(self).height,
            index == y * old(self).width + x,
            crate::specs::compact_pending_cache(old(self).width, old(self).height, old(self).entries@, x as int, y as int, 0),
            crate::specs::compact_coefficient(old(self).entries@[index as int]).significant,
            crate::specs::compact_coefficient(old(self).entries@[index as int]).negative == negative,
            forall|i:int| 0 <= i < old(self).entries.len() ==> crate::specs::compact_precision_word(old(self).entries@[i]),
        ensures final(self).shape(), final(self).width == old(self).width, final(self).height == old(self).height,
            final(self).view() == old(self).view(),
            crate::specs::compact_pending_cache(final(self).width, final(self).height, final(self).entries@, x as int, y as int, 8),
            crate::specs::compact_coefficient(final(self).entries@[index as int]).significant,
            crate::specs::compact_coefficient(final(self).entries@[index as int]).negative == negative,
            forall|i:int| 0 <= i < final(self).entries.len() ==> crate::specs::compact_precision_word(final(self).entries@[i]),
            forall|i:int| 0 <= i < final(self).entries.len() ==>
                final(self).entries@[i] & 0x1ff_ffff_ffffu64 == old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[inline(always)]
    fn mark_interior(&mut self, x: usize, y: usize, index: usize, negative: bool) {
        let width = self.width;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(width, self.height, self.entries@, (x - 1) as usize, (y - 1) as usize);
            crate::specs::compact_index(width, self.height, self.entries@, x, (y - 1) as usize);
            crate::specs::compact_index(width, self.height, self.entries@, (x + 1) as usize, (y - 1) as usize);
            crate::specs::compact_index(width, self.height, self.entries@, (x - 1) as usize, y);
            crate::specs::compact_index(width, self.height, self.entries@, (x + 1) as usize, y);
            crate::specs::compact_index(width, self.height, self.entries@, (x - 1) as usize, (y + 1) as usize);
            crate::specs::compact_index(width, self.height, self.entries@, x, (y + 1) as usize);
            crate::specs::compact_index(width, self.height, self.entries@, (x + 1) as usize, (y + 1) as usize);
            assert(index >= width) by (nonlinear_arith)
                requires index == y * width + x, y > 0, width > 0;
            assert(index - width == (y - 1) * width + x) by (nonlinear_arith)
                requires index == y * width + x, y > 0, width > 0;
            assert(index - width - 1 == (y - 1) * width + (x - 1)) by (nonlinear_arith)
                requires index == y * width + x, x > 0, y > 0, width > 0;
            assert(index - width + 1 == (y - 1) * width + (x + 1)) by (nonlinear_arith)
                requires index == y * width + x, y > 0, width > 0;
            assert(index + width - 1 == (y + 1) * width + (x - 1)) by (nonlinear_arith)
                requires index == y * width + x, x > 0, width > 0;
            assert(index + width == (y + 1) * width + x) by (nonlinear_arith)
                requires index == y * width + x, width > 0;
            assert(index + width + 1 == (y + 1) * width + (x + 1)) by (nonlinear_arith)
                requires index == y * width + x, width > 0;
        }
        let prev = index - width;
        let next = index + width;
        self.update_neighbor(x, y, prev - 1, 0, negative);
        self.update_neighbor(x, y, prev, 1, negative);
        self.update_neighbor(x, y, prev + 1, 2, negative);
        self.update_neighbor(x, y, index - 1, 3, negative);
        self.update_neighbor(x, y, index + 1, 4, negative);
        self.update_neighbor(x, y, next - 1, 5, negative);
        self.update_neighbor(x, y, next, 6, negative);
        self.update_neighbor(x, y, next + 1, 7, negative);
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).shape(),x<old(self).width,y<old(self).height,bp<31,
            crate::specs::compact_cache(old(self).width,old(self).height,old(self).entries@),
            forall|i:int|0<=i<old(self).entries.len() ==> crate::specs::compact_precision_word(old(self).entries@[i]),
            old(self).entries@[(y*old(self).width+x) as int] & SIG==0,
        ensures final(self).shape(),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_cache(final(self).width,final(self).height,final(self).entries@),
            forall|i:int|0<=i<final(self).entries.len() ==> crate::specs::compact_precision_word(final(self).entries@[i]),
            forall|i:int|0<=i<final(self).entries.len() ==>
                final(self).entries@[i] & 0x1ff_ffff_ffffu64==
                    (if i==(y*old(self).width+x) as int{crate::specs::compact_mark_word(old(self).entries@[i],bp,negative)}else{old(self).entries@[i]}) & 0x1ff_ffff_ffffu64,
            crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).significant,
            crate::specs::compact_coefficient(final(self).entries@[(y*old(self).width+x) as int]).legacy_bitplane==Some(bp),
            (Ok::<(),DecodeError>(()),final(self).view())==crate::specs::part1_legacy_mark(old(self).view(),x as u16,y as u16,bp,negative),
            final(self).view().coefficients==old(self).view().coefficients.update((y*old(self).width+x) as int,
                crate::specs::compact_coefficient(crate::specs::compact_mark_word(old(self).entries@[(y*old(self).width+x) as int],bp,negative))),
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[inline]
    fn mark(&mut self, x: usize, y: usize, bp: u16, negative: bool) {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_mark_coefficient(self.entries@[(y*self.width+x) as int],bp,negative);
            vstd::arithmetic::power2::lemma_pow2_pos(bp as nat);
            crate::specs::compact_cache_mark_start(self.width,self.height,self.entries@,x,y,bp,negative);
        }
        let width = self.width;
        let index = y * width + x;
        self.entries[index] = mark_word(self.entries[index], bp, negative);
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost marked=self.view();}
        if x > 0 && x + 1 < width && y > 0 && y + 1 < self.height {
            self.mark_interior(x, y, index, negative);
        } else {
            let mut direction = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant direction<=8,self.shape(),self.width==old(self).width,self.height==old(self).height,
                    self.view()==marked,marked.coefficients==old(self).view().coefficients.update(index as int,
                        crate::specs::compact_coefficient(crate::specs::compact_mark_word(old(self).entries@[index as int],bp,negative))),
                    index==y*self.width+x,x<self.width,y<self.height,
                    old(self).shape(),old(self).entries@[index as int] & SIG==0,bp<31,
                    crate::specs::compact_pending_cache(self.width,self.height,self.entries@,x as int,y as int,direction as u32),
                    crate::specs::compact_coefficient(self.entries@[index as int]).significant,
                    crate::specs::compact_coefficient(self.entries@[index as int]).negative==negative,
                    forall|i:int|0<=i<self.entries.len() ==> crate::specs::compact_precision_word(self.entries@[i]),
                    forall|i:int|0<=i<self.entries.len() ==> self.entries@[i] & 0x1ff_ffff_ffffu64==
                        (if i==index{crate::specs::compact_mark_word(old(self).entries@[i],bp,negative)}else{old(self).entries@[i]}) & 0x1ff_ffff_ffffu64,
                decreases 8-direction,
            ))]
            while direction < 8 {
                #[cfg(verus_keep_ghost)]
                proof_decl! {let ghost before_words=self.entries@;}
                let (dx, dy) = DIRECTIONS[direction];
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(direction==0 || direction==1 || direction==2 || direction==3
                        || direction==4 || direction==5 || direction==6 || direction==7);
                    assert(dx as int==crate::specs::compact_dx(direction as u32));
                    assert(dy as int==crate::specs::compact_dy(direction as u32));
                    crate::specs::compact_cache_mark_step(self.width,self.height,before_words,x,y,direction as u32,negative);
                }
                let nx = x as i32 + dx;
                let ny = y as i32 + dy;
                if nx >= 0 && ny >= 0 && nx < self.width as i32 && ny < self.height as i32 {
                    let bit = 7 - direction;
                    #[cfg(verus_keep_ghost)]
                    proof! {crate::specs::compact_index(self.width,self.height,self.entries@,nx as usize,ny as usize);}
                    let target = ny as usize * self.width + nx as usize;
                    self.entries[target] = cache_word(self.entries[target], bit as u32, negative);
                    #[cfg(verus_keep_ghost)]
                    proof! {assert(self.view().coefficients =~= marked.coefficients);}
                }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(self.entries@==match crate::specs::compact_neighbor_index(self.width,self.height,x as int,y as int,direction as u32){
                        None=>before_words,
                        Some(target)=>before_words.update(target,crate::specs::compact_add_neighbor(before_words[target],(7-direction) as u32,negative)),
                    });
                }
                direction += 1;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_mark_coefficient(old(self).entries@[index as int],bp,negative);
            crate::specs::compact_cache_mark_end(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_lower_fields(self.entries@[index as int],
                crate::specs::compact_mark_word(old(self).entries@[index as int],bp,negative));
            vstd::arithmetic::power2::lemma_pow2_pos(bp as nat);
            crate::specs::compact_index(old(self).width,old(self).height,old(self).entries@,x,y);
            assert(crate::specs::tier1_raw_plane_index(old(self).view(),x as u16,y as u16)==Ok(index));
            let expected=crate::specs::part1_legacy_mark(old(self).view(),x as u16,y as u16,bp,negative);
            assert(expected.0==Ok(()));
            assert(expected.1.coefficients =~= self.view().coefficients);
            assert((Ok::<(),DecodeError>(()),self.view())==crate::specs::part1_legacy_mark(old(self).view(),x as u16,y as u16,bp,negative));
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.shape(),bp<31,
        ensures crate::specs::part2_bitplane_initial_result(self.view(),bp,super::legacy_bitplane_outcome(result)),
            super::legacy_bitplane_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                super::legacy_bitplane_outcome(result)==crate::specs::part1_legacy_bitplane_initial(self.view(),bp),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>
                Ok::<crate::specs::Part1LegacyBitplane,DecodeError>(super::legacy_bitplane_view(&value))
                    ==crate::specs::part1_legacy_bitplane_initial(self.view(),bp)},
    ))]
    fn initial_state(&self, bp: u16) -> Result<Tier1BitplaneState, DecodeError> {
        let allocated = crate::allocation::empty_with_capacity(self.entries.len());
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.entries.len()>0) by(nonlinear_arith)
                requires self.width>0,self.height>0,self.entries.len()==self.width*self.height;
            crate::specs::part2_bitplane_capacity_observed(self.view(),bp,false,None,match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())});
            if let Err(error)=allocated{crate::specs::part2_bitplane_initial_first_error(self.view(),bp,error);}
        }
        let mut significant_before = allocated?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=self.entries.len(),significant_before.len()==index,
                self.shape(),bp<31,
                crate::specs::part2_bitplane_capacity_result(self.view(),bp,false,None,Ok(())),
                forall|i:int|0<=i<index ==> significant_before@[i]==crate::specs::compact_coefficient(self.entries@[i]).significant,
            decreases self.entries.len()-index,
        ))]
        while index < self.entries.len() {
            significant_before.push(self.entries[index] & SIG != 0);
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {assert(significant_before@ =~= crate::specs::part2_bitplane_significant(self.view()));}
        let visited = crate::allocation::filled_values(false, self.entries.len());
        #[cfg(verus_keep_ghost)]
        proof! {
            let result=match visited{Err(error)=>Err(error),Ok(_)=>Ok(())};
            crate::specs::part2_bitplane_capacity_observed(self.view(),bp,true,Some(significant_before@),result);
            crate::specs::part2_bitplane_initial_observed(self.view(),bp,result);
        }
        let significance_visited = visited?;
        #[cfg(verus_keep_ghost)]
        proof! {reveal(super::legacy_bitplane_view);}
        Ok(Tier1BitplaneState {
            width: self.width as u16,
            height: self.height as u16,
            bitplane: bp,
            significant_before,
            significance_visited,
            significance_propagation_complete: false,
            magnitude_refinement_complete: false,
            cleanup_complete: false,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),coordinate.0<old(self).width,coordinate.1<old(self).height,
            crate::specs::compact_statistics_room(*old(stats)),
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state))),
            (result,final(self).frame(final(state),final(decoder),*final(stats)))==crate::specs::part1_legacy_sig_cell(
                old(self).frame(old(state),old(decoder),*old(stats)),coordinate.0 as u16,coordinate.1 as u16,orientation,causal),
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),2),
            forall|i:int|0<=i<final(self).entries.len() && i!=(coordinate.1*old(self).width+coordinate.0) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            forall|i:int|0<=i<final(self).entries.len() && old(state).significant_before@[i]
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[inline(always)]
    fn sig_cell(
        &mut self,
        coordinate: (usize, usize),
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        orientation: SubbandOrientation,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;let ghost before_state=super::legacy_bitplane_view(state);}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_sig_cell);reveal(crate::specs::part1_legacy_symbol);
            reveal(crate::specs::compact_membership);
            reveal(super::legacy_bitplane_view);
            crate::specs::compact_index(self.width,self.height,self.entries@,coordinate.0,coordinate.1);
        }
        let (x, y) = coordinate;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
            let mask=if causal && y%4==3{0x1fu8}else{0xffu8};
            crate::specs::compact_mask_context(
                ((self.entries@[(y*self.width+x) as int]>>41) as u8)&mask,
                ((self.entries@[(y*self.width+x) as int]>>49) as u8)&mask,orientation);
        }
        stats.coefficients_scanned += 1;
        let index = y * self.width + x;
        if self.entries[index] & SIG == 0 {
            let sig = significance_mask(self.entries[index], y, causal);
            if sig != 0 {
                let bit = decoder.decode(usize::from(cached_zero_context(sig, orientation)))?;
                state.significance_visited[index] = true;
                stats.coding_symbols += 1;
                if bit {
                    let marked = self.sign_and_mark(x, y, state.bitplane, causal, decoder);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                            before_state,super::legacy_bitplane_view(state),index as int);
                    }
                    marked?;
                    stats.coding_symbols += 1;
                    stats.newly_significant += 1;
                }
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(state),x<old(self).width,y<old(self).height,
            crate::specs::compact_statistics_room(*old(stats)),
            state.significant_before@[(y*old(self).width+x) as int] ==>
                crate::specs::compact_refinement_frontier(old(self).entries@[(y*old(self).width+x) as int],state.bitplane),
        ensures final(self).ready(state),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).frame(state,final(decoder),*final(stats)))==crate::specs::part1_legacy_mag_cell(
                old(self).frame(state,old(decoder),*old(stats)),x as u16,y as u16,causal),
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),2),
            forall|i:int|0<=i<final(self).entries.len() && i!=(y*old(self).width+x) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            result.is_ok() && state.significant_before@[(y*old(self).width+x) as int] ==>
                ((final(self).entries@[(y*old(self).width+x) as int]>>32)&63)==state.bitplane,
    ))]
    #[inline(always)]
    fn refine_cell(
        &mut self,
        x: usize,
        y: usize,
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_mag_cell);reveal(crate::specs::part1_legacy_symbol);
            reveal(crate::specs::compact_membership);
            reveal(super::legacy_bitplane_view);
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
        }
        stats.coefficients_scanned += 1;
        let index = y * self.width + x;
        if state.significant_before[index] {
            let before = self.entries[index];
            let context = if before & REFINED != 0 {
                crate::refinement::tier1_refinement_context(true, 0)
            } else {
                #[cfg(verus_keep_ghost)]
                proof! {
                    let mask=if causal && y%4==3{0x1fu8}else{0xffu8};
                    crate::specs::compact_mask_context(
                        ((before>>41) as u8)&mask,
                        ((before>>49) as u8)&mask,SubbandOrientation::Ll);
                }
                let sig = significance_mask(before, y, causal);
                crate::refinement::tier1_refinement_context(false, if sig != 0 { 1 } else { 0 })
            };
            let bit = decoder.decode(usize::from(context))?;
            stats.coding_symbols += 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::compact_frontier_low_bits(before,state.bitplane);
                crate::specs::compact_refinement_plane(self.width,self.height,self.entries@,x,y,state.bitplane,bit);
            }
            let refined = refine_word(before, state.bitplane, bit);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::compact_cache_value_frame(self.width,self.height,self.entries@,index as int,refined);}
            self.entries[index] = refined;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                    super::legacy_bitplane_view(state),super::legacy_bitplane_view(state),index as int);
            }
            stats.refined_coefficients += 1;
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(state),coordinate.0<old(self).width,coordinate.1<old(self).height,
            crate::specs::compact_statistics_room(*old(stats)),
        ensures final(self).ready(state),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).frame(state,final(decoder),*final(stats)))==crate::specs::part1_legacy_cleanup_cell(
                old(self).frame(state,old(decoder),*old(stats)),coordinate.0 as u16,coordinate.1 as u16,orientation,causal),
            final(stats).coefficients_scanned==old(stats).coefficients_scanned,
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),2),
            forall|i:int|0<=i<final(self).entries.len() && i!=(coordinate.1*old(self).width+coordinate.0) as int
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
            forall|i:int|0<=i<final(self).entries.len() && state.significant_before@[i]
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[inline(always)]
    fn cleanup_cell(
        &mut self,
        coordinate: (usize, usize),
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        orientation: SubbandOrientation,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_cleanup_cell);reveal(crate::specs::part1_legacy_symbol);
            reveal(crate::specs::compact_membership);
            reveal(super::legacy_bitplane_view);
            crate::specs::compact_index(self.width,self.height,self.entries@,coordinate.0,coordinate.1);
        }
        let (x, y) = coordinate;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
            let mask=if causal && y%4==3{0x1fu8}else{0xffu8};
            crate::specs::compact_mask_context(
                ((self.entries@[(y*self.width+x) as int]>>41) as u8)&mask,
                ((self.entries@[(y*self.width+x) as int]>>49) as u8)&mask,orientation);
        }
        let index = y * self.width + x;
        if self.entries[index] & SIG == 0 && !state.significance_visited[index] {
            let sig = significance_mask(self.entries[index], y, causal);
            let bit = decoder.decode(usize::from(cached_zero_context(sig, orientation)))?;
            stats.coding_symbols += 1;
            if bit {
                let marked = self.sign_and_mark(x, y, state.bitplane, causal, decoder);
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                        super::legacy_bitplane_view(state),super::legacy_bitplane_view(state),index as int);
                }
                marked?;
                stats.coding_symbols += 1;
                stats.newly_significant += 1;
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(state),coordinate.0<old(self).width,coordinate.1<old(self).height,
            old(self).entries@[(coordinate.1*old(self).width+coordinate.0) as int] & SIG==0,
            crate::specs::compact_statistics_room(*old(stats)),
        ensures final(self).ready(state),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).frame(state,final(decoder),*final(stats)))==crate::specs::part1_legacy_sign_mark_stat(
                old(self).frame(state,old(decoder),*old(stats)),coordinate.0 as u16,coordinate.1 as u16,
                crate::specs::compact_flag_summary(
                    ((old(self).entries@[(coordinate.1*old(self).width+coordinate.0) as int]>>41) as u8)
                        & if causal && coordinate.1%4==3{0x1fu8}else{0xffu8},
                    ((old(self).entries@[(coordinate.1*old(self).width+coordinate.0) as int]>>49) as u8)
                        & if causal && coordinate.1%4==3{0x1fu8}else{0xffu8})),
            crate::specs::compact_statistics_delta(*old(stats),*final(stats),1),
            forall|i:int|0<=i<final(self).entries.len() && state.significant_before@[i]
                ==> final(self).entries@[i] & 0x1ff_ffff_ffffu64==old(self).entries@[i] & 0x1ff_ffff_ffffu64,
    ))]
    #[inline(always)]
    fn run_sign(
        &mut self,
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        coordinate: (usize, usize),
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before_words=self.entries@;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::legacy_bitplane_view);
            reveal(crate::specs::compact_membership);
            crate::specs::compact_index(self.width,self.height,self.entries@,coordinate.0,coordinate.1);
        }
        let (x, y) = coordinate;
        let marked = self.sign_and_mark(x, y, state.bitplane, causal, decoder);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_membership_cell(self.width,self.height,before_words,self.entries@,
                super::legacy_bitplane_view(state),super::legacy_bitplane_view(state),(y*self.width+x) as int);
        }
        marked?;
        stats.coding_symbols += 1;
        stats.newly_significant += 1;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.shape(),x<self.width,y<self.height,
            crate::specs::compact_cache(self.width,self.height,self.entries@),
            state.significance_visited.len()==self.entries.len(),
        ensures Ok::<bool,DecodeError>(result)==crate::specs::part1_legacy_cleanup_candidate(
            self.view(),super::legacy_bitplane_view(state),x as u16,y as u16,causal),
            result ==> self.entries@[(y*self.width+x) as int] & SIG==0,
    ))]
    #[inline(always)]
    fn run_candidate(&self, x: usize, y: usize, state: &Tier1BitplaneState, causal: bool) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_index(self.width,self.height,self.entries@,x,y);
            reveal(crate::specs::part1_legacy_cleanup_candidate);reveal(super::legacy_bitplane_view);
            crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,y,causal);
            let mask=if causal && y%4==3{0x1fu8}else{0xffu8};
            crate::specs::compact_mask_context(
                ((self.entries@[(y*self.width+x) as int]>>41) as u8)&mask,
                ((self.entries@[(y*self.width+x) as int]>>49) as u8)&mask,SubbandOrientation::Ll);
        }
        self.entries[y * self.width + x] & SIG == 0
            && !state.significance_visited[y * self.width + x]
            && significance_mask(self.entries[y * self.width + x], y, causal) == 0
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),coordinate.0<old(self).width,
            coordinate.2<=coordinate.3,0<coordinate.3<=4,coordinate.1+coordinate.3<=old(self).height,
            !coordinate.4 ==> context.0 is Cleanup,
            crate::specs::compact_statistics_le(*old(stats),
                (crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.3,coordinate.0)+4+2*coordinate.2) as nat),
            if context.0 is MagnitudeRefinement{
                crate::specs::compact_refinement_pending(old(self).width,old(self).height,old(self).entries@,
                    super::legacy_bitplane_view(old(state)),coordinate.1,coordinate.3,coordinate.0,coordinate.2)
            }else{crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),context.0 is Cleanup)},
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state))),
            (result,final(self).frame(final(state),final(decoder),*final(stats)))==crate::specs::compact_rows_model(
                old(self).frame(old(state),old(decoder),*old(stats)),context.0,context.1,context.2,
                coordinate.0,coordinate.1,coordinate.2,coordinate.3,coordinate.4),
            crate::specs::compact_statistics_le(*final(stats),
                (crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.3,coordinate.0)+4+2*coordinate.3) as nat),
            if context.0 is MagnitudeRefinement{
                result.is_ok() ==> crate::specs::compact_refinement_pending(final(self).width,final(self).height,final(self).entries@,
                    super::legacy_bitplane_view(final(state)),coordinate.1,coordinate.3,coordinate.0,coordinate.3)
            }else{crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),context.0 is Cleanup)},
    ))]
    #[inline(always)]
    fn rows(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        context: (Tier1PassKind, SubbandOrientation, bool),
        coordinate: (usize, usize, usize, usize, bool),
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        let (x, stripe, mut row, rows, scan) = coordinate;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=self.frame(state,decoder,*stats);
            let ghost goal=crate::specs::compact_rows_model(initial,context.0,context.1,context.2,x,stripe,row,rows,scan);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::compact_membership);
            crate::specs::compact_column_geometry(self.width,self.height,self.entries@,x,stripe,rows);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant coordinate.2<=row<=rows,rows>0,rows<=4,stripe+rows<=self.height,x<self.width,
                x==coordinate.0,stripe==coordinate.1,rows==coordinate.3,scan==coordinate.4,
                !scan ==> context.0 is Cleanup,
                self.ready(state),self.width==old(self).width,self.height==old(self).height,
                crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(state)),
                initial==old(self).frame(old(state),old(decoder),*old(stats)),
                goal==crate::specs::compact_rows_model(initial,context.0,context.1,context.2,
                    coordinate.0,coordinate.1,coordinate.2,coordinate.3,coordinate.4),
                goal==crate::specs::compact_rows_model(self.frame(state,decoder,*stats),context.0,context.1,context.2,x,stripe,row,rows,scan),
                crate::specs::compact_statistics_le(*stats,(crate::specs::compact_scan_bound(self.width,stripe,rows,x)+4+2*row) as nat),
                if context.0 is MagnitudeRefinement{
                    crate::specs::compact_refinement_pending(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,x,row)
                }else{crate::specs::compact_before_frontier(self.entries@,super::legacy_bitplane_view(state),context.0 is Cleanup)},
            decreases rows-row,
        ))]
        while row < rows {
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_words=self.entries@;let ghost before_state=super::legacy_bitplane_view(state);let ghost prior_statistics=*stats;}
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_legacy_rows);reveal(crate::specs::part1_legacy_cleanup_rows);
                reveal(crate::specs::compact_membership);
                reveal(super::legacy_bitplane_view);
                crate::specs::compact_column_geometry(self.width,self.height,self.entries@,x,stripe,rows);
                crate::specs::compact_index(self.width,self.height,self.entries@,x,(stripe+row) as usize);
                if context.0 is MagnitudeRefinement{
                    assert(!crate::specs::compact_processed(stripe,rows,x,row,x as int,(stripe+row) as int));
                    if state.significant_before@[((stripe+row)*self.width+x) as int]{
                        assert(((self.entries@[((stripe+row)*self.width+x) as int]>>32)&63)>state.bitplane);
                        assert(crate::specs::compact_refinement_frontier(self.entries@[((stripe+row)*self.width+x) as int],state.bitplane));
                    }
                }
            }
            let decoded = match context.0 {
                Tier1PassKind::SignificancePropagation => self.sig_cell(
                    (x, stripe + row),
                    state,
                    decoder,
                    context.1,
                    context.2,
                    stats,
                ),
                Tier1PassKind::MagnitudeRefinement => {
                    self.refine_cell(x, stripe + row, state, decoder, context.2, stats)
                }
                Tier1PassKind::Cleanup => {
                    if scan {
                        stats.coefficients_scanned += 1;
                    }
                    self.cleanup_cell(
                        (x, stripe + row),
                        state,
                        decoder,
                        context.1,
                        context.2,
                        stats,
                    )
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::compact_statistics_delta(prior_statistics,*stats,2));
                assert(crate::specs::compact_statistics_le(*stats,(crate::specs::compact_scan_bound(self.width,stripe,rows,x)+4+2*(row+1)) as nat));
                assert(crate::specs::compact_statistics_le(*stats,(crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.3,coordinate.0)+4+2*coordinate.3) as nat));
                if context.0 is MagnitudeRefinement{
                    if decoded.is_ok(){
                        crate::specs::compact_frontier_row_step(self.width,self.height,before_words,self.entries@,
                            super::legacy_bitplane_view(state),stripe,rows,x,row);
                    }
                }else{
                    crate::specs::compact_before_frontier_preserved(before_words,self.entries@,before_state,
                        super::legacy_bitplane_view(state),context.0 is Cleanup);
                }
            }
            decoded?;
            row += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_legacy_rows);reveal(crate::specs::part1_legacy_cleanup_rows);}
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),coordinate.0<old(self).width,
            0<coordinate.2<=4,coordinate.1+coordinate.2<=old(self).height,
            crate::specs::compact_statistics_le(*old(stats),crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.2,coordinate.0)),
            if context.0 is MagnitudeRefinement{
                crate::specs::compact_refinement_pending(old(self).width,old(self).height,old(self).entries@,
                    super::legacy_bitplane_view(old(state)),coordinate.1,coordinate.2,coordinate.0,0)
            }else{crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),context.0 is Cleanup)},
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state))),
            (result,final(self).frame(final(state),final(decoder),*final(stats)))==crate::specs::compact_column_model(
                old(self).frame(old(state),old(decoder),*old(stats)),context.0,context.1,context.2,coordinate.0,coordinate.1,coordinate.2),
            crate::specs::compact_statistics_le(*final(stats),crate::specs::compact_scan_bound(old(self).width,coordinate.1,coordinate.2,(coordinate.0+1) as usize)),
            if context.0 is MagnitudeRefinement{
                result.is_ok() ==> crate::specs::compact_refinement_pending(final(self).width,final(self).height,final(self).entries@,
                    super::legacy_bitplane_view(final(state)),coordinate.1,coordinate.2,coordinate.0,coordinate.2)
            }else{crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),context.0 is Cleanup)},
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[inline(always)]
    fn column(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        context: (Tier1PassKind, SubbandOrientation, bool),
        coordinate: (usize, usize, usize),
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        let (x, stripe, rows) = coordinate;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::compact_membership);
            crate::specs::compact_column_geometry(self.width,self.height,self.entries@,x,stripe,rows);
            crate::specs::compact_counter_algebra(self.width,stripe,rows,x);
        }
        if !matches!(context.0, Tier1PassKind::Cleanup) {
            return self.rows(state, decoder, context, (x, stripe, 0, rows, true), stats);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_cleanup_column);
            reveal(crate::specs::part1_legacy_cleanup_run);
            reveal(crate::specs::part1_legacy_symbol);
        }
        let run = rows == 4
            && self.run_candidate(x, stripe, state, context.2)
            && self.run_candidate(x, stripe + 1, state, context.2)
            && self.run_candidate(x, stripe + 2, state, context.2)
            && self.run_candidate(x, stripe + 3, state, context.2);
        if !run {
            return self.rows(state, decoder, context, (x, stripe, 0, rows, true), stats);
        }
        stats.coefficients_scanned += 4;
        stats.run_mode_columns += 1;
        let interrupted = decoder.decode(RUN_LENGTH_CONTEXT)?;
        stats.coding_symbols += 1;
        if interrupted {
            #[cfg(verus_keep_ghost)]
            proof! {reveal(crate::specs::part1_legacy_cleanup_interrupt);}
            let high = decoder.decode(UNIFORM_CONTEXT)?;
            let low = decoder.decode(UNIFORM_CONTEXT)?;
            stats.coding_symbols += 2;
            let row = if high {
                if low { 3 } else { 2 }
            } else if low {
                1
            } else {
                0
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row==0 || row==1 || row==2 || row==3);
                assert(self.entries@[((stripe+row)*self.width+x) as int] & SIG==0);
                crate::specs::compact_cached_summary(self.width,self.height,self.entries@,x,(stripe+row) as usize,context.2);
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost before_words=self.entries@;let ghost before_state=super::legacy_bitplane_view(state);}
            let marked = self.run_sign(state, decoder, (x, stripe + row), context.2, stats);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::compact_before_frontier_preserved(before_words,self.entries@,before_state,super::legacy_bitplane_view(state),true);}
            marked?;
            self.rows(
                state,
                decoder,
                context,
                (x, stripe, row + 1, rows, false),
                stats,
            )?;
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),crate::specs::compact_pass_order(super::legacy_bitplane_view(old(state)),kind),
            crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),kind is Cleanup),
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).view(),super::legacy_bitplane_view(final(state)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                ==crate::specs::compact_pass_model(old(self).view(),super::legacy_bitplane_view(old(state)),
                    crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),kind,orientation,causal),
            crate::specs::compact_pass_flags(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state)),kind,result.is_ok()),
            match result{Err(_)=>true,Ok(statistics)=>crate::specs::compact_statistics_le(statistics,crate::specs::compact_stripe_bound(old(self).width,old(self).height))
                && crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),!(kind is SignificancePropagation))},
    ))]
    fn pass(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        kind: Tier1PassKind,
        orientation: SubbandOrientation,
        causal: bool,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        match kind {
            Tier1PassKind::SignificancePropagation => {
                self.pass_specialized::<0>(state, decoder, kind, orientation, causal)
            }
            Tier1PassKind::MagnitudeRefinement => {
                self.pass_specialized::<1>(state, decoder, kind, orientation, causal)
            }
            Tier1PassKind::Cleanup => {
                self.pass_specialized::<2>(state, decoder, kind, orientation, causal)
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).ready(old(state)),crate::specs::compact_pass_order(super::legacy_bitplane_view(old(state)),kind),
            crate::specs::compact_before_frontier(old(self).entries@,super::legacy_bitplane_view(old(state)),kind is Cleanup),
            (KIND == 0) == (kind is SignificancePropagation),
            (KIND == 1) == (kind is MagnitudeRefinement),
            (KIND == 2) == (kind is Cleanup),
        ensures final(self).ready(final(state)),final(self).width==old(self).width,final(self).height==old(self).height,
            (result,final(self).view(),super::legacy_bitplane_view(final(state)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                ==crate::specs::compact_pass_model(old(self).view(),super::legacy_bitplane_view(old(state)),
                    crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),kind,orientation,causal),
            crate::specs::compact_pass_flags(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(final(state)),kind,result.is_ok()),
            match result{Err(_)=>true,Ok(statistics)=>crate::specs::compact_statistics_le(statistics,crate::specs::compact_stripe_bound(old(self).width,old(self).height))
                && crate::specs::compact_before_frontier(final(self).entries@,super::legacy_bitplane_view(final(state)),!(kind is SignificancePropagation))},
    ))]
    #[inline(never)]
    fn pass_specialized<const KIND: u8>(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        #[allow(unused_variables)] kind: Tier1PassKind,
        orientation: SubbandOrientation,
        causal: bool,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let pass_kind = match KIND {
            0 => Tier1PassKind::SignificancePropagation,
            1 => Tier1PassKind::MagnitudeRefinement,
            _ => Tier1PassKind::Cleanup,
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(pass_kind == kind); }
        let mut stats = ht_statistics_zero();
        let mut stripe = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=self.frame(state,decoder,stats);
            let ghost goal=crate::specs::compact_pass_model(initial.plane,initial.state,initial.symbols,kind,orientation,causal);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::legacy_bitplane_view);
            reveal(crate::specs::compact_pass_model);
            reveal(crate::specs::compact_membership);reveal(crate::specs::compact_before_frontier);
            if kind is MagnitudeRefinement{crate::specs::compact_frontier_initial(self.width,self.height,self.entries@,
                super::legacy_bitplane_view(state),if self.height<4{self.height}else{4});}
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant stripe<=self.height,self.ready(state),self.width==old(self).width,self.height==old(self).height,
                pass_kind==kind,
                crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(state)),
                initial==old(self).frame(old(state),old(decoder),crate::specs::tier1_statistics_zero()),
                goal==crate::specs::compact_pass_model(initial.plane,initial.state,initial.symbols,kind,orientation,causal),
                goal==crate::specs::compact_pass_suffix(self.frame(state,decoder,stats),stripe,kind,orientation,causal),
                crate::specs::compact_statistics_le(stats,crate::specs::compact_stripe_bound(self.width,stripe)),
                if kind is MagnitudeRefinement{
                    crate::specs::compact_refinement_pending(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),
                        stripe,if self.height-stripe<4{(self.height-stripe) as usize}else{4},0,0)
                }else{crate::specs::compact_before_frontier(self.entries@,super::legacy_bitplane_view(state),kind is Cleanup)},
            decreases self.height-stripe,
        ))]
        while stripe < self.height {
            #[cfg(feature = "cooperative-deadlines")]
            crate::deadline::checkpoint()?;
            #[cfg(verus_keep_ghost)]
            proof! {reveal(crate::specs::part1_legacy_stripes);}
            let rows = (self.height - stripe).min(4);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::compact_counter_algebra(self.width,stripe,rows,0);}
            let mut x = 0;
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x<=self.width,stripe<self.height,0<rows<=4,stripe+rows<=self.height,
                    pass_kind==kind,
                    self.ready(state),self.width==old(self).width,self.height==old(self).height,
                    crate::specs::compact_bitplane_flags_frame(super::legacy_bitplane_view(old(state)),super::legacy_bitplane_view(state)),
                    initial==old(self).frame(old(state),old(decoder),crate::specs::tier1_statistics_zero()),
                    goal==crate::specs::compact_pass_model(initial.plane,initial.state,initial.symbols,kind,orientation,causal),
                    goal==crate::specs::compact_column_suffix(self.frame(state,decoder,stats),x,stripe,rows,kind,orientation,causal),
                    crate::specs::compact_statistics_le(stats,crate::specs::compact_scan_bound(self.width,stripe,rows,x)),
                    if kind is MagnitudeRefinement{
                        crate::specs::compact_refinement_pending(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,x,0)
                    }else{crate::specs::compact_before_frontier(self.entries@,super::legacy_bitplane_view(state),kind is Cleanup)},
                decreases self.width-x,
            ))]
            while x < self.width {
                #[cfg(verus_keep_ghost)]
                proof! {reveal(crate::specs::part1_legacy_columns);}
                self.column(
                    state,
                    decoder,
                    (pass_kind, orientation, causal),
                    (x, stripe, rows),
                    &mut stats,
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {if kind is MagnitudeRefinement{
                    crate::specs::compact_frontier_column_end(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,x);
                }}
                x += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_legacy_columns);
                crate::specs::compact_counter_algebra(self.width,stripe,rows,0);
                if kind is MagnitudeRefinement{
                    crate::specs::compact_frontier_stripe_end(self.width,self.height,self.entries@,super::legacy_bitplane_view(state),stripe,rows,
                        if self.height-stripe-rows<4{(self.height-stripe-rows) as usize}else{4});
                }
            }
            stripe += rows;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_stripes);
            if kind is MagnitudeRefinement{crate::specs::compact_frontier_finished(self.width,self.height,self.entries@,super::legacy_bitplane_view(state));}
        }
        match pass_kind {
            Tier1PassKind::SignificancePropagation => {
                state.significance_propagation_complete = true
            }
            Tier1PassKind::MagnitudeRefinement => state.magnitude_refinement_complete = true,
            Tier1PassKind::Cleanup => state.cleanup_complete = true,
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::compact_membership);reveal(crate::specs::compact_before_frontier);}
        Ok(stats)
    }
}

impl Tier1CodeBlockDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result==crate::specs::compact_eligible(super::tier1_decoder_state(self),passes,decoded,wide_bytes),
    ))]
    fn compact_eligible(&self, passes: u32, decoded: u64, wide_bytes: usize) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(super::tier1_decoder_state);reveal(super::code_block_plane_view);}
        let width = usize::from(self.plane.width);
        let height = usize::from(self.plane.height);
        #[cfg(verus_keep_ghost)]
        proof! {assert(width*height<=usize::MAX) by(nonlinear_arith) requires width<=65535,height<=65535;}
        let count = width * height;
        if self.next_pass != 0
            || self.decoded_segments != 0
            || self.bitplane >= 31
            || self.bitplane_state.is_some()
            || self.legacy_segment.is_some()
            || passes == 0
            || passes > self.maximum_passes
            || self.maximum_passes != 3 * (u32::from(self.bitplane) + 1) - 2
            || count == 0
            || count > 4096
            || self.plane.coefficients.len() != count
            || !matches!(self.style.block_coding, Tier1BlockCoding::Legacy)
            || self.style.force_high_throughput
            || self.style.selective_arithmetic_coding_bypass
            || self.style.reset_contexts
            || self.style.terminate_all_passes
            || self.style.segmentation_symbols
        {
            return false;
        }
        let Some(per_cell) = (wide_bytes as u64).checked_add(10) else {
            #[cfg(verus_keep_ghost)]
            proof! {assert(count*(wide_bytes+10)>decoded) by(nonlinear_arith)
            requires count>0,wide_bytes+10>u64::MAX,decoded<=u64::MAX;}
            return false;
        };
        let Some(bytes) = (count as u64).checked_mul(per_cell) else {
            return false;
        };
        if bytes > decoded {
            return false;
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=count,count==self.plane.coefficients.len(),
                crate::specs::compact_admission(super::tier1_decoder_state(self),passes,decoded,wide_bytes),
                forall|i:int|0<=i<index ==> super::coefficient_raw_view(self.plane.coefficients@[i])==crate::specs::tier1_empty_coefficient(),
            decreases count-index,
        ))]
        while index < count {
            let c = self.plane.coefficients[index];
            if c.magnitude != 0
                || c.magnitude_high[0] != 0
                || c.magnitude_high[1] != 0
                || c.magnitude_high[2] != 0
                || c.magnitude_high[3] != 0
                || c.magnitude_high[4] != 0
                || c.legacy_bitplane.is_some()
                || c.significant
                || c.negative
                || c.refined
            {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(super::coefficient_raw_view);
                    reveal(super::code_block_plane_view);
                    let raw=super::coefficient_raw_view(c);
                    assert(raw.limbs[0]==c.magnitude);
                    assert(raw.limbs[1]==c.magnitude_high[0]);
                    assert(raw.limbs[2]==c.magnitude_high[1]);
                    assert(raw.limbs[3]==c.magnitude_high[2]);
                    assert(raw.limbs[4]==c.magnitude_high[3]);
                    assert(raw.limbs[5]==c.magnitude_high[4]);
                    assert(crate::specs::tier1_empty_coefficient().limbs==seq![0u64,0u64,0u64,0u64,0u64,0u64]) by(compute);
                    assert(super::coefficient_raw_view(c)!=crate::specs::tier1_empty_coefficient());
                    assert(super::code_block_plane_view(&self.plane).coefficients[index as int]==super::coefficient_raw_view(c));
                    assert(!crate::specs::compact_pristine(super::code_block_plane_view(&self.plane)));
                }
                return false;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(super::coefficient_raw_view(c).limbs =~= crate::specs::tier1_empty_coefficient().limbs);
                assert(super::coefficient_raw_view(c)==crate::specs::tier1_empty_coefficient());
            }
            index += 1;
        }
        true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result{
            None=>super::tier1_decoder_state(final(self))==super::tier1_decoder_state(old(self))
                && crate::mq::mq_decoder_view(final(decoder))==crate::mq::mq_decoder_view(old(decoder))
                && !crate::specs::compact_eligible(super::tier1_decoder_state(old(self)),passes,
                    crate::limits::resource_decoded_bytes_limit(limits),core::mem::size_of::<CoefficientState>()),
            Some(value)=>crate::specs::compact_eligible(super::tier1_decoder_state(old(self)),passes,
                    crate::limits::resource_decoded_bytes_limit(limits),core::mem::size_of::<CoefficientState>())
                && crate::specs::compact_inner_result(crate::specs::Part1LegacySegmentRun {
                    decoder:super::tier1_decoder_state(old(self)),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics:crate::specs::tier1_statistics_zero(),
                },passes,(value,super::tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder)))))
                && crate::specs::part2_legacy_inner_body_result(crate::specs::Part1LegacySegmentRun {
                    decoder:super::tier1_decoder_state(old(self)),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics:crate::specs::tier1_statistics_zero(),
                },passes,(value,super::tier1_decoder_state(final(self)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))),
        },
    ))]
    pub(super) fn try_compact_legacy(
        &mut self,
        decoder: &mut MqDecoder<'_>,
        passes: u32,
        limits: &ResourceLimits,
    ) -> Option<Result<Tier1PassStatistics, DecodeError>> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial=crate::specs::Part1LegacySegmentRun {
                decoder:super::tier1_decoder_state(self),
                symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),
                statistics:crate::specs::tier1_statistics_zero(),
            };
        }
        if !self.compact_eligible(
            passes,
            limits.maximum_decoded_bytes(),
            core::mem::size_of::<CoefficientState>(),
        ) {
            return None;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tier1_decoder_state);reveal(super::code_block_plane_view);
            assert(self.plane.width>0 && self.plane.height>0
                && self.plane.width<=4096 && self.plane.height<=4096) by(nonlinear_arith)
                requires self.plane.width as nat*self.plane.height as nat>0,
                    self.plane.width as nat*self.plane.height as nat<=4096;
        }
        let mut packed = match new_compact_plane(
            usize::from(self.plane.width),
            usize::from(self.plane.height),
        ) {
            Ok(v) => v,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::compact_inner_first_error(initial,passes,error);
                    crate::specs::compact_original_first_error(initial,passes);
                }
                return Some(Err(error));
            }
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_empty_word();
            assert(initial.decoder==super::tier1_decoder_state(self));
            assert(EMPTY==0x3f_0000_0000u64) by(compute);
            crate::specs::compact_fresh_projection(packed.width,packed.height,packed.entries@,initial.decoder.plane);
            crate::specs::compact_budget_monotone(initial.decoder,passes,crate::limits::resource_decoded_bytes_limit(limits),
                core::mem::size_of::<CoefficientState>());
            assert forall|i:int|0<=i<packed.entries.len() implies !crate::specs::compact_coefficient(packed.entries@[i]).significant by{
                assert(packed.entries@[i]==EMPTY);
            }
            crate::specs::compact_phase_initial(self.bitplane,packed.width,packed.height,packed.entries@);
        }
        let result = self.compact_passes(&mut packed, decoder, passes);
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_inner_observed(initial,passes,(result,self.compact_view(&packed),
                crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder))));
        }
        packed.commit(&mut self.plane);
        Some(result)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).bitplane<31,
            crate::specs::compact_block_phase(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                old(self).bitplane,super::legacy_bitplane_option_view(&old(self).bitplane_state)),
            ghost_decoded@<3*(ghost_top@ as nat+1)-2,
        ensures super::tier1_decoder_state(final(self))==(crate::specs::Tier1DecoderState {
                bitplane_state:super::legacy_bitplane_option_view(&final(self).bitplane_state),
                ..super::tier1_decoder_state(old(self))}),
            crate::specs::part2_legacy_ensure_result(old(self).compact_view(packed),(result,final(self).compact_view(packed))),
            match result {
                Err(error)=>error==DecodeError::AllocationFailed && final(self).compact_view(packed)==old(self).compact_view(packed),
                Ok(())=>final(self).bitplane_state.is_some()
                    && crate::specs::part1_legacy_ensure_bitplane(old(self).compact_view(packed))==(Ok(()),final(self).compact_view(packed))
                    && crate::specs::compact_membership(packed.width,packed.height,packed.entries@,
                        super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0)
                    && (super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0).bitplane==old(self).bitplane
                    && crate::specs::compact_pass_order(
                        super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0,
                        crate::specs::part1_legacy_pass_kind(ghost_decoded@))
                    && crate::specs::compact_before_frontier(packed.entries@,
                        super::legacy_bitplane_option_view(&final(self).bitplane_state)->Some_0,
                        crate::specs::part1_legacy_pass_kind(ghost_decoded@) is Cleanup),
            },
    ))]
    fn compact_prepare_bitplane(
        &mut self,
        packed: &CompactPlane,
        #[cfg(verus_keep_ghost)] ghost_top: Ghost<u16>,
        #[cfg(verus_keep_ghost)] ghost_decoded: Ghost<u32>,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=self.compact_view(packed);let ghost native_before=*self;}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(Tier1CodeBlockDecoder::compact_view);
            self.compact_metadata();
            crate::specs::compact_phase_shape(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state));
        }
        if self.bitplane_state.is_none() {
            let constructed = packed.initial_state(self.bitplane);
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_legacy_ensure_observed(before,super::legacy_bitplane_outcome(constructed));}
            let new_state = constructed?;
            #[cfg(verus_keep_ghost)]
            proof! {
                let state=super::legacy_bitplane_view(&new_state);
                assert(crate::specs::part1_legacy_bitplane_initial(before.plane,before.bitplane)==Ok(state));
                crate::specs::compact_phase_prepare(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                    self.bitplane,before.bitplane_state,state);
            }
            self.bitplane_state = Some(new_state);
            #[cfg(verus_keep_ghost)]
            proof! {
                Self::compact_native_store(native_before,*self);
                reveal(super::legacy_bitplane_option_view);
            }
            return Ok(());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_legacy_ensure_present(before);
            crate::specs::compact_phase_prepare(ghost_top@,ghost_decoded@,packed.width,packed.height,packed.entries@,
                self.bitplane,before.bitplane_state,before.bitplane_state->Some_0);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).next_pass==0,old(self).bitplane_state.is_none(),old(self).bitplane<31,
            passes>0,passes<=old(self).maximum_passes,old(self).maximum_passes==3*(old(self).bitplane as nat+1)-2,
            !old(self).style.selective_arithmetic_coding_bypass,!old(self).style.reset_contexts,!old(self).style.segmentation_symbols,
            crate::specs::compact_block_phase(old(self).bitplane,0,old(packed).width,old(packed).height,old(packed).entries@,old(self).bitplane,None),
        ensures final(packed).shape(),final(packed).width==old(packed).width,final(packed).height==old(packed).height,
            super::code_block_plane_view(&final(self).plane)==super::code_block_plane_view(&old(self).plane),
            crate::specs::part2_legacy_inner_body_result(crate::specs::Part1LegacySegmentRun {
                decoder:old(self).compact_view(old(packed)),
                symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                statistics:crate::specs::tier1_statistics_zero(),
            },passes,(result,final(self).compact_view(final(packed)),
                crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))),
            result!=Err(DecodeError::AllocationFailed) ==>
                (result,final(self).compact_view(final(packed)),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                    ==crate::specs::part1_legacy_segment_finish(crate::specs::part1_legacy_segment_run(crate::specs::Part1LegacySegmentRun {
                        decoder:old(self).compact_view(old(packed)),
                        symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                        statistics:crate::specs::tier1_statistics_zero(),
                    },passes as nat)),
    ))]
    fn compact_passes(
        &mut self,
        packed: &mut CompactPlane,
        decoder: &mut MqDecoder<'_>,
        passes: u32,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut total = ht_statistics_zero();
        let mut decoded = 0;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost phys=super::tier1_decoder_state(self);
            let ghost initial=crate::specs::Part1LegacySegmentRun {
                decoder:self.compact_view(packed),
                symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)),statistics:total,
            };
            let ghost mut prefix=Seq::<crate::specs::Part2Tier1StorageEvent>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.compact_metadata();self.compact_views(packed,decoder,total);
            reveal(super::legacy_bitplane_option_view);
            crate::specs::compact_phase_shape(initial.decoder.bitplane,0,packed.width,packed.height,packed.entries@,self.bitplane,None);
            crate::specs::compact_physical_start(phys);
            crate::specs::compact_progress_start(initial,passes);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant decoded<=passes,passes>0,passes<=initial.decoder.maximum_passes,self.maximum_passes==initial.decoder.maximum_passes,
                initial.decoder.bitplane<31,initial.decoder.maximum_passes==3*(initial.decoder.bitplane as nat+1)-2,
                !initial.decoder.style.selective_arithmetic_coding_bypass,
                !initial.decoder.style.reset_contexts,!initial.decoder.style.segmentation_symbols,
                packed.shape(),self.bitplane<31,packed.width==old(packed).width,packed.height==old(packed).height,
                super::code_block_plane_view(&self.plane)==phys.plane,
                phys==super::tier1_decoder_state(old(self)),
                self.next_pass==decoded,self.style==initial.decoder.style,self.orientation==initial.decoder.orientation,
                crate::specs::compact_physical_frame(phys,super::tier1_decoder_state(self)),
                crate::specs::compact_block_phase(initial.decoder.bitplane,decoded,packed.width,packed.height,packed.entries@,
                    self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state)),
                crate::specs::compact_statistics_le(total,(16*packed.entries.len()*decoded) as nat),
                initial==(crate::specs::Part1LegacySegmentRun {
                    decoder:old(self).compact_view(old(packed)),
                    symbols:crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))),
                    statistics:crate::specs::tier1_statistics_zero()}),
                crate::specs::compact_loop_progress(initial,passes,prefix,self.compact_run(packed,decoder,total),(passes-decoded) as nat),
            decreases passes-decoded,
        ))]
        while decoded < passes {
            total = self.compact_scheduled_pass(
                packed,
                decoder,
                total,
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(phys)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(initial)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(passes)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(decoded)),
                #[cfg(verus_keep_ghost)]
                verus_exec_expr!(Ghost(prefix)),
            )?;
            #[cfg(verus_keep_ghost)]
            proof! {
                prefix=choose|joined:Seq<crate::specs::Part2Tier1StorageEvent>|
                    #[trigger] crate::specs::compact_loop_progress(initial,passes,joined,self.compact_run(packed,decoder,total),
                        (passes-decoded-1) as nat);
            }
            decoded += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_progress_finish(initial,passes,prefix,self.compact_run(packed,decoder,total));
        }
        Ok(total)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires {
            let phys=ghost_phys@;let initial=ghost_initial@;let passes=ghost_passes@;let decoded=ghost_decoded@;let prefix=ghost_prefix@;
            decoded<passes && passes<=initial.decoder.maximum_passes && old(self).maximum_passes==initial.decoder.maximum_passes
            && initial.decoder.bitplane<31 && initial.decoder.maximum_passes==3*(initial.decoder.bitplane as nat+1)-2
            && !initial.decoder.style.selective_arithmetic_coding_bypass
            && !initial.decoder.style.reset_contexts && !initial.decoder.style.segmentation_symbols
            && old(packed).shape() && old(self).bitplane<31
            && super::code_block_plane_view(&old(self).plane)==phys.plane
            && old(self).next_pass==decoded && old(self).style==initial.decoder.style && old(self).orientation==initial.decoder.orientation
            && crate::specs::compact_physical_frame(phys,super::tier1_decoder_state(old(self)))
            && crate::specs::compact_block_phase(initial.decoder.bitplane,decoded,old(packed).width,old(packed).height,old(packed).entries@,
                old(self).bitplane,super::legacy_bitplane_option_view(&old(self).bitplane_state))
            && crate::specs::compact_statistics_le(total,(16*old(packed).entries.len()*decoded) as nat)
            && crate::specs::compact_loop_progress(initial,passes,prefix,old(self).compact_run(old(packed),old(decoder),total),
                (passes-decoded) as nat)
        },
        ensures {
            let phys=ghost_phys@;let initial=ghost_initial@;let passes=ghost_passes@;let decoded=ghost_decoded@;
            final(packed).shape() && final(packed).width==old(packed).width && final(packed).height==old(packed).height
            && super::code_block_plane_view(&final(self).plane)==phys.plane
            && final(self).maximum_passes==initial.decoder.maximum_passes && final(self).style==initial.decoder.style
            && final(self).orientation==initial.decoder.orientation
            && crate::specs::compact_physical_frame(phys,super::tier1_decoder_state(final(self)))
            && match result {
                Err(error)=>crate::specs::part2_legacy_inner_body_result(initial,passes,
                    (Err(error),final(self).compact_view(final(packed)),
                        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder)))))
                    && (error!=DecodeError::AllocationFailed ==>
                        (Err(error),final(self).compact_view(final(packed)),
                            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
                            ==crate::specs::part1_legacy_segment_finish(crate::specs::part1_legacy_segment_run(initial,passes as nat))),
                Ok(statistics)=>final(self).next_pass==decoded+1 && final(self).bitplane<31
                    && crate::specs::compact_block_phase(initial.decoder.bitplane,(decoded+1) as u32,
                        final(packed).width,final(packed).height,final(packed).entries@,final(self).bitplane,
                        super::legacy_bitplane_option_view(&final(self).bitplane_state))
                    && crate::specs::compact_statistics_le(statistics,(16*final(packed).entries.len()*(decoded+1)) as nat)
                    && exists|joined:Seq<crate::specs::Part2Tier1StorageEvent>|
                        #[trigger] crate::specs::compact_loop_progress(initial,passes,joined,
                            final(self).compact_run(final(packed),final(decoder),statistics),(passes-decoded-1) as nat),
            }
        },
    ))]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    fn compact_scheduled_pass(
        &mut self,
        packed: &mut CompactPlane,
        decoder: &mut MqDecoder<'_>,
        mut total: Tier1PassStatistics,
        #[cfg(verus_keep_ghost)] ghost_phys: Ghost<crate::specs::Tier1DecoderState>,
        #[cfg(verus_keep_ghost)] ghost_initial: Ghost<crate::specs::Part1LegacySegmentRun>,
        #[cfg(verus_keep_ghost)] ghost_passes: Ghost<u32>,
        #[cfg(verus_keep_ghost)] ghost_decoded: Ghost<u32>,
        #[cfg(verus_keep_ghost)] ghost_prefix: Ghost<Seq<crate::specs::Part2Tier1StorageEvent>>,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost phys=ghost_phys@;
            let ghost initial=ghost_initial@;let ghost passes=ghost_passes@;
            let ghost decoded=ghost_decoded@;let ghost prefix=ghost_prefix@;
        }
        #[cfg(feature = "cooperative-deadlines")]
        crate::deadline::checkpoint()?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before_step=self.compact_run(packed,decoder,total);
            let ghost before_words=packed.entries@;
            let ghost remaining=(passes-decoded) as nat;
            let ghost physical_before=super::tier1_decoder_state(self);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            self.compact_metadata();self.compact_views(packed,decoder,total);
            crate::specs::compact_block_schedule(initial.decoder.bitplane,decoded);
            crate::specs::compact_phase_shape(initial.decoder.bitplane,decoded,packed.width,packed.height,packed.entries@,
                self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state));
            reveal(super::legacy_bitplane_option_view);
        }
        let kind = self.style.pass_plan(self.next_pass).kind;
        let prepared = self.compact_prepare_bitplane(
            packed,
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(initial.decoder.bitplane)),
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(decoded)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            self.compact_metadata();self.compact_views(packed,decoder,total);
            crate::specs::compact_physical_updated(phys,physical_before,super::tier1_decoder_state(self));
            crate::specs::compact_physical_fields(phys,super::tier1_decoder_state(self));
            if let Err(error)=prepared {
                crate::specs::compact_allocation_error_exit(initial,passes,before_step,remaining,prefix,kind,error);
            }
        }
        prepared?;
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost ready=self.compact_view(packed);let ghost ready_state=ready.bitplane_state->Some_0;
        let ghost physical_ready=super::tier1_decoder_state(self);}
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tier1_decoder_state);
            self.compact_views(packed,decoder,total);
            assert(crate::specs::compact_physical_frame(phys,physical_ready)) by{
                assert(physical_ready==(crate::specs::Tier1DecoderState {
                    next_pass:physical_ready.next_pass,bitplane:physical_ready.bitplane,bitplane_state:physical_ready.bitplane_state,..physical_before}));
                crate::specs::compact_physical_updated(phys,physical_before,physical_ready);
            }
            self.compact_metadata();self.compact_views(packed,decoder,total);
            assert(self.bitplane_state.is_some());
        }
        let pass = packed.pass(
            self.bitplane_state
                .as_mut()
                .ok_or_else(invalid_code_block)?,
            decoder,
            kind,
            self.orientation,
            self.style.vertical_causal_context,
        );
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost pass_effect=(pass,self.compact_view(packed),crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)));
            let ghost expected=crate::specs::part2_legacy_step_after_pass(before_step,kind,pass_effect);
            let ghost after_state=self.compact_view(packed).bitplane_state->Some_0;
            let ghost physical_pass=super::tier1_decoder_state(self);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tier1_decoder_state);
            self.compact_metadata();
            assert(physical_pass==(crate::specs::Tier1DecoderState {bitplane_state:physical_pass.bitplane_state,..physical_ready}));
            crate::specs::compact_physical_updated(phys,physical_ready,physical_pass);
            crate::specs::compact_pass_store_frame(physical_ready,physical_pass,ready.plane,packed.view());
            self.compact_metadata();self.compact_views(packed,decoder,total);
            crate::specs::compact_physical_fields(phys,physical_pass);
            let effect=(pass,packed.view(),after_state,crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(decoder)));
            crate::specs::compact_pass_observed(before_step.decoder,before_step.symbols->Mq_0,kind,ready,effect);
            assert(self.compact_view(packed)==(crate::specs::Tier1DecoderState {plane:effect.1,bitplane_state:Some(effect.2),..ready}));
            if pass.is_err(){
                assert(crate::specs::part2_legacy_inner_body_result(initial,passes,pass_effect)
                    && (pass!=Err(DecodeError::AllocationFailed) ==> pass_effect==crate::specs::part1_legacy_segment_finish(
                        crate::specs::part1_legacy_segment_run(initial,passes as nat)))) by{
                    crate::specs::compact_pass_error_exit(initial,passes,before_step,remaining,prefix,kind,pass_effect);
                }
            }
        }
        let stats = pass?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::compact_area_bound(packed.width,packed.height,packed.entries@);
            crate::specs::compact_phase_after_pass(initial.decoder.bitplane,decoded,packed.width,packed.height,before_words,packed.entries@,
                before_step.decoder.bitplane,before_step.decoder.bitplane_state,ready_state,after_state);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost merged=crate::specs::tier1_statistics_merge(total,stats);}
        total = compact_merge_statistics(
            total,
            stats,
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(packed.entries@.len())),
            #[cfg(verus_keep_ghost)]
            verus_exec_expr!(Ghost(decoded)),
        );
        self.next_pass += 1;
        if matches!(kind, Tier1PassKind::Cleanup) {
            self.bitplane_state = None;
            if self.next_pass < self.maximum_passes {
                self.bitplane -= 1;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(total==merged.1);
            let physical_after=super::tier1_decoder_state(self);
            reveal(super::tier1_decoder_state);
            self.compact_metadata();
            assert(crate::specs::compact_advance_frame(physical_pass,physical_after,kind)) by{
                reveal(crate::specs::compact_advance_frame);
                reveal(super::legacy_bitplane_option_view);
            }
            crate::specs::compact_advance_fields(physical_pass,physical_after,kind);
            crate::specs::compact_physical_updated(phys,physical_pass,physical_after);
            crate::specs::compact_physical_fields(phys,physical_after);
            self.compact_metadata();self.compact_views(packed,decoder,total);
            assert(self.bitplane==crate::specs::compact_block_bitplane(initial.decoder.bitplane,(decoded+1) as u32));
            assert(super::legacy_bitplane_option_view(&self.bitplane_state)==if kind is Cleanup{None}else{Some(after_state)});
            crate::specs::compact_phase_shape(initial.decoder.bitplane,(decoded+1) as u32,packed.width,packed.height,packed.entries@,
                self.bitplane,super::legacy_bitplane_option_view(&self.bitplane_state));
            assert(expected==(Ok(()),self.compact_run(packed,decoder,total))) by{
                crate::specs::compact_success_store_frame(before_step,kind,pass_effect,stats,physical_pass,physical_after,
                    packed.view(),total,self.compact_run(packed,decoder,total));
            }
            let joined=crate::specs::compact_progress_continue(initial,passes,before_step,remaining,prefix,kind,pass_effect,self.compact_run(packed,decoder,total));
            assert(exists|next:Seq<crate::specs::Part2Tier1StorageEvent>|
                #[trigger] crate::specs::compact_loop_progress(initial,passes,next,self.compact_run(packed,decoder,total),(passes-decoded-1) as nat));
        }
        Ok(total)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        width > 0 && height > 0,
        (width as nat) * (height as nat) <= 4096,
        effective_bitplanes > 0 && effective_bitplanes <= 31,
        passes > 0 && passes <= 3 * (effective_bitplanes as nat) - 2,
        !style.selective_arithmetic_coding_bypass,
        !style.reset_contexts,
        !style.terminate_all_passes,
        !style.segmentation_symbols,
        !style.predictable_termination,
        !style.force_high_throughput,
        matches!(style.block_coding, super::Tier1BlockCoding::Legacy),
    ensures
        result.0 ==> {
            let words = result.1@;
            let count = (width as nat) * (height as nat);
            let initial_plane = crate::specs::private_legacy_empty_plane(width, height);
            let initial_state = crate::specs::Tier1DecoderState {
                plane: initial_plane,
                private_plan: false,
                orientation,
                style,
                maximum_passes: (3 * (effective_bitplanes as nat) - 2) as u32,
                next_pass: 0,
                bitplane: (effective_bitplanes - 1) as u16,
                zero_bitplanes: Some(zero_bitplanes),
                bitplane_state: None,
                mq_context_state: None,
                reset_contexts_before_mq: false,
                decoded_segments: 0,
                decoded_bytes: 0,
                legacy_segment: None,
                legacy_decode_work: 0,
                ht_cleanup_plane: None,
                ht_refinement_data: Seq::empty(),
                ht_refinement_passes: 0,
                ht_decoded_bitplanes: 0,
                ht_current_set_has_cleanup: false,
                ht_sets_seen: 0,
                allow_multiple_ht_sets,
                ht_magnitude_bound,
            };
            let seg = crate::specs::part1_legacy_segment(
                initial_state,
                input@,
                passes,
                crate::limits::resource_code_block_pass_limit(limits),
                crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),
                crate::limits::resource_work_limit(limits),
            );
            words.len() == count
                && seg.0.is_ok()
                && seg.1.plane == crate::specs::private_legacy_compact_plane(width, height, words)
        },
))]
#[allow(clippy::too_many_arguments)]
pub(crate) fn decode_compact_legacy_scratch(
    width: u16,
    height: u16,
    effective_bitplanes: u16,
    zero_bitplanes: u16,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
    orientation: super::SubbandOrientation,
    style: super::Tier1CodingStyle,
    input: &[u8],
    passes: u32,
    mut scratch: Vec<u64>,
    limits: &ResourceLimits,
) -> (bool, Vec<u64>) {
    let w = usize::from(width);
    let h = usize::from(height);
    let count = w * h;
    let maximum_passes = 3 * u32::from(effective_bitplanes) - 2;
    if input.is_empty()
        || passes > limits.maximum_code_block_passes()
        || (input.len() as u64) > limits.maximum_code_block_bytes()
        || (input.len() as u64) > limits.maximum_input_bytes()
        || (input.len() as u64) > u64::from(u32::MAX)
    {
        return (false, scratch);
    }
    scratch.clear();
    if crate::allocation::reserve_additional(&mut scratch, count).is_err() {
        return (false, scratch);
    }
    scratch.resize(count, EMPTY);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(w <= 4096 && h <= 4096) by(nonlinear_arith)
            requires w > 0, h > 0, w * h <= 4096;
        assert forall|i: int| 0 <= i < count implies scratch@[i] == EMPTY by {
            assert(vstd::pervasive::cloned::<u64>(EMPTY, scratch@[i]));
        }
        assert(scratch@ =~= Seq::new(count as nat, |_: int| EMPTY));
        assert(EMPTY == 0x3f_0000_0000u64) by(compute);
        crate::specs::compact_empty_cache(w, h, scratch@);
        assert(crate::specs::compact_precision_word(EMPTY)) by(compute);
    }
    let mut mq = match crate::mq::mq_from_input(
        input,
        limits.maximum_input_bytes(),
        limits.maximum_work_units(),
    ) {
        Ok(v) => v,
        Err(_) => return (false, scratch),
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost mq_raw = crate::mq::mq_decoder_view(&mq);
    }
    if super::state::initialize_tier1_contexts(&mut mq).is_err() {
        return (false, scratch);
    }
    let mut packed = CompactPlane {
        width: w,
        height: h,
        entries: scratch,
    };
    let mut decoder = Tier1CodeBlockDecoder {
        plane: super::CodeBlockPlane {
            width,
            height,
            coefficients: Vec::new(),
        },
        private_plan: false,
        orientation,
        style,
        maximum_passes,
        next_pass: 0,
        bitplane: effective_bitplanes - 1,
        zero_bitplanes: Some(zero_bitplanes),
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
        allow_multiple_ht_sets,
        ht_magnitude_bound,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_view = decoder.compact_view(&packed);
        let ghost mq_init = crate::mq::mq_decoder_view(&mq);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(super::tier1_decoder_state);
        crate::specs::compact_empty_word();
        assert forall|i: int| 0 <= i < packed.entries.len() implies !crate::specs::compact_coefficient(packed.entries@[i]).significant by {
            assert(packed.entries@[i] == EMPTY);
        }
        assert(packed.view() == crate::specs::private_legacy_empty_plane(width, height)) by {
            assert(packed.entries@.map_values(|word: u64| crate::specs::compact_coefficient(word))
                =~= crate::specs::private_legacy_empty_plane(width, height).coefficients);
        }
        crate::specs::compact_phase_initial(decoder.bitplane, packed.width, packed.height, packed.entries@);
    }
    let result = decoder.compact_passes(&mut packed, &mut mq, passes);
    let ok = result.is_ok();
    #[cfg(verus_keep_ghost)]
    proof! {
        if ok {
            reveal(crate::specs::part1_legacy_segment);
            reveal(crate::specs::part1_legacy_segment_admission);
            reveal(crate::specs::part1_legacy_segment_account);
            crate::specs::private_legacy_segment_passes_all(style, 0, passes);
            assert(crate::specs::part1_legacy_plan(style, 0).coding_mode is Mq);
            assert(crate::specs::part1_mq_initial(
                input@,
                crate::limits::resource_input_byte_limit(limits),
                crate::limits::resource_work_limit(limits),
            ) == Ok::<crate::specs::Part1MqState, DecodeError>(mq_raw));
            assert(crate::specs::part1_legacy_segment_setup(initial_view, mq_raw) == (initial_view, mq_init));
            assert(packed.view().coefficients =~= crate::specs::private_legacy_compact_plane(width, height, packed.entries@).coefficients);
            assert(packed.view() == crate::specs::private_legacy_compact_plane(width, height, packed.entries@));
        }
    }
    (ok, packed.entries)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires ghost_cells@<=4096,ghost_completed@<91,
        crate::specs::compact_statistics_le(total,(16*ghost_cells@*ghost_completed@) as nat),
        crate::specs::compact_statistics_le(pass,(16*ghost_cells@) as nat),
    ensures crate::specs::tier1_statistics_merge(total,pass)==(Ok(()),result),
        crate::specs::compact_statistics_le(result,(16*ghost_cells@*(ghost_completed@+1)) as nat),
))]
fn compact_merge_statistics(
    total: Tier1PassStatistics,
    pass: Tier1PassStatistics,
    #[cfg(verus_keep_ghost)] ghost_cells: Ghost<nat>,
    #[cfg(verus_keep_ghost)] ghost_completed: Ghost<u32>,
) -> Tier1PassStatistics {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::compact_total_merge(total,pass,ghost_cells@,ghost_completed@);}
    Tier1PassStatistics {
        coefficients_scanned: total.coefficients_scanned + pass.coefficients_scanned,
        coding_symbols: total.coding_symbols + pass.coding_symbols,
        newly_significant: total.newly_significant + pass.newly_significant,
        refined_coefficients: total.refined_coefficients + pass.refined_coefficients,
        run_mode_columns: total.run_mode_columns + pass.run_mode_columns,
    }
}

#[cfg(test)]
mod tests {
    use super::super::{CodeBlockPlane, Tier1CodingStyle};
    use super::*;

    #[test]
    fn scratch_is_one_real_owner_before_the_original_bitplane_owners() {
        let limits = ResourceLimits::default();
        let input = [0x84, 0x3f, 0x00, 0xff, 0x7f];
        for refusal in 0..18 {
            let mut actual = block(5, 7, 8, false);
            let mut expected = actual.clone();
            let mut mq =
                crate::mq::mq_from_input(&input, 100, limits.maximum_work_units()).unwrap();
            super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
            let mut reference =
                crate::mq::mq_from_input(&input, 100, limits.maximum_work_units()).unwrap();
            super::super::state::initialize_tier1_contexts(&mut reference).unwrap();
            let passes = actual.maximum_passes;
            let result = crate::allocation::with_refusal(refusal, || {
                actual.try_compact_legacy(&mut mq, passes, &limits)
            })
            .unwrap();
            if refusal == 0 {
                assert_eq!(result, Err(DecodeError::AllocationFailed));
            } else {
                let expected_result = crate::allocation::with_refusal(refusal - 1, || {
                    expected.decode_mq_segment_passes(&mut reference, passes)
                });
                assert_eq!(result, expected_result, "refusal {refusal}");
            }
            assert_eq!(
                format!("{actual:?}"),
                format!("{expected:?}"),
                "refusal {refusal}"
            );
            assert_eq!(
                format!("{mq:?}"),
                format!("{reference:?}"),
                "refusal {refusal}"
            );
        }
    }

    #[test]
    fn compact_admission_uses_coded_bitplanes_exact_capacity_and_pristine_state() {
        let original = block(5, 7, 31, false);
        let bytes = 5 * 7 * 66;
        assert!(original.compact_eligible(
            original.maximum_passes,
            bytes,
            core::mem::size_of::<CoefficientState>()
        ));
        assert!(!original.compact_eligible(
            original.maximum_passes,
            bytes - 1,
            core::mem::size_of::<CoefficientState>()
        ));
        assert!(original.compact_eligible(
            original.maximum_passes - 1,
            bytes,
            core::mem::size_of::<CoefficientState>()
        ));
        assert!(original.compact_eligible(1, bytes, core::mem::size_of::<CoefficientState>()));
        assert!(!original.compact_eligible(0, bytes, core::mem::size_of::<CoefficientState>()));
        assert!(!original.compact_eligible(
            original.maximum_passes + 1,
            bytes,
            core::mem::size_of::<CoefficientState>()
        ));
        let wide = block(5, 7, 32, false);
        assert!(!wide.compact_eligible(wide.maximum_passes, u64::MAX, 56));
        let maximum = block(64, 64, 31, false);
        assert!(maximum.compact_eligible(
            maximum.maximum_passes,
            4096 * 66,
            core::mem::size_of::<CoefficientState>()
        ));
        for field in 0..20 {
            let mut candidate = original.clone();
            match field {
                0 => candidate.next_pass = 1,
                1 => candidate.decoded_segments = 1,
                2 => {
                    candidate.bitplane_state =
                        Some(Tier1BitplaneState::new_at_bitplane(&candidate.plane, 30).unwrap())
                }
                3 => candidate.legacy_segment = Some(candidate.legacy_segment_snapshot().unwrap()),
                4 => candidate.style.selective_arithmetic_coding_bypass = true,
                5 => candidate.style.reset_contexts = true,
                6 => candidate.style.terminate_all_passes = true,
                7 => candidate.style.segmentation_symbols = true,
                8 => candidate.style.force_high_throughput = true,
                9 => candidate.plane.coefficients[0].magnitude = 1,
                10 => candidate.plane.coefficients[0].magnitude_high[4] = 1,
                11 => candidate.plane.coefficients[0].legacy_bitplane = Some(0),
                12 => candidate.plane.coefficients[0].significant = true,
                13 => candidate.plane.coefficients[0].negative = true,
                14 => candidate.plane.coefficients[0].refined = true,
                15 => {
                    candidate.plane.coefficients.pop();
                }
                16 => candidate.style.block_coding = Tier1BlockCoding::Mixed,
                17 => candidate.style.block_coding = Tier1BlockCoding::HighThroughput,
                18 => candidate.plane.width = 0,
                _ => candidate.plane.width = 4096,
            }
            let before = format!("{candidate:?}");
            let input = [0x84];
            let mut mq = crate::mq::mq_from_input(&input, 100, 100).unwrap();
            super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
            let mq_before = format!("{mq:?}");
            let passes = candidate.maximum_passes;
            assert!(
                crate::allocation::with_refusal(0, || candidate.try_compact_legacy(
                    &mut mq,
                    passes,
                    &ResourceLimits::default()
                ))
                .is_none(),
                "field {field}"
            );
            assert_eq!(format!("{candidate:?}"), before, "field {field}");
            assert_eq!(format!("{mq:?}"), mq_before, "field {field}");
        }
    }

    #[test]
    fn inherited_replay_keeps_checked_allocation_and_error_frontiers() {
        let limits = ResourceLimits::default();
        let wide_limits = limits.with_maximum_decoded_bytes(5 * 7 * 56).unwrap();
        let mut partial = block(5, 7, 8, false);
        partial
            .decode_legacy_contribution(&[0x84], 1, &limits)
            .unwrap();
        assert!(partial.legacy_segment.is_some());
        let remaining = (partial.maximum_passes - partial.next_pass) as u8;
        for refusal in 0..24 {
            let mut actual = partial.clone();
            let mut expected = partial.clone();
            let actual_result = crate::allocation::with_refusal(refusal, || {
                actual.decode_legacy_contribution(&[0x3f, 0x00, 0xff, 0x7f], remaining, &limits)
            });
            // Replaying into the compact kernel inserts one compact scratch reservation
            // immediately after the 3 legacy replay allocations (append + plane/bitplane restore):
            // refusals 0..3 hit identical replay-setup prefixes; refusal 3 hits compact scratch;
            // refusal >= 4 shifts by 1 relative to the wide decoder.
            if refusal == 3 {
                assert_eq!(actual_result, Err(DecodeError::AllocationFailed));
            } else {
                let wide_refusal = if refusal > 3 { refusal - 1 } else { refusal };
                let expected_result = crate::allocation::with_refusal(wide_refusal, || {
                    expected.decode_legacy_contribution(
                        &[0x3f, 0x00, 0xff, 0x7f],
                        remaining,
                        &wide_limits,
                    )
                });
                assert_eq!(actual_result, expected_result, "refusal {refusal}");
                assert_eq!(
                    format!("{actual:?}"),
                    format!("{expected:?}"),
                    "refusal {refusal}"
                );
            }
        }
    }

    fn block(width: u16, height: u16, planes: u16, causal: bool) -> Tier1CodeBlockDecoder {
        Tier1CodeBlockDecoder::new(
            width,
            height,
            planes,
            SubbandOrientation::Hh,
            Tier1CodingStyle {
                vertical_causal_context: causal,
                ..Tier1CodingStyle::default()
            },
        )
        .unwrap()
    }

    #[test]
    fn incremental_flags_match_checked_neighbors_after_every_mark() {
        let mut wide = CodeBlockPlane::new(7, 9).unwrap();
        let mut compact = new_compact_plane(7, 9).unwrap();
        for index in (0..63).map(|i| i * 17 % 63) {
            let (x, y) = (index % 7, index / 7);
            compact.mark(x, y, 4, index % 3 == 0);
            wide.mark_significant_at_bitplane(x as u16, y as u16, 4, index % 3 == 0)
                .unwrap();
            for causal in [false, true] {
                for yy in 0..9 {
                    for xx in 0..7 {
                        assert_eq!(
                            compact.summary(xx, yy, causal),
                            wide.neighbor_summary_with_causality(xx as u16, yy as u16, causal)
                                .unwrap()
                        );
                    }
                }
            }
        }
        compact.commit(&mut wide);
        assert!(
            wide.coefficients
                .iter()
                .all(|c| c.magnitude == 16 && c.legacy_bitplane == Some(4))
        );
    }

    #[test]
    fn bounded_complete_mq_block_reaches_compact_kernel() {
        let mut block = block(4, 4, 8, false);
        block.orientation = SubbandOrientation::Ll;
        let limits = ResourceLimits::default();
        let mut mq = crate::mq::mq_from_input(
            &[0x84, 0x3f, 0x00, 0xff, 0x7f],
            100,
            limits.maximum_work_units(),
        )
        .unwrap();
        super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
        let passes = block.maximum_passes;
        assert!(block.try_compact_legacy(&mut mq, passes, &limits).is_some());
    }

    #[test]
    fn compact_partial_pass_counts_match_wide_decoder_and_bitplane_state() {
        let limits = ResourceLimits::default();
        let input = [0x84, 0x3f, 0x00, 0xff, 0x7f, 0x12, 0x55];
        for causal in [false, true] {
            for passes in [1_u32, 2, 3, 4, 5, 7, 10, 12] {
                let mut compact = block(5, 7, 5, causal);
                let mut wide = compact.clone();
                let scalar_limits = limits.with_maximum_decoded_bytes(5 * 7 * 56).unwrap();
                let mut mq_compact =
                    crate::mq::mq_from_input(&input, 100, limits.maximum_work_units()).unwrap();
                super::super::state::initialize_tier1_contexts(&mut mq_compact).unwrap();
                assert!(
                    compact
                        .try_compact_legacy(&mut mq_compact, passes, &limits)
                        .is_some(),
                    "passes={passes} causal={causal} should enter compact kernel"
                );
                let mut compact_seg = block(5, 7, 5, causal);
                assert_eq!(
                    compact_seg.decode_segment(&input, passes as u8, &limits),
                    wide.decode_segment(&input, passes as u8, &scalar_limits),
                    "passes={passes} causal={causal}"
                );
                assert_eq!(
                    format!("{compact_seg:?}"),
                    format!("{wide:?}"),
                    "passes={passes} causal={causal}"
                );
            }
        }
    }

    #[test]
    fn compact_matches_checked_result_and_every_visible_error_prefix() {
        for (width, height) in [(1, 1), (3, 5), (16, 16)] {
            for planes in [1, 8, 31] {
                for causal in [false, true] {
                    for input in [
                        &[0x84][..],
                        &[0xff, 0x90][..],
                        &[0x84, 0x3f, 0x00, 0xff, 0x7f][..],
                    ] {
                        for work in [1, 2, 7, 128, 100_000] {
                            let mut compact = block(width, height, planes, causal);
                            let mut scalar = compact.clone();
                            let limits = ResourceLimits::default()
                                .with_maximum_work_units(work)
                                .unwrap();
                            let scalar_limits = limits
                                .with_maximum_decoded_bytes(
                                    u64::from(width) * u64::from(height) * 56,
                                )
                                .unwrap();
                            let passes = compact.maximum_passes as u8;
                            assert_eq!(
                                compact.decode_segment(input, passes, &limits),
                                scalar.decode_segment(input, passes, &scalar_limits)
                            );
                            assert_eq!(format!("{compact:?}"), format!("{scalar:?}"));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn compact_preserves_actual_mq_register_context_and_work_error_state() {
        for planes in [1, 8, 31] {
            for causal in [false, true] {
                for work in [1, 2, 7, 128, 100_000] {
                    let mut compact = block(5, 7, planes, causal);
                    compact.orientation = SubbandOrientation::Hl;
                    let mut scalar = compact.clone();
                    let limits = ResourceLimits::default()
                        .with_maximum_work_units(work)
                        .unwrap();
                    let input = [0x84, 0x3f, 0x00, 0xff, 0x7f];
                    let mut mq = crate::mq::mq_from_input(&input, 100, work).unwrap();
                    super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
                    let mut reference = crate::mq::mq_from_input(&input, 100, work).unwrap();
                    super::super::state::initialize_tier1_contexts(&mut reference).unwrap();
                    let passes = compact.maximum_passes;
                    assert_eq!(
                        compact
                            .try_compact_legacy(&mut mq, passes, &limits)
                            .unwrap(),
                        scalar.decode_mq_segment_passes(&mut reference, passes)
                    );
                    assert_eq!(format!("{compact:?}"), format!("{scalar:?}"));
                    assert_eq!(format!("{mq:?}"), format!("{reference:?}"));
                }
            }
        }
    }
}
