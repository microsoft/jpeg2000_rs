//! PIMA 7667:2001 Annex A.3's default encoded-RGB clipping conversion.
//!
//! The 10/12/16-bit encodings use scale 2^(n-9) and offset
//! 2^(n-2) + 2^(n-3) = 192 * scale (sections 4.1 and 4.4).
//! We retain fractional sRGB codes until the final 16-bit output, using
//! round-half-up quantization. That rounding choice is ours, not a PIMA rule.
//! Representable scalar codes alone do not establish physical RGB validity.

use super::geometry::unsupported;
use crate::{DecodeError, MalformedKind, UnsupportedColorConversion};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures result == crate::specs::color_esrgb_sample_to_srgb16(value, precision),
    )
)]
pub(super) fn esrgb_sample_to_srgb16(value: u64, precision: u8) -> Result<u16, DecodeError> {
    let scale = match precision {
        10 => 2_u64,
        12 => 8,
        16 => 128,
        _ => {
            return Err(unsupported(
                UnsupportedColorConversion::EnumeratedColorSpace,
            ));
        }
    };
    let maximum = 512 * scale - 1;
    if value > maximum {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidColorSpecification,
        });
    }
    let black = 192 * scale;
    let white = black + 255 * scale;
    if value <= black {
        return Ok(0);
    }
    if value >= white {
        return Ok(u16::MAX);
    }
    let numerator = (value - black) * 257 + scale / 2;
    let rounded = numerator / scale;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(rounded <= u16::MAX);
    }
    Ok(rounded as u16)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pima_anchors_and_encoded_rgb_clipping() {
        for (precision, black, white, maximum) in [
            (10, 384, 894, 1023),
            (12, 1536, 3576, 4095),
            (16, 24576, 57216, 65535),
        ] {
            for value in [0, black - 1, black] {
                assert_eq!(esrgb_sample_to_srgb16(value, precision), Ok(0));
            }
            for value in [white, white + 1, maximum] {
                assert_eq!(esrgb_sample_to_srgb16(value, precision), Ok(u16::MAX));
            }
        }
    }

    #[test]
    fn fractional_codes_keep_precision_and_round_half_up() {
        for (precision, black, half, before_tie, after_tie, near_white) in [
            (10, 384, 1, 0, 257, 65407),
            (12, 1536, 4, 96, 161, 65503),
            (16, 24576, 64, 126, 131, 65533),
        ] {
            assert_eq!(
                esrgb_sample_to_srgb16(black + half - 1, precision),
                Ok(before_tie),
            );
            assert_eq!(esrgb_sample_to_srgb16(black + half, precision), Ok(129));
            assert_eq!(
                esrgb_sample_to_srgb16(black + half + 1, precision),
                Ok(after_tie),
            );
            assert_eq!(esrgb_sample_to_srgb16(black + 3 * half, precision), Ok(386),);
            let white = black + 510 * half;
            assert_eq!(esrgb_sample_to_srgb16(white - 1, precision), Ok(near_white),);
        }
    }

    #[test]
    fn every_embedded_srgb_byte_recovers_exactly_at_every_pima_precision() {
        for precision in [10, 12, 16] {
            let scale = 1_u64 << (precision - 9);
            let offset = (1_u64 << (precision - 2)) + (1_u64 << (precision - 3));
            for srgb in 0_u16..=255 {
                let encoded = u64::from(srgb) * scale + offset;
                assert_eq!(esrgb_sample_to_srgb16(encoded, precision), Ok(srgb * 257));
            }
        }
    }

    #[test]
    fn rejects_non_pima_precision_and_out_of_range_codes() {
        for precision in 0_u8..=u8::MAX {
            if matches!(precision, 10 | 12 | 16) {
                let maximum = (1_u64 << precision) - 1;
                for value in [maximum + 1, u64::MAX] {
                    assert_eq!(
                        esrgb_sample_to_srgb16(value, precision),
                        Err(DecodeError::MalformedInput {
                            offset: 0,
                            kind: MalformedKind::InvalidColorSpecification,
                        }),
                    );
                }
            } else {
                for value in [0, u64::MAX] {
                    assert_eq!(
                        esrgb_sample_to_srgb16(value, precision),
                        Err(DecodeError::UnsupportedColorConversion {
                            reason: UnsupportedColorConversion::EnumeratedColorSpace,
                        }),
                    );
                }
            }
        }
    }
}
