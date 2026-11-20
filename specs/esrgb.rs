//! PIMA 7667:2001 sections 4.1/4.4 and normative Annex A.2/A.3.
//! This models the default encoded-RGB clipping path, not a gamut mapper.
//! Half-up quantization to 16 bits is an implementation choice.
use vstd::prelude::*;

verus! {

/// 2^(n-9) for the three PIMA precisions; zero denotes unsupported precision.
pub(crate) open spec fn color_esrgb_scale(precision: u8) -> int {
    if precision == 10 { 2 } else if precision == 12 { 8 }
    else if precision == 16 { 128 } else { 0 }
}

pub(crate) open spec fn color_esrgb_sample_to_srgb16(value: u64, precision: u8)
    -> Result<u16, crate::DecodeError>
{
    let scale = color_esrgb_scale(precision);
    if scale == 0 {
        Err(crate::DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::EnumeratedColorSpace,
        })
    } else if value as int > 512 * scale - 1 {
        Err(crate::DecodeError::MalformedInput {
            offset: 0,
            kind: crate::MalformedKind::InvalidColorSpecification,
        })
    } else {
        let delta = value as int - 192 * scale;
        let clipped = if delta < 0 { 0 } else if delta > 255 * scale { 255 * scale } else { delta };
        Ok(((clipped * 257 + scale / 2) / scale) as u16)
    }
}

/// Annex A.2 byte embeddings are representable and recover all 16 output bits.
pub(crate) proof fn color_esrgb_embedded_byte_roundtrip(srgb: u8, precision: u8)
    requires precision == 10 || precision == 12 || precision == 16,
    ensures
        0 <= (srgb as int + 192) * color_esrgb_scale(precision) <= u64::MAX,
        (srgb as int + 192) * color_esrgb_scale(precision)
            <= 512 * color_esrgb_scale(precision) - 1,
        color_esrgb_sample_to_srgb16(
            ((srgb as int + 192) * color_esrgb_scale(precision)) as u64, precision,
        ) == Ok(((srgb as int) * 257) as u16),
{
    if precision == 10 {
    } else if precision == 12 {
    } else {
        assert(precision == 16);
    }
}

}
