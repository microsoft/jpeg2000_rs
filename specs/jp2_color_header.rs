//! Actual color header metadata and complete borrowed ICC-byte copying.

use super::*;

verus! {

pub type Part2ColorSpecification = (crate::jp2::ColorMethod, u8, u8, Option<Seq<u8>>);

#[verifier::opaque]
pub open spec fn part2_validate_color_specification_prefix(input: Part2BoxReference, base: u64)
    -> Result<(), crate::DecodeError>
{
    if input.1.len() < 3 {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else { Ok(()) }
}

#[verifier::opaque]
pub open spec fn part2_parse_color_specification(input: Part2BoxReference, base: u64)
    -> Result<Part2ColorSpecification, crate::DecodeError>
{
    let payload = input.1;
    if payload.len() < 3 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
    else {
        let length = (payload.len() - 3) as nat;
        if length > u64::MAX as nat {
            Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::ArithmeticOverflow })
        } else if payload[0] == 1 {
            if payload.len() != 7 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
            else { Ok((crate::jp2::ColorMethod::Enumerated {
                color_space: part2_box_u32([payload[3], payload[4], payload[5], payload[6]]) },
                payload[1], payload[2], None)) }
        } else if payload[0] == 2 || payload[0] == 3 {
            if length == 0 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
            else { Ok((if payload[0] == 2 { crate::jp2::ColorMethod::RestrictedIcc { profile_bytes: length as u64 } }
                else { crate::jp2::ColorMethod::AnyIcc { profile_bytes: length as u64 } },
                payload[1], payload[2], Some(payload.subrange(3, payload.len() as int)))) }
        } else { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidColorSpecification)) }
    }
}

}
