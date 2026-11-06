//! Actual image-header and component-bit-depth bytes with native lazy errors.

use super::*;

verus! {

pub open spec fn part2_image_box_error(base: u64, header: Part2BoxHeader, kind: crate::MalformedKind)
    -> crate::DecodeError
{
    match part2_box_add_offset(base, header.1) {
        Err(error) => error, Ok(offset) => crate::DecodeError::MalformedInput { offset, kind },
    }
}

pub open spec fn part2_container_bit_depth(value: u8, offset: u64)
    -> Result<crate::jp2::ComponentBitDepth, crate::DecodeError>
{
    if value == 0xff { Ok(crate::jp2::ComponentBitDepth::Variable) }
    else {
        let bits = ((value & 0x7f) as nat + 1) as u8;
        if bits > 38 {
            Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxContents })
        } else { Ok(crate::jp2::ComponentBitDepth::Uniform { bits, signed: value & 0x80 != 0 }) }
    }
}

#[verifier::opaque]
pub open spec fn part2_parse_image_header(input: Part2BoxReference, limits: &crate::ResourceLimits, base: u64)
    -> Result<crate::jp2::ImageHeader, crate::DecodeError>
{
    let payload = input.1;
    if payload.len() != 14 { Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength)) }
    else {
        let height = part2_box_u32([payload[0], payload[1], payload[2], payload[3]]);
        let width = part2_box_u32([payload[4], payload[5], payload[6], payload[7]]);
        let components = part2_box_u16([payload[8], payload[9]]);
        if width == 0 || height == 0 || components == 0 || payload[11] != 7 {
            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
        } else if width > crate::limits::resource_width_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Width,
                limit: crate::limits::resource_width_limit(limits) as u64, actual: width as u64 })
        } else if height > crate::limits::resource_height_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Height,
                limit: crate::limits::resource_height_limit(limits) as u64, actual: height as u64 })
        } else if components > crate::limits::resource_component_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Components,
                limit: crate::limits::resource_component_limit(limits) as u64, actual: components as u64 })
        } else {
            let pixels = width as nat * height as nat;
            if pixels > u64::MAX as nat {
                Err(crate::DecodeError::MalformedInput { offset: base, kind: crate::MalformedKind::ArithmeticOverflow })
            } else if pixels > crate::limits::resource_pixel_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Pixels,
                    limit: crate::limits::resource_pixel_limit(limits), actual: pixels as u64 })
            } else {
                match part2_container_bit_depth(payload[10], base) {
                    Err(error) => Err(error),
                    Ok(bit_depth) => {
                        if payload[12] > 1 || payload[13] > 1 {
                            Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents))
                        } else {
                            Ok(crate::jp2::ImageHeader {
                                width, height, components, bit_depth,
                                unknown_color_space: payload[12] == 1, intellectual_property: payload[13] == 1,
                            })
                        }
                    },
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_bpcc_prefix(input: Part2BoxReference, base: u64, count: nat)
    -> Result<(), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(()) }
    else {
        match part2_bpcc_prefix(input, base, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => match part2_container_bit_depth(input.1[count - 1], base) {
                Err(error) => Err(error),
                Ok(crate::jp2::ComponentBitDepth::Variable) =>
                    Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents)),
                Ok(_) => Ok(()),
            },
        }
    }
}

pub open spec fn part2_validate_bpcc(input: Part2BoxReference, image: crate::jp2::ImageHeader, base: u64)
    -> Result<(), crate::DecodeError>
{
    if input.1.len() != image.components as nat {
        Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxLength))
    } else { part2_bpcc_prefix(input, base, input.1.len()) }
}

pub(crate) proof fn part2_bpcc_step(input: Part2BoxReference, base: u64, count: nat)
    ensures part2_bpcc_prefix(input, base, count + 1)
        == match part2_bpcc_prefix(input, base, count) {
            Err(error) => Err(error),
            Ok(()) => match part2_container_bit_depth(input.1[count as int], base) {
                Err(error) => Err(error),
                Ok(crate::jp2::ComponentBitDepth::Variable) =>
                    Err(part2_image_box_error(base, input.0, crate::MalformedKind::InvalidBoxContents)),
                Ok(_) => Ok(()),
            },
        },
{
    reveal(part2_bpcc_prefix);
}

pub(crate) proof fn part2_bpcc_error(input: Part2BoxReference, base: u64, count: nat, total: nat)
    requires count <= total,
    ensures match part2_bpcc_prefix(input, base, count) {
        Err(error) => part2_bpcc_prefix(input, base, total) == Err(error), Ok(()) => true,
    },
    decreases total - count,
{
    reveal(part2_bpcc_prefix);
    if count < total { part2_bpcc_error(input, base, count, (total - 1) as nat); }
}

}
