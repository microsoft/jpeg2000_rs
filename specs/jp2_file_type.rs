//! Actual raw file-type payload decoding, ordered brands and profile admission.

use super::*;

verus! {

pub open spec fn part2_file_type_brand_at(payload: Seq<u8>, index: nat) -> crate::jp2::BoxType {
    let position = 8 + 4 * index;
    crate::jp2::box_type_from_bytes_model([payload[position as int], payload[position as int + 1],
        payload[position as int + 2], payload[position as int + 3]])
}

#[verifier::opaque]
pub open spec fn part2_file_type_brands_prefix(payload: Seq<u8>, offset: u64, count: nat)
    -> Result<Seq<crate::jp2::BoxType>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_file_type_brands_prefix(payload, offset, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let brand = part2_file_type_brand_at(payload, (count - 1) as nat);
                if previous.contains(brand) {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxContents })
                } else { Ok(previous.push(brand)) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_parse_file_type(input: Part2BoxReference, maximum_brands: u32)
    -> Result<Part2FileType, crate::DecodeError>
{
    match part2_box_payload_offset(input.0) {
        Err(error) => Err(error),
        Ok(offset) => {
            let payload = input.1;
            if payload.len() < 8 || payload.len() % 4 != 0 {
                Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxLength })
            } else {
                let count = ((payload.len() - 8) / 4) as nat;
                if count > u64::MAX as nat {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::ArithmeticOverflow })
                } else if count > maximum_brands as nat {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CompatibleBrands,
                        limit: maximum_brands as u64, actual: count as u64 })
                } else {
                    match part2_file_type_brands_prefix(payload, offset, count) {
                        Err(error) => Err(error),
                        Ok(brands) => Ok((crate::jp2::box_type_from_bytes_model(
                            [payload[0], payload[1], payload[2], payload[3]]),
                            part2_box_u32([payload[4], payload[5], payload[6], payload[7]]), brands)),
                    }
                }
            }
        },
    }
}

pub open spec fn part2_validate_file_type_profile(input: Part2FileType, offset: u64)
    -> Result<(), crate::DecodeError>
{
    if input.0 == crate::jp2::BoxType::JP2_BRAND && part2_file_type_jpx(input) {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidFileType })
    } else if !part2_file_type_compatible(input, crate::jp2::BoxType::JPH_BRAND) { Ok(()) }
    else if !valid_jph_branding(input.0 == crate::jp2::BoxType::JPH_BRAND, input.1 as nat, input.2.len(),
        input.2.len() == 1 && input.2[0] == crate::jp2::BoxType::JPH_BRAND) {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidProfile })
    } else { Ok(()) }
}

#[verifier::opaque]
pub open spec fn part2_container_prologue(input: Seq<u8>, limits: crate::ResourceLimits)
    -> Result<(Part2FileType, Part2BoxReaderState), crate::DecodeError>
{
    match part2_box_reader_from_input(input, limits) {
        Err(error) => Err(error),
        Ok(reader) => {
            let first = part2_box_reader_required(reader, 0);
            match first.0 {
                Err(error) => Err(error),
                Ok(signature) => {
                    if signature.0.0 != crate::jp2::BoxType::SIGNATURE || signature.0.3 != 12
                        || signature.1 != seq![0x0du8, 0x0au8, 0x87u8, 0x0au8] {
                        Err(crate::DecodeError::MalformedInput {
                            offset: signature.0.1, kind: crate::MalformedKind::InvalidSignature })
                    } else {
                        let second = part2_box_reader_required(first.1, 1);
                        match second.0 {
                            Err(error) => Err(error),
                            Ok(file_type_box) => {
                                if file_type_box.0.0 != crate::jp2::BoxType::FILE_TYPE {
                                    Err(crate::DecodeError::MalformedInput {
                                        offset: file_type_box.0.1, kind: crate::MalformedKind::InvalidBoxOrder })
                                } else {
                                    match part2_parse_file_type(file_type_box,
                                        crate::limits::resource_compatible_brand_limit(&limits)) {
                                        Err(error) => Err(error),
                                        Ok(file_type) => match part2_validate_file_type_profile(file_type, file_type_box.0.1) {
                                            Err(error) => Err(error),
                                            Ok(()) => {
                                                if !part2_file_type_compatible(file_type, crate::jp2::BoxType::JP2_BRAND)
                                                    && !part2_file_type_jpx(file_type)
                                                    && !part2_file_type_compatible(file_type, crate::jp2::BoxType::JPH_BRAND) {
                                                    Err(crate::DecodeError::UnsupportedProfile {
                                                        feature: "unrecognized JPEG 2000 file brand" })
                                                } else { Ok((file_type, second.1)) }
                                            },
                                        },
                                    }
                                }
                            },
                        }
                    }
                },
            }
        },
    }
}

pub(crate) proof fn part2_file_type_brands_step(payload: Seq<u8>, offset: u64, count: nat)
    ensures part2_file_type_brands_prefix(payload, offset, count + 1)
        == match part2_file_type_brands_prefix(payload, offset, count) {
            Err(error) => Err(error),
            Ok(previous) => {
                let brand = part2_file_type_brand_at(payload, count);
                if previous.contains(brand) {
                    Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidBoxContents })
                } else { Ok(previous.push(brand)) }
            },
        },
{
    reveal(part2_file_type_brands_prefix);
}

pub(crate) proof fn part2_file_type_brands_error(payload: Seq<u8>, offset: u64, count: nat, total: nat)
    requires count <= total,
    ensures match part2_file_type_brands_prefix(payload, offset, count) {
        Err(error) => part2_file_type_brands_prefix(payload, offset, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_file_type_brands_prefix);
    if count < total { part2_file_type_brands_error(payload, offset, count, (total - 1) as nat); }
}

}
