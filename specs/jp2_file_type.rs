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
pub open spec fn part2_file_type_preflight(input: Part2BoxReference, maximum_brands: u32)
    -> Result<(u64, usize), crate::DecodeError>
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
                    Ok((offset, count as usize))
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_parse_file_type(input: Part2BoxReference, maximum_brands: u32)
    -> Result<Part2FileType, crate::DecodeError>
{
    match part2_file_type_preflight(input, maximum_brands) {
        Err(error) => Err(error),
        Ok((offset, count)) => match part2_file_type_brands_prefix(input.1, offset, count as nat) {
            Err(error) => Err(error),
            Ok(brands) => Ok((crate::jp2::box_type_from_bytes_model(
                [input.1[0], input.1[1], input.1[2], input.1[3]]),
                part2_box_u32([input.1[4], input.1[5], input.1[6], input.1[7]]), brands)),
        },
    }
}

pub open spec fn part2_validate_file_type_profile(input: Part2FileType, offset: u64)
    -> Result<(), crate::DecodeError>
{
    if input.0 == crate::jp2::BoxType::JP2_BRAND && part2_file_type_jpx(input)
        && !input.2.contains(crate::jp2::BoxType::JP2_BRAND) {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidFileType })
    } else if !part2_file_type_compatible(input, crate::jp2::BoxType::JPH_BRAND) { Ok(()) }
    else if !valid_jph_branding(input.0 == crate::jp2::BoxType::JPH_BRAND, input.1 as nat, input.2.len(),
        input.2.len() == 1 && input.2[0] == crate::jp2::BoxType::JPH_BRAND) {
        Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::InvalidProfile })
    } else { Ok(()) }
}

#[verifier::opaque]
pub open spec fn part2_container_file_type_prefix(input: Seq<u8>, limits: crate::ResourceLimits)
    -> Result<(Part2BoxReference, Part2BoxReaderState), crate::DecodeError>
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
                                    Ok((file_type_box, second.1))
                                }
                            },
                        }
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_container_prologue(input: Seq<u8>, limits: crate::ResourceLimits)
    -> Result<(Part2FileType, Part2BoxReaderState), crate::DecodeError>
{
    match part2_container_file_type_prefix(input, limits) {
        Err(error) => Err(error),
        Ok((file_type_box, reader)) => match part2_parse_file_type(file_type_box,
            crate::limits::resource_compatible_brand_limit(&limits)) {
            Err(error) => Err(error),
            Ok(file_type) => match part2_validate_file_type_profile(file_type, file_type_box.0.1) {
                Err(error) => Err(error),
                Ok(()) => if !part2_file_type_compatible(file_type, crate::jp2::BoxType::JP2_BRAND)
                    && !part2_file_type_jpx(file_type)
                    && !part2_file_type_compatible(file_type, crate::jp2::BoxType::JPH_BRAND) {
                    Err(crate::DecodeError::UnsupportedProfile {
                        feature: "unrecognized JPEG 2000 file brand" })
                } else { Ok((file_type, reader)) },
            },
        },
    }
}

pub(crate) open spec fn part2_file_type_cold_run(
    input: Part2BoxReference, maximum: u32, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2FileType> {
    match part2_file_type_preflight(input, maximum) {
        Err(error) => Some((Err(error), events)),
        Ok((_, count)) => part2_jpip_snapshot_bind(
            part2_inspection_capacity(crate::allocation::InspectionCollection::FileTypeBrands, count, events),
            |_: (), rest| Some((part2_parse_file_type(input, maximum), rest))),
    }
}

pub(crate) open spec fn part2_file_type_cold_calls(
    input: Part2BoxReference, maximum: u32,
) -> Seq<Part2JpipSnapshotEvent> {
    match part2_file_type_preflight(input, maximum) {
        Err(_) => Seq::empty(),
        Ok((_, count)) => part2_inspection_capacity_calls(
            crate::allocation::InspectionCollection::FileTypeBrands, count),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_file_type_cold_result(
    input: Part2BoxReference, maximum: u32, result: Result<Part2FileType, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_file_type_cold_run(input, maximum, events), result)
}

pub(crate) proof fn part2_file_type_cold_normal(
    input: Part2BoxReference, maximum: u32, tail: Seq<Part2JpipSnapshotEvent>,
)
    ensures part2_file_type_cold_result(input, maximum, part2_parse_file_type(input, maximum)),
        part2_file_type_cold_run(input, maximum, part2_file_type_cold_calls(input, maximum) + tail)
            == Some((part2_parse_file_type(input, maximum), tail)),
{
    reveal(part2_file_type_preflight);
    reveal(part2_parse_file_type);
    reveal(part2_file_type_cold_result);
    match part2_file_type_preflight(input, maximum) {
        Err(error) => { part2_cold_pure::<Part2FileType>(Err(error)); },
        Ok((_, count)) => {
            part2_inspection_capacity_normal(crate::allocation::InspectionCollection::FileTypeBrands, count, tail);
            part2_cold_pure(part2_parse_file_type(input, maximum));
            part2_cold_bind(
                |events| part2_inspection_capacity(crate::allocation::InspectionCollection::FileTypeBrands, count, events),
                |_: (), rest| Some((part2_parse_file_type(input, maximum), rest)),
                Ok(()), part2_parse_file_type(input, maximum));
        },
    }
}

pub(crate) proof fn part2_file_type_cold_refused(
    input: Part2BoxReference, maximum: u32, offset: u64, count: usize, error: crate::DecodeError,
)
    requires part2_file_type_preflight(input, maximum) == Ok((offset, count)),
        part2_inspection_capacity_result(crate::allocation::InspectionCollection::FileTypeBrands, count, Err(error)),
    ensures part2_file_type_cold_result(input, maximum, Err(error)),
{
    reveal(part2_file_type_cold_result);
    part2_inspection_capacity_frames(crate::allocation::InspectionCollection::FileTypeBrands, count, Err(error));
    part2_cold_bind(
        |events| part2_inspection_capacity(crate::allocation::InspectionCollection::FileTypeBrands, count, events),
        |_: (), rest| Some((part2_parse_file_type(input, maximum), rest)), Err(error), Err(error));
}

pub(crate) open spec fn part2_parse_container_cold_run(
    input: Seq<u8>, limits: crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawJp2File> {
    match part2_container_file_type_prefix(input, limits) {
        Err(error) => Some((Err(error), events)),
        Ok((file_type_box, _)) => part2_jpip_snapshot_bind(
            part2_file_type_cold_run(file_type_box, crate::limits::resource_compatible_brand_limit(&limits), events),
            |_: Part2FileType, rest| part2_parse_container_after_file_type_run(input, limits, rest)),
    }
}

pub(crate) open spec fn part2_parse_container_cold_calls(
    input: Seq<u8>, limits: crate::ResourceLimits,
) -> Seq<Part2JpipSnapshotEvent> {
    match part2_container_file_type_prefix(input, limits) {
        Err(_) => Seq::empty(),
        Ok((file_type_box, _)) => part2_file_type_cold_calls(
            file_type_box, crate::limits::resource_compatible_brand_limit(&limits))
            + part2_parse_container_after_file_type_calls(input, limits),
    }
}

#[verifier::opaque]
pub closed spec fn part2_parse_container_cold_result(
    input: Seq<u8>, limits: crate::ResourceLimits, result: Result<Part2RawJp2File, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_parse_container_cold_run(input, limits, events), result)
}

pub(crate) proof fn part2_parse_container_cold_frames(
    input: Seq<u8>, limits: crate::ResourceLimits, result: Result<Part2RawJp2File, crate::DecodeError>,
)
    requires part2_parse_container_cold_result(input, limits, result),
    ensures part2_cold_framed(|events| part2_parse_container_cold_run(input, limits, events), result),
{
    reveal(part2_parse_container_cold_result);
}

pub(crate) proof fn part2_parse_container_cold_observed(
    input: Seq<u8>, limits: crate::ResourceLimits, result: Result<Part2RawJp2File, crate::DecodeError>,
)
    requires part2_cold_framed(|events| part2_parse_container_cold_run(input, limits, events), result),
    ensures part2_parse_container_cold_result(input, limits, result),
{
    reveal(part2_parse_container_cold_result);
}

pub(crate) proof fn part2_parse_container_cold_normal(
    input: Seq<u8>, limits: crate::ResourceLimits, tail: Seq<Part2JpipSnapshotEvent>,
)
    ensures part2_parse_container_cold_result(input, limits, part2_parse_container(input, limits)),
        part2_parse_container_cold_run(input, limits, part2_parse_container_cold_calls(input, limits) + tail)
            == Some((part2_parse_container(input, limits), tail)),
{
    reveal(part2_parse_container);
    reveal(part2_container_prologue);
    reveal(part2_parse_container_cold_result);
    match part2_container_file_type_prefix(input, limits) {
        Err(error) => { part2_cold_pure::<Part2RawJp2File>(Err(error)); },
        Ok((file_type_box, _)) => {
            let maximum = crate::limits::resource_compatible_brand_limit(&limits);
            let rest = part2_parse_container_after_file_type_calls(input, limits);
            let continue_run = |_: Part2FileType, rest|
                part2_parse_container_after_file_type_run(input, limits, rest);
            part2_file_type_cold_normal(file_type_box, maximum, rest + tail);
            reveal(part2_file_type_cold_result);
            if let Ok(value) = part2_parse_file_type(file_type_box, maximum) {
                part2_parse_container_after_file_type_normal(input, limits, tail);
                part2_cold_framed_extensional(
                    |events| part2_parse_container_after_file_type_run(input, limits, events),
                    |events| continue_run(value, events), part2_parse_container(input, limits));
            }
            assert((part2_file_type_cold_calls(file_type_box, maximum) + rest) + tail
                =~= part2_file_type_cold_calls(file_type_box, maximum) + (rest + tail));
            part2_cold_bind(
                |events| part2_file_type_cold_run(file_type_box, maximum, events),
                continue_run,
                part2_parse_file_type(file_type_box, maximum), part2_parse_container(input, limits));
        },
    }
}

pub(crate) proof fn part2_parse_container_cold_file_type_error(
    input: Seq<u8>, limits: crate::ResourceLimits,
    file_type_box: Part2BoxReference, reader: Part2BoxReaderState, error: crate::DecodeError,
)
    requires part2_container_file_type_prefix(input, limits) == Ok((file_type_box, reader)),
        part2_file_type_cold_result(file_type_box, crate::limits::resource_compatible_brand_limit(&limits), Err(error)),
    ensures part2_parse_container_cold_result(input, limits, Err(error)),
{
    reveal(part2_parse_container_cold_result);
    reveal(part2_file_type_cold_result);
    let maximum = crate::limits::resource_compatible_brand_limit(&limits);
    part2_cold_bind(
        |events| part2_file_type_cold_run(file_type_box, maximum, events),
        |_: Part2FileType, rest| part2_parse_container_after_file_type_run(input, limits, rest), Err(error), Err(error));
}

pub(crate) proof fn part2_parse_container_cold_start(
    input: Seq<u8>, limits: crate::ResourceLimits, file_type: Part2FileType, reader: Part2BoxReaderState,
) -> (prefix: Seq<Part2JpipSnapshotEvent>)
    requires part2_container_prologue(input, limits) == Ok((file_type, reader)),
    ensures forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input, limits, prefix + tail)
            == part2_container_boxes_cold_run(input, reader, part2_container_initial_state(), file_type, limits, tail),
{
    reveal(part2_container_prologue);
    let source = part2_container_file_type_prefix(input, limits)->Ok_0;
    let maximum = crate::limits::resource_compatible_brand_limit(&limits);
    let prefix = part2_file_type_cold_calls(source.0, maximum);
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input, limits, prefix + tail)
            == part2_container_boxes_cold_run(input, reader, part2_container_initial_state(), file_type, limits, tail) by {
        part2_file_type_cold_normal(source.0, maximum, tail);
    }
    prefix
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
