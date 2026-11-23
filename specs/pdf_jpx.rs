//! Bounded single-image JPX reader requirements for the PDF embedding profile.
use super::*;
verus! {

pub(crate) open spec fn part2_pdf_rreq_error(offset: u64) -> crate::DecodeError {
    part2_container_error(offset, crate::MalformedKind::InvalidBoxContents)
}

pub(crate) open spec fn part2_pdf_rreq_unsupported() -> crate::DecodeError {
    crate::DecodeError::UnsupportedFeature {
        feature: "JPX reader requirements or composition for PDF image embedding",
    }
}

pub(crate) open spec fn part2_pdf_rreq_word(bytes: Seq<u8>, position: usize, width: usize, offset: u64)
    -> Result<(u64, usize), crate::DecodeError> {
    let end = position as int + width as int;
    if end > usize::MAX || end > bytes.len() {
        Err(part2_pdf_rreq_error(offset))
    } else {
        let p = position as int;
        match width {
            1 => Ok((bytes[p] as u64, end as usize)),
            2 => Ok((part2_box_u16([bytes[p], bytes[p+1]]) as u64, end as usize)),
            4 => Ok((part2_box_u32([bytes[p], bytes[p+1], bytes[p+2], bytes[p+3]]) as u64, end as usize)),
            8 => Ok((part2_box_u64([bytes[p], bytes[p+1], bytes[p+2], bytes[p+3],
                bytes[p+4], bytes[p+5], bytes[p+6], bytes[p+7]]), end as usize)),
            _ => Err(part2_pdf_rreq_error(offset)),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_pdf_rreq_features(
    bytes: Seq<u8>, offset: u64, width: usize, count: u64, index: u64, position: usize, covered: u64,
) -> Result<(usize, u64), crate::DecodeError>
    decreases count as int - index as int,
{
    if index >= count { Ok((position, covered)) } else {
        match part2_pdf_rreq_word(bytes, position, 2, offset) {
            Err(error) => Err(error), Ok(feature) => match part2_pdf_rreq_word(bytes, feature.1, width, offset) {
                Err(error) => Err(error), Ok(mask) => part2_pdf_rreq_features(bytes, offset, width, count,
                    (index + 1) as u64, mask.1,
                    if feature.0 == 1 || feature.0 == 4 || feature.0 == 5 { covered | mask.0 } else { covered }),
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_pdf_rreq_vendors(
    bytes: Seq<u8>, offset: u64, width: usize, count: u64, index: u64, position: usize,
) -> Result<usize, crate::DecodeError>
    decreases count as int - index as int,
{
    if index >= count { Ok(position) } else if position as int + 16 > usize::MAX || position as int + 16 > bytes.len() {
        Err(part2_pdf_rreq_error(offset))
    } else { match part2_pdf_rreq_word(bytes, (position as int + 16) as usize, width, offset) {
        Err(error) => Err(error),
        Ok(mask) => part2_pdf_rreq_vendors(bytes, offset, width, count, (index+1) as u64, mask.1),
    }}
}

pub(crate) open spec fn part2_pdf_rreq_work(actual: u64, limit: u64) -> Result<(), crate::DecodeError> {
    if actual > limit {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits, limit, actual })
    } else { Ok(()) }
}

pub(crate) open spec fn part2_pdf_rreq_after_features(
    bytes: Seq<u8>, offset: u64, width: usize, limit: u64, full: u64, display: u64, count: u64,
    features: (usize, u64),
) -> Result<(), crate::DecodeError> {
    match part2_pdf_rreq_word(bytes, features.0, 2, offset) {
        Err(error) => Err(error), Ok(vendors) =>
            if count as int + vendors.0 as int > u64::MAX { Err(part2_pdf_rreq_error(offset)) }
            else { match part2_pdf_rreq_work((count as int + vendors.0 as int) as u64, limit) {
                Err(error) => Err(error), Ok(()) =>
                    match part2_pdf_rreq_vendors(bytes, offset, width, vendors.0, 0, vendors.1) {
                        Err(error) => Err(error),
                        Ok(end) => if end != bytes.len() { Err(part2_pdf_rreq_error(offset)) }
                            else if features.1 & full != full || features.1 & display != display {
                                Err(part2_pdf_rreq_unsupported())
                            } else { Ok(()) },
                    },
            }},
    }
}

pub(crate) open spec fn part2_pdf_rreq_value(bytes: Seq<u8>, offset: u64, limit: u64)
    -> Result<(), crate::DecodeError> {
    if bytes.len() == 0 { Err(part2_pdf_rreq_error(offset)) } else {
        let width = bytes[0] as usize;
        if width != 1 && width != 2 && width != 4 && width != 8 { Err(part2_pdf_rreq_error(offset)) } else {
            match part2_pdf_rreq_word(bytes, 1, width, offset) {
                Err(error) => Err(error), Ok(full) => match part2_pdf_rreq_word(bytes, full.1, width, offset) {
                    Err(error) => Err(error), Ok(display) => match part2_pdf_rreq_word(bytes, display.1, 2, offset) {
                        Err(error) => Err(error), Ok(count) => match part2_pdf_rreq_work(count.0, limit) {
                            Err(error) => Err(error), Ok(()) => match part2_pdf_rreq_features(bytes, offset, width, count.0, 0, count.1, 0) {
                                Err(error) => Err(error), Ok(features) => part2_pdf_rreq_after_features(
                                    bytes, offset, width, limit, full.0, display.0, count.0, features),
                            },
                        },
                    },
                },
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_pdf_rreq_box(item: Part2BoxReference, seen: bool, limit: u64)
    -> Result<bool, crate::DecodeError> {
    if item.0.0 == crate::jp2::BoxType::READER_REQUIREMENTS {
        if seen { Err(part2_pdf_rreq_error(item.0.1)) }
        else { match part2_pdf_rreq_value(item.1, item.0.1, limit) {
            Err(error) => Err(error), Ok(()) => Ok(true),
        }}
    } else { Ok(seen) }
}

pub(crate) proof fn part2_pdf_rreq_reader_frame(reader: Part2BoxReaderState)
    ensures part2_box_reader_next_ref(reader).1.limits == reader.limits,
{
    reveal(part2_box_reader_next);
    reveal(part2_box_reader_after_work);
    reveal(part2_box_reader_after_header);
}

#[verifier::opaque]
pub(crate) open spec fn part2_pdf_rreq_scan(reader: Part2BoxReaderState, seen: bool)
    -> Result<(), crate::DecodeError>
    decreases reader.input.len() - reader.position,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => Ok(()), Some(Err(error)) => Err(error),
        Some(Ok(item)) =>
            if next.1.input != reader.input || next.1.position <= reader.position || next.1.position > reader.input.len() {
                Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow))
            } else { match part2_pdf_rreq_box(item, seen, crate::limits::resource_work_limit(&reader.limits)) {
                Err(error) => Err(error), Ok(updated) => part2_pdf_rreq_scan(next.1, updated),
            }},
    }
}

pub(crate) open spec fn part2_pdf_jpx_structure(file: Part2RawJp2File) -> bool {
    file.streams.len() == 1 && file.composition.is_none() && file.layers.len() <= 1
        && (file.layers.len() == 0 || file.layers[0].payload.len() == 0)
        && !(file.streams[0].1.len() >= 8 && file.streams[0].1[6] & 0xc0u8 != 0)
}

pub(crate) open spec fn part2_pdf_jpx_admission(input: Seq<u8>, file: Part2RawJp2File, limits: crate::ResourceLimits)
    -> Result<(), crate::DecodeError> {
    if !part2_pdf_jpx_structure(file) { Err(part2_pdf_rreq_unsupported()) }
    else { part2_pdf_rreq_scan_input(input, limits) }
}

pub(crate) open spec fn part2_pdf_rreq_scan_input(input: Seq<u8>, limits: crate::ResourceLimits)
    -> Result<(), crate::DecodeError> {
    match part2_box_reader_from_input(input, limits) {
        Err(error) => Err(error), Ok(reader) => part2_pdf_rreq_scan(reader, false),
    }
}
}
