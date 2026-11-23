use super::{BoxReader, BoxType, DecodeError, Jp2File, MalformedKind, Resource, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_error(offset),
))]
fn invalid(offset: u64) -> DecodeError {
    DecodeError::malformed(offset, MalformedKind::InvalidBoxContents)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_unsupported(),
))]
fn unsupported() -> DecodeError {
    DecodeError::UnsupportedFeature {
        feature: "JPX reader requirements or composition for PDF image embedding",
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_word(bytes@, position, width, offset),
))]
fn word(
    bytes: &[u8],
    position: usize,
    width: usize,
    offset: u64,
) -> Result<(u64, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_pdf_rreq_word); }
    let end = match position.checked_add(width) {
        Some(end) => end,
        None => return Err(invalid(offset)),
    };
    let data = match bytes.get(position..end) {
        Some(data) => data,
        None => return Err(invalid(offset)),
    };
    let value = match width {
        1 => u64::from(data[0]),
        2 => u64::from(super::read_u16([data[0], data[1]])),
        4 => u64::from(super::read_u32([data[0], data[1], data[2], data[3]])),
        8 => super::box_reader::read_u64([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]),
        _ => return Err(invalid(offset)),
    };
    Ok((value, end))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_features(bytes@, offset, width, count, 0, start, 0),
))]
fn features(
    bytes: &[u8],
    offset: u64,
    width: usize,
    count: u64,
    start: usize,
) -> Result<(usize, u64), DecodeError> {
    let mut position = start;
    let mut index = 0_u64;
    let mut covered = 0_u64;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count,
            crate::specs::part2_pdf_rreq_features(bytes@, offset, width, count, 0, start, 0)
                == crate::specs::part2_pdf_rreq_features(bytes@, offset, width, count, index, position, covered),
        decreases count - index,
    ))]
    while index < count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_pdf_rreq_features, 1); }
        let (feature, next) = word(bytes, position, 2, offset)?;
        let (mask, next) = word(bytes, next, width, offset)?;
        if matches!(feature, 1 | 4 | 5) {
            covered |= mask;
        }
        position = next;
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_pdf_rreq_features, 1); }
    Ok((position, covered))
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_vendors(bytes@, offset, width, count, 0, start),
))]
fn vendors(
    bytes: &[u8],
    offset: u64,
    width: usize,
    count: u64,
    start: usize,
) -> Result<usize, DecodeError> {
    let mut position = start;
    let mut index = 0_u64;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count,
            crate::specs::part2_pdf_rreq_vendors(bytes@, offset, width, count, 0, start)
                == crate::specs::part2_pdf_rreq_vendors(bytes@, offset, width, count, index, position),
        decreases count - index,
    ))]
    while index < count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_pdf_rreq_vendors, 1); }
        let uuid_end = match position.checked_add(16) {
            Some(end) => end,
            None => return Err(invalid(offset)),
        };
        if bytes.get(position..uuid_end).is_none() {
            return Err(invalid(offset));
        }
        let (_, next) = word(bytes, uuid_end, width, offset)?;
        position = next;
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_pdf_rreq_vendors, 1); }
    Ok(position)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_work(actual, limit),
))]
fn admit_work(actual: u64, limit: u64) -> Result<(), DecodeError> {
    if actual > limit {
        Err(DecodeError::LimitExceeded {
            resource: Resource::WorkUnits,
            limit,
            actual,
        })
    } else {
        Ok(())
    }
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_value(bytes@, offset,
        crate::limits::resource_work_limit(limits)),
))]
fn requirements(bytes: &[u8], offset: u64, limits: &ResourceLimits) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_pdf_rreq_value);
        reveal(crate::specs::part2_pdf_rreq_after_features);
    }
    let width = match bytes.first() {
        Some(width) => usize::from(*width),
        None => return Err(invalid(offset)),
    };
    if !matches!(width, 1 | 2 | 4 | 8) {
        return Err(invalid(offset));
    }
    let (full, position) = word(bytes, 1, width, offset)?;
    let (display, position) = word(bytes, position, width, offset)?;
    let (count, position) = word(bytes, position, 2, offset)?;
    admit_work(count, limits.maximum_work_units())?;
    let (position, covered) = features(bytes, offset, width, count, position)?;
    let (vendor_count, position) = word(bytes, position, 2, offset)?;
    let work = match count.checked_add(vendor_count) {
        Some(work) => work,
        None => return Err(invalid(offset)),
    };
    admit_work(work, limits.maximum_work_units())?;
    let position = vendors(bytes, offset, width, vendor_count, position)?;
    if position != bytes.len() {
        return Err(invalid(offset));
    }
    if covered & full != full || covered & display != display {
        return Err(unsupported());
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_jpx_admission(input@,
        super::raw_jp2_file_view(file), *limits),
))]
pub(crate) fn validate(
    input: &[u8],
    file: &Jp2File<'_>,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        super::raw_render_file_known(file);
        reveal(super::raw_jp2_file_view);
        reveal(crate::specs::part2_pdf_jpx_admission);
        reveal(crate::specs::part2_pdf_jpx_structure);
    }
    if file.codestreams.len() != 1
        || file.composition.is_some()
        || file.compositing_layers.len() > 1
        || (!file.compositing_layers.is_empty() && !file.compositing_layers[0].payload.is_empty())
    {
        return Err(unsupported());
    }
    let stream = file.codestreams[0].data();
    if stream.len() >= 8 && stream[6] & 0xc0 != 0 {
        return Err(unsupported());
    }
    scan(input, limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_box(super::box_reference_view(item), seen,
        crate::limits::resource_work_limit(limits)),
))]
fn check_box(
    item: super::BoxRef<'_>,
    seen: bool,
    limits: &ResourceLimits,
) -> Result<bool, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_pdf_rreq_box); }
    if item.header.box_type().equals(BoxType::READER_REQUIREMENTS) {
        if seen {
            return Err(invalid(item.header.offset()));
        }
        requirements(item.payload, item.header.offset(), limits)?;
        Ok(true)
    } else {
        Ok(seen)
    }
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_pdf_rreq_scan_input(input@, *limits),
))]
fn scan(input: &[u8], limits: &ResourceLimits) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_pdf_rreq_scan_input); }
    let mut reader = BoxReader::new(input, limits)?;
    let mut seen = false;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant super::box_reader_state(&reader).input == input@,
            super::box_reader_state(&reader).limits == *limits,
            super::box_reader_state(&reader).position <= input.len(),
            crate::specs::part2_pdf_rreq_scan_input(input@, *limits)
                == crate::specs::part2_pdf_rreq_scan(super::box_reader_state(&reader), seen),
        decreases input.len() - super::box_reader_state(&reader).position,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part2_pdf_rreq_scan, 1);
            crate::specs::part2_dimension_box_progress(super::box_reader_state(&reader));
            crate::specs::part2_pdf_rreq_reader_frame(super::box_reader_state(&reader));
        }
        let Some(next) = reader.next_box_ref() else {
            return Ok(());
        };
        let item = next?;
        seen = check_box(item, seen, limits)?;
    }
}
