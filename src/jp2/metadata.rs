//! Bounded nested metadata inspection and resolution metadata parsing.

use super::{
    BoxRef, BoxType, DecodeError, MalformedKind, Resolution, Resource, ResourceLimits, add_offset,
    box_reader_from_input, read_u16, rebase_error,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_inspect_metadata_box(
        super::box_reference_view(box_ref), *limits, depth, remaining_depth),
    decreases remaining_depth,
))]
pub(super) fn inspect_metadata_box(
    box_ref: BoxRef<'_>,
    limits: &ResourceLimits,
    depth: u32,
    remaining_depth: u32,
) -> Result<(u32, u32), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_inspect_metadata_box); }
    if depth > limits.maximum_box_depth() {
        return Err(DecodeError::limit(
            Resource::BoxDepth,
            u64::from(limits.maximum_box_depth()),
            u64::from(depth),
        ));
    }
    if !box_ref.header.box_type().equals(BoxType::ASSOCIATION) {
        return Ok((1, depth));
    }
    let child_depth = depth.checked_add(1).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_palette_arithmetic_error(0),
            ))]
        || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
    )?;
    let mut reader = box_reader_from_input(box_ref.payload, limits)?;
    let mut count = 1_u32;
    let mut maximum_depth = depth;
    let mut remaining_boxes = box_ref.payload.len();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost expected = crate::specs::part2_inspect_metadata_box(
    super::box_reference_view(box_ref), *limits, depth, remaining_depth); }
    #[cfg(verus_keep_ghost)]
    proof! {
    crate::specs::part2_metadata_start(super::box_reference_view(box_ref),
        super::box_reader_state(&reader), *limits, depth, remaining_depth);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
    invariant_except_break expected == crate::specs::part2_metadata_children(
            super::box_reference_view(box_ref), super::box_reader_state(&reader), *limits,
            child_depth, remaining_depth, count, maximum_depth, remaining_boxes as nat),
            expected == crate::specs::part2_inspect_metadata_box(
                super::box_reference_view(box_ref), *limits, depth, remaining_depth),
            depth < u32::MAX,
            child_depth == depth as nat + 1,
            depth <= crate::limits::resource_box_depth_limit(limits),
            super::box_reference_view(box_ref).0.0 == BoxType::ASSOCIATION,
        ensures expected == Ok((count, maximum_depth)),
        decreases remaining_boxes,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_metadata_children);
            reveal(crate::specs::part2_inspect_metadata_box);
        }
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if remaining_boxes == 0 {
            return Err(DecodeError::malformed(
                box_ref.header.offset(),
                MalformedKind::InvalidBoxLength,
            ));
        }
        remaining_boxes -= 1;
        let child = next?;
        let child_remaining = remaining_depth.checked_sub(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_palette_arithmetic_error(0),
                ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
        let (child_count, observed_depth) =
            inspect_metadata_box(child, limits, child_depth, child_remaining)?;
        if count > u32::MAX - child_count {
            return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow));
        }
        count = crate::refinement::metadata_count(count, child_count);
        if u64::from(count) > limits.maximum_work_units() {
            return Err(DecodeError::limit(
                Resource::WorkUnits,
                limits.maximum_work_units(),
                u64::from(count),
            ));
        }
        maximum_depth = maximum_depth.max(observed_depth);
    }
    Ok((count, maximum_depth))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::metadata_bytes_outcome(result) == crate::specs::part2_copy_metadata_bytes(input@),
))]
pub(super) fn copy_bytes(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    let mut output = Vec::with_capacity(input.len());
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= input.len(),
                output@ == input@.take(index as int),
            decreases input.len() - index,
        )
    )]
    while index < input.len() {
        output.push(
            *input
                .get(index)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        );
        index = index
            .checked_add(1)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= input@); }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_parse_resolution_superbox(payload@, *limits, base_offset),
))]
pub(super) fn parse_resolution_superbox(
    payload: &[u8],
    limits: &ResourceLimits,
    base_offset: u64,
) -> Result<(Option<Resolution>, Option<Resolution>), DecodeError> {
    let mut reader = box_reader_from_input(payload, limits)?;
    let mut capture = None;
    let mut display = None;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost expected = crate::specs::part2_parse_resolution_superbox(payload@, *limits, base_offset);
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant_except_break expected == crate::specs::part2_resolution_boxes(
                payload@, super::box_reader_state(&reader), base_offset, capture, display),
                expected == crate::specs::part2_parse_resolution_superbox(payload@, *limits, base_offset),
            ensures expected == crate::specs::part2_resolution_finish(base_offset, capture, display),
            decreases payload.len() as int - reader.position as int,
        )
    )]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_resolution_boxes); }
        let previous_position = reader.position;
        let Some(next) = reader.next_box_ref() else {
            break;
        };
        if reader.position <= previous_position || reader.position > payload.len() {
            return Err(DecodeError::malformed(
                add_offset(base_offset, previous_position as u64)?,
                MalformedKind::InvalidBoxLength,
            ));
        }
        let box_ref = next.map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_box_rebase_error(error, base_offset),
            ))]
            |error| rebase_error(error, base_offset),
        )?;
        let box_type = box_ref.header.box_type();
        if box_type.equals(BoxType::CAPTURE_RESOLUTION) {
            if capture.is_some() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            capture = Some(parse_resolution(box_ref, base_offset)?);
        } else if box_type.equals(BoxType::DISPLAY_RESOLUTION) {
            if display.is_some() {
                return Err(DecodeError::malformed(
                    add_offset(base_offset, box_ref.header.offset())?,
                    MalformedKind::InvalidBoxOrder,
                ));
            }
            display = Some(parse_resolution(box_ref, base_offset)?);
        }
    }
    if capture.is_none() && display.is_none() {
        return Err(DecodeError::malformed(
            base_offset,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    Ok((capture, display))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_parse_resolution(super::box_reference_view(box_ref), base_offset),
))]
pub(super) fn parse_resolution(
    box_ref: BoxRef<'_>,
    base_offset: u64,
) -> Result<Resolution, DecodeError> {
    if box_ref.payload.len() != 10 {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxLength,
        ));
    }
    let vertical_numerator = read_u16([box_ref.payload[0], box_ref.payload[1]]);
    let vertical_denominator = read_u16([box_ref.payload[2], box_ref.payload[3]]);
    let horizontal_numerator = read_u16([box_ref.payload[4], box_ref.payload[5]]);
    let horizontal_denominator = read_u16([box_ref.payload[6], box_ref.payload[7]]);
    if vertical_numerator == 0
        || vertical_denominator == 0
        || horizontal_numerator == 0
        || horizontal_denominator == 0
    {
        return Err(DecodeError::malformed(
            add_offset(base_offset, box_ref.header.offset())?,
            MalformedKind::InvalidBoxContents,
        ));
    }
    Ok(Resolution {
        vertical_numerator,
        vertical_denominator,
        horizontal_numerator,
        horizontal_denominator,
        vertical_exponent: box_ref.payload[8] as i8,
        horizontal_exponent: box_ref.payload[9] as i8,
    })
}
