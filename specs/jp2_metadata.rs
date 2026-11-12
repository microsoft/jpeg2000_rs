//! Actual recursive raw association inspection and bounded metadata aggregation.

use super::*;

verus! {

#[verifier::opaque]
pub open spec fn part2_inspect_metadata_box(
    input: Part2BoxReference, limits: crate::ResourceLimits, depth: u32, remaining: u32,
) -> Result<(u32, u32), crate::DecodeError>
    decreases remaining, input.1.len(), 1nat,
{
    if depth > crate::limits::resource_box_depth_limit(&limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::BoxDepth,
            limit: crate::limits::resource_box_depth_limit(&limits) as u64, actual: depth as u64 })
    } else if input.0.0 != crate::jp2::BoxType::ASSOCIATION { Ok((1, depth)) }
    else if depth == u32::MAX { Err(part2_palette_arithmetic_error(0)) }
    else {
        match part2_box_reader_from_input(input.1, limits) {
            Err(error) => Err(error),
            Ok(reader) => part2_metadata_children(input, reader, limits, (depth + 1) as u32,
                remaining, 1, depth, input.1.len(), 0),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_metadata_children(
    input: Part2BoxReference, reader: Part2BoxReaderState, limits: crate::ResourceLimits,
    child_depth: u32, remaining: u32, count: u32, maximum: u32, fuel: nat, immediate: usize,
) -> Result<(u32, u32), crate::DecodeError>
    decreases remaining, fuel, 0nat,
{
    let next = part2_box_reader_next_ref(reader);
    match next.0 {
        None => if immediate < 2 {
            Err(crate::DecodeError::MalformedInput { offset: input.0.1, kind: crate::MalformedKind::InvalidBoxContents })
        } else { Ok((count, maximum)) },
        Some(result) => {
            if fuel == 0 {
                Err(crate::DecodeError::MalformedInput { offset: input.0.1, kind: crate::MalformedKind::InvalidBoxLength })
            } else {
                match result {
                    Err(error) => Err(error),
                    Ok(child) => if remaining == 0 { Err(part2_palette_arithmetic_error(0)) }
                    else {
                        match part2_inspect_metadata_box(child, limits, child_depth, (remaining - 1) as u32) {
                            Err(error) => Err(error),
                            Ok(observed) => {
                                if count > u32::MAX - observed.0 { Err(part2_palette_arithmetic_error(0)) }
                                else {
                                    let updated = part2_metadata_count(count, observed.0);
                                    if updated > crate::limits::resource_work_limit(&limits) {
                                        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                                            limit: crate::limits::resource_work_limit(&limits), actual: updated as u64 })
                                    } else if immediate == usize::MAX {
                                        Err(part2_palette_arithmetic_error(0))
                                    } else {
                                        part2_metadata_children(input, next.1, limits, child_depth, remaining,
                                            updated, if maximum >= observed.1 { maximum } else { observed.1 }, (fuel - 1) as nat,
                                            (immediate + 1) as usize)
                                    }
                                }
                            },
                        }
                    },
                }
            }
        },
    }
}

pub(crate) proof fn part2_metadata_start(
    input: Part2BoxReference, reader: Part2BoxReaderState, limits: crate::ResourceLimits, depth: u32, remaining: u32,
)
    requires input.0.0 == crate::jp2::BoxType::ASSOCIATION,
        depth <= crate::limits::resource_box_depth_limit(&limits),
        depth < u32::MAX,
        part2_box_reader_from_input(input.1, limits) == Ok(reader),
    ensures part2_inspect_metadata_box(input, limits, depth, remaining)
        == part2_metadata_children(input, reader, limits, (depth + 1) as u32, remaining, 1, depth, input.1.len(), 0),
{
    reveal_with_fuel(part2_inspect_metadata_box, 2);
    reveal(part2_metadata_children);
}

}
