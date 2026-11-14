//! Distinct outer fresh inspection capacities, never child codestream Parse events.
use super::*;
use crate::allocation::InspectionCollection;
verus! {

pub(crate) open spec fn part2_inspection_capacity(collection: InspectionCollection, count: usize,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<()> {
    if count == 0 { Some((Ok(()), events)) } else if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipSnapshotEvent::InspectionCapacity { collection: actual, elements, succeeded } =>
                if actual != collection || elements != count { None } else {
                    Some((if succeeded { Ok(()) } else { Err(crate::DecodeError::AllocationFailed) }, events.drop_first()))
                },
            _ => None,
        }
    }
}
pub(crate) open spec fn part2_inspection_capacity_calls(collection: InspectionCollection, count: usize) -> Seq<Part2JpipSnapshotEvent> {
    if count == 0 { Seq::empty() } else {
        seq![Part2JpipSnapshotEvent::InspectionCapacity { collection, elements: count, succeeded: true }]
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_inspection_capacity_result(collection: InspectionCollection, count: usize,
    result: Result<(), crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_inspection_capacity(collection, count, events), result)
}
pub(crate) proof fn part2_inspection_capacity_observed(collection: InspectionCollection, count: usize, result: Result<(), crate::DecodeError>)
    requires result == Ok(()) || (count > 0 && result == Err(crate::DecodeError::AllocationFailed)),
    ensures part2_inspection_capacity_result(collection, count, result),
{
    reveal(part2_inspection_capacity_result);
    let calls = if count == 0 { Seq::empty() } else {
        seq![Part2JpipSnapshotEvent::InspectionCapacity { collection, elements: count, succeeded: result.is_ok() }]
    };
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| part2_inspection_capacity(collection, count, calls + tail) == Some((result, tail)) by {
        if count == 0 { assert(calls + tail =~= tail); }
        else { assert((calls + tail).drop_first() =~= tail); }
    }
    assert(part2_cold_prefix(|events| part2_inspection_capacity(collection, count, events), calls, result));
}
pub(crate) proof fn part2_inspection_capacity_normal(collection: InspectionCollection, count: usize, tail: Seq<Part2JpipSnapshotEvent>)
    ensures part2_inspection_capacity_result(collection, count, Ok(())),
        part2_cold_framed(|events| part2_inspection_capacity(collection, count, events), Ok(())),
        part2_inspection_capacity(collection, count, part2_inspection_capacity_calls(collection, count) + tail) == Some((Ok(()), tail)),
{
    reveal(part2_inspection_capacity_result);
    part2_inspection_capacity_observed(collection, count, Ok(()));
    if count == 0 { assert(Seq::<Part2JpipSnapshotEvent>::empty() + tail =~= tail); }
    else { assert((part2_inspection_capacity_calls(collection, count) + tail).drop_first() =~= tail); }
}
pub(crate) proof fn part2_inspection_capacity_frames(collection: InspectionCollection, count: usize, result: Result<(), crate::DecodeError>)
    requires part2_inspection_capacity_result(collection, count, result),
    ensures part2_cold_framed(|events| part2_inspection_capacity(collection, count, events), result),
{
    reveal(part2_inspection_capacity_result);
}

pub(crate) open spec fn part2_inspect_file_cold_run(input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>,
    maximum_frames: u32, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2JpxInspection> {
    part2_jpip_snapshot_bind(part2_inspection_capacity(InspectionCollection::Layers,
        part2_inspection_layer_count(input) as usize, events),
        |_: (), rest| Some((part2_inspect_jpx_file(input, geometries, maximum_frames), rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_inspect_file_cold_result(input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>,
    maximum_frames: u32, result: Result<Part2JpxInspection, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_inspect_file_cold_run(input, geometries, maximum_frames, events), result)
}
pub(crate) proof fn part2_inspect_file_cold_frames(input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>,
    maximum_frames: u32, result: Result<Part2JpxInspection, crate::DecodeError>)
    requires part2_inspect_file_cold_result(input, geometries, maximum_frames, result),
    ensures part2_cold_framed(|events| part2_inspect_file_cold_run(input, geometries, maximum_frames, events), result),
{
    reveal(part2_inspect_file_cold_result);
}
pub(crate) proof fn part2_inspect_file_cold_normal(input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>, maximum_frames: u32)
    ensures part2_inspect_file_cold_result(input, geometries, maximum_frames, part2_inspect_jpx_file(input, geometries, maximum_frames)),
        part2_cold_framed(|events| part2_inspect_file_cold_run(input, geometries, maximum_frames, events), part2_inspect_jpx_file(input, geometries, maximum_frames)),
{
    reveal(part2_inspect_file_cold_result);
    let count = part2_inspection_layer_count(input) as usize;
    part2_inspection_capacity_normal(InspectionCollection::Layers, count, Seq::empty());
    part2_cold_pure(part2_inspect_jpx_file(input, geometries, maximum_frames));
    part2_cold_bind(|events| part2_inspection_capacity(InspectionCollection::Layers, count, events),
        |_: (), rest| Some((part2_inspect_jpx_file(input, geometries, maximum_frames), rest)),
        Ok(()), part2_inspect_jpx_file(input, geometries, maximum_frames));
}
pub(crate) proof fn part2_inspect_file_capacity_refused(input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>,
    maximum_frames: u32, error: crate::DecodeError)
    requires part2_inspection_capacity_result(InspectionCollection::Layers, part2_inspection_layer_count(input) as usize, Err(error)),
    ensures part2_inspect_file_cold_result(input, geometries, maximum_frames, Err(error)),
{
    reveal(part2_inspect_file_cold_result);
    let count = part2_inspection_layer_count(input) as usize;
    part2_inspection_capacity_frames(InspectionCollection::Layers, count, Err(error));
    part2_cold_bind(|events| part2_inspection_capacity(InspectionCollection::Layers, count, events),
        |_: (), rest| Some((part2_inspect_jpx_file(input, geometries, maximum_frames), rest)), Err(error), Err(error));
}

}
