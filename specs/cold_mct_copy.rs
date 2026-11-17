//! Ordered deep-copy requests derived from the actual MCT owner and nested path.

use super::*;
use crate::codestream::{MctCopyPath, ResolvedCopyContext, ResolvedCopyPath, ResolvedCopyRole};

verus! {

pub(crate) struct Part1MctCopyRequest {
    pub path: MctCopyPath,
    pub elements: usize,
}

pub(crate) open spec fn part1_mct_copy_site(path: MctCopyPath) -> u8 {
    match path {
        MctCopyPath::Arrays => 16, MctCopyPath::ArrayValues(_) => 17,
        MctCopyPath::Records => 18, MctCopyPath::Collections(_) => 19,
        MctCopyPath::Inputs(_, _) => 20, MctCopyPath::Outputs(_, _) => 21,
        MctCopyPath::Order => 22,
        MctCopyPath::Extensions(path) => part1_part2_copy_site(path),
        MctCopyPath::Resolved(path) => part1_resolved_copy_site(path),
        MctCopyPath::PayloadExtensions(path) => (part1_part2_copy_site(path) + 26) as u8,
        MctCopyPath::FreshMarker(path) => part1_fresh_marker_site(path),
        MctCopyPath::FreshPart2(path) => part1_p2_fresh_site(path),
        MctCopyPath::ProfileWords(_, _, _) => 80,
        MctCopyPath::ProgressionBitmap(_, _, _, _) => 81,
        MctCopyPath::CollectedQuantizations => 83,
        MctCopyPath::CollectedProgression => 84,
    }
}

pub(crate) open spec fn part1_mct_copy_leaf(path: MctCopyPath, count: usize) -> Seq<Part1MctCopyRequest> {
    if count == 0 { Seq::empty() } else { seq![Part1MctCopyRequest { path, elements: count }] }
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_copy_run(
    requests: Seq<Part1MctCopyRequest>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<(), crate::DecodeError>, Seq<Part1ColdStorageEvent>)>
    decreases requests.len(),
{
    if requests.len() == 0 { Some((Ok(()), events)) } else {
        match part1_quantization_storage_request(part1_mct_copy_site(requests[0].path), requests[0].elements, events) {
            None => None,
            Some((Err(error), rest)) => Some((Err(error), rest)),
            Some((Ok(()), rest)) => part1_mct_copy_run(requests.drop_first(), rest),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_copy_result(
    requests: Seq<Part1MctCopyRequest>, result: Result<(), crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(requests, events) == Some((result, Seq::empty()))
}

pub(crate) open spec fn part1_mct_array_copy_requests(array: Part2MctArray, position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::ArrayValues(position), array.4.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_arrays_copy_requests(arrays: Seq<Part2MctArray>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases arrays.len() - position,
{
    if position >= arrays.len() { Seq::empty() } else {
        part1_mct_array_copy_requests(arrays[position as int], position as usize)
            + part1_mct_arrays_copy_requests(arrays, position + 1)
    }
}

pub(crate) open spec fn part1_mct_collection_copy_requests(
    collection: Part1MccCollectionReference, record: usize, position: usize,
) -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Inputs(record, position), collection.inputs.len() as usize)
        + part1_mct_copy_leaf(MctCopyPath::Outputs(record, position), collection.outputs.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_collections_copy_requests(
    collections: Seq<Part1MccCollectionReference>, record: usize, position: nat,
) -> Seq<Part1MctCopyRequest>
    decreases collections.len() - position,
{
    if position >= collections.len() { Seq::empty() } else {
        part1_mct_collection_copy_requests(collections[position as int], record, position as usize)
            + part1_mct_collections_copy_requests(collections, record, position + 1)
    }
}

pub(crate) open spec fn part1_mct_record_copy_requests(record: Part1MctRecord, position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Collections(position), record.1.len() as usize)
        + part1_mct_collections_copy_requests(record.1, position, 0)
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_records_copy_requests(records: Seq<Part1MctRecord>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases records.len() - position,
{
    if position >= records.len() { Seq::empty() } else {
        part1_mct_record_copy_requests(records[position as int], position as usize)
            + part1_mct_records_copy_requests(records, position + 1)
    }
}

pub(crate) open spec fn part1_mct_owner_copy_requests(
    owner: (Seq<Part2MctArray>, Seq<Part1MctRecord>, Seq<u8>),
) -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Arrays, owner.0.len() as usize)
        + part1_mct_arrays_copy_requests(owner.0, 0)
        + part1_mct_copy_leaf(MctCopyPath::Records, owner.1.len() as usize)
        + part1_mct_records_copy_requests(owner.1, 0)
        + part1_mct_copy_leaf(MctCopyPath::Order, owner.2.len() as usize)
}

pub(crate) open spec fn part1_mct_collection_duplicate_step(
    value: Part2MctCollection, context: ResolvedCopyContext, phase: nat,
) -> Seq<Part1MctCopyRequest> {
    if phase == 0 {
        part1_mct_copy_leaf(MctCopyPath::Resolved(ResolvedCopyPath::Inputs(context)), value.1.len() as usize)
    } else if phase == 1 {
        part1_mct_copy_leaf(MctCopyPath::Resolved(ResolvedCopyPath::Outputs(context)), value.2.len() as usize)
    } else if phase == 2 {
        match value.4 {
            None => Seq::empty(),
            Some(array) => part1_mct_copy_leaf(
                MctCopyPath::Resolved(ResolvedCopyPath::Matrix(context, array.0)), array.4.len() as usize),
        }
    } else if phase == 3 {
        match value.5 {
            None => Seq::empty(),
            Some(array) => part1_mct_copy_leaf(
                MctCopyPath::Resolved(ResolvedCopyPath::Offsets(context, array.0)), array.4.len() as usize),
        }
    } else { Seq::empty() }
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_collection_duplicate_tail(
    value: Part2MctCollection, context: ResolvedCopyContext, phase: nat,
) -> Seq<Part1MctCopyRequest>
    decreases if phase < 4 { 4 - phase } else { 0int },
{
    if phase >= 4 { Seq::empty() } else {
        part1_mct_collection_duplicate_step(value, context, phase)
            + part1_mct_collection_duplicate_tail(value, context, phase + 1)
    }
}

pub(crate) proof fn part1_mct_collection_duplicate_advance(
    value: Part2MctCollection, context: ResolvedCopyContext, phase: nat,
    done: Seq<Part1MctCopyRequest>, response: Result<(), crate::DecodeError>,
) -> (after: Seq<Part1MctCopyRequest>)
    requires phase < 4, part1_mct_copy_result(done, Ok(())),
        part1_mct_collection_duplicate_tail(value, context, 0)
            == done + part1_mct_collection_duplicate_tail(value, context, phase),
        part1_mct_copy_result(part1_mct_collection_duplicate_step(value, context, phase), response),
    ensures response.is_err() ==>
        part1_mct_copy_result(part1_mct_collection_duplicate_tail(value, context, 0), response),
        response.is_ok() ==> part1_mct_copy_result(after, Ok(()))
            && part1_mct_collection_duplicate_tail(value, context, 0)
                == after + part1_mct_collection_duplicate_tail(value, context, phase + 1),
{
    reveal_with_fuel(part1_mct_collection_duplicate_tail, 1);
    let step = part1_mct_collection_duplicate_step(value, context, phase);
    let rest = part1_mct_collection_duplicate_tail(value, context, phase + 1);
    part1_mct_copy_continue(done, step, rest, response);
    assert(done + (step + rest) =~= (done + step) + rest);
    done + step
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_collections_duplicate_requests(
    values: Seq<Part2MctCollection>, stage: usize, record: u8, position: nat,
) -> Seq<Part1MctCopyRequest>
    decreases if position < values.len() { values.len() - position } else { 0int },
{
    if position >= values.len() { Seq::empty() } else {
        let context = ResolvedCopyContext {
            role: ResolvedCopyRole::Tile, stage, record: record as usize, collection: position as usize,
        };
        part1_mct_collection_duplicate_tail(values[position as int], context, 0)
            + part1_mct_collections_duplicate_requests(values, stage, record, position + 1)
    }
}

pub(crate) open spec fn part1_mct_stage_duplicate_requests(value: Part2MctStage, stage: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Resolved(ResolvedCopyPath::Collections(
        ResolvedCopyRole::Tile, stage, value.0 as usize)), value.1.len() as usize)
        + part1_mct_collections_duplicate_requests(value.1, stage, value.0, 0)
}

#[verifier::opaque]
pub(crate) open spec fn part1_mct_stages_duplicate_requests(values: Seq<Part2MctStage>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases if position < values.len() { values.len() - position } else { 0int },
{
    if position >= values.len() { Seq::empty() } else {
        part1_mct_stage_duplicate_requests(values[position as int], position as usize)
            + part1_mct_stages_duplicate_requests(values, position + 1)
    }
}

pub(crate) open spec fn part1_mct_transform_duplicate_requests(values: Seq<Part2MctStage>)
    -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Resolved(ResolvedCopyPath::Stages(ResolvedCopyRole::Tile)), values.len() as usize)
        + part1_mct_stages_duplicate_requests(values, 0)
}

pub(crate) open spec fn part2_payload_duplicate_step(value: Part2OwnedTilePart, phase: nat)
    -> Seq<Part1MctCopyRequest> {
    if phase == 0 {
        part1_mct_copy_leaf(MctCopyPath::CollectedQuantizations, value.component_quantizations.1.len() as usize)
    } else if phase == 1 {
        part1_mct_copy_leaf(MctCopyPath::CollectedProgression, value.progression_changes.len() as usize)
    } else if phase == 2 {
        match value.multiple_component_transform {
            None => Seq::empty(),
            Some(stages) => part1_mct_transform_duplicate_requests(stages),
        }
    } else if phase == 3 {
        part1_part2_role_requests(true, part1_part2_copy_requests(value.part2_extensions))
    } else { Seq::empty() }
}

#[verifier::opaque]
pub(crate) open spec fn part2_payload_duplicate_tail(value: Part2OwnedTilePart, phase: nat)
    -> Seq<Part1MctCopyRequest>
    decreases if phase < 4 { 4 - phase } else { 0int },
{
    if phase >= 4 { Seq::empty() } else {
        part2_payload_duplicate_step(value, phase) + part2_payload_duplicate_tail(value, phase + 1)
    }
}

pub(crate) proof fn part2_payload_duplicate_advance(
    value: Part2OwnedTilePart, phase: nat, done: Seq<Part1MctCopyRequest>,
    response: Result<(), crate::DecodeError>,
) -> (after: Seq<Part1MctCopyRequest>)
    requires phase < 4, part1_mct_copy_result(done, Ok(())),
        part2_payload_duplicate_tail(value, 0) == done + part2_payload_duplicate_tail(value, phase),
        part1_mct_copy_result(part2_payload_duplicate_step(value, phase), response),
    ensures response.is_err() ==> part1_mct_copy_result(part2_payload_duplicate_tail(value, 0), response),
        response.is_ok() ==> part1_mct_copy_result(after, Ok(()))
            && part2_payload_duplicate_tail(value, 0) == after + part2_payload_duplicate_tail(value, phase + 1),
{
    reveal_with_fuel(part2_payload_duplicate_tail, 1);
    let step = part2_payload_duplicate_step(value, phase);
    let rest = part2_payload_duplicate_tail(value, phase + 1);
    part1_mct_copy_continue(done, step, rest, response);
    assert(done + (step + rest) =~= (done + step) + rest);
    done + step
}

pub(crate) proof fn part1_mct_copy_observed(path: MctCopyPath, count: usize, result: Result<(), crate::DecodeError>)
    requires result == Ok(()) || (count > 0 && result == Err(crate::DecodeError::AllocationFailed)),
    ensures part1_mct_copy_result(part1_mct_copy_leaf(path, count), result),
{
    reveal(part1_mct_copy_result);
    reveal_with_fuel(part1_mct_copy_run, 2);
    let events = if count == 0 { Seq::empty() } else {
        seq![Part1ColdStorageEvent { site: part1_mct_copy_site(path), elements: count, succeeded: result.is_ok() }]
    };
    if count > 0 { assert(events.drop_first() =~= Seq::<Part1ColdStorageEvent>::empty()); }
    assert(part1_mct_copy_run(part1_mct_copy_leaf(path, count), events) == Some((result, Seq::empty())));
}

pub(crate) proof fn part1_mct_copy_frame(
    requests: Seq<Part1MctCopyRequest>, events: Seq<Part1ColdStorageEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_mct_copy_run(requests, events) == Some((result, rest)),
    ensures part1_mct_copy_run(requests, events + tail) == Some((result, rest + tail)),
    decreases requests.len(),
{
    reveal_with_fuel(part1_mct_copy_run, 1);
    if requests.len() > 0 {
        if let Some((reserved, after)) = part1_quantization_storage_request(
            part1_mct_copy_site(requests[0].path), requests[0].elements, events) {
            assert((events + tail).drop_first() =~= events.drop_first() + tail);
            if reserved.is_ok() { part1_mct_copy_frame(requests.drop_first(), after, result, rest, tail); }
        }
    }
}

pub(crate) proof fn part1_mct_copy_bind(
    first: Seq<Part1MctCopyRequest>, next: Seq<Part1MctCopyRequest>, events: Seq<Part1ColdStorageEvent>,
)
    ensures part1_mct_copy_run(first + next, events) == match part1_mct_copy_run(first, events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => part1_mct_copy_run(next, rest),
    },
    decreases first.len(),
{
    reveal_with_fuel(part1_mct_copy_run, 1);
    if first.len() > 0 {
        assert((first + next).drop_first() =~= first.drop_first() + next);
        if let Some((reserved, after)) = part1_quantization_storage_request(
            part1_mct_copy_site(first[0].path), first[0].elements, events) {
            if reserved.is_ok() { part1_mct_copy_bind(first.drop_first(), next, after); }
        }
    } else { assert(first + next =~= next); }
}

pub(crate) proof fn part1_mct_copy_continue(
    prefix: Seq<Part1MctCopyRequest>, step: Seq<Part1MctCopyRequest>, suffix: Seq<Part1MctCopyRequest>,
    result: Result<(), crate::DecodeError>,
)
    requires part1_mct_copy_result(prefix, Ok(())), part1_mct_copy_result(step, result),
    ensures if result.is_ok() { part1_mct_copy_result(prefix + step, Ok(())) }
        else { part1_mct_copy_result((prefix + step) + suffix, result) },
{
    reveal(part1_mct_copy_result);
    let before = choose|events: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(prefix, events) == Some((Ok(()), Seq::empty()));
    let calls = choose|events: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(step, events) == Some((result, Seq::empty()));
    part1_mct_copy_projection(step, calls, result, Seq::empty());
    part1_mct_copy_frame(prefix, before, Ok(()), Seq::empty(), calls);
    assert(Seq::<Part1ColdStorageEvent>::empty() + calls =~= calls);
    part1_mct_copy_bind(prefix, step, before + calls);
    assert(part1_mct_copy_run(prefix + step, before + calls) == Some((result, Seq::empty())));
    if result.is_err() {
        part1_mct_copy_bind(prefix + step, suffix, before + calls);
        assert(part1_mct_copy_run((prefix + step) + suffix, before + calls) == Some((result, Seq::empty())));
        assert(exists|events: Seq<Part1ColdStorageEvent>|
            part1_mct_copy_run((prefix + step) + suffix, events) == Some((result, Seq::empty())));
    } else {
        assert(result == Ok(()));
        assert(part1_mct_copy_run(prefix + step, before + calls) == Some((Ok(()), Seq::empty())));
        assert(exists|events: Seq<Part1ColdStorageEvent>|
            part1_mct_copy_run(prefix + step, events) == Some((Ok(()), Seq::empty())));
    }
}

pub(crate) open spec fn part1_mct_copy_normal_calls(requests: Seq<Part1MctCopyRequest>)
    -> Seq<Part1ColdStorageEvent> {
    requests.map_values(|request: Part1MctCopyRequest| Part1ColdStorageEvent {
        site: part1_mct_copy_site(request.path), elements: request.elements, succeeded: true })
}

pub(crate) proof fn part1_mct_copy_normal(requests: Seq<Part1MctCopyRequest>, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_mct_copy_run(requests, part1_mct_copy_normal_calls(requests) + tail) == Some((Ok(()), tail)),
    decreases requests.len(),
{
    reveal_with_fuel(part1_mct_copy_run, 1);
    if requests.len() > 0 {
        let calls = part1_mct_copy_normal_calls(requests);
        assert((calls + tail).drop_first() =~= part1_mct_copy_normal_calls(requests.drop_first()) + tail);
        part1_mct_copy_normal(requests.drop_first(), tail);
    } else { assert(part1_mct_copy_normal_calls(requests) + tail =~= tail); }
}

pub(crate) proof fn part1_mct_copy_projection(
    requests: Seq<Part1MctCopyRequest>, events: Seq<Part1ColdStorageEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_mct_copy_run(requests, events) == Some((result, rest)),
    ensures result == Ok(()) || result == Err(crate::DecodeError::AllocationFailed),
    decreases requests.len(),
{
    reveal_with_fuel(part1_mct_copy_run, 1);
    if requests.len() > 0 {
        if let Some((reserved, after)) = part1_quantization_storage_request(
            part1_mct_copy_site(requests[0].path), requests[0].elements, events) {
            if reserved.is_ok() { part1_mct_copy_projection(requests.drop_first(), after, result, rest); }
        }
    }
}

}
