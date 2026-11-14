//! Source-derived main/tile resolved-transform request prefixes and exact Results.

use super::*;
use crate::codestream::{MctCopyPath, ResolvedCopyContext, ResolvedCopyPath, ResolvedCopyRole};

verus! {

pub(crate) open spec fn part1_resolved_copy_site(path: ResolvedCopyPath) -> u8 {
    let pair = match path {
        ResolvedCopyPath::Stages(role) => (role, 0u8),
        ResolvedCopyPath::Collections(role, _, _) => (role, 1u8),
        ResolvedCopyPath::Offsets(ctx, _) => (ctx.role, 2u8),
        ResolvedCopyPath::Matrix(ctx, _) => (ctx.role, 3u8),
        ResolvedCopyPath::Inputs(ctx) => (ctx.role, 4u8),
        ResolvedCopyPath::Outputs(ctx) => (ctx.role, 5u8),
    };
    ((if pair.0 == ResolvedCopyRole::Main { 37int } else { 43int }) + pair.1 as int) as u8
}

pub(crate) open spec fn part1_resolved_leaf(path: ResolvedCopyPath, count: usize) -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Resolved(path), count)
}

pub(crate) open spec fn part1_resolved_component_requests(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference,
) -> Seq<Part1MctCopyRequest> {
    part1_resolved_leaf(ResolvedCopyPath::Inputs(ctx), reference.inputs.len() as usize)
        + part1_resolved_leaf(ResolvedCopyPath::Outputs(ctx), reference.outputs.len() as usize)
}

pub(crate) open spec fn part1_resolved_collection_requests(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
) -> Seq<Part1MctCopyRequest> {
    if reference.inputs.len() == 0 || reference.inputs.len() != reference.outputs.len() { Seq::empty() } else {
        match reference.transform {
            Part1MccTransformReference::Wavelet(_) => part1_resolved_component_requests(ctx, reference),
            Part1MccTransformReference::Array { kind, reversible: _, transform_index, offset_index } => {
                let offset = if offset_index == 0 { Ok(None) } else {
                    match part1_mct_registry_reference(arrays, offset_index, crate::codestream::MctArrayKind::Offset) {
                        Err(error) => Err(error), Ok(value) => Ok(Some(value)),
                    }
                };
                match offset {
                    Err(_) => Seq::empty(),
                    Ok(offset) => {
                        let before = match offset { None => Seq::empty(), Some(value) =>
                            part1_resolved_leaf(ResolvedCopyPath::Offsets(ctx, value.0), value.4.len() as usize) };
                        let matrix = if transform_index == 0 { Ok(None) } else {
                            match part1_mct_registry_reference(arrays, transform_index, kind) {
                                Err(error) => Err(error), Ok(value) => Ok(Some(value)),
                            }
                        };
                        match matrix {
                            Err(_) => before,
                            Ok(matrix) => {
                                let copied = before + match matrix { None => Seq::empty(), Some(value) =>
                                    part1_resolved_leaf(ResolvedCopyPath::Matrix(ctx, value.0), value.4.len() as usize) };
                                copied + if part1_mct_graph_collection(reference, arrays).is_ok() {
                                    part1_resolved_component_requests(ctx, reference)
                                } else { Seq::empty() }
                            },
                        }
                    },
                }
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_resolved_stage_tail(
    role: ResolvedCopyRole, stage: usize, record_index: usize,
    record: Part1MctRecord, arrays: Seq<Part2MctArray>, position: nat,
) -> Seq<Part1MctCopyRequest>
    decreases record.1.len() - position,
{
    if position >= record.1.len() { Seq::empty() } else {
        let ctx = ResolvedCopyContext { role, stage, record: record_index, collection: position as usize };
        let current = part1_resolved_collection_requests(ctx, record.1[position as int], arrays);
        current + if part1_mct_graph_collection(record.1[position as int], arrays).is_ok() {
            part1_resolved_stage_tail(role, stage, record_index, record, arrays, position + 1)
        } else { Seq::empty() }
    }
}

pub(crate) open spec fn part1_resolved_stage_requests(
    role: ResolvedCopyRole, stage: usize, record_index: usize, record: Part1MctRecord, arrays: Seq<Part2MctArray>,
) -> Seq<Part1MctCopyRequest> {
    part1_resolved_leaf(ResolvedCopyPath::Collections(role, stage, record_index), record.1.len() as usize)
        + part1_resolved_stage_tail(role, stage, record_index, record, arrays, 0)
}

#[verifier::opaque]
pub(crate) open spec fn part1_resolved_graph_tail(
    role: ResolvedCopyRole, parameters: Part1MctParameters, position: nat,
) -> Seq<Part1MctCopyRequest>
    decreases parameters.order.len() - position,
{
    if position >= parameters.order.len() { Seq::empty() } else {
        match part1_mct_registry_record_find(parameters.records, parameters.order[position as int], 0) {
            None => Seq::empty(),
            Some(index) => {
                let current = part1_resolved_stage_requests(
                    role, position as usize, index, parameters.records[index as int], parameters.arrays);
                current + if part1_mct_graph_stage(parameters.records[index as int], parameters.arrays).is_ok() {
                    part1_resolved_graph_tail(role, parameters, position + 1)
                } else { Seq::empty() }
            },
        }
    }
}

pub(crate) open spec fn part1_resolved_graph_requests(role: ResolvedCopyRole, parameters: Part1MctParameters)
    -> Seq<Part1MctCopyRequest> {
    if parameters.order.len() == 0 { Seq::empty() } else {
        part1_resolved_leaf(ResolvedCopyPath::Stages(role), parameters.order.len() as usize)
            + part1_resolved_graph_tail(role, parameters, 0)
    }
}

pub(crate) open spec fn part1_resolved_collection_run(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Part2MctCollection, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_resolved_collection_requests(ctx, reference, arrays), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_mct_graph_collection(reference, arrays), rest)),
    }
}

pub(crate) open spec fn part1_resolved_stage_run(
    role: ResolvedCopyRole, stage: usize, index: usize, record: Part1MctRecord, arrays: Seq<Part2MctArray>,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Part2MctStage, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_resolved_stage_requests(role, stage, index, record, arrays), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_mct_graph_stage(record, arrays), rest)),
    }
}

pub(crate) open spec fn part1_resolved_graph_run(
    role: ResolvedCopyRole, parameters: Part1MctParameters, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Option<Seq<Part2MctStage>>, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_resolved_graph_requests(role, parameters), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_mct_graph(parameters), rest)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_resolved_collection_result(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
    result: Result<Part2MctCollection, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_resolved_collection_run(ctx, reference, arrays, events)
        == Some((result, Seq::empty()))
}

#[verifier::opaque]
pub(crate) open spec fn part1_resolved_stage_result(
    role: ResolvedCopyRole, stage: usize, index: usize, record: Part1MctRecord, arrays: Seq<Part2MctArray>,
    result: Result<Part2MctStage, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_resolved_stage_run(role, stage, index, record, arrays, events)
        == Some((result, Seq::empty()))
}

#[verifier::opaque]
pub(crate) open spec fn part1_resolved_graph_result(
    role: ResolvedCopyRole, parameters: Part1MctParameters,
    result: Result<Option<Seq<Part2MctStage>>, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_resolved_graph_run(role, parameters, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_resolved_graph_normal(
    role: ResolvedCopyRole, parameters: Part1MctParameters, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_resolved_graph_run(role, parameters,
        part1_mct_copy_normal_calls(part1_resolved_graph_requests(role, parameters)) + tail)
            == Some((part1_mct_graph(parameters), tail)),
{
    part1_mct_copy_normal(part1_resolved_graph_requests(role, parameters), tail);
}

pub(crate) proof fn part1_resolved_graph_frame(
    role: ResolvedCopyRole, parameters: Part1MctParameters, events: Seq<Part1ColdStorageEvent>,
    result: Result<Option<Seq<Part2MctStage>>, crate::DecodeError>,
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_resolved_graph_run(role, parameters, events) == Some((result, rest)),
    ensures part1_resolved_graph_run(role, parameters, events + tail) == Some((result, rest + tail)),
{
    if let Some((copied, after)) = part1_mct_copy_run(part1_resolved_graph_requests(role, parameters), events) {
        part1_mct_copy_frame(part1_resolved_graph_requests(role, parameters), events, copied, after, tail);
    }
}

pub(crate) proof fn part1_resolved_graph_projection(
    role: ResolvedCopyRole, parameters: Part1MctParameters, events: Seq<Part1ColdStorageEvent>,
    result: Result<Option<Seq<Part2MctStage>>, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_resolved_graph_run(role, parameters, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_mct_graph(parameters),
{
    if let Some((copied, after)) = part1_mct_copy_run(part1_resolved_graph_requests(role, parameters), events) {
        part1_mct_copy_projection(part1_resolved_graph_requests(role, parameters), events, copied, after);
    }
}

pub(crate) proof fn part1_resolved_registry_no_alloc(
    arrays: Seq<Part2MctArray>, index: u8, kind: crate::codestream::MctArrayKind, position: nat, found: Option<usize>,
)
    ensures part1_mct_registry_reference_from(arrays, index, kind, position, found) != Err(crate::DecodeError::AllocationFailed),
    decreases arrays.len() - position,
{
    reveal_with_fuel(part1_mct_registry_reference_from, 1);
    if position < arrays.len() {
        if arrays[position as int].0 == index && arrays[position as int].1 == kind {
            if found.is_none() { part1_resolved_registry_no_alloc(arrays, index, kind, position + 1, Some(position as usize)); }
        } else { part1_resolved_registry_no_alloc(arrays, index, kind, position + 1, found); }
    }
}

pub(crate) proof fn part1_resolved_scales_no_alloc(values: Seq<i64>, width: usize, count: nat)
    ensures part2_mct_scale_prefix(values, width, count) != Err(crate::DecodeError::AllocationFailed),
    decreases count,
{
    reveal_with_fuel(part2_mct_scale_prefix, 1);
    if count > 0 { part1_resolved_scales_no_alloc(values, width, (count - 1) as nat); }
}

pub(crate) proof fn part1_resolved_collection_no_alloc(reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>)
    ensures part1_mct_graph_collection(reference, arrays) != Err(crate::DecodeError::AllocationFailed),
{
    reveal(part1_mct_graph_collection);
    reveal(part1_mct_registry_reference);
    if let Part1MccTransformReference::Array { kind, reversible: _, transform_index, offset_index } = reference.transform {
        part1_resolved_registry_no_alloc(arrays, offset_index, crate::codestream::MctArrayKind::Offset, 0, None);
        part1_resolved_registry_no_alloc(arrays, transform_index, kind, 0, None);
        if let Ok(matrix) = part1_mct_registry_reference(arrays, transform_index, kind) {
            part1_resolved_scales_no_alloc(matrix.4, reference.inputs.len() as usize,
                (reference.inputs.len() as usize) as nat + 1);
        }
    }
}

pub(crate) proof fn part1_resolved_stage_no_alloc(
    record: Part1MctRecord, arrays: Seq<Part2MctArray>, position: nat, collections: Seq<Part2MctCollection>,
)
    ensures part1_mct_graph_stage_from(record, arrays, position, collections) != Err(crate::DecodeError::AllocationFailed),
    decreases record.1.len() - position,
{
    reveal_with_fuel(part1_mct_graph_stage_from, 1);
    if position < record.1.len() {
        part1_resolved_collection_no_alloc(record.1[position as int], arrays);
        if let Ok(value) = part1_mct_graph_collection(record.1[position as int], arrays) {
            part1_resolved_stage_no_alloc(record, arrays, position + 1, collections.push(value));
        }
    }
}

pub(crate) proof fn part1_resolved_graph_no_alloc(
    parameters: Part1MctParameters, position: nat, stages: Seq<Part2MctStage>,
)
    ensures part1_mct_graph_from(parameters, position, stages) != Err(crate::DecodeError::AllocationFailed),
    decreases parameters.order.len() - position,
{
    reveal_with_fuel(part1_mct_graph_from, 1);
    reveal(part1_mct_graph_stage);
    if position < parameters.order.len() {
        if let Some(index) = part1_mct_registry_record_find(parameters.records, parameters.order[position as int], 0) {
            part1_resolved_stage_no_alloc(parameters.records[index as int], parameters.arrays, 0, Seq::empty());
            if let Ok(value) = part1_mct_graph_stage(parameters.records[index as int], parameters.arrays) {
                part1_resolved_graph_no_alloc(parameters, position + 1, stages.push(value));
            }
        }
    }
}

pub(crate) proof fn part1_resolved_collection_normal(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
)
    ensures part1_resolved_collection_result(ctx, reference, arrays, part1_mct_graph_collection(reference, arrays)),
{
    reveal(part1_resolved_collection_result);
    let requests = part1_resolved_collection_requests(ctx, reference, arrays);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_resolved_collection_run(ctx, reference, arrays, calls)
        == Some((part1_mct_graph_collection(reference, arrays), Seq::empty())));
}

pub(crate) proof fn part1_resolved_stage_normal(
    role: ResolvedCopyRole, stage: usize, index: usize, record: Part1MctRecord, arrays: Seq<Part2MctArray>,
)
    ensures part1_resolved_stage_result(role, stage, index, record, arrays, part1_mct_graph_stage(record, arrays)),
{
    reveal(part1_resolved_stage_result);
    let requests = part1_resolved_stage_requests(role, stage, index, record, arrays);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_resolved_stage_run(role, stage, index, record, arrays, calls)
        == Some((part1_mct_graph_stage(record, arrays), Seq::empty())));
}

pub(crate) proof fn part1_resolved_graph_normal_result(role: ResolvedCopyRole, parameters: Part1MctParameters)
    ensures part1_resolved_graph_result(role, parameters, part1_mct_graph(parameters)),
{
    reveal(part1_resolved_graph_result);
    let calls = part1_mct_copy_normal_calls(part1_resolved_graph_requests(role, parameters));
    part1_resolved_graph_normal(role, parameters, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
}

pub(crate) proof fn part1_resolved_collection_refused(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
)
    requires part1_mct_copy_result(part1_resolved_collection_requests(ctx, reference, arrays), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_resolved_collection_result(ctx, reference, arrays, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_resolved_collection_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(
        part1_resolved_collection_requests(ctx, reference, arrays), calls)
            == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_resolved_collection_run(ctx, reference, arrays, calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_resolved_stage_refused(
    role: ResolvedCopyRole, stage: usize, index: usize, record: Part1MctRecord, arrays: Seq<Part2MctArray>,
)
    requires part1_mct_copy_result(part1_resolved_stage_requests(role, stage, index, record, arrays), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_resolved_stage_result(role, stage, index, record, arrays, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_resolved_stage_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(
        part1_resolved_stage_requests(role, stage, index, record, arrays), calls)
            == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_resolved_stage_run(role, stage, index, record, arrays, calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_resolved_graph_refused(role: ResolvedCopyRole, parameters: Part1MctParameters)
    requires part1_mct_copy_result(part1_resolved_graph_requests(role, parameters), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_resolved_graph_result(role, parameters, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_resolved_graph_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_resolved_graph_requests(role, parameters), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_resolved_graph_run(role, parameters, calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_resolved_collection_observed(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
    result: Result<Part2MctCollection, crate::DecodeError>,
)
    requires part1_resolved_collection_result(ctx, reference, arrays, result),
    ensures part1_mct_copy_result(part1_resolved_collection_requests(ctx, reference, arrays),
        if result == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == part1_mct_graph_collection(reference, arrays),
{
    reveal(part1_resolved_collection_result); reveal(part1_mct_copy_result);
    part1_resolved_collection_no_alloc(reference, arrays);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_resolved_collection_run(ctx, reference, arrays, calls)
        == Some((result, Seq::empty()));
    if let Some((copied, rest)) = part1_mct_copy_run(part1_resolved_collection_requests(ctx, reference, arrays), calls) {
        part1_mct_copy_projection(part1_resolved_collection_requests(ctx, reference, arrays), calls, copied, rest);
        assert(part1_mct_copy_run(part1_resolved_collection_requests(ctx, reference, arrays), calls)
            == Some((if result == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }, Seq::empty())));
    }
}

pub(crate) proof fn part1_resolved_stage_observed(
    role: ResolvedCopyRole, stage: usize, index: usize, record: Part1MctRecord, arrays: Seq<Part2MctArray>,
    result: Result<Part2MctStage, crate::DecodeError>,
)
    requires part1_resolved_stage_result(role, stage, index, record, arrays, result),
    ensures part1_mct_copy_result(part1_resolved_stage_requests(role, stage, index, record, arrays),
        if result == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == part1_mct_graph_stage(record, arrays),
{
    reveal(part1_resolved_stage_result); reveal(part1_mct_copy_result); reveal(part1_mct_graph_stage);
    part1_resolved_stage_no_alloc(record, arrays, 0, Seq::empty());
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_resolved_stage_run(role, stage, index, record, arrays, calls)
        == Some((result, Seq::empty()));
    if let Some((copied, rest)) = part1_mct_copy_run(part1_resolved_stage_requests(role, stage, index, record, arrays), calls) {
        part1_mct_copy_projection(part1_resolved_stage_requests(role, stage, index, record, arrays), calls, copied, rest);
        assert(part1_mct_copy_run(part1_resolved_stage_requests(role, stage, index, record, arrays), calls)
            == Some((if result == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }, Seq::empty())));
    }
}

pub(crate) proof fn part1_resolved_copy_prefix_step(
    all: Seq<Part1MctCopyRequest>, done: Seq<Part1MctCopyRequest>, step: Seq<Part1MctCopyRequest>,
    result: Result<(), crate::DecodeError>,
)
    requires part1_mct_copy_result(done, Ok(())), part1_mct_copy_result(step, result),
        done.len() + step.len() <= all.len(), all.take((done.len() + step.len()) as int) == done + step,
    ensures if result.is_ok() { part1_mct_copy_result(done + step, Ok(())) }
        else { part1_mct_copy_result(all, result) },
{
    let tail = all.skip((done.len() + step.len()) as int);
    assert(all =~= (done + step) + tail);
    part1_mct_copy_continue(done, step, tail, result);
}

pub(crate) proof fn part1_resolved_offset_prefix(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
    array: Part2MctArray,
)
    requires reference.inputs.len() > 0, reference.inputs.len() == reference.outputs.len(),
        match reference.transform {
            Part1MccTransformReference::Array { kind: _, reversible: _, transform_index: _, offset_index } =>
                offset_index != 0 && part1_mct_registry_reference(arrays, offset_index, crate::codestream::MctArrayKind::Offset) == Ok(array),
            _ => false,
        },
    ensures ({
        let all = part1_resolved_collection_requests(ctx, reference, arrays);
        let step = part1_resolved_leaf(ResolvedCopyPath::Offsets(ctx, array.0), array.4.len() as usize);
        step.len() <= all.len() && all.take(step.len() as int) == step
    }),
{
    let all = part1_resolved_collection_requests(ctx, reference, arrays);
    let step = part1_resolved_leaf(ResolvedCopyPath::Offsets(ctx, array.0), array.4.len() as usize);
    assert(all.take(step.len() as int) =~= step);
}

pub(crate) proof fn part1_resolved_matrix_prefix(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
    matrix: Part2MctArray, before: Seq<Part1MctCopyRequest>,
)
    requires reference.inputs.len() > 0, reference.inputs.len() == reference.outputs.len(),
        match reference.transform {
            Part1MccTransformReference::Array { kind, reversible: _, transform_index, offset_index } =>
                transform_index != 0 && part1_mct_registry_reference(arrays, transform_index, kind) == Ok(matrix)
                && (if offset_index == 0 { before.len() == 0 } else {
                    match part1_mct_registry_reference(arrays, offset_index, crate::codestream::MctArrayKind::Offset) {
                        Err(_) => false, Ok(array) => before ==
                            part1_resolved_leaf(ResolvedCopyPath::Offsets(ctx, array.0), array.4.len() as usize),
                    }
                }),
            _ => false,
        },
    ensures ({
        let all = part1_resolved_collection_requests(ctx, reference, arrays);
        let step = part1_resolved_leaf(ResolvedCopyPath::Matrix(ctx, matrix.0), matrix.4.len() as usize);
        before.len() + step.len() <= all.len() && all.take((before.len() + step.len()) as int) == before + step
    }),
{
    let all = part1_resolved_collection_requests(ctx, reference, arrays);
    let step = part1_resolved_leaf(ResolvedCopyPath::Matrix(ctx, matrix.0), matrix.4.len() as usize);
    if let Part1MccTransformReference::Array { kind: _, reversible: _, transform_index: _, offset_index } = reference.transform {
        if offset_index == 0 { assert(before =~= Seq::<Part1MctCopyRequest>::empty()); }
    }
    assert(all.take((before.len() + step.len()) as int) =~= before + step);
}

pub(crate) open spec fn part1_resolved_array_requests(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
) -> Seq<Part1MctCopyRequest> {
    match reference.transform {
        Part1MccTransformReference::Wavelet(_) => Seq::empty(),
        Part1MccTransformReference::Array { kind, reversible: _, transform_index, offset_index } => {
            let before = if offset_index == 0 { Seq::empty() } else {
                match part1_mct_registry_reference(arrays, offset_index, crate::codestream::MctArrayKind::Offset) {
                    Err(_) => Seq::empty(), Ok(array) =>
                        part1_resolved_leaf(ResolvedCopyPath::Offsets(ctx, array.0), array.4.len() as usize),
                }
            };
            before + if transform_index == 0 { Seq::empty() } else {
                match part1_mct_registry_reference(arrays, transform_index, kind) {
                    Err(_) => Seq::empty(), Ok(array) =>
                        part1_resolved_leaf(ResolvedCopyPath::Matrix(ctx, array.0), array.4.len() as usize),
                }
            }
        },
    }
}

pub(crate) proof fn part1_resolved_components_prefix(
    ctx: ResolvedCopyContext, reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
    before: Seq<Part1MctCopyRequest>,
)
    requires part1_mct_graph_collection(reference, arrays).is_ok(),
        before == part1_resolved_array_requests(ctx, reference, arrays),
    ensures part1_resolved_collection_requests(ctx, reference, arrays)
        == before + part1_resolved_component_requests(ctx, reference),
        ({
            let first = part1_resolved_leaf(ResolvedCopyPath::Inputs(ctx), reference.inputs.len() as usize);
            let last = part1_resolved_leaf(ResolvedCopyPath::Outputs(ctx), reference.outputs.len() as usize);
            let all = part1_resolved_collection_requests(ctx, reference, arrays);
            all == (before + first) + last
                && all.take((before.len() + first.len()) as int) == before + first
        }),
{
    reveal(part1_mct_graph_collection);
    let first = part1_resolved_leaf(ResolvedCopyPath::Inputs(ctx), reference.inputs.len() as usize);
    let last = part1_resolved_leaf(ResolvedCopyPath::Outputs(ctx), reference.outputs.len() as usize);
    let all = part1_resolved_collection_requests(ctx, reference, arrays);
    assert(all =~= (before + first) + last);
    assert(all.take((before.len() + first.len()) as int) =~= before + first);
}

}
