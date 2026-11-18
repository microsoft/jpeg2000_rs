//! Fresh marker requests at actual syntax/reassembly and reached growth cutpoints.

use super::*;
use crate::codestream::{FreshMarkerPath, MctCopyPath};

verus! {

pub(crate) open spec fn part1_fresh_marker_site(path: FreshMarkerPath) -> u8 {
    match path {
        FreshMarkerPath::Values(_) => 63, FreshMarkerPath::Collections(_) => 64,
        FreshMarkerPath::Inputs(_, _) => 65, FreshMarkerPath::Outputs(_, _) => 66,
        FreshMarkerPath::Order(_) => 67, FreshMarkerPath::MctReassembly(_) => 68,
        FreshMarkerPath::MccReassembly(_) => 69, FreshMarkerPath::MctInitial(_) => 70,
        FreshMarkerPath::MccInitial(_) => 71,
        FreshMarkerPath::MctPending(_, _) => 86,
        FreshMarkerPath::MctCompleted(_, _) => 87,
        FreshMarkerPath::MctRetainedMain(_, _) => 88,
        FreshMarkerPath::MccPending(_, _) => 89,
        FreshMarkerPath::MccCompleted(_, _) => 90,
        FreshMarkerPath::MccRetainedMain(_, _) => 91,
    }
}

pub(crate) open spec fn part1_fresh_leaf(path: FreshMarkerPath, count: usize) -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::FreshMarker(path), count)
}

pub(crate) open spec fn part1_fresh_mct_requests(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    -> Seq<Part1MctCopyRequest> {
    match part1_mct_header(segment, limits) {
        Err(_) => Seq::empty(),
        Ok(header) => part1_fresh_leaf(FreshMarkerPath::Values(segment.offset), header.count),
    }
}

pub(crate) open spec fn part1_fresh_mco_requests(segment: Part1CodestreamSegment) -> Seq<Part1MctCopyRequest> {
    if segment.payload.len() == 0 { Seq::empty() } else {
        let count = segment.payload[0] as usize;
        if segment.payload.len() != count + 1 { Seq::empty() } else {
            part1_fresh_leaf(FreshMarkerPath::Order(segment.offset), count)
        }
    }
}

pub(crate) open spec fn part1_fresh_list_shape(
    payload: Seq<u8>, start: usize, components: u16,
) -> Option<(usize, usize)> {
    if start as int + 2 > payload.len() { None } else {
        let encoded = part1_marker_value(payload[start as int], payload[start as int + 1]);
        let position = (start + 2) as usize;
        let width = if encoded & 0x8000 == 0 { 1usize } else { 2usize };
        let count = encoded & 0x7fff;
        if count == 0 || count > components || position as int + count as int * width as int > payload.len() {
            None
        } else { Some((count as usize, position)) }
    }
}

pub(crate) open spec fn part1_fresh_list_requests(
    payload: Seq<u8>, start: usize, components: u16, offset: usize, output: bool,
) -> Seq<Part1MctCopyRequest> {
    match part1_fresh_list_shape(payload, start, components) {
        None => Seq::empty(),
        Some((count, position)) => part1_fresh_leaf(
            if output { FreshMarkerPath::Outputs(offset, position) } else { FreshMarkerPath::Inputs(offset, position) }, count),
    }
}

pub(crate) open spec fn part1_fresh_collection_requests(
    segment: Part1CodestreamSegment, components: u16, start: usize,
) -> Seq<Part1MctCopyRequest> {
    if start >= segment.payload.len() || segment.payload[start as int] & 0xfc != 0
        || segment.payload[start as int] & 3 == 2 { Seq::empty() } else {
        let first = part1_fresh_list_requests(segment.payload, (start + 1) as usize, components, segment.offset, false);
        let input = part1_parse_mcc_component_list(segment.payload, (start + 1) as usize, components, segment.offset);
        first + if input.0.is_ok() {
            part1_fresh_list_requests(segment.payload, input.1, components, segment.offset, true)
        } else { Seq::empty() }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_fresh_records_requests(
    segment: Part1CodestreamSegment, components: u16, position: usize, remaining: nat,
) -> Seq<Part1MctCopyRequest>
    decreases remaining,
{
    if remaining == 0 { Seq::empty() } else {
        part1_fresh_collection_requests(segment, components, position) +
            match part1_mcc_collection(segment, components, position) {
                Err(_) => Seq::empty(),
                Ok((_, next)) => part1_fresh_records_requests(segment, components, next, (remaining - 1) as nat),
            }
    }
}

pub(crate) open spec fn part1_fresh_mcc_count(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits) -> Option<usize> {
    if segment.payload.len() < 7 || part1_marker_value(segment.payload[0], segment.payload[1]) != 0
        || part1_marker_value(segment.payload[3], segment.payload[4]) != 0 { None } else {
        let index = segment.payload[2];
        let count = part1_marker_value(segment.payload[5], segment.payload[6]);
        if index == 0 || count == 0 || count > crate::limits::resource_component_limit(limits) { None }
        else { Some(count as usize) }
    }
}

pub(crate) open spec fn part1_fresh_mcc_requests(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
) -> Seq<Part1MctCopyRequest> {
    match part1_fresh_mcc_count(segment, limits) {
        None => Seq::empty(),
        Some(count) => part1_fresh_leaf(FreshMarkerPath::Collections(segment.offset), count)
            + part1_fresh_records_requests(segment, components, 7, count as nat),
    }
}

pub(crate) open spec fn part1_fresh_mct_run(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>)
    -> Option<(Result<Part2MctArray, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_mct_requests(segment, limits), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_parse_mct(segment, limits), rest)),
    }
}

pub(crate) open spec fn part1_fresh_mco_run(segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>)
    -> Option<(Result<Seq<u8>, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_mco_requests(segment), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_parse_mco(segment), rest)),
    }
}

pub(crate) open spec fn part1_fresh_list_run(
    payload: Seq<u8>, start: usize, components: u16, offset: usize, output: bool, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<Seq<u16>, crate::DecodeError>, usize), Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_list_requests(payload, start, components, offset, output), events) {
        None => None,
        Some((Err(error), rest)) => Some(((Err(error), (start + 2) as usize), rest)),
        Some((Ok(()), rest)) => Some((part1_parse_mcc_component_list(payload, start, components, offset), rest)),
    }
}

pub(crate) open spec fn part1_fresh_collection_run(
    segment: Part1CodestreamSegment, components: u16, start: usize, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<(Part1MccCollectionReference, usize), crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_collection_requests(segment, components, start), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_mcc_collection(segment, components, start), rest)),
    }
}

pub(crate) open spec fn part1_fresh_mcc_run(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Part1MctRecord, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_mcc_requests(segment, components, limits), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_parse_mcc(segment, components, limits), rest)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_fresh_mct_result(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, result: Result<Part2MctArray, crate::DecodeError>) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_mct_run(segment, limits, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_mco_result(segment: Part1CodestreamSegment, result: Result<Seq<u8>, crate::DecodeError>) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_mco_run(segment, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_list_result(payload: Seq<u8>, start: usize, components: u16, offset: usize, output: bool,
    result: (Result<Seq<u16>, crate::DecodeError>, usize)) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_list_run(payload, start, components, offset, output, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_collection_result(segment: Part1CodestreamSegment, components: u16, start: usize,
    result: Result<(Part1MccCollectionReference, usize), crate::DecodeError>) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_collection_run(segment, components, start, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_mcc_result(segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
    result: Result<Part1MctRecord, crate::DecodeError>) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_mcc_run(segment, components, limits, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_fresh_mct_normal(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    ensures part1_fresh_mct_result(segment, limits, part1_parse_mct(segment, limits)),
{
    reveal(part1_fresh_mct_result);
    let requests = part1_fresh_mct_requests(segment, limits);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_mct_run(segment, limits, calls) == Some((part1_parse_mct(segment, limits), Seq::empty())));
}

pub(crate) proof fn part1_fresh_mco_normal(segment: Part1CodestreamSegment)
    ensures part1_fresh_mco_result(segment, part1_parse_mco(segment)),
{
    reveal(part1_fresh_mco_result);
    let requests = part1_fresh_mco_requests(segment);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_mco_run(segment, calls) == Some((part1_parse_mco(segment), Seq::empty())));
}

pub(crate) proof fn part1_fresh_list_normal(payload: Seq<u8>, start: usize, components: u16, offset: usize, output: bool)
    ensures part1_fresh_list_result(payload, start, components, offset, output, part1_parse_mcc_component_list(payload, start, components, offset)),
{
    reveal(part1_fresh_list_result);
    let requests = part1_fresh_list_requests(payload, start, components, offset, output);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_list_run(payload, start, components, offset, output, calls)
        == Some((part1_parse_mcc_component_list(payload, start, components, offset), Seq::empty())));
}

pub(crate) proof fn part1_fresh_collection_normal(segment: Part1CodestreamSegment, components: u16, start: usize)
    ensures part1_fresh_collection_result(segment, components, start, part1_mcc_collection(segment, components, start)),
{
    reveal(part1_fresh_collection_result);
    let requests = part1_fresh_collection_requests(segment, components, start);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_collection_run(segment, components, start, calls)
        == Some((part1_mcc_collection(segment, components, start), Seq::empty())));
}

pub(crate) proof fn part1_fresh_mcc_normal(segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits)
    ensures part1_fresh_mcc_result(segment, components, limits, part1_parse_mcc(segment, components, limits)),
{
    reveal(part1_fresh_mcc_result);
    let requests = part1_fresh_mcc_requests(segment, components, limits);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_mcc_run(segment, components, limits, calls)
        == Some((part1_parse_mcc(segment, components, limits), Seq::empty())));
}

pub(crate) proof fn part1_fresh_mct_refused(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    requires part1_mct_copy_result(part1_fresh_mct_requests(segment, limits), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_mct_result(segment, limits, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_mct_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_mct_requests(segment, limits), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_mct_run(segment, limits, calls) == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_fresh_mco_refused(segment: Part1CodestreamSegment)
    requires part1_mct_copy_result(part1_fresh_mco_requests(segment), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_mco_result(segment, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_mco_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_mco_requests(segment), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_mco_run(segment, calls) == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_fresh_list_refused(
    payload: Seq<u8>, start: usize, components: u16, offset: usize, output: bool,
)
    requires part1_mct_copy_result(part1_fresh_list_requests(payload, start, components, offset, output), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_list_result(payload, start, components, offset, output,
        (Err(crate::DecodeError::AllocationFailed), (start + 2) as usize)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_list_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(
        part1_fresh_list_requests(payload, start, components, offset, output), calls)
            == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_list_run(payload, start, components, offset, output, calls)
        == Some(((Err(crate::DecodeError::AllocationFailed), (start + 2) as usize), Seq::empty())));
}

pub(crate) proof fn part1_fresh_collection_refused(segment: Part1CodestreamSegment, components: u16, start: usize)
    requires part1_mct_copy_result(part1_fresh_collection_requests(segment, components, start), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_collection_result(segment, components, start, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_collection_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_collection_requests(segment, components, start), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_collection_run(segment, components, start, calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_fresh_mcc_refused(segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits)
    requires part1_mct_copy_result(part1_fresh_mcc_requests(segment, components, limits), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_mcc_result(segment, components, limits, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_mcc_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_mcc_requests(segment, components, limits), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_mcc_run(segment, components, limits, calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_fresh_references_no_alloc(
    payload: Seq<u8>, components: u16, offset: usize, position: usize, width: usize, remaining: nat, references: Seq<u16>,
)
    ensures part1_mcc_reference_run(payload, components, offset, position, width, remaining, references).0 != Err(crate::DecodeError::AllocationFailed),
    decreases remaining,
{
    reveal_with_fuel(part1_mcc_reference_run, 1);
    if remaining > 0 && (width == 1 || width == 2) && position as int + width as int <= payload.len() {
        let value = part1_mcc_reference_value(payload, position as int, width);
        if value < components && !part1_mcc_reference_present(references, value) {
            part1_fresh_references_no_alloc(payload, components, offset, (position + width) as usize, width,
                (remaining - 1) as nat, references.push(value));
        }
    }
}

pub(crate) proof fn part1_fresh_list_no_alloc(payload: Seq<u8>, start: usize, components: u16, offset: usize)
    ensures part1_parse_mcc_component_list(payload, start, components, offset).0 != Err(crate::DecodeError::AllocationFailed),
{
    reveal(part1_parse_mcc_component_list);
    if start as int + 2 <= payload.len() {
        let encoded = part1_marker_value(payload[start as int], payload[start as int + 1]);
        let width = if encoded & 0x8000 == 0 { 1usize } else { 2usize };
        part1_fresh_references_no_alloc(payload, components, offset, (start + 2) as usize,
            width, (encoded & 0x7fff) as nat, Seq::empty());
    }
}

pub(crate) proof fn part1_fresh_collection_no_alloc(segment: Part1CodestreamSegment, components: u16, start: usize)
    ensures part1_mcc_collection(segment, components, start) != Err(crate::DecodeError::AllocationFailed),
{
    reveal(part1_mcc_collection);
    part1_fresh_list_no_alloc(segment.payload, (start + 1) as usize, components, segment.offset);
    let input = part1_parse_mcc_component_list(segment.payload, (start + 1) as usize, components, segment.offset);
    if input.0.is_ok() { part1_fresh_list_no_alloc(segment.payload, input.1, components, segment.offset); }
}

pub(crate) proof fn part1_fresh_records_no_alloc(
    segment: Part1CodestreamSegment, components: u16, position: usize, remaining: nat, values: Seq<Part1MccCollectionReference>,
)
    ensures part1_mcc_records(segment, components, position, remaining, values) != Err(crate::DecodeError::AllocationFailed),
    decreases remaining,
{
    reveal_with_fuel(part1_mcc_records, 1);
    if remaining > 0 {
        part1_fresh_collection_no_alloc(segment, components, position);
        if let Ok((value, next)) = part1_mcc_collection(segment, components, position) {
            part1_fresh_records_no_alloc(segment, components, next, (remaining - 1) as nat, values.push(value));
        }
    }
}

pub(crate) proof fn part1_fresh_values_no_alloc(
    offset: usize, data: Seq<u8>, format: crate::codestream::MctNumericFormat, position: nat, values: Seq<i64>,
)
    ensures part1_mct_values(offset, data, format, position, values) != Err(crate::DecodeError::AllocationFailed),
    decreases data.len() - position,
{
    reveal_with_fuel(part1_mct_values, 1); reveal(part1_mct_element);
    let width = part1_mct_element_width(format) as nat;
    if position < data.len() && position + width <= data.len() {
        if let Ok(value) = part1_mct_element(offset, data, position as usize, format) {
            part1_fresh_values_no_alloc(offset, data, format, position + width, values.push(value));
        }
    }
}

pub(crate) proof fn part1_fresh_order_no_alloc(segment: Part1CodestreamSegment, position: nat, values: Seq<u8>)
    ensures part1_mco_run(segment, position, values) != Err(crate::DecodeError::AllocationFailed),
    decreases segment.payload.len() - position,
{
    reveal_with_fuel(part1_mco_run, 1);
    if position + 1 < segment.payload.len() {
        let value = segment.payload[position as int + 1];
        if !values.contains(value) && value != 0 { part1_fresh_order_no_alloc(segment, position + 1, values.push(value)); }
    }
}

pub(crate) proof fn part1_fresh_unit_observed<T>(
    requests: Seq<Part1MctCopyRequest>, ordinary: Result<T, crate::DecodeError>,
    result: Result<T, crate::DecodeError>, events: Seq<Part1ColdStorageEvent>,
)
    requires ordinary != Err(crate::DecodeError::AllocationFailed),
        (match part1_mct_copy_run(requests, events) {
            None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
            Some((Ok(()), rest)) => Some((ordinary, rest)),
        }) == Some((result, Seq::empty())),
    ensures part1_mct_copy_result(requests, if result == Err(crate::DecodeError::AllocationFailed) {
        Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == ordinary,
{
    reveal(part1_mct_copy_result);
    if let Some((copied, rest)) = part1_mct_copy_run(requests, events) {
        part1_mct_copy_projection(requests, events, copied, rest);
        assert(part1_mct_copy_run(requests, events) == Some((if result == Err(crate::DecodeError::AllocationFailed) {
            Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }, Seq::empty())));
    }
}

pub(crate) proof fn part1_fresh_mct_observed(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, result: Result<Part2MctArray, crate::DecodeError>,
)
    requires part1_fresh_mct_result(segment, limits, result),
    ensures part1_mct_copy_result(part1_fresh_mct_requests(segment, limits), if result == Err(crate::DecodeError::AllocationFailed) {
        Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == part1_parse_mct(segment, limits),
{
    reveal(part1_fresh_mct_result); reveal(part1_parse_mct); reveal(part1_mct_header);
    if let Ok(header) = part1_mct_header(segment, limits) {
        part1_fresh_values_no_alloc(segment.offset, segment.payload.subrange(6, segment.payload.len() as int), header.format, 0, Seq::empty());
    }
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mct_run(segment, limits, calls) == Some((result, Seq::empty()));
    part1_fresh_unit_observed(part1_fresh_mct_requests(segment, limits), part1_parse_mct(segment, limits), result, calls);
}

pub(crate) proof fn part1_fresh_mco_observed(segment: Part1CodestreamSegment, result: Result<Seq<u8>, crate::DecodeError>)
    requires part1_fresh_mco_result(segment, result),
    ensures part1_mct_copy_result(part1_fresh_mco_requests(segment), if result == Err(crate::DecodeError::AllocationFailed) {
        Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == part1_parse_mco(segment),
{
    reveal(part1_fresh_mco_result); reveal(part1_parse_mco);
    part1_fresh_order_no_alloc(segment, 0, Seq::empty());
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mco_run(segment, calls) == Some((result, Seq::empty()));
    part1_fresh_unit_observed(part1_fresh_mco_requests(segment), part1_parse_mco(segment), result, calls);
}

pub(crate) proof fn part1_fresh_list_observed(
    payload: Seq<u8>, start: usize, components: u16, offset: usize, output: bool,
    result: (Result<Seq<u16>, crate::DecodeError>, usize),
)
    requires part1_fresh_list_result(payload, start, components, offset, output, result),
    ensures part1_mct_copy_result(part1_fresh_list_requests(payload, start, components, offset, output),
        if result.0 == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result.0 != Err(crate::DecodeError::AllocationFailed) ==> result == part1_parse_mcc_component_list(payload, start, components, offset),
{
    reveal(part1_fresh_list_result); reveal(part1_mct_copy_result);
    part1_fresh_list_no_alloc(payload, start, components, offset);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_list_run(payload, start, components, offset, output, calls)
        == Some((result, Seq::empty()));
    let requests = part1_fresh_list_requests(payload, start, components, offset, output);
    if let Some((copied, rest)) = part1_mct_copy_run(requests, calls) {
        part1_mct_copy_projection(requests, calls, copied, rest);
        assert(part1_mct_copy_run(requests, calls) == Some((
            if result.0 == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }, Seq::empty())));
    }
}

pub(crate) proof fn part1_fresh_collection_observed(
    segment: Part1CodestreamSegment, components: u16, start: usize,
    result: Result<(Part1MccCollectionReference, usize), crate::DecodeError>,
)
    requires part1_fresh_collection_result(segment, components, start, result),
    ensures part1_mct_copy_result(part1_fresh_collection_requests(segment, components, start),
        if result == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == part1_mcc_collection(segment, components, start),
{
    reveal(part1_fresh_collection_result);
    part1_fresh_collection_no_alloc(segment, components, start);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_collection_run(segment, components, start, calls)
        == Some((result, Seq::empty()));
    part1_fresh_unit_observed(part1_fresh_collection_requests(segment, components, start),
        part1_mcc_collection(segment, components, start), result, calls);
}

pub(crate) proof fn part1_fresh_mcc_observed(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, result: Result<Part1MctRecord, crate::DecodeError>,
)
    requires part1_fresh_mcc_result(segment, components, limits, result),
    ensures part1_mct_copy_result(part1_fresh_mcc_requests(segment, components, limits),
        if result == Err(crate::DecodeError::AllocationFailed) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != Err(crate::DecodeError::AllocationFailed) ==> result == part1_parse_mcc(segment, components, limits),
{
    reveal(part1_fresh_mcc_result); reveal(part1_parse_mcc);
    if let Some(count) = part1_fresh_mcc_count(segment, limits) {
        part1_fresh_records_no_alloc(segment, components, 7, count as nat, Seq::empty());
    }
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mcc_run(segment, components, limits, calls)
        == Some((result, Seq::empty()));
    part1_fresh_unit_observed(part1_fresh_mcc_requests(segment, components, limits),
        part1_parse_mcc(segment, components, limits), result, calls);
}

pub(crate) open spec fn part1_fresh_prepare_mct_requests(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
) -> Seq<Part1MctCopyRequest> {
    if segment.payload.len() >= 6 && part1_marker_value(segment.payload[0], segment.payload[1]) == 0
        && part1_prepare_mct_fragment(segment, limits, pending, completed).0.is_ok() {
        part1_fresh_leaf(FreshMarkerPath::MctInitial(segment.offset), (segment.payload.len() - 6) as usize)
            + part1_fresh_leaf(FreshMarkerPath::MctPending(segment.offset, pending.len() as usize), 1)
    } else { Seq::empty() }
}

pub(crate) open spec fn part1_fresh_prepare_mcc_requests(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
) -> Seq<Part1MctCopyRequest> {
    if segment.payload.len() >= 7 && part1_marker_value(segment.payload[0], segment.payload[1]) == 0
        && part1_prepare_mcc_fragment(segment, components, pending, completed).0.is_ok() {
        part1_fresh_leaf(FreshMarkerPath::MccInitial(segment.offset), (segment.payload.len() - 7) as usize)
            + part1_fresh_leaf(FreshMarkerPath::MccPending(segment.offset, pending.len() as usize), 1)
    } else { Seq::empty() }
}

pub(crate) open spec fn part1_fresh_prepare_mct_run(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(usize, u64), crate::DecodeError>, Seq<Part1MctFragment>), Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_prepare_mct_requests(segment, limits, pending, completed), events) {
        None => None, Some((Err(error), rest)) => Some(((Err(error), pending), rest)),
        Some((Ok(()), rest)) => Some((part1_prepare_mct_fragment(segment, limits, pending, completed), rest)),
    }
}

pub(crate) open spec fn part1_fresh_prepare_mcc_run(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(usize, u64), crate::DecodeError>, Seq<Part1MccFragment>), Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_fresh_prepare_mcc_requests(segment, components, pending, completed), events) {
        None => None, Some((Err(error), rest)) => Some(((Err(error), pending), rest)),
        Some((Ok(()), rest)) => Some((part1_prepare_mcc_fragment(segment, components, pending, completed), rest)),
    }
}

pub(crate) open spec fn part1_fresh_mct_reassembled(state: Part1MctFragment) -> Part1CodestreamSegment {
    Part1CodestreamSegment { marker: 0xff74, offset: state.offset, payload: part1_mct_fragment_payload(state) }
}
pub(crate) open spec fn part1_fresh_mcc_reassembled(state: Part1MccFragment) -> Part1CodestreamSegment {
    Part1CodestreamSegment { marker: 0xff75, offset: state.offset, payload: part1_mcc_fragment_payload(state) }
}
pub(crate) open spec fn part1_fresh_reassembly_count(length: nat, header: usize) -> usize {
    if length + header > usize::MAX { usize::MAX } else { (length + header) as usize }
}

pub(crate) open spec fn part1_fresh_mct_completed_requests(
    segment: Part1CodestreamSegment, completed: Seq<u8>,
) -> Seq<Part1MctCopyRequest> {
    part1_fresh_leaf(FreshMarkerPath::MctCompleted(segment.offset, completed.len() as usize), 1)
}

pub(crate) open spec fn part1_fresh_mcc_completed_requests(
    segment: Part1CodestreamSegment, completed: Seq<u8>,
) -> Seq<Part1MctCopyRequest> {
    part1_fresh_leaf(FreshMarkerPath::MccCompleted(segment.offset, completed.len() as usize), 1)
}

pub(crate) open spec fn part1_fresh_consume_mct_run(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<Option<Part2MctArray>, crate::DecodeError>, Seq<Part1MctFragment>, Seq<u8>), Seq<Part1ColdStorageEvent>)> {
    match part1_fresh_prepare_mct_run(segment, limits, pending, completed, events) {
        None => None,
        Some(((Err(error), changed), rest)) => Some(((Err(error), changed, completed), rest)),
        Some(((Ok((index, maximum)), changed), rest)) => {
            let state = changed[index as int];
            if !part2_fragment_complete(state.next_index, state.final_index) { Some(((Ok(None), changed, completed), rest)) } else {
                let removed = part1_mct_fragment_swap_remove(changed, index);
                if state.data.len() as u64 > maximum {
                    Some(((Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                        limit: maximum, actual: state.data.len() as u64 }), removed, completed), rest))
                } else {
                    let requests = part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset),
                        part1_fresh_reassembly_count(state.data.len(), 6));
                    match part1_mct_copy_run(requests, rest) {
                        None => None,
                        Some((Err(error), tail)) => Some(((Err(error), removed, completed), tail)),
                        Some((Ok(()), tail)) => match part1_fresh_mct_run(part1_fresh_mct_reassembled(state), limits, tail) {
                            None => None,
                            Some((Err(error), last)) => Some(((Err(error), removed, completed), last)),
                            Some((Ok(array), last)) => match part1_mct_copy_run(part1_fresh_mct_completed_requests(segment, completed), last) {
                                None => None,
                                Some((Err(error), end)) => Some(((Err(error), removed, completed), end)),
                                Some((Ok(()), end)) => Some(((Ok(Some(array)), removed, completed.push(segment.payload[3])), end)),
                            },
                        },
                    }
                }
            }
        },
    }
}

pub(crate) open spec fn part1_fresh_consume_mcc_run(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
    pending: Seq<Part1MccFragment>, completed: Seq<u8>, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<Option<Part1MctRecord>, crate::DecodeError>, Seq<Part1MccFragment>, Seq<u8>), Seq<Part1ColdStorageEvent>)> {
    match part1_fresh_prepare_mcc_run(segment, components, pending, completed, events) {
        None => None,
        Some(((Err(error), changed), rest)) => Some(((Err(error), changed, completed), rest)),
        Some(((Ok((index, maximum)), changed), rest)) => {
            let state = changed[index as int];
            if !part2_fragment_complete(state.next_index, state.final_index) { Some(((Ok(None), changed, completed), rest)) } else {
                let removed = part1_mcc_fragment_swap_remove(changed, index);
                if state.data.len() as u64 > maximum {
                    Some(((Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                        limit: maximum, actual: state.data.len() as u64 }), removed, completed), rest))
                } else {
                    let requests = part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset),
                        part1_fresh_reassembly_count(state.data.len(), 7));
                    match part1_mct_copy_run(requests, rest) {
                        None => None,
                        Some((Err(error), tail)) => Some(((Err(error), removed, completed), tail)),
                        Some((Ok(()), tail)) => match part1_fresh_mcc_run(part1_fresh_mcc_reassembled(state), components, limits, tail) {
                            None => None,
                            Some((Err(error), last)) => Some(((Err(error), removed, completed), last)),
                            Some((Ok(record), last)) => match part1_mct_copy_run(part1_fresh_mcc_completed_requests(segment, completed), last) {
                                None => None,
                                Some((Err(error), end)) => Some(((Err(error), removed, completed), end)),
                                Some((Ok(()), end)) => Some(((Ok(Some(record)), removed, completed.push(segment.payload[2])), end)),
                            },
                        },
                    }
                }
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_fresh_prepare_mct_result(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MctFragment>),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_prepare_mct_run(segment, limits, pending, completed, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_prepare_mcc_result(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MccFragment>),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_prepare_mcc_run(segment, components, pending, completed, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_consume_mct_result(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    result: (Result<Option<Part2MctArray>, crate::DecodeError>, Seq<Part1MctFragment>, Seq<u8>),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_consume_mct_run(segment, limits, pending, completed, events) == Some((result, Seq::empty()))
}
#[verifier::opaque]
pub(crate) open spec fn part1_fresh_consume_mcc_result(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
    pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    result: (Result<Option<Part1MctRecord>, crate::DecodeError>, Seq<Part1MccFragment>, Seq<u8>),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_fresh_prepare_mct_normal(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
)
    ensures part1_fresh_prepare_mct_result(segment, limits, pending, completed, part1_prepare_mct_fragment(segment, limits, pending, completed)),
{
    reveal(part1_fresh_prepare_mct_result);
    let requests = part1_fresh_prepare_mct_requests(segment, limits, pending, completed);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_prepare_mct_run(segment, limits, pending, completed, calls)
        == Some((part1_prepare_mct_fragment(segment, limits, pending, completed), Seq::empty())));
}
pub(crate) proof fn part1_fresh_prepare_mcc_normal(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
)
    ensures part1_fresh_prepare_mcc_result(segment, components, pending, completed, part1_prepare_mcc_fragment(segment, components, pending, completed)),
{
    reveal(part1_fresh_prepare_mcc_result);
    let requests = part1_fresh_prepare_mcc_requests(segment, components, pending, completed);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_fresh_prepare_mcc_run(segment, components, pending, completed, calls)
        == Some((part1_prepare_mcc_fragment(segment, components, pending, completed), Seq::empty())));
}
pub(crate) proof fn part1_fresh_prepare_mct_normal_rule(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
)
    ensures forall|result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MctFragment>)|
        result == part1_prepare_mct_fragment(segment, limits, pending, completed)
            ==> #[trigger] part1_fresh_prepare_mct_result(segment, limits, pending, completed, result),
{
    part1_fresh_prepare_mct_normal(segment, limits, pending, completed);
}
pub(crate) proof fn part1_fresh_prepare_mcc_normal_rule(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
)
    ensures forall|result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MccFragment>)|
        result == part1_prepare_mcc_fragment(segment, components, pending, completed)
            ==> #[trigger] part1_fresh_prepare_mcc_result(segment, components, pending, completed, result),
{
    part1_fresh_prepare_mcc_normal(segment, components, pending, completed);
}
pub(crate) proof fn part1_fresh_prepare_mct_refused(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
)
    requires part1_mct_copy_result(part1_fresh_prepare_mct_requests(segment, limits, pending, completed), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_prepare_mct_result(segment, limits, pending, completed, (Err(crate::DecodeError::AllocationFailed), pending)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_prepare_mct_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_prepare_mct_requests(segment, limits, pending, completed), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_prepare_mct_run(segment, limits, pending, completed, calls)
        == Some(((Err(crate::DecodeError::AllocationFailed), pending), Seq::empty())));
}
pub(crate) proof fn part1_fresh_prepare_mcc_refused(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
)
    requires part1_mct_copy_result(part1_fresh_prepare_mcc_requests(segment, components, pending, completed), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_fresh_prepare_mcc_result(segment, components, pending, completed, (Err(crate::DecodeError::AllocationFailed), pending)),
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_prepare_mcc_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_prepare_mcc_requests(segment, components, pending, completed), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_fresh_prepare_mcc_run(segment, components, pending, completed, calls)
        == Some(((Err(crate::DecodeError::AllocationFailed), pending), Seq::empty())));
}

pub(crate) proof fn part1_fresh_prepare_mct_projection(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MctFragment>), calls: Seq<Part1ColdStorageEvent>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_prepare_mct_run(segment, limits, pending, completed, calls) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_prepare_mct_fragment(segment, limits, pending, completed),
{
    if let Some((copied, tail)) = part1_mct_copy_run(part1_fresh_prepare_mct_requests(segment, limits, pending, completed), calls) {
        part1_mct_copy_projection(part1_fresh_prepare_mct_requests(segment, limits, pending, completed), calls, copied, tail);
    }
}
pub(crate) proof fn part1_fresh_prepare_mcc_projection(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MccFragment>), calls: Seq<Part1ColdStorageEvent>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_prepare_mcc_run(segment, components, pending, completed, calls) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_prepare_mcc_fragment(segment, components, pending, completed),
{
    if let Some((copied, tail)) = part1_mct_copy_run(part1_fresh_prepare_mcc_requests(segment, components, pending, completed), calls) {
        part1_mct_copy_projection(part1_fresh_prepare_mcc_requests(segment, components, pending, completed), calls, copied, tail);
    }
}
pub(crate) proof fn part1_fresh_prepare_mct_observed(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MctFragment>),
)
    requires part1_fresh_prepare_mct_result(segment, limits, pending, completed, result),
    ensures result.0 != Err(crate::DecodeError::AllocationFailed) ==> result == part1_prepare_mct_fragment(segment, limits, pending, completed),
{
    reveal(part1_fresh_prepare_mct_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_prepare_mct_run(segment, limits, pending, completed, calls) == Some((result, Seq::empty()));
    if result.0 != Err(crate::DecodeError::AllocationFailed) {
        part1_fresh_prepare_mct_projection(segment, limits, pending, completed, result, calls, Seq::empty());
    }
}
pub(crate) proof fn part1_fresh_prepare_mcc_observed(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    result: (Result<(usize, u64), crate::DecodeError>, Seq<Part1MccFragment>),
)
    requires part1_fresh_prepare_mcc_result(segment, components, pending, completed, result),
    ensures result.0 != Err(crate::DecodeError::AllocationFailed) ==> result == part1_prepare_mcc_fragment(segment, components, pending, completed),
{
    reveal(part1_fresh_prepare_mcc_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_prepare_mcc_run(segment, components, pending, completed, calls) == Some((result, Seq::empty()));
    if result.0 != Err(crate::DecodeError::AllocationFailed) {
        part1_fresh_prepare_mcc_projection(segment, components, pending, completed, result, calls, Seq::empty());
    }
}

pub(crate) open spec fn part1_fresh_consume_mct_calls(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
) -> Seq<Part1ColdStorageEvent> {
    let first = part1_mct_copy_normal_calls(part1_fresh_prepare_mct_requests(segment, limits, pending, completed));
    let prepared = part1_prepare_mct_fragment(segment, limits, pending, completed);
    match prepared.0 {
        Err(_) => first,
        Ok((index, maximum)) => {
            let state = prepared.1[index as int];
            if !part2_fragment_complete(state.next_index, state.final_index) || state.data.len() as u64 > maximum { first } else {
                first + part1_mct_copy_normal_calls(part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset),
                    part1_fresh_reassembly_count(state.data.len(), 6)))
                    + part1_mct_copy_normal_calls(part1_fresh_mct_requests(part1_fresh_mct_reassembled(state), limits))
                    + part1_mct_copy_normal_calls(if part1_parse_mct(part1_fresh_mct_reassembled(state), limits).is_ok() {
                        part1_fresh_mct_completed_requests(segment, completed)
                    } else { Seq::empty() })
            }
        },
    }
}
pub(crate) open spec fn part1_fresh_consume_mcc_calls(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
) -> Seq<Part1ColdStorageEvent> {
    let first = part1_mct_copy_normal_calls(part1_fresh_prepare_mcc_requests(segment, components, pending, completed));
    let prepared = part1_prepare_mcc_fragment(segment, components, pending, completed);
    match prepared.0 {
        Err(_) => first,
        Ok((index, maximum)) => {
            let state = prepared.1[index as int];
            if !part2_fragment_complete(state.next_index, state.final_index) || state.data.len() as u64 > maximum { first } else {
                first + part1_mct_copy_normal_calls(part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset),
                    part1_fresh_reassembly_count(state.data.len(), 7)))
                    + part1_mct_copy_normal_calls(part1_fresh_mcc_requests(part1_fresh_mcc_reassembled(state), components, limits))
                    + part1_mct_copy_normal_calls(if part1_parse_mcc(part1_fresh_mcc_reassembled(state), components, limits).is_ok() {
                        part1_fresh_mcc_completed_requests(segment, completed)
                    } else { Seq::empty() })
            }
        },
    }
}
pub(crate) proof fn part1_fresh_consume_mct_normal(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_fresh_consume_mct_run(segment, limits, pending, completed,
        part1_fresh_consume_mct_calls(segment, limits, pending, completed) + tail)
            == Some((part1_consume_mct_fragment(segment, limits, pending, completed), tail)),
        part1_fresh_consume_mct_result(segment, limits, pending, completed, part1_consume_mct_fragment(segment, limits, pending, completed)),
{
    reveal(part1_consume_mct_fragment); reveal(part1_fresh_consume_mct_result);
    let first = part1_fresh_prepare_mct_requests(segment, limits, pending, completed);
    let prepared = part1_prepare_mct_fragment(segment, limits, pending, completed);
    let mut later = Seq::empty();
    if let Ok((index, maximum)) = prepared.0 {
        let state = prepared.1[index as int];
        if part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum {
            let second = part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6));
            let third = part1_fresh_mct_requests(part1_fresh_mct_reassembled(state), limits);
            let fourth = if part1_parse_mct(part1_fresh_mct_reassembled(state), limits).is_ok() {
                part1_fresh_mct_completed_requests(segment, completed)
            } else { Seq::empty() };
            let final_calls = part1_mct_copy_normal_calls(fourth);
            later = part1_mct_copy_normal_calls(second) + part1_mct_copy_normal_calls(third) + final_calls;
            part1_mct_copy_normal(fourth, tail); part1_mct_copy_normal(fourth, Seq::empty());
            part1_mct_copy_normal(third, final_calls + tail);
            part1_mct_copy_normal(second, part1_mct_copy_normal_calls(third) + (final_calls + tail));
            part1_mct_copy_normal(third, final_calls);
            part1_mct_copy_normal(second, part1_mct_copy_normal_calls(third) + final_calls);
            assert(later =~= part1_mct_copy_normal_calls(second) + (part1_mct_copy_normal_calls(third) + final_calls));
            if fourth.len()==0 {assert(final_calls =~= Seq::<Part1ColdStorageEvent>::empty());}
            assert((later + tail) =~= part1_mct_copy_normal_calls(second) + (part1_mct_copy_normal_calls(third) + (final_calls + tail)));
        }
    }
    part1_mct_copy_normal(first, later + tail); part1_mct_copy_normal(first, later);
    assert(part1_fresh_consume_mct_calls(segment, limits, pending, completed) =~= part1_mct_copy_normal_calls(first) + later);
    assert((part1_mct_copy_normal_calls(first) + later) + tail =~= part1_mct_copy_normal_calls(first) + (later + tail));
    assert(part1_fresh_consume_mct_run(segment, limits, pending, completed, part1_fresh_consume_mct_calls(segment, limits, pending, completed))
        == Some((part1_consume_mct_fragment(segment, limits, pending, completed), Seq::empty())));
}
pub(crate) proof fn part1_fresh_consume_mcc_normal(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
    pending: Seq<Part1MccFragment>, completed: Seq<u8>, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_fresh_consume_mcc_run(segment, components, limits, pending, completed,
        part1_fresh_consume_mcc_calls(segment, components, limits, pending, completed) + tail)
            == Some((part1_consume_mcc_fragment(segment, components, limits, pending, completed), tail)),
        part1_fresh_consume_mcc_result(segment, components, limits, pending, completed, part1_consume_mcc_fragment(segment, components, limits, pending, completed)),
{
    reveal(part1_consume_mcc_fragment); reveal(part1_fresh_consume_mcc_result);
    let first = part1_fresh_prepare_mcc_requests(segment, components, pending, completed);
    let prepared = part1_prepare_mcc_fragment(segment, components, pending, completed);
    let mut later = Seq::empty();
    if let Ok((index, maximum)) = prepared.0 {
        let state = prepared.1[index as int];
        if part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum {
            let second = part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7));
            let third = part1_fresh_mcc_requests(part1_fresh_mcc_reassembled(state), components, limits);
            let fourth = if part1_parse_mcc(part1_fresh_mcc_reassembled(state), components, limits).is_ok() {
                part1_fresh_mcc_completed_requests(segment, completed)
            } else { Seq::empty() };
            let final_calls = part1_mct_copy_normal_calls(fourth);
            later = part1_mct_copy_normal_calls(second) + part1_mct_copy_normal_calls(third) + final_calls;
            part1_mct_copy_normal(fourth, tail); part1_mct_copy_normal(fourth, Seq::empty());
            part1_mct_copy_normal(third, final_calls + tail);
            part1_mct_copy_normal(second, part1_mct_copy_normal_calls(third) + (final_calls + tail));
            part1_mct_copy_normal(third, final_calls);
            part1_mct_copy_normal(second, part1_mct_copy_normal_calls(third) + final_calls);
            assert(later =~= part1_mct_copy_normal_calls(second) + (part1_mct_copy_normal_calls(third) + final_calls));
            if fourth.len()==0 {assert(final_calls =~= Seq::<Part1ColdStorageEvent>::empty());}
            assert((later + tail) =~= part1_mct_copy_normal_calls(second) + (part1_mct_copy_normal_calls(third) + (final_calls + tail)));
        }
    }
    part1_mct_copy_normal(first, later + tail); part1_mct_copy_normal(first, later);
    assert(part1_fresh_consume_mcc_calls(segment, components, limits, pending, completed) =~= part1_mct_copy_normal_calls(first) + later);
    assert((part1_mct_copy_normal_calls(first) + later) + tail =~= part1_mct_copy_normal_calls(first) + (later + tail));
    assert(part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, part1_fresh_consume_mcc_calls(segment, components, limits, pending, completed))
        == Some((part1_consume_mcc_fragment(segment, components, limits, pending, completed), Seq::empty())));
}

pub(crate) proof fn part1_fresh_consume_mct_prepare_error(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    error: crate::DecodeError, changed: Seq<Part1MctFragment>,
)
    requires part1_fresh_prepare_mct_result(segment, limits, pending, completed, (Err(error), changed)),
    ensures part1_fresh_consume_mct_result(segment, limits, pending, completed, (Err(error), changed, completed)),
{
    reveal(part1_fresh_prepare_mct_result); reveal(part1_fresh_consume_mct_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_prepare_mct_run(segment, limits, pending, completed, calls) == Some(((Err(error), changed), Seq::empty()));
    assert(part1_fresh_consume_mct_run(segment, limits, pending, completed, calls) == Some(((Err(error), changed, completed), Seq::empty())));
}
pub(crate) proof fn part1_fresh_consume_mcc_prepare_error(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    error: crate::DecodeError, changed: Seq<Part1MccFragment>,
)
    requires part1_fresh_prepare_mcc_result(segment, components, pending, completed, (Err(error), changed)),
    ensures part1_fresh_consume_mcc_result(segment, components, limits, pending, completed, (Err(error), changed, completed)),
{
    reveal(part1_fresh_prepare_mcc_result); reveal(part1_fresh_consume_mcc_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_prepare_mcc_run(segment, components, pending, completed, calls) == Some(((Err(error), changed), Seq::empty()));
    assert(part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, calls) == Some(((Err(error), changed, completed), Seq::empty())));
}

pub(crate) proof fn part1_fresh_consume_mct_reassembly_error(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
)
    requires match part1_prepare_mct_fragment(segment, limits, pending, completed) {
        (Ok((index, maximum)), changed) => {
            let state = changed[index as int];
            part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum
            && part1_mct_copy_result(part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6)),
                Err(crate::DecodeError::AllocationFailed))
        }, _ => false,
    },
    ensures match part1_prepare_mct_fragment(segment, limits, pending, completed) {
        (Ok((index, _)), changed) => part1_fresh_consume_mct_result(segment, limits, pending, completed,
            (Err(crate::DecodeError::AllocationFailed), part1_mct_fragment_swap_remove(changed, index), completed)), _ => false,
    },
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_consume_mct_result);
    let prepared = part1_prepare_mct_fragment(segment, limits, pending, completed);
    if let Ok((index, maximum)) = prepared.0 {
        let state = prepared.1[index as int];
        let second = part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6));
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(second, calls) == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
        let first = part1_fresh_prepare_mct_requests(segment, limits, pending, completed);
        part1_mct_copy_normal(first, calls);
        assert(part1_fresh_consume_mct_run(segment, limits, pending, completed, part1_mct_copy_normal_calls(first) + calls)
            == Some(((Err(crate::DecodeError::AllocationFailed), part1_mct_fragment_swap_remove(prepared.1, index), completed), Seq::empty())));
    }
}
pub(crate) proof fn part1_fresh_consume_mcc_reassembly_error(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
)
    requires match part1_prepare_mcc_fragment(segment, components, pending, completed) {
        (Ok((index, maximum)), changed) => {
            let state = changed[index as int];
            part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum
            && part1_mct_copy_result(part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7)),
                Err(crate::DecodeError::AllocationFailed))
        }, _ => false,
    },
    ensures match part1_prepare_mcc_fragment(segment, components, pending, completed) {
        (Ok((index, _)), changed) => part1_fresh_consume_mcc_result(segment, components, limits, pending, completed,
            (Err(crate::DecodeError::AllocationFailed), part1_mcc_fragment_swap_remove(changed, index), completed)), _ => false,
    },
{
    reveal(part1_mct_copy_result); reveal(part1_fresh_consume_mcc_result);
    let prepared = part1_prepare_mcc_fragment(segment, components, pending, completed);
    if let Ok((index, maximum)) = prepared.0 {
        let state = prepared.1[index as int];
        let second = part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7));
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(second, calls) == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
        let first = part1_fresh_prepare_mcc_requests(segment, components, pending, completed);
        part1_mct_copy_normal(first, calls);
        assert(part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, part1_mct_copy_normal_calls(first) + calls)
            == Some(((Err(crate::DecodeError::AllocationFailed), part1_mcc_fragment_swap_remove(prepared.1, index), completed), Seq::empty())));
    }
}

pub(crate) proof fn part1_fresh_consume_mct_parsed(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    parsed: Result<Part2MctArray, crate::DecodeError>, capacity: Result<(), crate::DecodeError>,
)
    requires match part1_prepare_mct_fragment(segment, limits, pending, completed) {
        (Ok((index, maximum)), changed) => {
            let state = changed[index as int];
            part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum
            && part1_fresh_mct_result(part1_fresh_mct_reassembled(state), limits, parsed)
            && part1_mct_copy_result(part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6)), Ok(()))
        }, _ => false,
    },
        parsed.is_ok() ==> part1_mct_copy_result(part1_fresh_mct_completed_requests(segment, completed), capacity),
        parsed.is_err() ==> capacity.is_ok(),
    ensures match part1_prepare_mct_fragment(segment, limits, pending, completed) {
        (Ok((index, _)), changed) => part1_fresh_consume_mct_result(segment, limits, pending, completed,
            (match parsed { Err(error) => Err(error), Ok(value) => match capacity {Err(error)=>Err(error),Ok(())=>Ok(Some(value))} },
                part1_mct_fragment_swap_remove(changed, index),
                if parsed.is_ok() && capacity.is_ok() { completed.push(segment.payload[3]) } else { completed })), _ => false,
    },
{
    reveal(part1_fresh_mct_result); reveal(part1_fresh_consume_mct_result); reveal(part1_mct_copy_result);
    let prepared = part1_prepare_mct_fragment(segment, limits, pending, completed);
    if let Ok((index, maximum)) = prepared.0 {
        let state = prepared.1[index as int];
        let raw = part1_fresh_mct_reassembled(state);
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mct_run(raw, limits, calls) == Some((parsed, Seq::empty()));
        let last = if parsed.is_ok() {
            choose|events: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_mct_completed_requests(segment, completed), events)
                == Some((capacity, Seq::empty()))
        } else { Seq::empty() };
        part1_fresh_mct_frame(raw, limits, calls, parsed, Seq::empty(), last);
        assert(Seq::<Part1ColdStorageEvent>::empty() + last =~= last);
        let second = part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6));
        let first = part1_fresh_prepare_mct_requests(segment, limits, pending, completed);
        part1_mct_copy_normal(second, calls + last); part1_mct_copy_normal(first, part1_mct_copy_normal_calls(second) + (calls + last));
        assert(part1_fresh_consume_mct_run(segment, limits, pending, completed, part1_mct_copy_normal_calls(first) + (part1_mct_copy_normal_calls(second) + (calls + last)))
            == Some(((match parsed { Err(error) => Err(error), Ok(value) => match capacity {Err(error)=>Err(error),Ok(())=>Ok(Some(value))} },
                part1_mct_fragment_swap_remove(prepared.1, index),
                if parsed.is_ok() && capacity.is_ok() { completed.push(segment.payload[3]) } else { completed }), Seq::empty())));
    }
}
pub(crate) proof fn part1_fresh_consume_mcc_parsed(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    parsed: Result<Part1MctRecord, crate::DecodeError>, capacity: Result<(), crate::DecodeError>,
)
    requires match part1_prepare_mcc_fragment(segment, components, pending, completed) {
        (Ok((index, maximum)), changed) => {
            let state = changed[index as int];
            part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum
            && part1_fresh_mcc_result(part1_fresh_mcc_reassembled(state), components, limits, parsed)
            && part1_mct_copy_result(part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7)), Ok(()))
        }, _ => false,
    },
        parsed.is_ok() ==> part1_mct_copy_result(part1_fresh_mcc_completed_requests(segment, completed), capacity),
        parsed.is_err() ==> capacity.is_ok(),
    ensures match part1_prepare_mcc_fragment(segment, components, pending, completed) {
        (Ok((index, _)), changed) => part1_fresh_consume_mcc_result(segment, components, limits, pending, completed,
            (match parsed { Err(error) => Err(error), Ok(value) => match capacity {Err(error)=>Err(error),Ok(())=>Ok(Some(value))} },
                part1_mcc_fragment_swap_remove(changed, index),
                if parsed.is_ok() && capacity.is_ok() { completed.push(segment.payload[2]) } else { completed })), _ => false,
    },
{
    reveal(part1_fresh_mcc_result); reveal(part1_fresh_consume_mcc_result); reveal(part1_mct_copy_result);
    let prepared = part1_prepare_mcc_fragment(segment, components, pending, completed);
    if let Ok((index, maximum)) = prepared.0 {
        let state = prepared.1[index as int];
        let raw = part1_fresh_mcc_reassembled(state);
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mcc_run(raw, components, limits, calls) == Some((parsed, Seq::empty()));
        let last = if parsed.is_ok() {
            choose|events: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_fresh_mcc_completed_requests(segment, completed), events)
                == Some((capacity, Seq::empty()))
        } else { Seq::empty() };
        part1_fresh_mcc_frame(raw, components, limits, calls, parsed, Seq::empty(), last);
        assert(Seq::<Part1ColdStorageEvent>::empty() + last =~= last);
        let second = part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7));
        let first = part1_fresh_prepare_mcc_requests(segment, components, pending, completed);
        part1_mct_copy_normal(second, calls + last); part1_mct_copy_normal(first, part1_mct_copy_normal_calls(second) + (calls + last));
        assert(part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, part1_mct_copy_normal_calls(first) + (part1_mct_copy_normal_calls(second) + (calls + last)))
            == Some(((match parsed { Err(error) => Err(error), Ok(value) => match capacity {Err(error)=>Err(error),Ok(())=>Ok(Some(value))} },
                part1_mcc_fragment_swap_remove(prepared.1, index),
                if parsed.is_ok() && capacity.is_ok() { completed.push(segment.payload[2]) } else { completed }), Seq::empty())));
    }
}

pub(crate) proof fn part1_fresh_mct_frame(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<Part2MctArray, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_mct_run(segment, limits, events) == Some((result, rest)),
    ensures part1_fresh_mct_run(segment, limits, events + tail) == Some((result, rest + tail)),
{
    let requests = part1_fresh_mct_requests(segment, limits);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_frame(requests, events, copied, after, tail); }
}
pub(crate) proof fn part1_fresh_mcc_frame(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<Part1MctRecord, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_mcc_run(segment, components, limits, events) == Some((result, rest)),
    ensures part1_fresh_mcc_run(segment, components, limits, events + tail) == Some((result, rest + tail)),
{
    let requests = part1_fresh_mcc_requests(segment, components, limits);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_frame(requests, events, copied, after, tail); }
}
pub(crate) proof fn part1_fresh_mco_frame(
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
    result: Result<Seq<u8>, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_mco_run(segment, events) == Some((result, rest)),
    ensures part1_fresh_mco_run(segment, events + tail) == Some((result, rest + tail)),
{
    let requests = part1_fresh_mco_requests(segment);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_frame(requests, events, copied, after, tail); }
}
pub(crate) proof fn part1_fresh_mct_projection(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<Part2MctArray, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_mct_run(segment, limits, events) == Some((result, rest)), result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_parse_mct(segment, limits),
{
    let requests = part1_fresh_mct_requests(segment, limits);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_projection(requests, events, copied, after); }
}
pub(crate) proof fn part1_fresh_mcc_projection(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<Part1MctRecord, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_mcc_run(segment, components, limits, events) == Some((result, rest)), result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_parse_mcc(segment, components, limits),
{
    let requests = part1_fresh_mcc_requests(segment, components, limits);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_projection(requests, events, copied, after); }
}
pub(crate) proof fn part1_fresh_mco_projection(
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
    result: Result<Seq<u8>, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_mco_run(segment, events) == Some((result, rest)), result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_parse_mco(segment),
{
    let requests = part1_fresh_mco_requests(segment);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_projection(requests, events, copied, after); }
}

pub(crate) proof fn part1_fresh_consume_mct_frame(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>, result: (Result<Option<Part2MctArray>, crate::DecodeError>, Seq<Part1MctFragment>, Seq<u8>),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_consume_mct_run(segment, limits, pending, completed, events) == Some((result, rest)),
    ensures part1_fresh_consume_mct_run(segment, limits, pending, completed, events + tail) == Some((result, rest + tail)),
{
    let first = part1_fresh_prepare_mct_requests(segment, limits, pending, completed);
    if let Some((unit, after)) = part1_mct_copy_run(first, events) { part1_mct_copy_frame(first, events, unit, after, tail); }
    if let Some(((Ok((index, maximum)), changed), after)) = part1_fresh_prepare_mct_run(segment, limits, pending, completed, events) {
        let state = changed[index as int];
        if part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum {
            let second = part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6));
            if let Some((unit, after_second)) = part1_mct_copy_run(second, after) {
                part1_mct_copy_frame(second, after, unit, after_second, tail);
                if unit.is_ok() {
                    if let Some((parsed, last)) = part1_fresh_mct_run(part1_fresh_mct_reassembled(state), limits, after_second) {
                        part1_fresh_mct_frame(part1_fresh_mct_reassembled(state), limits, after_second, parsed, last, tail);
                        if parsed.is_ok() {
                            let fourth=part1_fresh_mct_completed_requests(segment, completed);
                            if let Some((capacity,end))=part1_mct_copy_run(fourth,last) {
                                part1_mct_copy_frame(fourth,last,capacity,end,tail);
                            }
                        }
                    }
                }
            }
        }
    }
}
pub(crate) proof fn part1_fresh_consume_mcc_frame(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>, result: (Result<Option<Part1MctRecord>, crate::DecodeError>, Seq<Part1MccFragment>, Seq<u8>),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, events) == Some((result, rest)),
    ensures part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, events + tail) == Some((result, rest + tail)),
{
    let first = part1_fresh_prepare_mcc_requests(segment, components, pending, completed);
    if let Some((unit, after)) = part1_mct_copy_run(first, events) { part1_mct_copy_frame(first, events, unit, after, tail); }
    if let Some(((Ok((index, maximum)), changed), after)) = part1_fresh_prepare_mcc_run(segment, components, pending, completed, events) {
        let state = changed[index as int];
        if part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum {
            let second = part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7));
            if let Some((unit, after_second)) = part1_mct_copy_run(second, after) {
                part1_mct_copy_frame(second, after, unit, after_second, tail);
                if unit.is_ok() {
                    if let Some((parsed, last)) = part1_fresh_mcc_run(part1_fresh_mcc_reassembled(state), components, limits, after_second) {
                        part1_fresh_mcc_frame(part1_fresh_mcc_reassembled(state), components, limits, after_second, parsed, last, tail);
                        if parsed.is_ok() {
                            let fourth=part1_fresh_mcc_completed_requests(segment, completed);
                            if let Some((capacity,end))=part1_mct_copy_run(fourth,last) {
                                part1_mct_copy_frame(fourth,last,capacity,end,tail);
                            }
                        }
                    }
                }
            }
        }
    }
}
pub(crate) proof fn part1_fresh_consume_mct_projection(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>, result: (Result<Option<Part2MctArray>, crate::DecodeError>, Seq<Part1MctFragment>, Seq<u8>), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_consume_mct_run(segment, limits, pending, completed, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_consume_mct_fragment(segment, limits, pending, completed),
{
    reveal(part1_consume_mct_fragment);
    if let Some((prepared, after)) = part1_fresh_prepare_mct_run(segment, limits, pending, completed, events) {
        part1_fresh_prepare_mct_projection(segment, limits, pending, completed, prepared, events, after);
        if let Ok((index, maximum)) = prepared.0 {
            let state = prepared.1[index as int];
            if part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum {
                let second = part1_fresh_leaf(FreshMarkerPath::MctReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 6));
                if let Some((unit, after_second)) = part1_mct_copy_run(second, after) {
                    part1_mct_copy_projection(second, after, unit, after_second);
                    if unit.is_ok() {
                        if let Some((parsed, last)) = part1_fresh_mct_run(part1_fresh_mct_reassembled(state), limits, after_second) {
                            part1_fresh_mct_projection(part1_fresh_mct_reassembled(state), limits, after_second, parsed, last);
                            if parsed.is_ok() {
                                let fourth=part1_fresh_mct_completed_requests(segment, completed);
                                if let Some((capacity,end))=part1_mct_copy_run(fourth,last) {
                                    part1_mct_copy_projection(fourth,last,capacity,end);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub(crate) proof fn part1_fresh_consume_mcc_projection(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    events: Seq<Part1ColdStorageEvent>, result: (Result<Option<Part1MctRecord>, crate::DecodeError>, Seq<Part1MccFragment>, Seq<u8>), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_consume_mcc_run(segment, components, limits, pending, completed, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_consume_mcc_fragment(segment, components, limits, pending, completed),
{
    reveal(part1_consume_mcc_fragment);
    if let Some((prepared, after)) = part1_fresh_prepare_mcc_run(segment, components, pending, completed, events) {
        part1_fresh_prepare_mcc_projection(segment, components, pending, completed, prepared, events, after);
        if let Ok((index, maximum)) = prepared.0 {
            let state = prepared.1[index as int];
            if part2_fragment_complete(state.next_index, state.final_index) && state.data.len() as u64 <= maximum {
                let second = part1_fresh_leaf(FreshMarkerPath::MccReassembly(state.offset), part1_fresh_reassembly_count(state.data.len(), 7));
                if let Some((unit, after_second)) = part1_mct_copy_run(second, after) {
                    part1_mct_copy_projection(second, after, unit, after_second);
                    if unit.is_ok() {
                        if let Some((parsed, last)) = part1_fresh_mcc_run(part1_fresh_mcc_reassembled(state), components, limits, after_second) {
                            part1_fresh_mcc_projection(part1_fresh_mcc_reassembled(state), components, limits, after_second, parsed, last);
                            if parsed.is_ok() {
                                let fourth=part1_fresh_mcc_completed_requests(segment, completed);
                                if let Some((capacity,end))=part1_mct_copy_run(fourth,last) {
                                    part1_mct_copy_projection(fourth,last,capacity,end);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

}
