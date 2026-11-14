//! Flat POC storage and exact ordered construction/copy responses.

use super::*;

verus! {

pub(crate) open spec fn part1_poc_storage_shape(segment: Part1CodestreamSegment, components: u16) -> bool {
    let width = if components < 257 { 7int } else { 9int };
    segment.payload.len() > 0 && (segment.payload.len() as int) % width == 0
}

pub(crate) open spec fn part1_poc_storage_elements(segment: Part1CodestreamSegment, components: u16) -> usize {
    (segment.payload.len() / if components < 257 { 7nat } else { 9nat }) as usize
}

pub(crate) open spec fn part1_parse_poc_storage(
    segment: Part1CodestreamSegment, components: u16, reserved: bool,
) -> Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError> {
    if !part1_poc_storage_shape(segment, components) || reserved {
        part1_parse_poc(segment, components)
    } else { Err(crate::DecodeError::AllocationFailed) }
}

pub(crate) open spec fn part1_parse_poc_storage_result(
    segment: Part1CodestreamSegment, components: u16,
    result: Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>,
) -> bool {
    exists|reserved: bool| result == part1_parse_poc_storage(segment, components, reserved)
}

pub(crate) proof fn part1_parse_poc_storage_observed(
    segment: Part1CodestreamSegment, components: u16, reserved: bool,
    result: Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>,
)
    requires result == part1_parse_poc_storage(segment, components, reserved),
    ensures part1_parse_poc_storage_result(segment, components, result),
{
    assert(exists|response: bool| result == part1_parse_poc_storage(segment, components, response));
}

pub(crate) proof fn part1_parse_poc_storage_normal(segment: Part1CodestreamSegment, components: u16)
    ensures part1_parse_poc_storage_result(segment, components, part1_parse_poc(segment, components)),
{
    part1_parse_poc_storage_observed(segment, components, true, part1_parse_poc(segment, components));
}

pub(crate) open spec fn part1_poc_cold_run(
    site: u8, segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    if !part1_poc_storage_shape(segment, components) {
        Some((part1_parse_poc(segment, components), events))
    } else {
        match part1_quantization_storage_request(site, part1_poc_storage_elements(segment, components), events) {
            None => None,
            Some((Err(error), rest)) => Some((Err(error), rest)),
            Some((Ok(()), rest)) => Some((part1_parse_poc(segment, components), rest)),
        }
    }
}

pub(crate) open spec fn part1_poc_normal_calls(
    site: u8, segment: Part1CodestreamSegment, components: u16,
) -> Seq<Part1ColdStorageEvent> {
    if part1_poc_storage_shape(segment, components) {
        seq![Part1ColdStorageEvent { site, elements: part1_poc_storage_elements(segment, components), succeeded: true }]
    } else { Seq::empty() }
}

pub(crate) proof fn part1_poc_cold_normal(
    site: u8, segment: Part1CodestreamSegment, components: u16, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_poc_cold_run(site, segment, components, part1_poc_normal_calls(site, segment, components) + tail)
        == Some((part1_parse_poc(segment, components), tail)),
{
    if part1_poc_storage_shape(segment, components) {
        let response = Part1ColdStorageEvent {
            site, elements: part1_poc_storage_elements(segment, components), succeeded: true };
        assert((seq![response] + tail).drop_first() =~= tail);
    } else { assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail); }
}

pub(crate) proof fn part1_poc_cold_frame(
    site: u8, segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>,
    result: Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>,
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_poc_cold_run(site, segment, components, events) == Some((result, rest)),
    ensures part1_poc_cold_run(site, segment, components, events + tail) == Some((result, rest + tail)),
{
    if events.len() > 0 { assert((events + tail).drop_first() =~= events.drop_first() + tail); }
}

pub(crate) proof fn part1_poc_cold_projection(
    site: u8, segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>,
    result: Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_poc_cold_run(site, segment, components, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_parse_poc(segment, components),
{
}

pub(crate) proof fn part1_poc_cold_observed(
    site: u8, segment: Part1CodestreamSegment, components: u16,
    result: Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>,
) -> (calls: Seq<Part1ColdStorageEvent>)
    requires part1_parse_poc_storage_result(segment, components, result),
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_poc_cold_run(site, segment, components, calls + tail) == Some((result, tail)),
{
    let reserved = choose|reserved: bool| result == part1_parse_poc_storage(segment, components, reserved);
    if part1_poc_storage_shape(segment, components) {
        let response = Part1ColdStorageEvent {
            site, elements: part1_poc_storage_elements(segment, components), succeeded: reserved };
        assert forall|tail: Seq<Part1ColdStorageEvent>|
            part1_poc_cold_run(site, segment, components, seq![response] + tail) == Some((result, tail)) by {
            assert((seq![response] + tail).drop_first() =~= tail);
        }
        seq![response]
    } else {
        assert forall|tail: Seq<Part1ColdStorageEvent>|
            part1_poc_cold_run(site, segment, components, Seq::empty() + tail) == Some((result, tail)) by {
            assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
        }
        Seq::empty()
    }
}

pub(crate) open spec fn part1_progression_owner_copy_result(
    source: Seq<crate::codestream::ProgressionChange>,
    result: Result<crate::codestream::ProgressionChanges, crate::DecodeError>,
) -> bool {
    match result {
        Err(error) => source.len() > 0 && error == crate::DecodeError::AllocationFailed,
        Ok(owner) => crate::codestream::progression_changes_view(&owner) == source,
    }
}

}
