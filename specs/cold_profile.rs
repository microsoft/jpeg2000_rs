//! Fresh profile words at the original read frontier, excluding growth.
use super::*;
use crate::codestream::MctCopyPath;
verus! {

pub(crate) enum ProfileFreshInput {
    Words(Part1CodestreamSegment, usize),
    Cap(Part1CodestreamSegment),
    Number(Part1CodestreamSegment),
}
pub(crate) enum ProfileFreshValue {
    Words(Result<Seq<u16>, crate::DecodeError>),
    Cap(Result<(u32, Seq<u16>), crate::DecodeError>),
    Number(Result<Seq<u16>, crate::DecodeError>),
}
pub(crate) open spec fn part1_profile_words_requests(segment: Part1CodestreamSegment, start: usize) -> Seq<Part1MctCopyRequest> {
    if start > segment.payload.len() { Seq::empty() } else {
        part1_mct_copy_leaf(MctCopyPath::ProfileWords(segment.marker, segment.offset, start), ((segment.payload.len() - start) / 2) as usize)
    }
}
pub(crate) open spec fn part1_profile_requests(input: ProfileFreshInput) -> Seq<Part1MctCopyRequest> {
    match input {
        ProfileFreshInput::Words(segment, start) => part1_profile_words_requests(segment, start),
        ProfileFreshInput::Cap(segment) => if segment.payload.len() < 4 { Seq::empty() } else {
            let p = part1_siz_word(segment.payload, 0);
            if p == 0 || segment.payload.len() != part15_cap_payload_length(part1_set_bits_prefix(p, 32) as u8) { Seq::empty() }
            else { part1_profile_words_requests(segment, 4) }
        },
        ProfileFreshInput::Number(segment) => if segment.payload.len() < 2 || segment.payload.len() % 2 != 0 { Seq::empty() }
            else { part1_profile_words_requests(segment, 0) },
    }
}
pub(crate) open spec fn part1_profile_ordinary(input: ProfileFreshInput) -> ProfileFreshValue {
    match input {
        ProfileFreshInput::Words(segment, start) => ProfileFreshValue::Words(part1_marker_words(segment, start)),
        ProfileFreshInput::Cap(segment) => ProfileFreshValue::Cap(part1_parse_cap(segment)),
        ProfileFreshInput::Number(segment) => ProfileFreshValue::Number(part1_parse_profile_number(segment)),
    }
}
pub(crate) open spec fn part1_profile_failure(input: ProfileFreshInput) -> ProfileFreshValue {
    match input {
        ProfileFreshInput::Words(_, _) => ProfileFreshValue::Words(Err(crate::DecodeError::AllocationFailed)),
        ProfileFreshInput::Cap(_) => ProfileFreshValue::Cap(Err(crate::DecodeError::AllocationFailed)),
        ProfileFreshInput::Number(_) => ProfileFreshValue::Number(Err(crate::DecodeError::AllocationFailed)),
    }
}
pub(crate) open spec fn part1_profile_run(input: ProfileFreshInput, events: Seq<Part1ColdStorageEvent>) -> Option<(ProfileFreshValue, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_profile_requests(input), events) {
        None => None, Some((Err(_), rest)) => Some((part1_profile_failure(input), rest)),
        Some((Ok(()), rest)) => Some((part1_profile_ordinary(input), rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_profile_result(input: ProfileFreshInput, result: ProfileFreshValue) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_profile_run(input, events) == Some((result, Seq::empty()))
}
pub(crate) proof fn part1_profile_normal(input: ProfileFreshInput)
    ensures part1_profile_result(input, part1_profile_ordinary(input)),
{
    reveal(part1_profile_result);
    let requests = part1_profile_requests(input);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_profile_run(input, calls) == Some((part1_profile_ordinary(input), Seq::empty())));
}
pub(crate) proof fn part1_profile_refused(input: ProfileFreshInput)
    requires part1_mct_copy_result(part1_profile_requests(input), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_profile_result(input, part1_profile_failure(input)),
{
    reveal(part1_profile_result); reveal(part1_mct_copy_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_profile_requests(input), calls) == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_profile_run(input, calls) == Some((part1_profile_failure(input), Seq::empty())));
}
pub(crate) proof fn part1_profile_no_alloc(input: ProfileFreshInput)
    ensures part1_profile_ordinary(input) != part1_profile_failure(input),
{
    reveal(part1_parse_cap); reveal(part1_parse_profile_number); reveal(part1_marker_words);
}
pub(crate) proof fn part1_profile_observed(input: ProfileFreshInput, result: ProfileFreshValue)
    requires part1_profile_result(input, result),
    ensures part1_mct_copy_result(part1_profile_requests(input), if result == part1_profile_failure(input) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != part1_profile_failure(input) ==> result == part1_profile_ordinary(input),
{
    reveal(part1_profile_result); reveal(part1_mct_copy_result);
    part1_profile_no_alloc(input);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_profile_run(input, calls) == Some((result, Seq::empty()));
    if let Some((unit, rest)) = part1_mct_copy_run(part1_profile_requests(input), calls) {
        part1_mct_copy_projection(part1_profile_requests(input), calls, unit, rest);
        assert(part1_mct_copy_run(part1_profile_requests(input), calls) == Some((if result == part1_profile_failure(input) { Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }, Seq::empty())));
    }
}
pub(crate) open spec fn part1_profile_storage_result(input: ProfileFreshInput, result: ProfileFreshValue) -> bool {
    if result == part1_profile_failure(input) { part1_profile_result(input, result) }
    else { result == part1_profile_ordinary(input) }
}
pub(crate) proof fn part1_profile_storage_normal(input: ProfileFreshInput)
    ensures part1_profile_storage_result(input, part1_profile_ordinary(input)),
{
    part1_profile_normal(input);
}
pub(crate) proof fn part1_profile_storage_observed(input: ProfileFreshInput, result: ProfileFreshValue)
    requires part1_profile_storage_result(input, result),
    ensures part1_profile_result(input, result),
        result != part1_profile_failure(input) ==> result == part1_profile_ordinary(input),
{
    if result != part1_profile_failure(input) { part1_profile_normal(input); }
}
pub(crate) proof fn part1_profile_frame(input: ProfileFreshInput, events: Seq<Part1ColdStorageEvent>, result: ProfileFreshValue, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>)
    requires part1_profile_run(input, events) == Some((result, rest)),
    ensures part1_profile_run(input, events + tail) == Some((result, rest + tail)),
{
    if let Some((unit, after)) = part1_mct_copy_run(part1_profile_requests(input), events) {
        part1_mct_copy_frame(part1_profile_requests(input), events, unit, after, tail);
    }
}
pub(crate) proof fn part1_profile_projection(input: ProfileFreshInput, events: Seq<Part1ColdStorageEvent>, result: ProfileFreshValue, rest: Seq<Part1ColdStorageEvent>)
    requires part1_profile_run(input, events) == Some((result, rest)), result != part1_profile_failure(input),
    ensures result == part1_profile_ordinary(input),
{
    if let Some((unit, after)) = part1_mct_copy_run(part1_profile_requests(input), events) {
        part1_mct_copy_projection(part1_profile_requests(input), events, unit, after);
    }
}
pub(crate) proof fn part1_profile_storage_equivalent(input: ProfileFreshInput, result: ProfileFreshValue)
    requires part1_profile_result(input, result),
    ensures part1_profile_storage_result(input, result),
{
    reveal(part1_profile_result);
    if result != part1_profile_failure(input) {
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_profile_run(input, calls) == Some((result, Seq::empty()));
        part1_profile_projection(input, calls, result, Seq::empty());
    }
}

pub(crate) proof fn part1_profile_run_normal(input: ProfileFreshInput, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_profile_run(input, part1_mct_copy_normal_calls(part1_profile_requests(input)) + tail)
        == Some((part1_profile_ordinary(input), tail)),
{
    part1_mct_copy_normal(part1_profile_requests(input), tail);
}
pub(crate) open spec fn part1_profile_main_input(raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment) -> Option<ProfileFreshInput> {
    if segment.marker == 0xff50 && raw.capabilities.is_none() { Some(ProfileFreshInput::Cap(segment)) }
    else if (segment.marker == 0xff56 && raw.profile.is_none()) || (segment.marker == 0xff59 && raw.corresponding_profile.is_none()) {
        Some(ProfileFreshInput::Number(segment))
    } else { None }
}
pub(crate) open spec fn part1_profile_main_calls(raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment) -> Seq<Part1ColdStorageEvent> {
    match part1_profile_main_input(raw, segment) {
        None => Seq::empty(), Some(input) => part1_mct_copy_normal_calls(part1_profile_requests(input)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_profile_main_run<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>)
    -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    match part1_profile_main_input(raw, segment) {
        None => Some((part1_main_header_payload(reader, raw, segment), events)),
        Some(input) => match part1_profile_run(input, events) {
            None => None,
            Some((ProfileFreshValue::Cap(parsed), rest)) => Some((match parsed {
                Err(error) => (Err(error), reader, raw),
                Ok(capabilities) => (Ok(()), reader, Part1MainHeaderAccumulator { capabilities: Some(capabilities), ..raw }),
            }, rest)),
            Some((ProfileFreshValue::Number(parsed), rest)) => Some((match parsed {
                Err(error) => (Err(error), reader, raw),
                Ok(words) => (Ok(()), reader, if segment.marker == 0xff56 {
                    Part1MainHeaderAccumulator { profile: Some(words), ..raw }
                } else { Part1MainHeaderAccumulator { corresponding_profile: Some(words), ..raw } }),
            }, rest)),
            _ => None,
        },
    }
}
pub(crate) proof fn part1_profile_main_normal<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_profile_main_run(reader, raw, segment, part1_profile_main_calls(raw, segment) + tail)
        == Some((part1_main_header_payload(reader, raw, segment), tail)),
{
    reveal(part1_profile_main_run); reveal(part1_main_header_payload);
    if let Some(input) = part1_profile_main_input(raw, segment) { part1_profile_run_normal(input, tail); }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}
pub(crate) proof fn part1_profile_main_frame<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>)
    requires part1_profile_main_run(reader, raw, segment, events) == Some((result, rest)),
    ensures part1_profile_main_run(reader, raw, segment, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_profile_main_run);
    if let Some(input) = part1_profile_main_input(raw, segment) {
        if let Some((parsed, after)) = part1_profile_run(input, events) { part1_profile_frame(input, events, parsed, after, tail); }
    }
}
pub(crate) proof fn part1_profile_main_projection<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>)
    requires part1_profile_main_run(reader, raw, segment, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_main_header_payload(reader, raw, segment),
{
    reveal(part1_profile_main_run); reveal(part1_main_header_payload);
    if let Some(input) = part1_profile_main_input(raw, segment) {
        if let Some((parsed, after)) = part1_profile_run(input, events) { part1_profile_projection(input, events, parsed, after); }
    }
}
pub(crate) proof fn part1_cold_main_profile_step<'a>(initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, result: ProfileFreshValue)
    requires part1_cold_main_prefix(initial, reader, raw), part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        match part1_profile_main_input(raw, segment) { None => false, Some(input) => part1_profile_storage_result(input, result) },
    ensures match result {
        ProfileFreshValue::Cap(Err(error)) | ProfileFreshValue::Number(Err(error)) => part1_cold_layout_result(initial, Err(error)),
        _ => true,
    },
        match result {
            ProfileFreshValue::Cap(value) => value != Err(crate::DecodeError::AllocationFailed) ==> value == part1_parse_cap(segment),
            ProfileFreshValue::Number(value) => value != Err(crate::DecodeError::AllocationFailed) ==> value == part1_parse_profile_number(segment),
            _ => false,
        },
{
    reveal(part1_cold_main_prefix); reveal(part1_profile_result); reveal(part1_profile_main_run);
    let input = match part1_profile_main_input(raw, segment) { Some(input) => input, None => { assert(false); return; } };
    part1_profile_storage_observed(input, result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_profile_run(input, calls) == Some((result, Seq::empty()));
    if result != part1_profile_failure(input) { part1_profile_projection(input, calls, result, Seq::empty()); }
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_cold_main_prefix_at(initial, reader, raw, prefix);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    match result {
        ProfileFreshValue::Cap(Err(error)) | ProfileFreshValue::Number(Err(error)) => {
            reveal_with_fuel(part1_main_progression_continuation, 1);
            assert(part1_prepare_main_progression_run(initial, prefix + calls) == Some((Err(error), Seq::empty())));
            reveal(part1_cold_layout_result);
            assert(part1_layout_with_cold_storage(initial, prefix + calls) == Some((Err(error), Seq::empty())));
        },
        _ => {},
    }
}
pub(crate) proof fn part1_profile_tile_no_events<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, index: u8, lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>)
    requires segment.marker == 0xff50 || segment.marker == 0xff56 || segment.marker == 0xff59,
    ensures part1_tile_progression_payload(reader, raw, segment, components, index, lengths, headers, events)
        == Some((part1_tile_header_payload(reader, raw, segment, components, index, lengths, headers), events)),
{
}

}
