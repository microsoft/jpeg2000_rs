//! Fresh marker responses at actual main/tile dispatch, retaining partial owners.

use super::*;

verus! {

pub(crate) open spec fn part1_fresh_main_mct_array_requests(
    raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
) -> Seq<Part1MctCopyRequest> {
    part1_fresh_leaf(crate::codestream::FreshMarkerPath::MctRetainedMain(segment.offset, raw.arrays.len() as usize), 1)
}

pub(crate) open spec fn part1_fresh_main_mcc_record_requests(
    raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
) -> Seq<Part1MctCopyRequest> {
    part1_fresh_leaf(crate::codestream::FreshMarkerPath::MccRetainedMain(segment.offset, raw.records.len() as usize), 1)
}

#[verifier::opaque]
pub(crate) open spec fn part1_fresh_main_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    match segment.marker {
        0xff74 => match part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, events) {
            None => None, Some((result, rest)) => {
                let changed = Part1MainHeaderAccumulator { pending_mct: result.1, completed_mct: result.2, ..raw };
                match result.0 {
                    Err(error) => Some(((Err(error), reader, changed), rest)),
                    Ok(None) => Some(((Ok(()), reader, changed), rest)),
                    Ok(Some(array)) => match part1_mct_copy_run(part1_fresh_main_mct_array_requests(raw, segment), rest) {
                        None => None,
                        Some((Err(error), tail)) => Some(((Err(error), reader, changed), tail)),
                        Some((Ok(()), tail)) => {
                            let arrays = raw.arrays.push(array);
                            Some(((part1_mct_registry_unique_array(arrays, segment.offset), reader,
                                Part1MainHeaderAccumulator { arrays, ..changed }), tail))
                        },
                    },
                }
            },
        },
        0xff75 => match part1_fresh_consume_mcc_run(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc, events) {
            None => None, Some((result, rest)) => {
                let changed = Part1MainHeaderAccumulator { pending_mcc: result.1, completed_mcc: result.2, ..raw };
                match result.0 {
                    Err(error) => Some(((Err(error), reader, changed), rest)),
                    Ok(None) => Some(((Ok(()), reader, changed), rest)),
                    Ok(Some(record)) => match part1_mct_copy_run(part1_fresh_main_mcc_record_requests(raw, segment), rest) {
                        None => None,
                        Some((Err(error), tail)) => Some(((Err(error), reader, changed), tail)),
                        Some((Ok(()), tail)) => {
                            let records = raw.records.push(record);
                            Some(((part1_mct_registry_unique_record(records, segment.offset), reader,
                                Part1MainHeaderAccumulator { records, ..changed }), tail))
                        },
                    },
                }
            },
        },
        0xff77 => if raw.order.is_some() {
            Some(((Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), reader, raw), events))
        } else {
            match part1_fresh_mco_run(segment, events) {
                None => None, Some((parsed, rest)) => Some((match parsed {
                    Err(error) => (Err(error), reader, raw),
                    Ok(order) => (Ok(()), reader, Part1MainHeaderAccumulator { order: Some(order), ..raw }),
                }, rest)),
            }
        },
        _ => Some((part1_main_header_mct_payload(reader, raw, segment), events)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_fresh_tile_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    match segment.marker {
        0xff74 => match part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, events) {
            None => None, Some((result, rest)) => {
                let changed = Part1TileHeaderAccumulator { pending_mct: result.1, completed_mct: result.2, ..raw };
                Some((match result.0 {
                    Err(error) => (Err(error), reader, changed),
                    Ok(None) => (Ok(()), reader, changed),
                    Ok(Some(array)) => {
                        let replaced = part1_mct_registry_replace_array(raw.mct_parameters.arrays, array);
                        (Ok(()), reader, Part1TileHeaderAccumulator {
                            mct_parameters: Part1MctParameters { arrays: replaced.1, ..raw.mct_parameters }, ..changed })
                    },
                }, rest))
            },
        },
        0xff75 => match part1_fresh_consume_mcc_run(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, events) {
            None => None, Some((result, rest)) => {
                let changed = Part1TileHeaderAccumulator { pending_mcc: result.1, completed_mcc: result.2, ..raw };
                Some((match result.0 {
                    Err(error) => (Err(error), reader, changed),
                    Ok(None) => (Ok(()), reader, changed),
                    Ok(Some(record)) => {
                        let replaced = part1_mct_registry_replace_record(raw.mct_parameters.records, record);
                        (Ok(()), reader, Part1TileHeaderAccumulator {
                            mct_parameters: Part1MctParameters { records: replaced.1, ..raw.mct_parameters }, ..changed })
                    },
                }, rest))
            },
        },
        0xff77 => if raw.tile_mco_seen {
            Some(((Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), reader, raw), events))
        } else {
            let changed = Part1TileHeaderAccumulator { tile_mco_seen: true, ..raw };
            match part1_fresh_mco_run(segment, events) {
                None => None, Some((parsed, rest)) => Some((match parsed {
                    Err(error) => (Err(error), reader, changed),
                    Ok(order) => (Ok(()), reader, Part1TileHeaderAccumulator {
                        mct_parameters: Part1MctParameters { order, ..raw.mct_parameters }, ..changed }),
                }, rest)),
            }
        },
        _ => Some((part1_tile_header_mct_payload(reader, raw, segment, components), events)),
    }
}

pub(crate) open spec fn part1_fresh_main_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
) -> Seq<Part1ColdStorageEvent> {
    match segment.marker {
        0xff74 => part1_fresh_consume_mct_calls(segment, reader.limits, raw.pending_mct, raw.completed_mct)
            + part1_mct_copy_normal_calls(
                if matches!(part1_consume_mct_fragment(segment, reader.limits, raw.pending_mct, raw.completed_mct).0, Ok(Some(_))) {
                    part1_fresh_main_mct_array_requests(raw, segment)
                } else { Seq::empty() }),
        0xff75 => part1_fresh_consume_mcc_calls(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc)
            + part1_mct_copy_normal_calls(
                if matches!(part1_consume_mcc_fragment(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc).0, Ok(Some(_))) {
                    part1_fresh_main_mcc_record_requests(raw, segment)
                } else { Seq::empty() }),
        0xff77 => if raw.order.is_some() { Seq::empty() } else { part1_mct_copy_normal_calls(part1_fresh_mco_requests(segment)) },
        _ => Seq::empty(),
    }
}
pub(crate) open spec fn part1_fresh_tile_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
) -> Seq<Part1ColdStorageEvent> {
    match segment.marker {
        0xff74 => part1_fresh_consume_mct_calls(segment, reader.limits, raw.pending_mct, raw.completed_mct),
        0xff75 => part1_fresh_consume_mcc_calls(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc),
        0xff77 => if raw.tile_mco_seen { Seq::empty() } else { part1_mct_copy_normal_calls(part1_fresh_mco_requests(segment)) },
        _ => Seq::empty(),
    }
}

pub(crate) proof fn part1_fresh_main_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_fresh_main_payload(reader, raw, segment, part1_fresh_main_calls(reader, raw, segment) + tail)
        == Some((part1_main_header_mct_payload(reader, raw, segment), tail)),
{
    reveal(part1_fresh_main_payload); reveal(part1_main_header_mct_payload);
    match segment.marker {
        0xff74 => {
            let requests=if matches!(part1_consume_mct_fragment(segment, reader.limits, raw.pending_mct, raw.completed_mct).0, Ok(Some(_))) {
                part1_fresh_main_mct_array_requests(raw, segment)
            } else {Seq::empty()};
            let calls=part1_mct_copy_normal_calls(requests);
            part1_mct_copy_normal(requests,tail);
            part1_fresh_consume_mct_normal(segment, reader.limits, raw.pending_mct, raw.completed_mct, calls+tail);
            if requests.len()==0 {assert(calls =~= Seq::<Part1ColdStorageEvent>::empty());}
            assert((part1_fresh_consume_mct_calls(segment,reader.limits,raw.pending_mct,raw.completed_mct)+calls)+tail
                =~=part1_fresh_consume_mct_calls(segment,reader.limits,raw.pending_mct,raw.completed_mct)+(calls+tail));
        },
        0xff75 => {
            let requests=if matches!(part1_consume_mcc_fragment(segment,raw.image_size.components,reader.limits,raw.pending_mcc,raw.completed_mcc).0,Ok(Some(_))) {
                part1_fresh_main_mcc_record_requests(raw,segment)
            } else {Seq::empty()};
            let calls=part1_mct_copy_normal_calls(requests);
            part1_mct_copy_normal(requests,tail);
            part1_fresh_consume_mcc_normal(segment,raw.image_size.components,reader.limits,raw.pending_mcc,raw.completed_mcc,calls+tail);
            if requests.len()==0 {assert(calls =~= Seq::<Part1ColdStorageEvent>::empty());}
            assert((part1_fresh_consume_mcc_calls(segment,raw.image_size.components,reader.limits,raw.pending_mcc,raw.completed_mcc)+calls)+tail
                =~=part1_fresh_consume_mcc_calls(segment,raw.image_size.components,reader.limits,raw.pending_mcc,raw.completed_mcc)+(calls+tail));
        },
        0xff77 => { if raw.order.is_none() { part1_mct_copy_normal(part1_fresh_mco_requests(segment), tail); } },
        _ => {},
    }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}
pub(crate) proof fn part1_fresh_tile_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_fresh_tile_payload(reader, raw, segment, components, part1_fresh_tile_calls(reader, raw, segment, components) + tail)
        == Some((part1_tile_header_mct_payload(reader, raw, segment, components), tail)),
{
    reveal(part1_fresh_tile_payload); reveal(part1_tile_header_mct_payload);
    match segment.marker {
        0xff74 => part1_fresh_consume_mct_normal(segment, reader.limits, raw.pending_mct, raw.completed_mct, tail),
        0xff75 => part1_fresh_consume_mcc_normal(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, tail),
        0xff77 => { if !raw.tile_mco_seen { part1_mct_copy_normal(part1_fresh_mco_requests(segment), tail); } },
        _ => {},
    }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}

pub(crate) proof fn part1_fresh_main_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_main_payload(reader, raw, segment, events) == Some((result, rest)),
    ensures part1_fresh_main_payload(reader, raw, segment, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_fresh_main_payload);
    match segment.marker {
        0xff74 => if let Some((parsed, after)) = part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, events) {
            part1_fresh_consume_mct_frame(segment, reader.limits, raw.pending_mct, raw.completed_mct, events, parsed, after, tail);
            if matches!(parsed.0,Ok(Some(_))) {
                let requests=part1_fresh_main_mct_array_requests(raw,segment);
                if let Some((capacity,last))=part1_mct_copy_run(requests,after) {
                    part1_mct_copy_frame(requests,after,capacity,last,tail);
                }
            }
        },
        0xff75 => if let Some((parsed, after)) = part1_fresh_consume_mcc_run(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc, events) {
            part1_fresh_consume_mcc_frame(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc, events, parsed, after, tail);
            if matches!(parsed.0,Ok(Some(_))) {
                let requests=part1_fresh_main_mcc_record_requests(raw,segment);
                if let Some((capacity,last))=part1_mct_copy_run(requests,after) {
                    part1_mct_copy_frame(requests,after,capacity,last,tail);
                }
            }
        },
        0xff77 => if raw.order.is_none() { if let Some((parsed, after)) = part1_fresh_mco_run(segment, events) { part1_fresh_mco_frame(segment, events, parsed, after, tail); } },
        _ => {},
    }
}
pub(crate) proof fn part1_fresh_tile_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_tile_payload(reader, raw, segment, components, events) == Some((result, rest)),
    ensures part1_fresh_tile_payload(reader, raw, segment, components, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_fresh_tile_payload);
    match segment.marker {
        0xff74 => if let Some((parsed, after)) = part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, events) {
            part1_fresh_consume_mct_frame(segment, reader.limits, raw.pending_mct, raw.completed_mct, events, parsed, after, tail);
        },
        0xff75 => if let Some((parsed, after)) = part1_fresh_consume_mcc_run(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, events) {
            part1_fresh_consume_mcc_frame(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, events, parsed, after, tail);
        },
        0xff77 => if !raw.tile_mco_seen { if let Some((parsed, after)) = part1_fresh_mco_run(segment, events) { part1_fresh_mco_frame(segment, events, parsed, after, tail); } },
        _ => {},
    }
}
pub(crate) proof fn part1_fresh_main_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_main_payload(reader, raw, segment, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_main_header_mct_payload(reader, raw, segment),
{
    reveal(part1_fresh_main_payload); reveal(part1_main_header_mct_payload);
    match segment.marker {
        0xff74 => if let Some((parsed, after)) = part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, events) {
            part1_fresh_consume_mct_projection(segment, reader.limits, raw.pending_mct, raw.completed_mct, events, parsed, after);
            if matches!(parsed.0,Ok(Some(_))) {
                let requests=part1_fresh_main_mct_array_requests(raw,segment);
                if let Some((capacity,last))=part1_mct_copy_run(requests,after) {
                    part1_mct_copy_projection(requests,after,capacity,last);
                }
            }
        },
        0xff75 => if let Some((parsed, after)) = part1_fresh_consume_mcc_run(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc, events) {
            part1_fresh_consume_mcc_projection(segment, raw.image_size.components, reader.limits, raw.pending_mcc, raw.completed_mcc, events, parsed, after);
            if matches!(parsed.0,Ok(Some(_))) {
                let requests=part1_fresh_main_mcc_record_requests(raw,segment);
                if let Some((capacity,last))=part1_mct_copy_run(requests,after) {
                    part1_mct_copy_projection(requests,after,capacity,last);
                }
            }
        },
        0xff77 => if raw.order.is_none() { if let Some((parsed, after)) = part1_fresh_mco_run(segment, events) { part1_fresh_mco_projection(segment, events, parsed, after); } },
        _ => {},
    }
}
pub(crate) proof fn part1_fresh_tile_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_fresh_tile_payload(reader, raw, segment, components, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_header_mct_payload(reader, raw, segment, components),
{
    reveal(part1_fresh_tile_payload); reveal(part1_tile_header_mct_payload);
    match segment.marker {
        0xff74 => if let Some((parsed, after)) = part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, events) {
            part1_fresh_consume_mct_projection(segment, reader.limits, raw.pending_mct, raw.completed_mct, events, parsed, after);
        },
        0xff75 => if let Some((parsed, after)) = part1_fresh_consume_mcc_run(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, events) {
            part1_fresh_consume_mcc_projection(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, events, parsed, after);
        },
        0xff77 => if !raw.tile_mco_seen { if let Some((parsed, after)) = part1_fresh_mco_run(segment, events) { part1_fresh_mco_projection(segment, events, parsed, after); } },
        _ => {},
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_fresh_tile_result<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_fresh_tile_payload(reader, raw, segment, components, events) == Some((result, Seq::empty()))
}
pub(crate) proof fn part1_fresh_tile_normal_result<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
)
    ensures part1_fresh_tile_result(reader, raw, segment, components, part1_tile_header_mct_payload(reader, raw, segment, components)),
{
    reveal(part1_fresh_tile_result);
    part1_fresh_tile_normal(reader, raw, segment, components, Seq::empty());
    assert(part1_fresh_tile_calls(reader, raw, segment, components) + Seq::<Part1ColdStorageEvent>::empty()
        =~= part1_fresh_tile_calls(reader, raw, segment, components));
}

pub(crate) proof fn part1_fresh_tile_error<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
    error: crate::DecodeError, mct_pending: Seq<Part1MctFragment>, mct_completed: Seq<u8>, mcc_pending: Seq<Part1MccFragment>, mcc_completed: Seq<u8>,
)
    requires match segment.marker {
        0xff74 => part1_fresh_consume_mct_result(segment, reader.limits, raw.pending_mct, raw.completed_mct, (Err(error), mct_pending, mct_completed)),
        0xff75 => part1_fresh_consume_mcc_result(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, (Err(error), mcc_pending, mcc_completed)),
        0xff77 => !raw.tile_mco_seen && part1_fresh_mco_result(segment, Err(error)), _ => false,
    },
    ensures part1_fresh_tile_result(reader, raw, segment, components, (Err(error), reader,
        match segment.marker {
            0xff74 => Part1TileHeaderAccumulator { pending_mct: mct_pending, completed_mct: mct_completed, ..raw },
            0xff75 => Part1TileHeaderAccumulator { pending_mcc: mcc_pending, completed_mcc: mcc_completed, ..raw },
            _ => Part1TileHeaderAccumulator { tile_mco_seen: true, ..raw },
        })),
{
    reveal(part1_fresh_tile_result); reveal(part1_fresh_tile_payload);
    match segment.marker {
        0xff74 => {
            reveal(part1_fresh_consume_mct_result);
            let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_consume_mct_run(segment, reader.limits, raw.pending_mct, raw.completed_mct, calls)
                == Some(((Err(error), mct_pending, mct_completed), Seq::empty()));
            assert(part1_fresh_tile_payload(reader, raw, segment, components, calls)
                == Some(((Err(error), reader, Part1TileHeaderAccumulator { pending_mct: mct_pending, completed_mct: mct_completed, ..raw }), Seq::empty())));
        },
        0xff75 => {
            reveal(part1_fresh_consume_mcc_result);
            let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_consume_mcc_run(segment, components, reader.limits, raw.pending_mcc, raw.completed_mcc, calls)
                == Some(((Err(error), mcc_pending, mcc_completed), Seq::empty()));
            assert(part1_fresh_tile_payload(reader, raw, segment, components, calls)
                == Some(((Err(error), reader, Part1TileHeaderAccumulator { pending_mcc: mcc_pending, completed_mcc: mcc_completed, ..raw }), Seq::empty())));
        },
        _ => {
            reveal(part1_fresh_mco_result);
            let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mco_run(segment, calls) == Some((Err(error), Seq::empty()));
            assert(part1_fresh_tile_payload(reader, raw, segment, components, calls)
                == Some(((Err(error), reader, Part1TileHeaderAccumulator { tile_mco_seen: true, ..raw }), Seq::empty())));
        },
    }
}

pub(crate) proof fn part1_cold_main_mct_array_error<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, array: Part2MctArray, pending: Seq<Part1MctFragment>, completed: Seq<u8>,
    error: crate::DecodeError,
)
    requires part1_cold_main_prefix(initial, reader, raw), segment.marker==0xff74,
        part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        part1_fresh_consume_mct_result(segment, part1_read_main_header_segment(reader, raw.segments).1.limits,
            raw.pending_mct, raw.completed_mct, (Ok(Some(array)),pending,completed)),
        part1_mct_copy_result(part1_fresh_main_mct_array_requests(raw,segment),Err(error)),
    ensures part1_cold_layout_result(initial,Err(error)),
{
    reveal(part1_cold_main_prefix); reveal(part1_fresh_main_payload);
    reveal(part1_fresh_consume_mct_result); reveal(part1_mct_copy_result);
    let prefix=choose|prefix:Seq<Part1ColdStorageEvent>|part1_cold_main_prefix_at(initial,reader,raw,prefix);
    let admitted=part1_read_main_header_segment(reader,raw.segments);
    let copied=choose|calls:Seq<Part1ColdStorageEvent>|part1_fresh_consume_mct_run(segment,admitted.1.limits,
        raw.pending_mct,raw.completed_mct,calls)==Some(((Ok(Some(array)),pending,completed),Seq::empty()));
    let last=choose|calls:Seq<Part1ColdStorageEvent>|part1_mct_copy_run(part1_fresh_main_mct_array_requests(raw,segment),calls)
        ==Some((Err(error),Seq::empty()));
    part1_fresh_consume_mct_frame(segment,admitted.1.limits,raw.pending_mct,raw.completed_mct,
        copied,(Ok(Some(array)),pending,completed),Seq::empty(),last);
    assert(Seq::<Part1ColdStorageEvent>::empty()+last =~= last);
    reveal_with_fuel(part1_main_progression_continuation,1);
    assert(part1_prepare_main_progression_run(initial,prefix+(copied+last))==Some((Err(error),Seq::empty())));
    reveal(part1_cold_layout_result);
    assert(part1_layout_with_cold_storage(initial,prefix+(copied+last))==Some((Err(error),Seq::empty())));
}

pub(crate) proof fn part1_cold_main_mcc_record_error<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, record: Part1MctRecord, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
    error: crate::DecodeError,
)
    requires part1_cold_main_prefix(initial, reader, raw), segment.marker==0xff75,
        part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        part1_fresh_consume_mcc_result(segment,raw.image_size.components,part1_read_main_header_segment(reader,raw.segments).1.limits,
            raw.pending_mcc,raw.completed_mcc,(Ok(Some(record)),pending,completed)),
        part1_mct_copy_result(part1_fresh_main_mcc_record_requests(raw,segment),Err(error)),
    ensures part1_cold_layout_result(initial,Err(error)),
{
    reveal(part1_cold_main_prefix); reveal(part1_fresh_main_payload);
    reveal(part1_fresh_consume_mcc_result); reveal(part1_mct_copy_result);
    let prefix=choose|prefix:Seq<Part1ColdStorageEvent>|part1_cold_main_prefix_at(initial,reader,raw,prefix);
    let admitted=part1_read_main_header_segment(reader,raw.segments);
    let copied=choose|calls:Seq<Part1ColdStorageEvent>|part1_fresh_consume_mcc_run(segment,raw.image_size.components,admitted.1.limits,
        raw.pending_mcc,raw.completed_mcc,calls)==Some(((Ok(Some(record)),pending,completed),Seq::empty()));
    let last=choose|calls:Seq<Part1ColdStorageEvent>|part1_mct_copy_run(part1_fresh_main_mcc_record_requests(raw,segment),calls)
        ==Some((Err(error),Seq::empty()));
    part1_fresh_consume_mcc_frame(segment,raw.image_size.components,admitted.1.limits,raw.pending_mcc,raw.completed_mcc,
        copied,(Ok(Some(record)),pending,completed),Seq::empty(),last);
    assert(Seq::<Part1ColdStorageEvent>::empty()+last =~= last);
    reveal_with_fuel(part1_main_progression_continuation,1);
    assert(part1_prepare_main_progression_run(initial,prefix+(copied+last))==Some((Err(error),Seq::empty())));
    reveal(part1_cold_layout_result);
    assert(part1_layout_with_cold_storage(initial,prefix+(copied+last))==Some((Err(error),Seq::empty())));
}

pub(crate) proof fn part1_cold_main_fresh_error<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, error: crate::DecodeError,
    mct_pending: Seq<Part1MctFragment>, mct_completed: Seq<u8>, mcc_pending: Seq<Part1MccFragment>, mcc_completed: Seq<u8>,
)
    requires part1_cold_main_prefix(initial, reader, raw),
        part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        match segment.marker {
            0xff74 => part1_fresh_consume_mct_result(segment, part1_read_main_header_segment(reader, raw.segments).1.limits, raw.pending_mct, raw.completed_mct, (Err(error), mct_pending, mct_completed)),
            0xff75 => part1_fresh_consume_mcc_result(segment, raw.image_size.components, part1_read_main_header_segment(reader, raw.segments).1.limits, raw.pending_mcc, raw.completed_mcc, (Err(error), mcc_pending, mcc_completed)),
            0xff77 => raw.order.is_none() && part1_fresh_mco_result(segment, Err(error)), _ => false,
        },
    ensures part1_cold_layout_result(initial, Err(error)),
{
    reveal(part1_cold_main_prefix); reveal(part1_fresh_main_payload);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_cold_main_prefix_at(initial, reader, raw, prefix);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let before = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    let calls = match segment.marker {
        0xff74 => {
            reveal(part1_fresh_consume_mct_result);
            choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_consume_mct_run(segment, admitted.1.limits, raw.pending_mct, raw.completed_mct, calls)
                == Some(((Err(error), mct_pending, mct_completed), Seq::empty()))
        },
        0xff75 => {
            reveal(part1_fresh_consume_mcc_result);
            choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_consume_mcc_run(segment, raw.image_size.components, admitted.1.limits, raw.pending_mcc, raw.completed_mcc, calls)
                == Some(((Err(error), mcc_pending, mcc_completed), Seq::empty()))
        },
        _ => {
            reveal(part1_fresh_mco_result);
            choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_mco_run(segment, calls) == Some((Err(error), Seq::empty()))
        },
    };
    reveal_with_fuel(part1_main_progression_continuation, 1);
    assert(part1_prepare_main_progression_run(initial, prefix + calls) == Some((Err(error), Seq::empty())));
    reveal(part1_cold_layout_result);
    assert(part1_layout_with_cold_storage(initial, prefix + calls) == Some((Err(error), Seq::empty())));
}

}
