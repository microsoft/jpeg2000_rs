//! Actual packed-header allocation requests, separate from parse/inspection/JPIP capacities.
use super::*;
verus! {

pub(crate) open spec fn part2_packed_requests(source: Part1PackedHeaders, maximum: u64) -> Seq<Part1PackedHeaders> {
    if source.length as u64 > maximum || source.length == 0 { Seq::empty() } else {
        match source.source {
            Part1PackedHeaderSource::None => Seq::empty(),
            Part1PackedHeaderSource::MarkerSegments { logical_start, .. } =>
                if logical_start as int + source.length as int > usize::MAX { Seq::empty() } else { seq![source] },
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_packed_requests_run(requests: Seq<Part1PackedHeaders>, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<()>
    decreases requests.len(),
{
    if requests.len() == 0 { Some((Ok(()), events)) } else if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipSnapshotEvent::PackedHeaderCapacity { source, succeeded } =>
                if source != requests[0] { None } else if !succeeded {
                    Some((Err(crate::DecodeError::AllocationFailed), events.drop_first()))
                } else { part2_packed_requests_run(requests.drop_first(), events.drop_first()) },
            _ => None,
        }
    }
}
pub(crate) open spec fn part2_packed_normal_calls(requests: Seq<Part1PackedHeaders>) -> Seq<Part2JpipSnapshotEvent> {
    requests.map_values(|source: Part1PackedHeaders| Part2JpipSnapshotEvent::PackedHeaderCapacity { source, succeeded: true })
}
pub(crate) proof fn part2_packed_requests_normal(requests: Seq<Part1PackedHeaders>, tail: Seq<Part2JpipSnapshotEvent>)
    ensures part2_packed_requests_run(requests, part2_packed_normal_calls(requests) + tail) == Some((Ok(()), tail)),
    decreases requests.len(),
{
    reveal_with_fuel(part2_packed_requests_run, 1);
    if requests.len() == 0 { assert(part2_packed_normal_calls(requests) + tail =~= tail); }
    else {
        let calls = part2_packed_normal_calls(requests);
        assert((calls + tail).drop_first() =~= part2_packed_normal_calls(requests.drop_first()) + tail);
        part2_packed_requests_normal(requests.drop_first(), tail);
    }
}
pub(crate) proof fn part2_packed_requests_frame(requests: Seq<Part1PackedHeaders>, events: Seq<Part2JpipSnapshotEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part2JpipSnapshotEvent>, tail: Seq<Part2JpipSnapshotEvent>)
    requires part2_packed_requests_run(requests, events) == Some((result, rest)),
    ensures part2_packed_requests_run(requests, events + tail) == Some((result, rest + tail)),
    decreases requests.len(),
{
    reveal_with_fuel(part2_packed_requests_run, 1);
    if requests.len() > 0 && events.len() > 0 {
        assert((events + tail).drop_first() =~= events.drop_first() + tail);
        if let Part2JpipSnapshotEvent::PackedHeaderCapacity { source, succeeded } = events[0] {
            if source == requests[0] && succeeded { part2_packed_requests_frame(requests.drop_first(), events.drop_first(), result, rest, tail); }
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_packed_requests_result(requests: Seq<Part1PackedHeaders>, result: Result<(), crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_packed_requests_run(requests, events), result)
}
pub(crate) proof fn part2_packed_capacity_observed(source: Part1PackedHeaders, maximum: u64, result: Result<(), crate::DecodeError>)
    requires result == Ok(()) || (part2_packed_requests(source, maximum).len() == 1 && result == Err(crate::DecodeError::AllocationFailed)),
    ensures part2_packed_requests_result(part2_packed_requests(source, maximum), result),
{
    reveal(part2_packed_requests_result);
    let requests = part2_packed_requests(source, maximum);
    let calls = if requests.len() == 0 { Seq::empty() } else {
        seq![Part2JpipSnapshotEvent::PackedHeaderCapacity { source, succeeded: result.is_ok() }]
    };
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| part2_packed_requests_run(requests, calls + tail) == Some((result, tail)) by {
        reveal_with_fuel(part2_packed_requests_run, 2);
        if requests.len() == 0 { assert(calls + tail =~= tail); } else { assert((calls + tail).drop_first() =~= tail); }
    }
    assert(part2_cold_prefix(|events| part2_packed_requests_run(requests, events), calls, result));
}
pub(crate) open spec fn part2_packed_reassembly_run(source: Part1PackedHeaders, maximum: u64,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Seq<u8>> {
    part2_jpip_snapshot_bind(part2_packed_requests_run(part2_packed_requests(source, maximum), events),
        |_: (), rest| Some((part1_packed_header_reassembly(source, maximum), rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_packed_reassembly_result(source: Part1PackedHeaders, maximum: u64, result: Result<Seq<u8>, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_packed_reassembly_run(source, maximum, events), result)
}
pub(crate) proof fn part2_packed_reassembly_normal(source: Part1PackedHeaders, maximum: u64)
    ensures part2_packed_reassembly_result(source, maximum, part1_packed_header_reassembly(source, maximum)),
{
    reveal(part2_packed_reassembly_result); reveal(part2_packed_requests_result);
    part2_packed_capacity_observed(source, maximum, Ok(()));
    part2_cold_pure(part1_packed_header_reassembly(source, maximum));
    part2_cold_bind(|events| part2_packed_requests_run(part2_packed_requests(source, maximum), events),
        |_: (), rest| Some((part1_packed_header_reassembly(source, maximum), rest)),
        Ok(()), part1_packed_header_reassembly(source, maximum));
}
pub(crate) proof fn part2_packed_reassembly_refused(source: Part1PackedHeaders, maximum: u64)
    requires part2_packed_requests_result(part2_packed_requests(source, maximum), Err(crate::DecodeError::AllocationFailed)),
    ensures part2_packed_reassembly_result(source, maximum, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_packed_reassembly_result); reveal(part2_packed_requests_result);
    part2_cold_bind(|events| part2_packed_requests_run(part2_packed_requests(source, maximum), events),
        |_: (), rest| Some((part1_packed_header_reassembly(source, maximum), rest)), Err(crate::DecodeError::AllocationFailed), Err(crate::DecodeError::AllocationFailed));
}

pub(crate) open spec fn part2_payload_before(parts: Seq<Part2OwnedTilePart>, s: Part1TilePacketPreparation)
    -> Result<(), crate::DecodeError> {
    let part = parts[s.index as int];
    if s.index > u8::MAX || part.tile_index != s.tile_index || part.tile_part_index != s.index
        || (part.tile_part_count != 0 && part.tile_part_count as nat != parts.len()) {
        Err(ht_reader_error(crate::MalformedKind::InvalidTilePart))
    } else if s.payload_bytes as nat + (part.data.len() as u64) as nat > u64::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else { Ok(()) }
}
pub(crate) open spec fn part2_payload_after(parts: Seq<Part2OwnedTilePart>, s: Part1TilePacketPreparation,
    maximum: u64, packed: Seq<u8>) -> Result<Part1TilePacketPreparation, crate::DecodeError> {
    let part = parts[s.index as int];
    let total = s.packed_payload_bytes as nat + (packed.len() as u64) as nat;
    let present = !matches!(part.packet_lengths.source, Part1PacketLengthSource::None);
    if total > u64::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else if total > maximum { Err(part1_packet_reader_limit(crate::Resource::PacketHeaderBytes, maximum, total as u64)) }
    else if present && s.declared_packets as nat + part.packet_lengths.packet_count as nat > u64::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else if s.index == usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else { Ok(Part1TilePacketPreparation {
        tile_index: s.tile_index, index: (s.index + 1) as usize,
        payload_bytes: (s.payload_bytes + part.data.len() as u64) as u64,
        packed_payload_bytes: total as u64,
        declared_packets: if present { (s.declared_packets + part.packet_lengths.packet_count) as u64 } else { s.declared_packets },
        all_lengths: s.all_lengths && present, packed: s.packed.push(packed),
    }) }
}
#[verifier::opaque]
pub(crate) open spec fn part2_payloads_run(parts: Seq<Part2OwnedTilePart>, s: Part1TilePacketPreparation,
    maximum: u64, events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1TilePacketPreparation>
    decreases parts.len() - s.index as nat,
{
    if s.index >= parts.len() { Some((Ok(s), events)) } else {
        match part2_payload_before(parts, s) {
            Err(error) => Some((Err(error), events)),
            Ok(()) => part2_jpip_snapshot_bind(part2_packed_reassembly_run(parts[s.index as int].packed_packet_headers, maximum, events),
                |packed: Seq<u8>, rest| match part2_payload_after(parts, s, maximum, packed) {
                    Err(error) => Some((Err(error), rest)),
                    Ok(after) => part2_payloads_run(parts, after, maximum, rest),
                }),
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_payloads_result(parts: Seq<Part2OwnedTilePart>, s: Part1TilePacketPreparation,
    maximum: u64, result: Result<Part1TilePacketPreparation, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_payloads_run(parts, s, maximum, events), result)
}
pub(crate) proof fn part2_payloads_normal(parts: Seq<Part2OwnedTilePart>, s: Part1TilePacketPreparation, maximum: u64)
    ensures part2_payloads_result(parts, s, maximum, part1_progression_payloads_owned(parts, s, maximum)),
        part2_cold_framed(|events| part2_payloads_run(parts, s, maximum, events), part1_progression_payloads_owned(parts, s, maximum)),
    decreases parts.len() - s.index as nat,
{
    reveal(part2_payloads_result); reveal_with_fuel(part2_payloads_run, 1); reveal_with_fuel(part1_progression_payloads_owned, 1);
    if s.index >= parts.len() { part2_cold_pure(Ok(s)); } else if part2_payload_before(parts, s).is_err() {
        part2_cold_pure::<Part1TilePacketPreparation>(part1_progression_payloads_owned(parts, s, maximum));
    } else {
        let source = parts[s.index as int].packed_packet_headers;
        part2_packed_reassembly_normal(source, maximum); reveal(part2_packed_reassembly_result);
        let parsed = part1_packed_header_reassembly(source, maximum);
        if let Ok(packed) = parsed {
            match part2_payload_after(parts, s, maximum, packed) {
                Err(error) => { part2_cold_pure::<Part1TilePacketPreparation>(Err(error)); },
                Ok(after) => {
                    part2_payloads_normal(parts, after, maximum);
                    part2_decode_eta(|events|part2_payloads_run(parts,after,maximum,events),part1_progression_payloads_owned(parts,after,maximum));
                },
            }
        }
        part2_cold_bind(|events| part2_packed_reassembly_run(source, maximum, events),
            |packed: Seq<u8>, rest| match part2_payload_after(parts, s, maximum, packed) {
                Err(error) => Some((Err(error), rest)), Ok(after) => part2_payloads_run(parts, after, maximum, rest),
            }, parsed, part1_progression_payloads_owned(parts, s, maximum));
    }
}
pub(crate) proof fn part2_payloads_error(parts: Seq<Part2OwnedTilePart>, initial: Part1TilePacketPreparation,
    current: Part1TilePacketPreparation, maximum: u64, prefix: Seq<Part2JpipSnapshotEvent>, error: crate::DecodeError)
    requires current.index < parts.len(), part2_payload_before(parts, current) == Ok(()),
        forall|tail: Seq<Part2JpipSnapshotEvent>| part2_payloads_run(parts, initial, maximum, prefix + tail)
            == part2_payloads_run(parts, current, maximum, tail),
        part2_packed_reassembly_result(parts[current.index as int].packed_packet_headers, maximum, Err(error)),
    ensures part2_payloads_result(parts, initial, maximum, Err(error)),
{
    reveal(part2_payloads_result); reveal(part2_packed_reassembly_result);
    let source = parts[current.index as int].packed_packet_headers;
    let child = |events| part2_packed_reassembly_run(source, maximum, events);
    let calls = part2_cold_witness(child, Err(error));
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| part2_payloads_run(parts, initial, maximum, (prefix + calls) + tail) == Some((Err(error), tail)) by {
        assert((prefix + calls) + tail =~= prefix + (calls + tail));
        part2_cold_prefix_at(child, calls, Err(error), tail);
        reveal_with_fuel(part2_payloads_run, 1);
        assert(part2_payloads_run(parts,current,maximum,calls+tail)==Some((Err(error),tail)));
        assert(part2_payloads_run(parts,initial,maximum,prefix+(calls+tail))==part2_payloads_run(parts,current,maximum,calls+tail));
    }
    assert(part2_cold_prefix(|events| part2_payloads_run(parts, initial, maximum, events), prefix + calls, Err(error)));
}
pub(crate) proof fn part2_payloads_advance(parts: Seq<Part2OwnedTilePart>, initial: Part1TilePacketPreparation,
    current: Part1TilePacketPreparation, after: Part1TilePacketPreparation, packed: Seq<u8>, maximum: u64,
    prefix: Seq<Part2JpipSnapshotEvent>) -> (next: Seq<Part2JpipSnapshotEvent>)
    requires current.index < parts.len(), part2_payload_before(parts, current) == Ok(()),
        forall|tail: Seq<Part2JpipSnapshotEvent>| part2_payloads_run(parts, initial, maximum, prefix + tail)
            == part2_payloads_run(parts, current, maximum, tail),
        part2_packed_reassembly_result(parts[current.index as int].packed_packet_headers, maximum, Ok(packed)),
        part2_payload_after(parts, current, maximum, packed) == Ok(after),
    ensures forall|tail: Seq<Part2JpipSnapshotEvent>| part2_payloads_run(parts, initial, maximum, next + tail)
        == part2_payloads_run(parts, after, maximum, tail),
{
    reveal(part2_packed_reassembly_result);
    let child = |events| part2_packed_reassembly_run(parts[current.index as int].packed_packet_headers, maximum, events);
    let calls = part2_cold_witness(child, Ok(packed));
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| part2_payloads_run(parts, initial, maximum, (prefix + calls) + tail)
        == part2_payloads_run(parts, after, maximum, tail) by {
        assert((prefix + calls) + tail =~= prefix + (calls + tail));
        part2_cold_prefix_at(child, calls, Ok(packed), tail); reveal_with_fuel(part2_payloads_run, 1);
        assert(part2_payloads_run(parts,current,maximum,calls+tail)==part2_payloads_run(parts,after,maximum,tail));
        assert(part2_payloads_run(parts,initial,maximum,prefix+(calls+tail))==part2_payloads_run(parts,current,maximum,calls+tail));
    }
    prefix + calls
}

pub(crate) proof fn part2_packed_requests_projection(requests: Seq<Part1PackedHeaders>, events: Seq<Part2JpipSnapshotEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part2JpipSnapshotEvent>)
    requires part2_packed_requests_run(requests, events) == Some((result, rest)),
    ensures result == Ok(()) || result == Err(crate::DecodeError::AllocationFailed),
    decreases requests.len(),
{
    reveal_with_fuel(part2_packed_requests_run, 1);
    if requests.len() > 0 && events.len() > 0 {
        if let Part2JpipSnapshotEvent::PackedHeaderCapacity { source, succeeded } = events[0] {
            if source == requests[0] && succeeded { part2_packed_requests_projection(requests.drop_first(), events.drop_first(), result, rest); }
        }
    }
}
pub(crate) proof fn part2_packed_reassembly_projection(source: Part1PackedHeaders, maximum: u64,
    events: Seq<Part2JpipSnapshotEvent>, result: Result<Seq<u8>, crate::DecodeError>, rest: Seq<Part2JpipSnapshotEvent>)
    requires part2_packed_reassembly_run(source, maximum, events) == Some((result, rest)), result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_packed_header_reassembly(source, maximum),
{
    if let Some((unit, after)) = part2_packed_requests_run(part2_packed_requests(source, maximum), events) {
        part2_packed_requests_projection(part2_packed_requests(source, maximum), events, unit, after);
    }
}
pub(crate) proof fn part2_payloads_projection(parts: Seq<Part2OwnedTilePart>, s: Part1TilePacketPreparation,
    maximum: u64, events: Seq<Part2JpipSnapshotEvent>, result: Result<Part1TilePacketPreparation, crate::DecodeError>, rest: Seq<Part2JpipSnapshotEvent>)
    requires part2_payloads_run(parts, s, maximum, events) == Some((result, rest)), result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_progression_payloads_owned(parts, s, maximum),
    decreases parts.len() - s.index as nat,
{
    reveal_with_fuel(part2_payloads_run, 1); reveal_with_fuel(part1_progression_payloads_owned, 1);
    if s.index < parts.len() && part2_payload_before(parts, s).is_ok() {
        let source = parts[s.index as int].packed_packet_headers;
        if let Some((parsed, after)) = part2_packed_reassembly_run(source, maximum, events) {
            part2_packed_reassembly_projection(source, maximum, events, parsed, after);
            if let Ok(packed) = parsed { if let Ok(next) = part2_payload_after(parts, s, maximum, packed) {
                part2_payloads_projection(parts, next, maximum, after, result, rest);
            }}
        }
    }
}
pub(crate) open spec fn part2_packet_input_run(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1TilePacketPreparation> {
    match part1_progression_layout_owned(parts, grid, selection, limits) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(part2_prepare_payloads_run(parts, parts[0].tile_index,
            crate::limits::resource_packet_header_byte_limit(limits), events), |_: Part1TilePacketPreparation, rest|
            Some((part1_progression_tile_input_owned(parts, grid, precincts, selection, limits), rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_packet_input_result(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    result: Result<Part1TilePacketPreparation, crate::DecodeError>) -> bool {
    part2_cold_framed(|events| part2_packet_input_run(parts, grid, precincts, selection, limits, events), result)
}
pub(crate) proof fn part2_packet_input_normal(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits)
    ensures part2_packet_input_result(parts, grid, precincts, selection, limits, part1_progression_tile_input_owned(parts, grid, precincts, selection, limits)),
{
    reveal(part2_packet_input_result); reveal(part2_prepare_payloads_result);
    let result = part1_progression_tile_input_owned(parts, grid, precincts, selection, limits);
    if part1_progression_layout_owned(parts, grid, selection, limits).is_err() { part2_cold_pure::<Part1TilePacketPreparation>(result); }
    else {
        let initial = Part1TilePacketPreparation { tile_index: parts[0].tile_index, index: 0, payload_bytes: 0,
            packed_payload_bytes: 0, declared_packets: 0, all_lengths: true, packed: Seq::empty() };
        let maximum = crate::limits::resource_packet_header_byte_limit(limits);
        part2_prepare_payloads_normal(parts, parts[0].tile_index, maximum);
        part2_decode_eta(|events|part2_prepare_payloads_run(parts,parts[0].tile_index,maximum,events),part1_progression_payloads_owned(parts,initial,maximum));
        let prepared = part1_progression_payloads_owned(parts, initial, maximum);
        if prepared.is_ok() { part2_cold_pure(result); }
        part2_cold_bind(|events| part2_prepare_payloads_run(parts, parts[0].tile_index, maximum, events),
            |_: Part1TilePacketPreparation, rest| Some((result, rest)), prepared, result);
    }
}
pub(crate) proof fn part2_packet_input_payload_error(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, error: crate::DecodeError)
    requires part1_progression_layout_owned(parts, grid, selection, limits) == Ok(()),
        part2_prepare_payloads_result(parts, parts[0].tile_index,
            crate::limits::resource_packet_header_byte_limit(limits), Err(error)),
    ensures part2_packet_input_result(parts, grid, precincts, selection, limits, Err(error)),
{
    reveal(part2_packet_input_result); reveal(part2_prepare_payloads_result);
    let initial = Part1TilePacketPreparation { tile_index: parts[0].tile_index, index: 0, payload_bytes: 0,
        packed_payload_bytes: 0, declared_packets: 0, all_lengths: true, packed: Seq::empty() };
    part2_cold_bind(|events| part2_prepare_payloads_run(parts, parts[0].tile_index, crate::limits::resource_packet_header_byte_limit(limits), events),
        |_: Part1TilePacketPreparation, rest| Some((part1_progression_tile_input_owned(parts, grid, precincts, selection, limits), rest)), Err(error), Err(error));
}
pub(crate) open spec fn part2_packet_run(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>) -> Option<((Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>), Seq<Part2JpipSnapshotEvent>)> {
    match part2_packet_input_run(parts, grid, precincts, selection, limits, events) {
        None => None, Some((Err(error), rest)) => Some(((Err(error), precincts), rest)),
        Some((Ok(input), rest)) => match part2_progress_initial_run(part2_packet_parameters(parts,grid,input,selection,limits),rest) {
            None=>None,Some((Err(error),tail))=>Some(((Err(error),precincts),tail)),
            Some((Ok(progress),tail))=>match part2_packet_after_progress_run(parts,grid,precincts,selection,limits,input,progress,tail) {
                None=>None,Some((Err(error),rest))=>Some(((Err(error),precincts),rest)),Some((Ok(result),rest))=>Some((result,rest)),
            },
        },
    }
}
pub(crate) open spec fn part2_packet_prefix(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    prefix: Seq<Part2JpipSnapshotEvent>, result: (Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>)) -> bool {
    forall|tail: Seq<Part2JpipSnapshotEvent>| #[trigger]
        part2_packet_run(parts, grid, precincts, selection, limits, prefix + tail) == Some((result, tail))
}
#[verifier::opaque]
pub(crate) open spec fn part2_packet_result(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    result: (Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>)) -> bool {
    exists|prefix: Seq<Part2JpipSnapshotEvent>| #[trigger] part2_packet_prefix(parts, grid, precincts, selection, limits, prefix, result)
}
pub closed spec fn part1_progression_tile_cold_result(parts: Seq<crate::codestream::TilePartPayload<'_>>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits,
    result: (Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>)) -> bool {
    part2_packet_result(crate::codestream::tile_parts_owned_view(parts), grid, precincts, selection, limits, result)
}
pub(crate) proof fn part2_packet_public_result_equivalent(parts: Seq<crate::codestream::TilePartPayload<'_>>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits)
    ensures forall|result: (Result<crate::packet::TilePacketDecode, crate::DecodeError>, Seq<Part1PacketPrecinctState>)|
        part1_progression_tile_cold_result(parts, grid, precincts, selection, limits, result)
            == part2_packet_result(crate::codestream::tile_parts_owned_view(parts), grid, precincts, selection, limits, result),
{}
pub(crate) proof fn part2_packet_normal(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits)
    ensures part2_packet_result(parts, grid, precincts, selection, limits, part1_progression_tile_decode_owned(parts, grid, precincts, selection, limits)),
{
    part2_packet_input_normal(parts, grid, precincts, selection, limits);
    let prepared = part1_progression_tile_input_owned(parts, grid, precincts, selection, limits);
    match prepared {
        Err(error)=>{part2_packet_input_error(parts,grid,precincts,selection,limits,error);},
        Ok(input)=>{
            let params=part2_packet_parameters(parts,grid,input,selection,limits);
            part2_progress_initial_normal(params);
            part2_packet_stages_actual(parts,grid,precincts,selection,limits,input,part1_tile_progress_initial(params));
        },
    }
}
pub(crate) proof fn part2_packet_input_error(parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid,
    precincts: Seq<Part1PacketPrecinctState>, selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, error: crate::DecodeError)
    requires part2_packet_input_result(parts, grid, precincts, selection, limits, Err(error)),
    ensures part2_packet_result(parts, grid, precincts, selection, limits, (Err(error), precincts)),
{
    reveal(part2_packet_result); reveal(part2_packet_input_result);
    let run = |events| part2_packet_input_run(parts, grid, precincts, selection, limits, events);
    let calls = part2_cold_witness(run, Err(error));
    assert forall|tail: Seq<Part2JpipSnapshotEvent>| part2_packet_run(parts, grid, precincts, selection, limits, calls + tail)
        == Some(((Err(error), precincts), tail)) by { part2_cold_prefix_at(run, calls, Err(error), tail); }
    assert(part2_packet_prefix(parts, grid, precincts, selection, limits, calls, (Err(error), precincts)));
}

}
