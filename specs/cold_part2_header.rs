//! Actual fresh Part 2 dispatch, charged reader/owner frames and public binds.
use super::*;
verus! {

pub(crate) open spec fn part1_p2_marker(marker: u16) -> bool {
    marker == 0xff72 || marker == 0xff73 || marker == 0xff76 || marker == 0xff79
}
pub(crate) open spec fn part1_p2_kind(marker: u16) -> Part2FreshKind {
    match marker { 0xff73 => Part2FreshKind::Ads, 0xff76 => Part2FreshKind::Nlt, 0xff79 => Part2FreshKind::Atk, _ => Part2FreshKind::Dfs }
}
pub(crate) open spec fn part1_p2_components(marker: u16, components: u16) -> u16 {
    if marker == 0xff76 { components } else { 0 }
}
pub(crate) open spec fn part1_p2_tile_extensions(raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment) -> Part2OwnedExtensions {
    if segment.marker == 0xff76 && raw.part2_extensions.nonlinear_local_count.is_none() {
        Part2OwnedExtensions { nonlinear_local_count: Some(0), ..raw.part2_extensions }
    } else { raw.part2_extensions }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_main_run<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>)
    -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    if part1_p2_marker(segment.marker) {
        match part1_p2_marker_run(part1_p2_kind(segment.marker), reader, segment,
            part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, events) {
            None => None, Some((result, rest)) =>
                Some(((result.0, result.1, Part1MainHeaderAccumulator { extensions: result.2, ..raw }), rest)),
        }
    } else { Some((part1_main_header_extension_payload(reader, raw, segment), events)) }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_tile_run<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, events: Seq<Part1ColdStorageEvent>)
    -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    if part1_p2_marker(segment.marker) {
        match part1_p2_marker_run(part1_p2_kind(segment.marker), reader, segment,
            part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), events) {
            None => None, Some((result, rest)) =>
                Some(((result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw }), rest)),
        }
    } else { Some((part1_tile_header_extension_payload(reader, raw, segment, components), events)) }
}
pub(crate) open spec fn part1_p2_main_calls(reader: Part1CodestreamReader<'_>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment) -> Seq<Part1ColdStorageEvent> {
    if part1_p2_marker(segment.marker) {
        part1_p2_marker_calls(part1_p2_kind(segment.marker), reader, segment, part1_p2_components(segment.marker, raw.image_size.components), raw.extensions)
    } else { Seq::empty() }
}
pub(crate) open spec fn part1_p2_tile_calls(reader: Part1CodestreamReader<'_>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16) -> Seq<Part1ColdStorageEvent> {
    if part1_p2_marker(segment.marker) {
        part1_p2_marker_calls(part1_p2_kind(segment.marker), reader, segment, part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment))
    } else { Seq::empty() }
}
pub(crate) proof fn part1_p2_main_normal<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_p2_main_run(reader, raw, segment, part1_p2_main_calls(reader, raw, segment) + tail)
        == Some((part1_main_header_extension_payload(reader, raw, segment), tail)),
{
    reveal(part1_p2_main_run); reveal(part1_main_header_extension_payload);
    if part1_p2_marker(segment.marker) {
        part1_p2_marker_normal(part1_p2_kind(segment.marker), reader, segment, part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, tail);
    }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}
pub(crate) proof fn part1_p2_tile_normal<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_p2_tile_run(reader, raw, segment, components, part1_p2_tile_calls(reader, raw, segment, components) + tail)
        == Some((part1_tile_header_extension_payload(reader, raw, segment, components), tail)),
{
    reveal(part1_p2_tile_run); reveal(part1_tile_header_extension_payload);
    if part1_p2_marker(segment.marker) {
        part1_p2_marker_normal(part1_p2_kind(segment.marker), reader, segment, part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), tail);
    }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}
pub(crate) proof fn part1_p2_main_frame<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>)
    requires part1_p2_main_run(reader, raw, segment, events) == Some((result, rest)),
    ensures part1_p2_main_run(reader, raw, segment, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_p2_main_run);
    if part1_p2_marker(segment.marker) {
        let kind = part1_p2_kind(segment.marker); let components = part1_p2_components(segment.marker, raw.image_size.components);
        if let Some((step, after)) = part1_p2_marker_run(kind, reader, segment, components, raw.extensions, events) {
            part1_p2_marker_frame(kind, reader, segment, components, raw.extensions, events, step, after, tail);
        }
    }
}
pub(crate) proof fn part1_p2_tile_frame<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>)
    requires part1_p2_tile_run(reader, raw, segment, components, events) == Some((result, rest)),
    ensures part1_p2_tile_run(reader, raw, segment, components, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_p2_tile_run);
    if part1_p2_marker(segment.marker) {
        let kind = part1_p2_kind(segment.marker); let count = part1_p2_components(segment.marker, components); let extensions = part1_p2_tile_extensions(raw, segment);
        if let Some((step, after)) = part1_p2_marker_run(kind, reader, segment, count, extensions, events) {
            part1_p2_marker_frame(kind, reader, segment, count, extensions, events, step, after, tail);
        }
    }
}
pub(crate) proof fn part1_p2_main_projection<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>)
    requires part1_p2_main_run(reader, raw, segment, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_main_header_extension_payload(reader, raw, segment),
{
    reveal(part1_p2_main_run); reveal(part1_main_header_extension_payload);
    if part1_p2_marker(segment.marker) {
        let kind = part1_p2_kind(segment.marker); let components = part1_p2_components(segment.marker, raw.image_size.components);
        if let Some((step, after)) = part1_p2_marker_run(kind, reader, segment, components, raw.extensions, events) {
            part1_p2_marker_projection(kind, reader, segment, components, raw.extensions, events, step, after);
        }
    }
}
pub(crate) proof fn part1_p2_tile_projection<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), rest: Seq<Part1ColdStorageEvent>)
    requires part1_p2_tile_run(reader, raw, segment, components, events) == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_header_extension_payload(reader, raw, segment, components),
{
    reveal(part1_p2_tile_run); reveal(part1_tile_header_extension_payload);
    if part1_p2_marker(segment.marker) {
        let kind = part1_p2_kind(segment.marker); let count = part1_p2_components(segment.marker, components); let extensions = part1_p2_tile_extensions(raw, segment);
        if let Some((step, after)) = part1_p2_marker_run(kind, reader, segment, count, extensions, events) {
            part1_p2_marker_projection(kind, reader, segment, count, extensions, events, step, after);
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_tile_result<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator)) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_p2_tile_run(reader, raw, segment, components, events) == Some((result, Seq::empty()))
}
pub(crate) proof fn part1_p2_tile_normal_result<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16)
    ensures part1_p2_tile_result(reader, raw, segment, components, part1_tile_header_extension_payload(reader, raw, segment, components)),
{
    reveal(part1_p2_tile_result); part1_p2_tile_normal(reader, raw, segment, components, Seq::empty());
    assert(part1_p2_tile_calls(reader, raw, segment, components) + Seq::<Part1ColdStorageEvent>::empty() =~= part1_p2_tile_calls(reader, raw, segment, components));
}
pub(crate) proof fn part1_p2_tile_error<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16,
    error: crate::DecodeError, after: Part1CodestreamReader<'a>, extensions: Part2OwnedExtensions)
    requires part1_p2_marker(segment.marker), part1_p2_marker_result(part1_p2_kind(segment.marker), reader, segment,
        part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), (Err(error), after, extensions)),
    ensures part1_p2_tile_result(reader, raw, segment, components, (Err(error), after, Part1TileHeaderAccumulator { part2_extensions: extensions, ..raw })),
{
    reveal(part1_p2_tile_result); reveal(part1_p2_tile_run); reveal(part1_p2_marker_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_marker_run(part1_p2_kind(segment.marker), reader, segment,
        part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), calls) == Some(((Err(error), after, extensions), Seq::empty()));
    assert(part1_p2_tile_run(reader, raw, segment, components, calls)
        == Some(((Err(error), after, Part1TileHeaderAccumulator { part2_extensions: extensions, ..raw }), Seq::empty())));
}
pub(crate) proof fn part1_cold_main_p2_error<'a>(initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, error: crate::DecodeError, after: Part1CodestreamReader<'a>, extensions: Part2OwnedExtensions)
    requires part1_cold_main_prefix(initial, reader, raw), part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        part1_p2_marker(segment.marker), part1_p2_marker_result(part1_p2_kind(segment.marker),
            part1_read_main_header_segment(reader, raw.segments).1, segment,
            part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, (Err(error), after, extensions)),
    ensures part1_cold_layout_result(initial, Err(error)),
{
    reveal(part1_cold_main_prefix); reveal(part1_p2_marker_result); reveal(part1_p2_main_run);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_cold_main_prefix_at(initial, reader, raw, prefix);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_marker_run(part1_p2_kind(segment.marker), admitted.1, segment,
        part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, calls) == Some(((Err(error), after, extensions), Seq::empty()));
    reveal_with_fuel(part1_main_progression_continuation, 1);
    assert(part1_prepare_main_progression_run(initial, prefix + calls) == Some((Err(error), Seq::empty())));
    reveal(part1_cold_layout_result);
    assert(part1_layout_with_cold_storage(initial, prefix + calls) == Some((Err(error), Seq::empty())));
}
pub(crate) proof fn part1_p2_main_observed<'a>(reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions))
    requires part1_p2_marker(segment.marker), part1_p2_marker_result(part1_p2_kind(segment.marker), reader, segment,
        part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, result),
    ensures result.0 != Err(crate::DecodeError::AllocationFailed) ==>
        part1_main_header_extension_payload(reader, raw, segment) ==
            (result.0, result.1, Part1MainHeaderAccumulator { extensions: result.2, ..raw }),
{
    reveal(part1_p2_marker_result); reveal(part1_main_header_extension_payload);
    if result.0 != Err(crate::DecodeError::AllocationFailed) {
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_marker_run(part1_p2_kind(segment.marker), reader, segment,
            part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, calls) == Some((result, Seq::empty()));
        part1_p2_marker_projection(part1_p2_kind(segment.marker), reader, segment,
            part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, calls, result, Seq::empty());
    }
}
pub(crate) proof fn part1_cold_main_p2_step<'a>(initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions))
    requires part1_cold_main_prefix(initial, reader, raw), part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        part1_p2_marker(segment.marker), part1_p2_marker_storage_result(part1_p2_kind(segment.marker),
            part1_read_main_header_segment(reader, raw.segments).1, segment,
            part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, result),
    ensures match result.0 { Err(error) => part1_cold_layout_result(initial, Err(error)), Ok(()) => true },
        result.0 != Err(crate::DecodeError::AllocationFailed) ==>
            part1_main_header_payload(part1_read_main_header_segment(reader, raw.segments).1,
                Part1MainHeaderAccumulator { segments: part1_read_main_header_segment(reader, raw.segments).2, ..raw }, segment)
            == (result.0, result.1, Part1MainHeaderAccumulator { segments: part1_read_main_header_segment(reader, raw.segments).2, extensions: result.2, ..raw }),
{
    reveal(part1_main_header_payload);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    part1_p2_marker_storage_observed(part1_p2_kind(segment.marker), admitted.1, segment,
        part1_p2_components(segment.marker, raw.image_size.components), raw.extensions, result);
    part1_p2_main_observed(admitted.1, Part1MainHeaderAccumulator { segments: admitted.2, ..raw }, segment, result);
    if let Err(error) = result.0 { part1_cold_main_p2_error(initial, reader, raw, segment, error, result.1, result.2); }
}
pub(crate) proof fn part1_p2_tile_step<'a>(reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions))
    requires part1_p2_marker(segment.marker), part1_p2_marker_storage_result(part1_p2_kind(segment.marker), reader, segment,
        part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), result),
    ensures part1_p2_tile_result(reader, raw, segment, components,
        (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw })),
        result.0 != Err(crate::DecodeError::AllocationFailed) ==>
            part1_tile_header_extension_payload(reader, raw, segment, components) ==
                (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw }),
{
    part1_p2_marker_storage_observed(part1_p2_kind(segment.marker), reader, segment,
        part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), result);
    reveal(part1_p2_marker_result); reveal(part1_p2_tile_result); reveal(part1_p2_tile_run);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_marker_run(part1_p2_kind(segment.marker), reader, segment,
        part1_p2_components(segment.marker, components), part1_p2_tile_extensions(raw, segment), calls) == Some((result, Seq::empty()));
    assert(part1_p2_tile_run(reader, raw, segment, components, calls) ==
        Some(((result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw }), Seq::empty())));
    if result.0 != Err(crate::DecodeError::AllocationFailed) {
        part1_p2_tile_projection(reader, raw, segment, components, calls,
            (result.0, result.1, Part1TileHeaderAccumulator { part2_extensions: result.2, ..raw }), Seq::empty());
    }
}
}
