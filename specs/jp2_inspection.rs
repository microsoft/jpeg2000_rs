//! Raw container and codestream-info composition with native validation order.

use super::*;

verus! {

pub(crate) type Part2RawCodestreamInfo = (Part1LayoutMainFields, Part1ProfileMetadata, u32, u64);
pub(crate) type Part2RawInspectedContainer = (Part2RawJp2File, Seq<Part2RawCodestreamInfo>);

pub(crate) open spec fn part2_inspection_count(file: Part2RawJp2File, display_first: bool) -> nat {
    if display_first && part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)
        && !part2_file_type_jpx(file.file_type)
        && !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND) {
        if file.streams.len() > 0 { 1 } else { 0 }
    } else { file.streams.len() }
}

pub(crate) open spec fn part2_validate_jp2_display_profile(file: Part2RawJp2File)
    -> Result<(), crate::DecodeError>
{
    if !part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JP2_BRAND)
        || file.streams.len() == 0 || (part2_file_type_jpx(file.file_type) && file.streams.len() != 1) {
        Err(part2_container_error(0, crate::MalformedKind::InvalidProfile))
    } else { Ok(()) }
}

pub(crate) open spec fn part2_inspected_header(
    file: Part2RawJp2File, index: usize, info: Part2RawCodestreamInfo,
) -> Result<(), crate::DecodeError> {
    let stream = file.streams[index as int];
    if part2_file_type_compatible(file.file_type, crate::jp2::BoxType::JPH_BRAND)
        != part1_profile_optional_advertises_ht(info.1.2) {
        Err(part2_container_error(stream.0.1, crate::MalformedKind::InvalidProfile))
    } else {
        let header = match stream.2 {
            Some(association) => association.2,
            None => if index == 0 { Some(file.header) } else { None },
        };
        match header {
            None => Ok(()),
            Some(header) => part2_validate_selected_header(header.image,
                info.0.image_size.geometry.0, info.0.image_size.geometry.1, info.0.image_size.components,
                info.0.image_size.uniform_bit_depth, info.0.image_size.uniform_signed, stream.0.1),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_inspected_codestreams(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, index: usize, infos: Seq<Part2RawCodestreamInfo>,
    display_first: bool,
) -> Result<Part2RawInspectedContainer, crate::DecodeError>
    decreases file.streams.len() as int - index as int,
{
    if index >= part2_inspection_count(file, display_first) { Ok((file, infos)) }
    else {
        match part1_parse_info(file.streams[index as int].1, limits) {
            Err(error) => Err(error),
            Ok(info) => match part2_inspected_header(file, index, info) {
                Err(error) => Err(error),
                Ok(()) => if index == usize::MAX {
                    Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    part2_inspected_codestreams(file, limits, (index + 1) as usize, infos.push(info), display_first)
                },
            },
        }
    }
}

#[verifier::opaque]
pub closed spec fn part2_parse_and_inspect_container(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2RawInspectedContainer, crate::DecodeError>
{
    part2_parse_and_inspect_container_mode(input, limits, false)
}

#[verifier::opaque]
pub closed spec fn part2_parse_and_inspect_container_mode(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
) -> Result<Part2RawInspectedContainer, crate::DecodeError>
{
    match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => part2_inspected_codestreams(file, limits, 0, Seq::empty(), display_first),
    }
}

#[verifier::opaque]
pub closed spec fn part2_inspect_jph_container(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2RawInspectedContainer, crate::DecodeError>
{
    match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => if part2_file_type_compatible(inspected.0.file_type, crate::jp2::BoxType::JPH_BRAND) {
            Ok(inspected)
        } else { Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)) },
    }
}

pub(crate) proof fn part2_parse_and_inspect_container_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_parse_and_inspect_container(input, limits)
        == part2_parse_and_inspect_container_mode(input, limits, false),
        part2_parse_and_inspect_container(input, limits) == match part2_parse_container(input, *limits) {
        Err(error) => Err(error),
        Ok(file) => part2_inspected_codestreams(file, limits, 0, Seq::empty(), false),
    },
{
    reveal(part2_parse_and_inspect_container);
    reveal(part2_parse_and_inspect_container_mode);
}

pub(crate) proof fn part2_parse_and_inspect_container_mode_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
)
    ensures part2_parse_and_inspect_container_mode(input, limits, display_first)
        == match part2_parse_container(input, *limits) {
            Err(error) => Err(error),
            Ok(file) => part2_inspected_codestreams(file, limits, 0, Seq::empty(), display_first),
        },
{
    reveal(part2_parse_and_inspect_container_mode);
}

pub(crate) proof fn part2_inspect_jph_container_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_inspect_jph_container(input, limits) == match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => if part2_file_type_compatible(inspected.0.file_type, crate::jp2::BoxType::JPH_BRAND) {
            Ok(inspected)
        } else { Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)) },
    },
{
    reveal(part2_inspect_jph_container);
}

#[verifier::opaque]
pub(crate) open spec fn part2_inspected_cold_streams(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, index: usize,
    infos: Seq<Part2RawCodestreamInfo>, display_first: bool, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawInspectedContainer>
    decreases file.streams.len() as int - index as int,
{
    if index >= part2_inspection_count(file, display_first) { Some((Ok((file, infos)), events)) }
    else {
        part2_jpip_snapshot_bind(part2_cold_info(file.streams[index as int].1, limits, 4, index, events),
            |info: Part2RawCodestreamInfo, rest| match part2_inspected_header(file, index, info) {
                Err(error) => Some((Err(error), rest)),
                Ok(()) => if index == usize::MAX {
                    Some((Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow)), rest))
                } else {
                    part2_inspected_cold_streams(file, limits, (index + 1) as usize,
                        infos.push(info), display_first, rest)
                },
            })
    }
}

pub(crate) open spec fn part2_inspection_after_container(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, display_first: bool,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawInspectedContainer> {
    part2_jpip_snapshot_bind(part2_inspection_capacity(crate::allocation::InspectionCollection::Infos(display_first),
        part2_inspection_count(file, display_first) as usize, events),
        |_: (), rest| part2_inspected_cold_streams(file, limits, 0, Seq::empty(), display_first, rest))
}

pub(crate) open spec fn part2_inspection_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawInspectedContainer> {
    part2_jpip_snapshot_bind(part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_inspection_after_container(file, limits, display_first, rest))
}

pub closed spec fn part2_inspection_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
    result: Result<Part2RawInspectedContainer, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_inspection_cold_run(input, limits, display_first, events), result)
}

pub(crate) proof fn part2_inspection_cold_frames(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
    result: Result<Part2RawInspectedContainer, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, display_first, result),
    ensures part2_cold_framed(
        |events| part2_inspection_cold_run(input, limits, display_first, events), result),
{
    reveal(part2_inspection_cold_result);
}

pub(crate) proof fn part2_inspected_cold_normal(
    file: Part2RawJp2File, limits: &crate::ResourceLimits, index: usize,
    infos: Seq<Part2RawCodestreamInfo>, display_first: bool,
)
    ensures part2_cold_framed(
        |events| part2_inspected_cold_streams(file, limits, index, infos, display_first, events),
        part2_inspected_codestreams(file, limits, index, infos, display_first)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2RawInspectedContainer>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_inspected_cold_streams(file, limits, index, infos, display_first, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_inspected_codestreams(file, limits, index, infos, display_first)),
    decreases file.streams.len() as int - index as int,
{
    reveal_with_fuel(part2_inspected_cold_streams, 1);
    reveal_with_fuel(part2_inspected_codestreams, 1);
    if index >= part2_inspection_count(file, display_first) {
        part2_cold_pure(Ok((file, infos)));
    } else {
        let parsed = part1_parse_info(file.streams[index as int].1, limits);
        part2_cold_info_normal(file.streams[index as int].1, limits, 4, index);
        if let Ok(info) = parsed {
            match part2_inspected_header(file, index, info) {
                Err(error) => { part2_cold_pure::<Part2RawInspectedContainer>(Err(error)); },
                Ok(()) => if index == usize::MAX {
                    part2_cold_pure::<Part2RawInspectedContainer>(Err(part2_container_error(
                        0, crate::MalformedKind::ArithmeticOverflow)));
                } else {
                    part2_inspected_cold_normal(file, limits, (index + 1) as usize,
                        infos.push(info), display_first);
                },
            }
        }
        part2_cold_bind(
            |events| part2_cold_info(file.streams[index as int].1, limits, 4, index, events),
            |info: Part2RawCodestreamInfo, rest| match part2_inspected_header(file, index, info) {
                Err(error) => Some((Err(error), rest)),
                Ok(()) => if index == usize::MAX {
                    Some((Err(part2_container_error(0, crate::MalformedKind::ArithmeticOverflow)), rest))
                } else {
                    part2_inspected_cold_streams(file, limits, (index + 1) as usize,
                        infos.push(info), display_first, rest)
                },
            }, parsed, part2_inspected_codestreams(file, limits, index, infos, display_first));
    }
}

pub(crate) proof fn part2_inspection_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
)
    ensures part2_inspection_cold_result(input, limits, display_first,
        part2_parse_and_inspect_container_mode(input, limits, display_first)),
{
    reveal(part2_inspection_cold_result);
    part2_parse_and_inspect_container_mode_unfold(input, limits, display_first);
    match part2_parse_container(input, *limits) {
        Err(error) => { part2_cold_pure::<Part2RawInspectedContainer>(Err(error)); },
        Ok(file) => {
            let collection = crate::allocation::InspectionCollection::Infos(display_first);
            let count = part2_inspection_count(file, display_first) as usize;
            part2_inspection_capacity_normal(collection, count, Seq::empty());
            part2_inspected_cold_normal(file, limits, 0, Seq::empty(), display_first);
            part2_cold_bind(|events| part2_inspection_capacity(collection, count, events),
                |_: (), rest| part2_inspected_cold_streams(file, limits, 0, Seq::empty(), display_first, rest),
                Ok(()), part2_inspected_codestreams(file, limits, 0, Seq::empty(), display_first));
        },
    }
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, part2_parse_container(input, *limits));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_inspection_after_container(file, limits, display_first, rest),
        part2_parse_container(input, *limits),
        part2_parse_and_inspect_container_mode(input, limits, display_first));
}

pub(crate) proof fn part2_inspection_cold_container_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool, error: crate::DecodeError,
)
    requires part2_parse_container_cold_result(input, *limits, Err(error)),
    ensures part2_inspection_cold_result(input, limits, display_first, Err(error)),
{
    reveal(part2_inspection_cold_result);
    part2_parse_container_cold_frames(input, *limits, Err(error));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_inspection_after_container(file, limits, display_first, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_inspection_cold_start(input: Seq<u8>, limits: &crate::ResourceLimits,
    display_first: bool, file: Part2RawJp2File) -> (prefix: Seq<Part2JpipSnapshotEvent>)
    requires part2_parse_container(input, *limits) == Ok(file),
    ensures forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_inspection_cold_run(input, limits, display_first, prefix + tail)
            == part2_inspected_cold_streams(file, limits, 0, Seq::empty(), display_first, tail),
{
    let collection = crate::allocation::InspectionCollection::Infos(display_first);
    let count = part2_inspection_count(file, display_first) as usize;
    let parsed = part2_parse_container_cold_calls(input, *limits);
    let capacity = part2_inspection_capacity_calls(collection, count);
    let prefix = parsed + capacity;
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_inspection_cold_run(input, limits, display_first, prefix + tail)
            == part2_inspected_cold_streams(file, limits, 0, Seq::empty(), display_first, tail) by {
        assert(prefix + tail =~= parsed + (capacity + tail));
        part2_parse_container_cold_normal(input, *limits, capacity + tail);
        part2_inspection_capacity_normal(collection, count, tail);
    }
    prefix
}
pub(crate) proof fn part2_inspection_capacity_refused(input: Seq<u8>, limits: &crate::ResourceLimits,
    display_first: bool, file: Part2RawJp2File, error: crate::DecodeError)
    requires part2_parse_container(input, *limits) == Ok(file),
        part2_inspection_capacity_result(crate::allocation::InspectionCollection::Infos(display_first),
            part2_inspection_count(file, display_first) as usize, Err(error)),
    ensures part2_inspection_cold_result(input, limits, display_first, Err(error)),
{
    reveal(part2_inspection_cold_result);
    let collection = crate::allocation::InspectionCollection::Infos(display_first);
    let count = part2_inspection_count(file, display_first) as usize;
    part2_inspection_capacity_frames(collection, count, Err(error));
    part2_cold_bind(|events| part2_inspection_capacity(collection, count, events),
        |_: (), rest| part2_inspected_cold_streams(file, limits, 0, Seq::empty(), display_first, rest),
        Err(error), Err(error));
    part2_parse_container_cold_normal(input, *limits, Seq::empty());
    part2_parse_container_cold_frames(input, *limits, Ok(file));
    part2_cold_bind(
        |events| part2_parse_container_cold_run(input, *limits, events),
        |file, rest| part2_inspection_after_container(file, limits, display_first, rest),
        Ok(file), Err(error));
}

pub(crate) proof fn part2_inspection_cold_parse_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
    file: Part2RawJp2File, index: usize, infos: Seq<Part2RawCodestreamInfo>,
    prefix: Seq<Part2JpipSnapshotEvent>, error: crate::DecodeError,
)
    requires index < part2_inspection_count(file, display_first),
        forall|tail: Seq<Part2JpipSnapshotEvent>|
            part2_inspection_cold_run(input, limits, display_first, prefix + tail)
                == part2_inspected_cold_streams(file, limits, index, infos, display_first, tail),
        part1_parse_info_cold_result(file.streams[index as int].1, limits, Err(error)),
    ensures part2_inspection_cold_result(input, limits, display_first, Err(error)),
{
    reveal(part2_inspection_cold_result);
    reveal_with_fuel(part2_inspected_cold_streams, 1);
    part2_cold_info_actual(file.streams[index as int].1, limits, 4, index, Err(error));
    let run = |events| part2_cold_info(file.streams[index as int].1, limits, 4, index, events);
    let calls = part2_cold_witness(run, Err(error));
    assert(part2_cold_info(file.streams[index as int].1, limits, 4, index, calls)
        == Some((Err(error), Seq::empty())));
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_inspection_cold_run(input, limits, display_first, (prefix + calls) + tail)
            == Some((Err(error), tail)) by {
        assert((prefix + calls) + tail =~= prefix + (calls + tail));
        part2_cold_prefix_at(run, calls, Err(error), tail);
        assert(part2_cold_info(file.streams[index as int].1, limits, 4, index, calls + tail)
            == Some((Err(error), tail)));
        assert(part2_inspection_cold_run(input, limits, display_first, prefix + (calls + tail))
            == part2_inspected_cold_streams(file, limits, index, infos, display_first, calls + tail));
        reveal_with_fuel(part2_inspected_cold_streams, 1);
        reveal(part2_jpip_snapshot_bind);
    }
    assert(part2_cold_prefix(
        |events| part2_inspection_cold_run(input, limits, display_first, events), prefix + calls, Err(error)));
}

pub(crate) proof fn part2_inspection_cold_advance(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
    file: Part2RawJp2File, index: usize, infos: Seq<Part2RawCodestreamInfo>,
    prefix: Seq<Part2JpipSnapshotEvent>, info: Part2RawCodestreamInfo,
) -> (after: Seq<Part2JpipSnapshotEvent>)
    requires index < part2_inspection_count(file, display_first), index < usize::MAX,
        forall|tail: Seq<Part2JpipSnapshotEvent>|
            part2_inspection_cold_run(input, limits, display_first, prefix + tail)
                == part2_inspected_cold_streams(file, limits, index, infos, display_first, tail),
        part1_parse_info_cold_result(file.streams[index as int].1, limits, Ok(info)),
        part2_inspected_header(file, index, info) == Ok(()),
    ensures forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_inspection_cold_run(input, limits, display_first, after + tail)
            == part2_inspected_cold_streams(file, limits, (index + 1) as usize,
                infos.push(info), display_first, tail),
{
    reveal_with_fuel(part2_inspected_cold_streams, 1);
    part2_cold_info_actual(file.streams[index as int].1, limits, 4, index, Ok(info));
    let run = |events| part2_cold_info(file.streams[index as int].1, limits, 4, index, events);
    let calls = part2_cold_witness(run, Ok(info));
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        part2_inspection_cold_run(input, limits, display_first, (prefix + calls) + tail)
            == part2_inspected_cold_streams(file, limits, (index + 1) as usize,
                infos.push(info), display_first, tail) by {
        assert((prefix + calls) + tail =~= prefix + (calls + tail));
        part2_cold_prefix_at(run, calls, Ok(info), tail);
        assert(part2_cold_info(file.streams[index as int].1, limits, 4, index, calls + tail)
            == Some((Ok(info), tail)));
        assert(part2_inspection_cold_run(input, limits, display_first, prefix + (calls + tail))
            == part2_inspected_cold_streams(file, limits, index, infos, display_first, calls + tail));
        reveal_with_fuel(part2_inspected_cold_streams, 1);
        reveal(part2_jpip_snapshot_bind);
    }
    prefix + calls
}

pub(crate) open spec fn part2_inspect_jph_cold_finish(
    inspected: Part2RawInspectedContainer,
) -> Result<Part2RawInspectedContainer, crate::DecodeError> {
    if part2_file_type_compatible(inspected.0.file_type, crate::jp2::BoxType::JPH_BRAND) {
        Ok(inspected)
    } else { Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)) }
}

pub(crate) open spec fn part2_inspect_jph_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawInspectedContainer> {
    part2_jpip_snapshot_bind(part2_inspection_cold_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest| Some((part2_inspect_jph_cold_finish(inspected), rest)))
}

pub closed spec fn part2_inspect_jph_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part2RawInspectedContainer, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_inspect_jph_cold_run(input, limits, events), result)
}

pub(crate) proof fn part2_inspect_jph_cold_frames(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Result<Part2RawInspectedContainer, crate::DecodeError>,
)
    requires part2_inspect_jph_cold_result(input, limits, result),
    ensures part2_cold_framed(|events| part2_inspect_jph_cold_run(input, limits, events), result),
{
    reveal(part2_inspect_jph_cold_result);
}

pub(crate) proof fn part2_inspection_cold_normal_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, display_first: bool,
)
    ensures part2_inspection_cold_result(input, limits, display_first,
        part2_parse_and_inspect_container_mode(input, limits, display_first)),
{
    reveal(part2_inspection_cold_result);
    part2_inspection_cold_normal(input, limits, display_first);
}

pub(crate) proof fn part2_inspect_jph_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_inspect_jph_cold_result(input, limits, part2_inspect_jph_container(input, limits)),
{
    reveal(part2_inspection_cold_result);
    part2_inspection_cold_normal(input, limits, false);
    part2_inspect_jph_cold_actual(input, limits, part2_parse_and_inspect_container_mode(input, limits, false));
    part2_parse_and_inspect_container_unfold(input, limits);
    part2_inspect_jph_container_unfold(input, limits);
}

pub(crate) proof fn part2_inspect_jph_cold_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    inspected: Result<Part2RawInspectedContainer, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, false, inspected),
    ensures part2_inspect_jph_cold_result(input, limits, match inspected {
        Err(error) => Err(error), Ok(value) => part2_inspect_jph_cold_finish(value),
    }),
{
    reveal(part2_inspection_cold_result);
    reveal(part2_inspect_jph_cold_result);
    if let Ok(value) = inspected { part2_cold_pure(part2_inspect_jph_cold_finish(value)); }
    part2_cold_bind(
        |events| part2_inspection_cold_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest| Some((part2_inspect_jph_cold_finish(value), rest)),
        inspected, match inspected { Err(error) => Err(error), Ok(value) => part2_inspect_jph_cold_finish(value) });
}

}
