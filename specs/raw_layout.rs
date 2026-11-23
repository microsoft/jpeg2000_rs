//! Complete raw-input layout composition through the actual accepted producers.

use super::*;

verus! {

pub(crate) type Part1CompleteLayout = (
    Part1LayoutMainFields, Part1ProfileMetadata, u32, u64, Seq<Part1TilePartPayload>,
);
pub(crate) type Part1CompleteLayoutResult = Result<Part1CompleteLayout, crate::DecodeError>;

pub(crate) open spec fn part1_layout_profile_tiles(parts: Seq<Part1TilePartPayload>) -> Seq<Part1ProfileTile> {
    parts.map_values(|part: Part1TilePartPayload| Part1ProfileTile {
        styles: part.component_coding_styles, roi: part.roi_shifts,
        has_roi: part.has_roi_marker, has_functional: part.has_functional_header_marker,
    })
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_after_tiles<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
) -> Part1CompleteLayoutResult {
    match part1_complete_poc_coverage(state.3, reader.limits) {
        Err(error)=>Err(error),Ok(())=>match part1_classify_codestream_profile(
        main.raw.r_siz, main.raw.capabilities, main.raw.profile, main.raw.corresponding_profile,
        main.styles, main.raw.roi, part1_layout_profile_tiles(state.3), main.raw.image_size.components,
        exists|index: int| 0 <= index < main.raw.roi_seen.len() && main.raw.roi_seen[index],
    ) {
        Err(error) => Err(error),
        Ok(profile) => Ok((part1_main_header_fields(main), profile, tile_parts,
            part1_codestream_offset(reader.position), state.3)),
    }}
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState) {
    if tile_parts == u32::MAX {
        (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::ArithmeticOverflow)), reader, tile_parts, state)
    } else {
        let next = (tile_parts as int + 1) as u32;
        if next > crate::limits::resource_tile_part_limit(reader.limits) {
            (Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::TileParts,
                limit: crate::limits::resource_tile_part_limit(reader.limits) as u64,
                actual: next as u64,
            }), reader, next, state)
        } else {
            let sot = part1_codestream_read_sot(reader, main.tile_count);
            match sot.0 {
                Err(error) => (Err(error), sot.1, next, state),
                Ok(tile) => {
                    let metadata = part1_tile_part_main_metadata(sot.1.position, tile, (next - 1) as u32,
                        main.raw.extensions.lengths, main.raw.plm_seen, main.raw.plm, main.ppm_frames,
                        main.raw.ppm_fragments, main.header);
                    match metadata {
                        Err(error) => (Err(error), sot.1, next, state),
                        Ok((lengths, headers)) => part1_layout_inherited_tile_part(sot.1, main, next, state, tile, lengths, headers),
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_inherited_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
    tile: (usize, u32, u16, u8, u8), lengths: Part1PacketLengths, headers: Part1PackedHeaders,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState) {
    let index = tile.2 as usize;
    let selection = part1_select_inherited_tile_configuration(reader.position, index,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3));
    match selection {
        Err(error) => (Err(error), reader, tile_parts, state),
        Ok(selected) => {
            let quantizations = part1_inherited_tile_owner(index, main.quantizations, state.0.4);
            let progression = part1_inherited_tile_owner(index, main.raw.progression, state.0.5);
            let copied_mct = part1_inherited_tile_owner(index,
                (main.mct.arrays, main.mct.records, main.mct.order), state.1);
            let mct = Part1MctParameters { arrays: copied_mct.0, records: copied_mct.1, order: copied_mct.2 };
            let extensions = part1_inherited_tile_owner(index, main.raw.extensions, state.2);
            let read = part1_read_tile_part(reader, tile, (selected.2, selected.3),
                selected.4, quantizations, selected.1, progression, mct, extensions,
                main.raw.image_size.components, lengths, headers);
            match read.0 {
                Err(error) => (Err(error), read.1, tile_parts, state),
                Ok((payload, parameters, extensions)) => {
                    let committed = part1_commit_persistent_tile_state(state, Part1PersistentTileCommit {
                        position: read.1.position, start: tile.0, index,
                        previous_roi: selected.0, payload,
                        parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
                    });
                    (committed.0, read.1, tile_parts, committed.1)
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_continuation<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState, input_length: usize,
) -> Part1CompleteLayoutResult
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    match part1_codestream_peek_marker(reader) {
        Err(error) => Err(error),
        Ok(marker) => if marker == 0xff90 {
            let step = part1_layout_tile_part(reader, main, tile_parts, state);
            match step.0 {
                Err(error) => Err(error),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidTilePart))
                } else { part1_layout_continuation(step.1, main, step.2, step.3, input_length) },
            }
        } else if marker == 0xffd9 {
            let finished = part1_finish_tile_part_traversal(reader, tile_parts,
                main.raw.plm_seen, main.raw.plm.len() as usize, main.raw.ppm_fragments,
                main.ppm_frames.len() as usize, main.raw.extensions.lengths.len() as usize);
            match finished.0 {
                Err(error) => Err(error),
                Ok(()) => part1_layout_after_tiles(finished.1, main, tile_parts, state),
            }
        } else { Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidMarkerOrder)) },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_layout_from_main_result<'a>(main: Part1MainHeaderResult<'a>, input_length: usize)
    -> Part1CompleteLayoutResult
{
    match main {
        Err(error) => Err(error),
        Ok(header) => if header.tile_count > usize::MAX {
            Err(part1_codestream_malformed(header.reader.position, crate::MalformedKind::ArithmeticOverflow))
        } else {
            part1_layout_continuation(header.reader, header, 0,
                part1_empty_persistent_tile_state(header.tile_count as usize),
                input_length)
        },
    }
}

pub(crate) open spec fn part1_read_layout(reader: Part1CodestreamReader<'_>) -> Part1CompleteLayoutResult {
    part1_layout_from_main_result(part1_read_main_header(reader),
        part1_parse_layout_prologue(reader).1.input.len() as usize)
}

pub(crate) struct Part1ColdStorageEvent {
    pub site: u8,
    pub elements: usize,
    pub succeeded: bool,
}

pub(crate) open spec fn part1_cold_tile_storage(
    count: usize, site: nat, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<(), crate::DecodeError>, Seq<Part1ColdStorageEvent>)>
    decreases 8 - site,
{
    if site >= 8 { Some((Ok(()), events)) }
    else if events.len() == 0 { None }
    else {
        let event = events[0];
        if event.site != site || event.elements != count { None }
        else if !event.succeeded {
            Some((Err(crate::DecodeError::AllocationFailed), events.drop_first()))
        } else { part1_cold_tile_storage(count, site + 1, events.drop_first()) }
    }
}

pub(crate) open spec fn part1_layout_with_cold_storage(
    reader: Part1CodestreamReader<'_>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1CompleteLayoutResult, Seq<Part1ColdStorageEvent>)> {
    part1_quantized_layout_cold_run(reader, events)
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_layout_result(
    reader: Part1CodestreamReader<'_>, result: Part1CompleteLayoutResult,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>|
        part1_layout_with_cold_storage(reader, events) == Some((result, Seq::empty()))
}

pub(crate) open spec fn part1_cold_storage_trace(
    count: usize, site: nat, refusal: Option<u8>,
) -> Seq<Part1ColdStorageEvent>
    decreases 8 - site,
{
    if site >= 8 { Seq::empty() } else {
        let succeeded = refusal != Some(site as u8);
        seq![Part1ColdStorageEvent { site: site as u8, elements: count, succeeded }]
            + if succeeded { part1_cold_storage_trace(count, site + 1, refusal) } else { Seq::empty() }
    }
}

pub(crate) proof fn part1_cold_storage_trace_runs(
    count: usize, site: nat, refusal: Option<u8>,
)
    requires site <= 8,
        match refusal { None => true, Some(at) => site <= at < 8 },
    ensures part1_cold_tile_storage(count, site, part1_cold_storage_trace(count, site, refusal))
        == Some((match refusal { None => Ok(()), Some(_) => Err(crate::DecodeError::AllocationFailed) },
            Seq::empty())),
    decreases 8 - site,
{
    reveal_with_fuel(part1_cold_storage_trace, 2);
    reveal_with_fuel(part1_cold_tile_storage, 2);
    if site < 8 {
        if refusal != Some(site as u8) {
            part1_cold_storage_trace_runs(count, site + 1, refusal);
        }
        let event = Part1ColdStorageEvent {
            site: site as u8, elements: count, succeeded: refusal != Some(site as u8) };
        let rest = if event.succeeded {
            part1_cold_storage_trace(count, site + 1, refusal)
        } else { Seq::empty() };
        assert((seq![event] + rest).drop_first() =~= rest);
    }
}

pub(crate) proof fn part1_cold_layout_normal(reader: Part1CodestreamReader<'_>)
    ensures part1_cold_layout_result(reader, part1_read_layout(reader)),
{
    reveal(part1_cold_layout_result);
    let events = part1_quantized_layout_cold_normal(reader);
    assert(events + Seq::<Part1ColdStorageEvent>::empty() =~= events);
    assert(part1_layout_with_cold_storage(reader, events)
        == Some((part1_read_layout(reader), Seq::empty())));
}

pub(crate) proof fn part1_cold_layout_refused(
    reader: Part1CodestreamReader<'_>, header: Part1MainHeader<'_>, site: u8,
    response: Result<(), crate::DecodeError>,
)
    requires part1_read_main_header(reader) == Ok(header),
        header.tile_count <= usize::MAX, site < 8,
        response == Err(crate::DecodeError::AllocationFailed),
    ensures part1_cold_layout_result(reader, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_cold_layout_result);
    part1_cold_storage_trace_runs(header.tile_count as usize, 0, Some(site));
    let later = part1_cold_storage_trace(header.tile_count as usize, 0, Some(site));
    let main_calls = part1_main_header_normal_calls(reader);
    part1_main_header_cold_normal(reader, later);
    let events = main_calls + later;
    assert(part1_layout_with_cold_storage(reader, events)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}

pub(crate) proof fn part1_cold_tile_storage_errors(
    count: usize, site: nat, events: Seq<Part1ColdStorageEvent>,
)
    requires site <= 8,
    ensures match part1_cold_tile_storage(count, site, events) {
        Some((Err(error), _)) => error == crate::DecodeError::AllocationFailed,
        _ => true,
    },
    decreases 8 - site,
{
    reveal_with_fuel(part1_cold_tile_storage, 2);
    if site < 8 && events.len() > 0 && events[0].site == site
        && events[0].elements == count && events[0].succeeded {
        part1_cold_tile_storage_errors(count, site + 1, events.drop_first());
    }
}

pub(crate) proof fn part1_cold_layout_normal_projection(
    reader: Part1CodestreamReader<'_>, result: Part1CompleteLayoutResult,
)
    requires part1_cold_layout_result(reader, result),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_read_layout(reader),
{
    reveal(part1_cold_layout_result);
    let events = choose|events: Seq<Part1ColdStorageEvent>|
        part1_layout_with_cold_storage(reader, events) == Some((result, Seq::empty()));
    part1_quantized_layout_cold_projection(reader, events, result, Seq::empty());
}

pub(crate) proof fn part1_cold_layout_calls(
    reader: Part1CodestreamReader<'_>, result: Part1CompleteLayoutResult,
)
    requires part1_cold_layout_result(reader, result),
    ensures exists|events: Seq<Part1ColdStorageEvent>|
        part1_layout_with_cold_storage(reader, events) == Some((result, Seq::empty())),
{
    reveal(part1_cold_layout_result);
}

pub(crate) proof fn part1_cold_tile_storage_frame(
    count: usize, site: nat, events: Seq<Part1ColdStorageEvent>,
    tail: Seq<Part1ColdStorageEvent>, result: Result<(), crate::DecodeError>,
)
    requires site <= 8,
        part1_cold_tile_storage(count, site, events) == Some((result, Seq::empty())),
    ensures part1_cold_tile_storage(count, site, events + tail) == Some((result, tail)),
    decreases 8 - site,
{
    reveal_with_fuel(part1_cold_tile_storage, 2);
    if site < 8 {
        assert(events.len() > 0);
        assert((events + tail).drop_first() =~= events.drop_first() + tail);
        if events[0].succeeded {
            part1_cold_tile_storage_frame(count, site + 1, events.drop_first(), tail, result);
        }
    } else {
        assert(events =~= Seq::empty());
    }
}

pub(crate) proof fn part1_layout_with_cold_storage_frame(
    reader: Part1CodestreamReader<'_>, events: Seq<Part1ColdStorageEvent>,
    tail: Seq<Part1ColdStorageEvent>, result: Part1CompleteLayoutResult,
)
    requires part1_layout_with_cold_storage(reader, events) == Some((result, Seq::empty())),
    ensures part1_layout_with_cold_storage(reader, events + tail) == Some((result, tail)),
{
    part1_quantized_layout_cold_frame(reader, events, result, Seq::empty(), tail);
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}

pub(crate) open spec fn part1_parse_layout_with_cold_storage(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1CompleteLayoutResult, Seq<Part1ColdStorageEvent>)> {
    match part1_codestream_reader_new(input, limits) {
        Err(error) => Some((Err(error), events)),
        Ok(reader) => part1_layout_with_cold_storage(reader, events),
    }
}

pub closed spec fn part1_parse_layout_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Part1CompleteLayoutResult,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>|
        part1_parse_layout_with_cold_storage(input, limits, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_parse_layout_cold_witness(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Part1CompleteLayoutResult,
    events: Seq<Part1ColdStorageEvent>,
)
    requires part1_parse_layout_with_cold_storage(input, limits, events)
        == Some((result, Seq::empty())),
    ensures part1_parse_layout_cold_result(input, limits, result),
{
    reveal(part1_parse_layout_cold_result);
}

pub(crate) open spec fn part1_layout_info(result: Part1CompleteLayoutResult)
    -> Result<(Part1LayoutMainFields, Part1ProfileMetadata, u32, u64), crate::DecodeError> {
    match result {
        Err(error) => Err(error),
        Ok(layout) => Ok((layout.0, layout.1, layout.2, layout.3)),
    }
}

pub(crate) open spec fn part1_parse_info_with_cold_storage(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<(Part1LayoutMainFields, Part1ProfileMetadata, u32, u64), crate::DecodeError>,
    Seq<Part1ColdStorageEvent>)> {
    match part1_parse_layout_with_cold_storage(input, limits, events) {
        None => None,
        Some((result, rest)) => Some((part1_layout_info(result), rest)),
    }
}

pub closed spec fn part1_parse_info_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1LayoutMainFields, Part1ProfileMetadata, u32, u64), crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>|
        part1_parse_info_with_cold_storage(input, limits, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_parse_layout_cold_projection(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Part1CompleteLayoutResult,
)
    requires part1_parse_layout_cold_result(input, limits, result),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_parse_layout(input, limits),
{
    reveal(part1_parse_layout_cold_result);
    reveal(part1_cold_layout_result);
    let events = choose|events: Seq<Part1ColdStorageEvent>|
        part1_parse_layout_with_cold_storage(input, limits, events) == Some((result, Seq::empty()));
    part1_parse_layout_unfold(input, limits);
    if let Ok(reader) = part1_codestream_reader_new(input, limits) {
        assert(part1_layout_with_cold_storage(reader, events) == Some((result, Seq::empty())));
        part1_cold_layout_normal_projection(reader, result);
    }
}

pub(crate) proof fn part1_parse_info_cold_projection(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Part1CompleteLayoutResult,
)
    requires part1_parse_layout_cold_result(input, limits, result),
    ensures part1_parse_info_cold_result(input, limits, part1_layout_info(result)),
        result != Err(crate::DecodeError::AllocationFailed) ==>
            part1_layout_info(result) == part1_parse_info(input, limits),
{
    reveal(part1_parse_layout_cold_result);
    reveal(part1_parse_info_cold_result);
    let events = choose|events: Seq<Part1ColdStorageEvent>|
        part1_parse_layout_with_cold_storage(input, limits, events) == Some((result, Seq::empty()));
    assert(part1_parse_info_with_cold_storage(input, limits, events)
        == Some((part1_layout_info(result), Seq::empty())));
    if result != Err(crate::DecodeError::AllocationFailed) {
        part1_parse_layout_cold_projection(input, limits, result);
        part1_parse_info_unfold(input, limits);
    }
}

pub(crate) proof fn part1_parse_layout_cold_calls(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Part1CompleteLayoutResult,
)
    requires part1_parse_layout_cold_result(input, limits, result),
    ensures exists|calls: Seq<Part1ColdStorageEvent>|
        part1_parse_layout_with_cold_storage(input, limits, calls)
            == Some((result, Seq::empty())),
{
    reveal(part1_parse_layout_cold_result);
}

pub(crate) proof fn part1_parse_info_cold_calls(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<(Part1LayoutMainFields, Part1ProfileMetadata, u32, u64), crate::DecodeError>,
)
    requires part1_parse_info_cold_result(input, limits, result),
    ensures exists|calls: Seq<Part1ColdStorageEvent>|
        part1_parse_info_with_cold_storage(input, limits, calls)
            == Some((result, Seq::empty())),
{
    reveal(part1_parse_info_cold_result);
}

pub(crate) proof fn part1_parse_layout_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part1_parse_layout_cold_result(input, limits, part1_parse_layout(input, limits)),
{
    part1_parse_layout_unfold(input, limits);
    match part1_codestream_reader_new(input, limits) {
        Err(error) => {
            part1_parse_layout_cold_witness(input, limits, Err(error), Seq::empty());
        },
        Ok(reader) => {
            part1_cold_layout_normal(reader);
            part1_cold_layout_calls(reader, part1_read_layout(reader));
            let calls = choose|calls: Seq<Part1ColdStorageEvent>|
                part1_layout_with_cold_storage(reader, calls)
                    == Some((part1_read_layout(reader), Seq::empty()));
            part1_parse_layout_cold_witness(input, limits, part1_read_layout(reader), calls);
        },
    }
}

pub(crate) proof fn part1_parse_info_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part1_parse_info_cold_result(input, limits, part1_parse_info(input, limits)),
{
    part1_parse_layout_cold_normal(input, limits);
    part1_parse_info_cold_projection(input, limits, part1_parse_layout(input, limits));
    part1_parse_info_unfold(input, limits);
}

pub closed spec fn part1_parse_layout(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Part1CompleteLayoutResult
{
    match part1_codestream_reader_new(input, limits) {
        Err(error) => Err(error), Ok(reader) => part1_read_layout(reader),
    }
}

pub closed spec fn part1_parse_info(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<(Part1LayoutMainFields, Part1ProfileMetadata, u32, u64), crate::DecodeError>
{
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error), Ok(layout) => Ok((layout.0, layout.1, layout.2, layout.3)),
    }
}

pub(crate) proof fn part1_parse_layout_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part1_parse_layout(input, limits) == match part1_codestream_reader_new(input, limits) {
        Err(error) => Err(error), Ok(reader) => part1_read_layout(reader),
    },
{
}

pub(crate) proof fn part1_parse_info_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part1_parse_info(input, limits) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error), Ok(layout) => Ok((layout.0, layout.1, layout.2, layout.3)),
    },
{
}

}
