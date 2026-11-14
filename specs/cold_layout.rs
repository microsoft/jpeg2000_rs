//! Ordered main construction, inherited/committed owner copies and tile creation.

use super::*;

verus! {

pub(crate) open spec fn part1_cold_commit_finish(
    state: Part1PersistentTileState, commit: Part1PersistentTileCommit,
    configured: (Result<(), crate::DecodeError>, Part1PersistentTileConfiguration),
) -> (Result<(), crate::DecodeError>, Part1PersistentTileState) {
    let prefix = (configured.1, state.1, state.2, state.3);
    match configured.0 {
        Err(error) => (Err(error), prefix),
        Ok(()) => if commit.index as int >= state.1.len() {
            (Err(part1_codestream_malformed(commit.position, crate::MalformedKind::InvalidTilePart)), prefix)
        } else {
            let parameters = state.1.update(commit.index as int, Some(commit.parameters));
            if commit.index as int >= state.2.len() {
                (Err(part1_codestream_malformed(commit.position, crate::MalformedKind::InvalidTilePart)),
                 (configured.1, parameters, state.2, state.3))
            } else {
                (Ok(()), (configured.1, parameters,
                    state.2.update(commit.index as int, Some(commit.extensions)),
                    state.3.push(commit.payload)))
            }
        },
    }
}

pub(crate) open spec fn part1_cold_commit_state(
    state: Part1PersistentTileState, commit: Part1PersistentTileCommit, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1PersistentTileState), Seq<Part1ColdStorageEvent>)> {
    match part1_commit_quantization_cold_run(commit.position, commit.start, commit.index,
        state.3.len() as usize, commit.previous_roi, commit.payload, state.0, events) {
        None => None,
        Some((configured, rest)) => Some((part1_cold_commit_finish(state, commit, configured), rest)),
    }
}

pub(crate) open spec fn part1_cold_layout_read_input<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    selected: Part1InheritedTileConfiguration,
) -> Part1ColdTileInput<'a> {
    let index = tile.2 as usize;
    let quantizations = part1_inherited_tile_owner(index, main.quantizations, state.0.4);
    let copied_mct = part1_inherited_tile_owner(index,
        (main.mct.arrays, main.mct.records, main.mct.order), state.1);
    Part1ColdTileInput {
        reader, tile, defaults: (selected.2, selected.3), styles: selected.4, quantizations,
        roi: selected.1, progression: part1_inherited_tile_owner(index, main.raw.progression, state.0.5),
        mct: Part1MctParameters { arrays: copied_mct.0, records: copied_mct.1, order: copied_mct.2 },
        extensions: part1_inherited_tile_owner(index, main.raw.extensions, state.2),
        components: main.raw.image_size.components, lengths, headers,
    }
}

pub(crate) open spec fn part1_cold_layout_after_mct_copy<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    selected: Part1InheritedTileConfiguration, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState), Seq<Part1ColdStorageEvent>)> {
    let index = tile.2 as usize;
    let input = part1_cold_layout_read_input(reader, main, state, tile, lengths, headers, selected);
    match part1_cold_tile_part_run(input, events) {
        None => None,
        Some(((result, after), rest)) => match result {
            Err(error) => Some(((Err(error), after, tile_parts, state), rest)),
            Ok((payload, parameters, extensions)) => {
                match part1_cold_commit_state(state, Part1PersistentTileCommit {
                    position: after.position, start: tile.0, index, previous_roi: selected.0, payload,
                    parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
                }, rest) {
                    None => None,
                    Some((committed, tail)) => Some(((committed.0, after, tile_parts, committed.1), tail)),
                }
            },
        },
    }
}

pub(crate) open spec fn part1_cold_layout_mct_requests(
    main: Part1MainHeader<'_>, state: Part1PersistentTileState, index: usize,
) -> Seq<Part1MctCopyRequest> {
    part1_mct_owner_copy_requests(part1_inherited_tile_owner(
        index, (main.mct.arrays, main.mct.records, main.mct.order), state.1))
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_layout_after_progression_copy<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    selected: Part1InheritedTileConfiguration, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState), Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_cold_layout_mct_requests(main, state, tile.2 as usize), events) {
        None => None,
        Some((Err(error), rest)) => Some(((Err(error), reader, tile_parts, state), rest)),
        Some((Ok(()), rest)) => part1_cold_layout_after_mct_copy(
            reader, main, tile_parts, state, tile, lengths, headers, selected, rest),
    }
}

pub(crate) proof fn part1_cold_layout_mct_normal_bind<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, selected: Part1InheritedTileConfiguration,
    calls: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_after_mct_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, calls) == Some((result, rest)),
    ensures part1_cold_layout_after_progression_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected,
        part1_mct_copy_normal_calls(part1_cold_layout_mct_requests(main, state, tile.2 as usize)) + calls)
            == Some((result, rest)),
{
    reveal(part1_cold_layout_after_progression_copy);
    part1_mct_copy_normal(part1_cold_layout_mct_requests(main, state, tile.2 as usize), calls);
}

pub(crate) open spec fn part1_cold_layout_after_inherited_copy<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    selected: Part1InheritedTileConfiguration, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState), Seq<Part1ColdStorageEvent>)> {
    let progression = part1_inherited_tile_owner(tile.2 as usize, main.raw.progression, state.0.5);
    if progression.len() == 0 {
        part1_cold_layout_after_progression_copy(
            reader, main, tile_parts, state, tile, lengths, headers, selected, events)
    } else {
        match part1_quantization_storage_request(14, progression.len() as usize, events) {
            None => None,
            Some((Err(error), rest)) => Some(((Err(error), reader, tile_parts, state), rest)),
            Some((Ok(()), rest)) => part1_cold_layout_after_progression_copy(
                reader, main, tile_parts, state, tile, lengths, headers, selected, rest),
        }
    }
}

pub(crate) open spec fn part1_cold_layout_inherited<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState), Seq<Part1ColdStorageEvent>)> {
    let index = tile.2 as usize;
    match part1_select_inherited_tile_configuration(reader.position, index,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3)) {
        Err(error) => Some(((Err(error), reader, tile_parts, state), events)),
        Ok(selected) => {
            let quantizations = part1_inherited_tile_owner(index, main.quantizations, state.0.4);
            if quantizations.1.len() == 0 {
                part1_cold_layout_after_inherited_copy(
                    reader, main, tile_parts, state, tile, lengths, headers, selected, events)
            } else {
                match part1_quantization_storage_request(10, quantizations.1.len() as usize, events) {
                    None => None,
                    Some((Err(error), rest)) => Some(((Err(error), reader, tile_parts, state), rest)),
                    Some((Ok(()), rest)) => part1_cold_layout_after_inherited_copy(
                        reader, main, tile_parts, state, tile, lengths, headers, selected, rest),
                }
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_layout_tile_part<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState), Seq<Part1ColdStorageEvent>)> {
    if tile_parts == u32::MAX {
        Some(((Err(part1_codestream_malformed(reader.position, crate::MalformedKind::ArithmeticOverflow)),
            reader, tile_parts, state), events))
    } else {
        let next = (tile_parts as int + 1) as u32;
        if next > crate::limits::resource_tile_part_limit(reader.limits) {
            Some(((Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::TileParts, limit: crate::limits::resource_tile_part_limit(reader.limits) as u64,
                actual: next as u64 }), reader, next, state), events))
        } else {
            let sot = part1_codestream_read_sot(reader, main.tile_count);
            match sot.0 {
                Err(error) => Some(((Err(error), sot.1, next, state), events)),
                Ok(tile) => match part1_tile_part_main_metadata(sot.1.position, tile, (next - 1) as u32,
                    main.raw.extensions.lengths, main.raw.plm_seen, main.raw.plm, main.ppm_frames,
                    main.raw.ppm_fragments, main.header) {
                    Err(error) => Some(((Err(error), sot.1, next, state), events)),
                    Ok((lengths, headers)) => part1_cold_layout_inherited(
                        sot.1, main, next, state, tile, lengths, headers, events),
                },
            }
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_layout_continuation<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState, input_length: usize, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1CompleteLayoutResult, Seq<Part1ColdStorageEvent>)>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    match part1_codestream_peek_marker(reader) {
        Err(error) => Some((Err(error), events)),
        Ok(marker) => if marker == 0xff90 {
            match part1_cold_layout_tile_part(reader, main, tile_parts, state, events) {
                None => None,
                Some((step, rest)) => match step.0 {
                    Err(error) => Some((Err(error), rest)),
                    Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                        Some((Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidTilePart)), rest))
                    } else { part1_cold_layout_continuation(
                        step.1, main, step.2, step.3, input_length, rest) },
                },
            }
        } else if marker == 0xffd9 {
            let finished = part1_finish_tile_part_traversal(reader, tile_parts,
                main.raw.plm_seen, main.raw.plm.len() as usize, main.raw.ppm_fragments,
                main.ppm_frames.len() as usize, main.raw.extensions.lengths.len() as usize);
            Some((match finished.0 {
                Err(error) => Err(error),
                Ok(()) => part1_layout_after_tiles(finished.1, main, tile_parts, state),
            }, events))
        } else { Some((Err(part1_codestream_malformed(
            reader.position, crate::MalformedKind::InvalidMarkerOrder)), events)) },
    }
}

pub(crate) open spec fn part1_cold_layout_after_main<'a>(
    reader: Part1CodestreamReader<'a>, header: Part1MainHeader<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1CompleteLayoutResult, Seq<Part1ColdStorageEvent>)> {
    if header.tile_count > usize::MAX {
        Some((Err(part1_codestream_malformed(header.reader.position, crate::MalformedKind::ArithmeticOverflow)), events))
    } else {
        match part1_cold_tile_storage(header.tile_count as usize, 0, events) {
            None => None,
            Some((Err(error), rest)) => Some((Err(error), rest)),
            Some((Ok(()), rest)) => part1_cold_layout_continuation(header.reader, header, 0,
                part1_empty_persistent_tile_state(header.tile_count as usize),
                part1_parse_layout_prologue(reader).1.input.len() as usize, rest),
        }
    }
}

pub(crate) open spec fn part1_quantized_layout_cold_run(
    reader: Part1CodestreamReader<'_>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1CompleteLayoutResult, Seq<Part1ColdStorageEvent>)> {
    match part1_main_header_cold_run(reader, events) {
        None => None,
        Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(header), rest)) => part1_cold_layout_after_main(reader, header, rest),
    }
}

pub(crate) proof fn part1_cold_commit_normal(
    state: Part1PersistentTileState, commit: Part1PersistentTileCommit,
)
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_commit_state(state, commit,
            part1_commit_quantization_normal_calls(commit.position, commit.start, commit.index,
                state.3.len() as usize, commit.previous_roi, commit.payload, state.0) + tail)
                == Some((part1_commit_persistent_tile_state(state, commit), tail)),
{
    reveal(part1_commit_persistent_tile_state);
    part1_commit_quantization_cold_normal(commit.position, commit.start, commit.index,
        state.3.len() as usize, commit.previous_roi, commit.payload, state.0);
}

pub(crate) proof fn part1_cold_layout_after_mct_normal<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, selected: Part1InheritedTileConfiguration,
) -> (calls: Seq<Part1ColdStorageEvent>)
    requires part1_select_inherited_tile_configuration(reader.position, tile.2 as usize,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3)) == Ok(selected),
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_layout_after_mct_copy(reader, main, tile_parts, state, tile, lengths, headers, selected, calls + tail)
            == Some((part1_layout_inherited_tile_part(reader, main, tile_parts, state, tile, lengths, headers), tail)),
{
    reveal(part1_layout_inherited_tile_part);
    reveal(part1_cold_layout_read_input);
    reveal(part1_cold_tile_normal);
    reveal(part1_cold_commit_state);
    reveal(part1_cold_commit_finish);
    let index = tile.2 as usize;
    let input = part1_cold_layout_read_input(reader, main, state, tile, lengths, headers, selected);
    part1_cold_tile_part_normal(input);
    let read_calls = part1_cold_tile_part_normal_calls(input);
    let normal = part1_cold_tile_normal(input);
    let committed = match normal.0 {
        Err(_) => Seq::empty(),
        Ok((payload, parameters, extensions)) => {
            let commit = Part1PersistentTileCommit {
                position: normal.1.position, start: tile.0, index, previous_roi: selected.0, payload,
                parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
            };
            part1_cold_commit_normal(state, commit);
            part1_commit_quantization_normal_calls(commit.position, commit.start, commit.index,
                state.3.len() as usize, commit.previous_roi, commit.payload, state.0)
        },
    };
    let calls = read_calls + committed;
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_layout_after_mct_copy(reader, main, tile_parts, state, tile, lengths, headers, selected, calls + tail)
            == Some((part1_layout_inherited_tile_part(reader, main, tile_parts, state, tile, lengths, headers), tail)) by {
        assert(calls + tail =~= read_calls + (committed + tail));
        assert(part1_cold_tile_part_run(input, read_calls + (committed + tail)) == Some((normal, committed + tail)));
        match normal.0 {
            Err(error) => {
                assert(committed =~= Seq::<Part1ColdStorageEvent>::empty());
            },
            Ok((payload, parameters, extensions)) => {
                let commit = Part1PersistentTileCommit {
                    position: normal.1.position, start: tile.0, index, previous_roi: selected.0, payload,
                    parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
                };
                assert(part1_cold_commit_state(state, commit, committed + tail)
                    == Some((part1_commit_persistent_tile_state(state, commit), tail)));
            },
        }
    }
    calls
}

pub(crate) proof fn part1_cold_layout_inherited_normal<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
) -> (calls: Seq<Part1ColdStorageEvent>)
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_layout_inherited(reader, main, tile_parts, state, tile, lengths, headers, calls + tail)
            == Some((part1_layout_inherited_tile_part(reader, main, tile_parts, state, tile, lengths, headers), tail)),
{
    let index = tile.2 as usize;
    let selection = part1_select_inherited_tile_configuration(reader.position, index,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3));
    match selection {
        Err(_) => {
            reveal(part1_layout_inherited_tile_part);
            Seq::empty()
        },
        Ok(selected) => {
            let quantizations = part1_inherited_tile_owner(index, main.quantizations, state.0.4);
            let copied = if quantizations.1.len() == 0 { Seq::empty() } else {
                seq![Part1ColdStorageEvent { site: 10, elements: quantizations.1.len() as usize, succeeded: true }]
            };
            let progression = part1_inherited_tile_owner(index, main.raw.progression, state.0.5);
            let progression_calls = if progression.len() == 0 { Seq::empty() } else {
                seq![Part1ColdStorageEvent { site: 14, elements: progression.len() as usize, succeeded: true }]
            };
            let rest_calls = part1_cold_layout_after_mct_normal(
                reader, main, tile_parts, state, tile, lengths, headers, selected);
            let mct_requests = part1_cold_layout_mct_requests(main, state, index);
            let mct_calls = part1_mct_copy_normal_calls(mct_requests);
            let calls = copied + progression_calls + mct_calls + rest_calls;
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_cold_layout_inherited(reader, main, tile_parts, state, tile, lengths, headers, calls + tail)
                    == Some((part1_layout_inherited_tile_part(
                        reader, main, tile_parts, state, tile, lengths, headers), tail)) by {
                assert(calls + tail =~= copied + (progression_calls + (mct_calls + (rest_calls + tail))));
                part1_cold_layout_mct_normal_bind(reader, main, tile_parts, state, tile, lengths, headers, selected,
                    rest_calls + tail, part1_layout_inherited_tile_part(reader, main, tile_parts, state, tile, lengths, headers), tail);
                let after_progression = mct_calls + (rest_calls + tail);
                let after_quantization = progression_calls + after_progression;
                if progression_calls.len() > 0 {
                    assert(after_quantization.drop_first() =~= after_progression);
                } else { assert(after_quantization =~= after_progression); }
                if copied.len() > 0 {
                    assert((calls + tail).drop_first() =~= after_quantization);
                } else { assert(calls + tail =~= after_quantization); }
            }
            calls
        },
    }
}

pub(crate) proof fn part1_cold_layout_tile_normal<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState,
) -> (calls: Seq<Part1ColdStorageEvent>)
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_layout_tile_part(reader, main, tile_parts, state, calls + tail)
            == Some((part1_layout_tile_part(reader, main, tile_parts, state), tail)),
{
    reveal(part1_cold_layout_tile_part);
    reveal(part1_layout_tile_part);
    if tile_parts == u32::MAX { Seq::empty() } else {
        let next = (tile_parts as int + 1) as u32;
        if next > crate::limits::resource_tile_part_limit(reader.limits) { Seq::empty() } else {
            let sot = part1_codestream_read_sot(reader, main.tile_count);
            match sot.0 {
                Err(_) => Seq::empty(),
                Ok(tile) => match part1_tile_part_main_metadata(sot.1.position, tile, (next - 1) as u32,
                    main.raw.extensions.lengths, main.raw.plm_seen, main.raw.plm, main.ppm_frames,
                    main.raw.ppm_fragments, main.header) {
                    Err(_) => Seq::empty(),
                    Ok((lengths, headers)) => part1_cold_layout_inherited_normal(
                        sot.1, main, next, state, tile, lengths, headers),
                },
            }
        }
    }
}

pub(crate) proof fn part1_cold_layout_continuation_normal<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
    tile_parts: u32, state: Part1PersistentTileState, input_length: usize,
) -> (calls: Seq<Part1ColdStorageEvent>)
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_layout_continuation(reader, main, tile_parts, state, input_length, calls + tail)
            == Some((part1_layout_continuation(reader, main, tile_parts, state, input_length), tail)),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    reveal_with_fuel(part1_layout_continuation, 1);
    match part1_codestream_peek_marker(reader) {
        Err(_) => Seq::empty(),
        Ok(marker) => if marker == 0xff90 {
            let calls = part1_cold_layout_tile_normal(reader, main, tile_parts, state);
            let step = part1_layout_tile_part(reader, main, tile_parts, state);
            let rest = if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_cold_layout_continuation_normal(step.1, main, step.2, step.3, input_length)
            } else { Seq::empty() };
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_cold_layout_continuation(reader, main, tile_parts, state, input_length, (calls + rest) + tail)
                    == Some((part1_layout_continuation(reader, main, tile_parts, state, input_length), tail)) by {
                assert((calls + rest) + tail =~= calls + (rest + tail));
                reveal_with_fuel(part1_cold_layout_continuation, 1);
                reveal_with_fuel(part1_layout_continuation, 1);
            }
            calls + rest
        } else { Seq::empty() },
    }
}

pub(crate) proof fn part1_quantized_layout_cold_normal(reader: Part1CodestreamReader<'_>)
    -> (calls: Seq<Part1ColdStorageEvent>)
    ensures forall|tail: Seq<Part1ColdStorageEvent>|
        part1_quantized_layout_cold_run(reader, calls + tail)
            == Some((part1_read_layout(reader), tail)),
{
    reveal(part1_layout_from_main_result);
    let main_calls = part1_main_header_normal_calls(reader);
    match part1_read_main_header(reader) {
        Err(_) => {
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_quantized_layout_cold_run(reader, main_calls + tail)
                    == Some((part1_read_layout(reader), tail)) by {
                part1_main_header_cold_normal(reader, tail);
            }
            main_calls
        },
        Ok(main) => if main.tile_count > usize::MAX {
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_quantized_layout_cold_run(reader, main_calls + tail)
                    == Some((part1_read_layout(reader), tail)) by {
                part1_main_header_cold_normal(reader, tail);
            }
            main_calls
        } else {
            let none_calls = part1_cold_storage_trace(main.tile_count as usize, 0, None);
            part1_cold_storage_trace_runs(main.tile_count as usize, 0, None);
            let tile_calls = part1_cold_layout_continuation_normal(
                main.reader, main, 0, part1_empty_persistent_tile_state(main.tile_count as usize),
                part1_parse_layout_prologue(reader).1.input.len() as usize);
            let calls = main_calls + none_calls + tile_calls;
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_quantized_layout_cold_run(reader, calls + tail)
                    == Some((part1_read_layout(reader), tail)) by {
                assert(calls + tail =~= main_calls + (none_calls + (tile_calls + tail)));
                part1_main_header_cold_normal(reader, none_calls + (tile_calls + tail));
                part1_cold_tile_storage_frame(main.tile_count as usize, 0, none_calls,
                    tile_calls + tail, Ok(()));
                assert(Seq::<Part1ColdStorageEvent>::empty() + (tile_calls + tail) =~= tile_calls + tail);
            }
            calls
        },
    }
}

pub(crate) proof fn part1_cold_commit_projection(
    state: Part1PersistentTileState, commit: Part1PersistentTileCommit,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_commit_state(state, commit, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_commit_persistent_tile_state(state, commit),
{
    reveal(part1_commit_persistent_tile_state);
    if let Some((configured, after)) = part1_commit_quantization_cold_run(
        commit.position, commit.start, commit.index, state.3.len() as usize,
        commit.previous_roi, commit.payload, state.0, events) {
        part1_commit_quantization_cold_projection(commit.position, commit.start, commit.index,
            state.3.len() as usize, commit.previous_roi, commit.payload, state.0, events, configured, after);
    }
}

pub(crate) proof fn part1_cold_layout_inherited_projection<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_inherited(reader, main, tile_parts, state, tile, lengths, headers, events)
        == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_layout_inherited_tile_part(reader, main, tile_parts, state, tile, lengths, headers),
{
    reveal(part1_cold_layout_after_progression_copy);
    reveal(part1_layout_inherited_tile_part);
    let index = tile.2 as usize;
    if let Ok(selected) = part1_select_inherited_tile_configuration(reader.position, index,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3)) {
        let quantizations = part1_inherited_tile_owner(index, main.quantizations, state.0.4);
        let after_quantization = if quantizations.1.len() == 0 { events } else { events.drop_first() };
        let progression = part1_inherited_tile_owner(index, main.raw.progression, state.0.5);
        let after_progression = if progression.len() == 0 { after_quantization } else { after_quantization.drop_first() };
        let copied = part1_mct_copy_run(part1_cold_layout_mct_requests(main, state, index), after_progression);
        assert(copied.is_some());
        let (status, after_copy) = copied.unwrap();
        part1_mct_copy_projection(part1_cold_layout_mct_requests(main, state, index), after_progression, status, after_copy);
        assert(status == Ok(()));
        let input = part1_cold_layout_read_input(reader, main, state, tile, lengths, headers, selected);
        if let Some((read, after_read)) = part1_cold_tile_part_run(input, after_copy) {
            part1_cold_tile_part_projection(input, after_copy, read, after_read);
            if let Ok((payload, parameters, extensions)) = read.0 {
                let commit = Part1PersistentTileCommit {
                    position: read.1.position, start: tile.0, index, previous_roi: selected.0, payload,
                    parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
                };
                if let Some((committed, after)) = part1_cold_commit_state(state, commit, after_read) {
                    part1_cold_commit_projection(state, commit, after_read, committed, after);
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_layout_tile_projection<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_tile_part(reader, main, tile_parts, state, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_layout_tile_part(reader, main, tile_parts, state),
{
    reveal(part1_cold_layout_tile_part);
    reveal(part1_layout_tile_part);
    if tile_parts < u32::MAX {
        let next = (tile_parts as int + 1) as u32;
        if next <= crate::limits::resource_tile_part_limit(reader.limits) {
            let sot = part1_codestream_read_sot(reader, main.tile_count);
            if let Ok(tile) = sot.0 {
                if let Ok((lengths, headers)) = part1_tile_part_main_metadata(sot.1.position, tile,
                    (next - 1) as u32, main.raw.extensions.lengths, main.raw.plm_seen, main.raw.plm,
                    main.ppm_frames, main.raw.ppm_fragments, main.header) {
                    part1_cold_layout_inherited_projection(
                        sot.1, main, next, state, tile, lengths, headers, events, result, rest);
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_layout_continuation_projection<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, input_length: usize, events: Seq<Part1ColdStorageEvent>,
    result: Part1CompleteLayoutResult, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_continuation(reader, main, tile_parts, state, input_length, events)
        == Some((result, rest)), result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_layout_continuation(reader, main, tile_parts, state, input_length),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    reveal_with_fuel(part1_layout_continuation, 1);
    if part1_codestream_peek_marker(reader) == Ok(0xff90) {
        if let Some((step, after)) = part1_cold_layout_tile_part(reader, main, tile_parts, state, events) {
            part1_cold_layout_tile_projection(reader, main, tile_parts, state, events, step, after);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_cold_layout_continuation_projection(
                    step.1, main, step.2, step.3, input_length, after, result, rest);
            }
        }
    }
}

pub(crate) proof fn part1_quantized_layout_cold_projection(
    reader: Part1CodestreamReader<'_>, events: Seq<Part1ColdStorageEvent>,
    result: Part1CompleteLayoutResult, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_quantized_layout_cold_run(reader, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_read_layout(reader),
{
    reveal(part1_layout_from_main_result);
    if let Some((main_result, after_main)) = part1_main_header_cold_run(reader, events) {
        part1_main_header_cold_projection(reader, events, main_result, after_main);
        if let Ok(main) = main_result {
            if main.tile_count <= usize::MAX {
                if let Some((reserved, after_none)) = part1_cold_tile_storage(main.tile_count as usize, 0, after_main) {
                    part1_cold_tile_storage_errors(main.tile_count as usize, 0, after_main);
                    if reserved.is_ok() {
                        part1_cold_layout_continuation_projection(main.reader, main, 0,
                            part1_empty_persistent_tile_state(main.tile_count as usize),
                            part1_parse_layout_prologue(reader).1.input.len() as usize, after_none, result, rest);
                    }
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_commit_frame(
    state: Part1PersistentTileState, commit: Part1PersistentTileCommit,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_commit_state(state, commit, events) == Some((result, rest)),
    ensures part1_cold_commit_state(state, commit, events + tail) == Some((result, rest + tail)),
{
    if let Some((configured, after)) = part1_commit_quantization_cold_run(
        commit.position, commit.start, commit.index, state.3.len() as usize,
        commit.previous_roi, commit.payload, state.0, events) {
        part1_commit_quantization_cold_frame(commit.position, commit.start, commit.index,
            state.3.len() as usize, commit.previous_roi, commit.payload, state.0, events, tail, configured, after);
    }
}

pub(crate) proof fn part1_cold_layout_after_mct_frame<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, selected: Part1InheritedTileConfiguration,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_after_mct_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, events) == Some((result, rest)),
    ensures part1_cold_layout_after_mct_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, events + tail) == Some((result, rest + tail)),
{
    let input = part1_cold_layout_read_input(reader, main, state, tile, lengths, headers, selected);
    if let Some((read, after_read)) = part1_cold_tile_part_run(input, events) {
        part1_cold_tile_part_frame(input, events, tail, read, after_read);
        if let Ok((payload, parameters, extensions)) = read.0 {
            let commit = Part1PersistentTileCommit {
                position: read.1.position, start: tile.0, index: tile.2 as usize, previous_roi: selected.0, payload,
                parameters: (parameters.arrays, parameters.records, parameters.order), extensions,
            };
            if let Some((committed, after)) = part1_cold_commit_state(state, commit, after_read) {
                part1_cold_commit_frame(state, commit, after_read, committed, after, tail);
            }
        }
    }
}

pub(crate) proof fn part1_cold_layout_after_progression_frame<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, selected: Part1InheritedTileConfiguration,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_after_progression_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, events) == Some((result, rest)),
    ensures part1_cold_layout_after_progression_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_cold_layout_after_progression_copy);
    let requests = part1_cold_layout_mct_requests(main, state, tile.2 as usize);
    if let Some((copied, after)) = part1_mct_copy_run(requests, events) {
        part1_mct_copy_frame(requests, events, copied, after, tail);
        if copied.is_ok() {
            part1_cold_layout_after_mct_frame(
                reader, main, tile_parts, state, tile, lengths, headers, selected, after, result, rest, tail);
        }
    }
}

pub(crate) proof fn part1_cold_layout_after_copy_frame<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, selected: Part1InheritedTileConfiguration,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_after_inherited_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, events) == Some((result, rest)),
    ensures part1_cold_layout_after_inherited_copy(
        reader, main, tile_parts, state, tile, lengths, headers, selected, events + tail) == Some((result, rest + tail)),
{
    let progression = part1_inherited_tile_owner(tile.2 as usize, main.raw.progression, state.0.5);
    if progression.len() == 0 {
        part1_cold_layout_after_progression_frame(
            reader, main, tile_parts, state, tile, lengths, headers, selected, events, result, rest, tail);
    } else if let Some((copied, after)) = part1_quantization_storage_request(14, progression.len() as usize, events) {
        assert((events + tail).drop_first() =~= events.drop_first() + tail);
        if copied.is_ok() {
            part1_cold_layout_after_progression_frame(
                reader, main, tile_parts, state, tile, lengths, headers, selected, after, result, rest, tail);
        }
    }
}

pub(crate) proof fn part1_cold_layout_inherited_frame<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, tile: (usize, u32, u16, u8, u8),
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_inherited(
        reader, main, tile_parts, state, tile, lengths, headers, events) == Some((result, rest)),
    ensures part1_cold_layout_inherited(
        reader, main, tile_parts, state, tile, lengths, headers, events + tail) == Some((result, rest + tail)),
{
    if let Ok(selected) = part1_select_inherited_tile_configuration(reader.position, tile.2 as usize,
        main.raw.roi, main.coding_style, main.quantization, main.styles,
        (state.0.0, state.0.1, state.0.2, state.0.3, state.3)) {
        let quantizations = part1_inherited_tile_owner(tile.2 as usize, main.quantizations, state.0.4);
        if quantizations.1.len() == 0 {
            part1_cold_layout_after_copy_frame(reader, main, tile_parts, state, tile, lengths, headers,
                selected, events, result, rest, tail);
        } else if let Some((copied, after_copy)) = part1_quantization_storage_request(
            10, quantizations.1.len() as usize, events) {
            assert((events + tail).drop_first() =~= events.drop_first() + tail);
            if copied.is_ok() {
                part1_cold_layout_after_copy_frame(reader, main, tile_parts, state, tile, lengths, headers,
                    selected, after_copy, result, rest, tail);
            }
        }
    }
}

pub(crate) proof fn part1_cold_layout_tile_frame<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u32, Part1PersistentTileState),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_tile_part(reader, main, tile_parts, state, events) == Some((result, rest)),
    ensures part1_cold_layout_tile_part(reader, main, tile_parts, state, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_cold_layout_tile_part);
    if tile_parts < u32::MAX {
        let next = (tile_parts as int + 1) as u32;
        if next <= crate::limits::resource_tile_part_limit(reader.limits) {
            let sot = part1_codestream_read_sot(reader, main.tile_count);
            if let Ok(tile) = sot.0 {
                if let Ok((lengths, headers)) = part1_tile_part_main_metadata(sot.1.position, tile,
                    (next - 1) as u32, main.raw.extensions.lengths, main.raw.plm_seen, main.raw.plm,
                    main.ppm_frames, main.raw.ppm_fragments, main.header) {
                    part1_cold_layout_inherited_frame(sot.1, main, next, state,
                        tile, lengths, headers, events, result, rest, tail);
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_layout_continuation_frame<'a>(
    reader: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>, tile_parts: u32,
    state: Part1PersistentTileState, input_length: usize, events: Seq<Part1ColdStorageEvent>,
    result: Part1CompleteLayoutResult, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_layout_continuation(reader, main, tile_parts, state, input_length, events)
        == Some((result, rest)),
    ensures part1_cold_layout_continuation(reader, main, tile_parts, state, input_length, events + tail)
        == Some((result, rest + tail)),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_cold_layout_continuation, 1);
    if part1_codestream_peek_marker(reader) == Ok(0xff90) {
        if let Some((step, after)) = part1_cold_layout_tile_part(reader, main, tile_parts, state, events) {
            part1_cold_layout_tile_frame(reader, main, tile_parts, state, events, step, after, tail);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_cold_layout_continuation_frame(
                    step.1, main, step.2, step.3, input_length, after, result, rest, tail);
            }
        }
    }
}

pub(crate) proof fn part1_cold_tile_storage_frame_rest(
    count: usize, site: nat, events: Seq<Part1ColdStorageEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires site <= 8, part1_cold_tile_storage(count, site, events) == Some((result, rest)),
    ensures part1_cold_tile_storage(count, site, events + tail) == Some((result, rest + tail)),
    decreases 8 - site,
{
    reveal_with_fuel(part1_cold_tile_storage, 2);
    if site < 8 {
        assert((events + tail).drop_first() =~= events.drop_first() + tail);
        if events[0].succeeded {
            part1_cold_tile_storage_frame_rest(count, site + 1, events.drop_first(), result, rest, tail);
        }
    }
}

pub(crate) proof fn part1_quantized_layout_cold_frame(
    reader: Part1CodestreamReader<'_>, events: Seq<Part1ColdStorageEvent>,
    result: Part1CompleteLayoutResult, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_quantized_layout_cold_run(reader, events) == Some((result, rest)),
    ensures part1_quantized_layout_cold_run(reader, events + tail) == Some((result, rest + tail)),
{
    if let Some((main_result, after_main)) = part1_main_header_cold_run(reader, events) {
        part1_main_header_cold_frame(reader, events, main_result, after_main, tail);
        if let Ok(main) = main_result {
            if main.tile_count <= usize::MAX {
                if let Some((reserved, after_none)) = part1_cold_tile_storage(main.tile_count as usize, 0, after_main) {
                    part1_cold_tile_storage_frame_rest(main.tile_count as usize, 0, after_main, reserved, after_none, tail);
                    if reserved.is_ok() {
                        part1_cold_layout_continuation_frame(main.reader, main, 0,
                            part1_empty_persistent_tile_state(main.tile_count as usize),
                            part1_parse_layout_prologue(reader).1.input.len() as usize, after_none, result, rest, tail);
                    }
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_main_quantization_error(
    reader: Part1CodestreamReader<'_>, input: Part1MainQuantizationInput<'_>, error: crate::DecodeError,
)
    requires part1_prepare_main_quantization(reader) == Ok(input),
        part1_finish_main_quantizations_storage_result(input.raw.image_size.components, input.quantization,
            input.styles, input.raw.qcc, Err(error)),
    ensures part1_cold_layout_result(reader, Err(error)),
{
    reveal(part1_cold_layout_result);
    reveal(part1_finish_main_quantizations);
    let reserved = choose|reserved: bool|
        part1_finish_main_quantizations_storage(input.raw.image_size.components,
            input.quantization, input.styles, input.raw.qcc, reserved) == Err(error);
    let calls = if input.raw.image_size.components == 0 || input.raw.image_size.components > 64 {
        Seq::empty()
    } else {
        seq![Part1ColdStorageEvent {
            site: 8, elements: input.raw.image_size.components as usize, succeeded: reserved }]
    };
    if calls.len() > 0 { assert(calls.drop_first() =~= Seq::<Part1ColdStorageEvent>::empty()); }
    let first = part1_prepare_main_progression_normal(reader);
    assert(part1_prepare_main_progression_run(reader, first + calls) == Some((Ok(input), calls)));
    assert(part1_layout_with_cold_storage(reader, first + calls) == Some((Err(error), Seq::empty())));
}

pub(crate) struct Part1ColdLayoutRoot<'a> {
    pub initial: Part1CodestreamReader<'a>,
    pub main: Part1MainHeader<'a>,
    pub reader: Part1CodestreamReader<'a>,
    pub parts: u32,
    pub state: Part1PersistentTileState,
    pub input_length: usize,
}

pub(crate) open spec fn part1_cold_layout_prefix_at(
    root: Part1ColdLayoutRoot<'_>, prefix: Seq<Part1ColdStorageEvent>,
) -> bool {
    forall|tail: Seq<Part1ColdStorageEvent>|
        #[trigger] part1_quantized_layout_cold_run(root.initial, prefix + tail)
            == part1_cold_layout_continuation(
                root.reader, root.main, root.parts, root.state, root.input_length, tail)
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_layout_prefix(root: Part1ColdLayoutRoot<'_>) -> bool {
    exists|prefix: Seq<Part1ColdStorageEvent>| #[trigger] part1_cold_layout_prefix_at(root, prefix)
}

pub(crate) proof fn part1_cold_layout_start<'a>(
    initial: Part1CodestreamReader<'a>, main: Part1MainHeader<'a>,
)
    requires part1_read_main_header(initial) == Ok(main), main.tile_count <= usize::MAX,
    ensures part1_cold_layout_prefix(Part1ColdLayoutRoot {
        initial, main, reader: main.reader, parts: 0,
        state: part1_empty_persistent_tile_state(main.tile_count as usize),
        input_length: part1_parse_layout_prologue(initial).1.input.len() as usize }),
{
    reveal(part1_cold_layout_prefix);
    let main_calls = part1_main_header_normal_calls(initial);
    let none_calls = part1_cold_storage_trace(main.tile_count as usize, 0, None);
    part1_cold_storage_trace_runs(main.tile_count as usize, 0, None);
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_quantized_layout_cold_run(initial, (main_calls + none_calls) + tail)
            == part1_cold_layout_continuation(main.reader, main, 0,
                part1_empty_persistent_tile_state(main.tile_count as usize),
                part1_parse_layout_prologue(initial).1.input.len() as usize, tail) by {
        assert((main_calls + none_calls) + tail =~= main_calls + (none_calls + tail));
        part1_main_header_cold_normal(initial, none_calls + tail);
        part1_cold_tile_storage_frame(main.tile_count as usize, 0, none_calls, tail, Ok(()));
    }
    assert(part1_cold_layout_prefix_at(Part1ColdLayoutRoot {
        initial, main, reader: main.reader, parts: 0,
        state: part1_empty_persistent_tile_state(main.tile_count as usize),
        input_length: part1_parse_layout_prologue(initial).1.input.len() as usize }, main_calls + none_calls));
}

pub(crate) proof fn part1_cold_layout_error(
    root: Part1ColdLayoutRoot<'_>, calls: Seq<Part1ColdStorageEvent>, error: crate::DecodeError,
)
    requires part1_cold_layout_prefix(root),
        part1_cold_layout_continuation(
            root.reader, root.main, root.parts, root.state, root.input_length, calls)
                == Some((Err(error), Seq::empty())),
    ensures part1_cold_layout_result(root.initial, Err(error)),
{
    reveal(part1_cold_layout_result);
    reveal(part1_cold_layout_prefix);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_cold_layout_prefix_at(root, prefix);
    assert(part1_layout_with_cold_storage(root.initial, prefix + calls)
        == Some((Err(error), Seq::empty())));
}

pub(crate) proof fn part1_cold_layout_advance<'a>(
    root: Part1ColdLayoutRoot<'a>, calls: Seq<Part1ColdStorageEvent>,
    reader: Part1CodestreamReader<'a>, parts: u32, state: Part1PersistentTileState,
)
    requires part1_cold_layout_prefix(root),
        part1_codestream_peek_marker(root.reader) == Ok(0xff90),
        part1_cold_layout_tile_part(root.reader, root.main, root.parts, root.state, calls)
            == Some(((Ok(()), reader, parts, state), Seq::empty())),
        part1_parser_progress(root.reader.position, reader.position, root.input_length),
    ensures part1_cold_layout_prefix(Part1ColdLayoutRoot { reader, parts, state, ..root }),
{
    reveal(part1_cold_layout_prefix);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_cold_layout_prefix_at(root, prefix);
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_quantized_layout_cold_run(root.initial, (prefix + calls) + tail)
            == part1_cold_layout_continuation(reader, root.main, parts, state, root.input_length, tail) by {
        assert((prefix + calls) + tail =~= prefix + (calls + tail));
        part1_cold_layout_tile_frame(root.reader, root.main, root.parts, root.state,
            calls, (Ok(()), reader, parts, state), Seq::empty(), tail);
        reveal_with_fuel(part1_cold_layout_continuation, 1);
        assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
    }
    assert(part1_cold_layout_prefix_at(Part1ColdLayoutRoot { reader, parts, state, ..root }, prefix + calls));
}

pub(crate) proof fn part1_cold_layout_advance_normal<'a>(
    root: Part1ColdLayoutRoot<'a>,
    reader: Part1CodestreamReader<'a>, parts: u32, state: Part1PersistentTileState,
)
    requires part1_cold_layout_prefix(root),
        part1_codestream_peek_marker(root.reader) == Ok(0xff90),
        part1_layout_tile_part(root.reader, root.main, root.parts, root.state) == (Ok(()), reader, parts, state),
        part1_parser_progress(root.reader.position, reader.position, root.input_length),
    ensures part1_cold_layout_prefix(Part1ColdLayoutRoot { reader, parts, state, ..root }),
{
    let calls = part1_cold_layout_tile_normal(root.reader, root.main, root.parts, root.state);
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    part1_cold_layout_advance(root, calls, reader, parts, state);
}

}
