//! Input-derived graph/payload-owner cutpoints in main and tile construction.

use super::*;
use crate::codestream::ResolvedCopyRole;

verus! {

pub(crate) struct Part1MainResolvedInput<'a> {
    pub input: Part1MainQuantizationInput<'a>,
    pub size: Part1ParsedImageSize,
    pub quantizations: (u16, Seq<Part2Quantization>),
    pub mct: Part1MctParameters,
}

pub(crate) open spec fn part1_main_resolved_prepare<'a>(input: Part1MainQuantizationInput<'a>)
    -> Result<Part1MainResolvedInput<'a>, crate::DecodeError> {
    match part1_finish_main_quantizations(input.raw.image_size.components,
        input.quantization, input.styles, input.raw.qcc) {
        Err(error) => Err(error),
        Ok(quantizations) => {
            let styles = crate::codestream::tile_part_native_styles(input.styles);
            match part1_validate_progression_changes(0, input.raw.progression, input.style.layers, &styles, input.reader.limits) {
                Err(error) => Err(error),
                Ok(()) => if (input.raw.arrays.len() != 0 || input.raw.records.len() != 0) && input.raw.order.is_none() {
                    Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure))
                } else {
                    let registered = part1_apply_component_registrations(
                        input.raw.image_size, input.raw.extensions.registrations, input.reader.position);
                    match registered.0 {
                        Err(error) => Err(error),
                        Ok(()) => Ok(Part1MainResolvedInput {
                            input, size: registered.1, quantizations,
                            mct: Part1MctParameters { arrays: input.raw.arrays, records: input.raw.records,
                                order: match input.raw.order { None => Seq::empty(), Some(order) => order } },
                        }),
                    }
                },
            }
        },
    }
}

pub(crate) open spec fn part1_main_resolved_finish<'a>(
    ctx: Part1MainResolvedInput<'a>, transform: Option<Seq<Part2MctStage>>,
) -> Part1MainHeaderResult<'a> {
    match part2_selection_tile_count(ctx.size.geometry) {
        Err(error) => Err(error),
        Ok(tile_count) => Ok(Part1MainHeader {
            reader: ctx.input.reader, raw: Part1MainHeaderAccumulator { image_size: ctx.size, ..ctx.input.raw },
            end: ctx.input.reader.position, header: ctx.input.header, ppm_frames: ctx.input.frames,
            coding_style: ctx.input.style, quantization: ctx.input.quantization, styles: ctx.input.styles,
            quantizations: ctx.quantizations, mct: ctx.mct, transform, tile_count,
        }),
    }
}

pub(crate) open spec fn part1_main_bitmap_run(input: Part1MainQuantizationInput<'_>, events: Seq<Part1ColdStorageEvent>)
    -> Option<(Result<(), crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_finish_main_quantizations(input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc) {
        Err(error) => Some((Err(error), events)),
        Ok(_) => part1_bitmap_run(0, input.raw.progression, input.style.layers,
            &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, events),
    }
}
pub(crate) open spec fn part1_main_bitmap_calls(input: Part1MainQuantizationInput<'_>) -> Seq<Part1ColdStorageEvent> {
    if part1_finish_main_quantizations(input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc).is_err() { Seq::empty() }
    else { part1_bitmap_calls(0, input.raw.progression, input.style.layers,
        &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits) }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_resolved_run<'a>(
    input: Part1MainQuantizationInput<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1MainHeaderResult<'a>, Seq<Part1ColdStorageEvent>)> {
    match part1_main_bitmap_run(input, events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => match part1_main_resolved_prepare(input) {
        Err(error) => Some((Err(error), rest)),
        Ok(ctx) => match part1_resolved_graph_run(ResolvedCopyRole::Main, ctx.mct, rest) {
            None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
            Some((Ok(transform), rest)) => Some((part1_main_resolved_finish(ctx, transform), rest)),
        },
        },
    }
}

pub(crate) open spec fn part1_main_resolved_calls(prepared: Part1MainQuantizationPreparation<'_>)
    -> Seq<Part1ColdStorageEvent> {
    match prepared {
        Err(_) => Seq::empty(),
        Ok(input) => part1_main_bitmap_calls(input) + match part1_main_resolved_prepare(input) {
            Err(_) => Seq::empty(),
            Ok(ctx) => part1_mct_copy_normal_calls(part1_resolved_graph_requests(ResolvedCopyRole::Main, ctx.mct)),
        },
    }
}

pub(crate) proof fn part1_main_resolved_normal<'a>(
    input: Part1MainQuantizationInput<'a>, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_main_resolved_run(input, part1_main_resolved_calls(Ok(input)) + tail)
        == Some((part1_main_quantization_reserved(input), tail)),
{
    reveal(part1_main_resolved_run);
    reveal(part1_main_header_after_components);
    let graph = match part1_main_resolved_prepare(input) { Err(_) => Seq::empty(),
        Ok(ctx) => part1_mct_copy_normal_calls(part1_resolved_graph_requests(ResolvedCopyRole::Main, ctx.mct)) };
    if part1_finish_main_quantizations(input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc).is_ok() {
        part1_bitmap_normal(0, input.raw.progression, input.style.layers, &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, graph + tail);
    }
    assert((part1_main_bitmap_calls(input) + graph) + tail =~= part1_main_bitmap_calls(input) + (graph + tail));
    if let Ok(ctx) = part1_main_resolved_prepare(input) {
        part1_resolved_graph_normal(ResolvedCopyRole::Main, ctx.mct, tail);
    }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}

pub(crate) proof fn part1_main_resolved_frame<'a>(
    input: Part1MainQuantizationInput<'a>, events: Seq<Part1ColdStorageEvent>,
    result: Part1MainHeaderResult<'a>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_resolved_run(input, events) == Some((result, rest)),
    ensures part1_main_resolved_run(input, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_main_resolved_run);
    if part1_finish_main_quantizations(input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc).is_ok() {
        if let Some((bitmap, after_bitmap)) = part1_main_bitmap_run(input, events) {
            part1_bitmap_frame(0, input.raw.progression, input.style.layers, &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, events, bitmap, after_bitmap, tail);
            if bitmap.is_ok() { if let Ok(ctx) = part1_main_resolved_prepare(input) {
        if let Some((graph, after)) = part1_resolved_graph_run(ResolvedCopyRole::Main, ctx.mct, after_bitmap) {
            part1_resolved_graph_frame(ResolvedCopyRole::Main, ctx.mct, after_bitmap, graph, after, tail);
        }
            }}
        }
    }
}

pub(crate) proof fn part1_main_resolved_projection<'a>(
    input: Part1MainQuantizationInput<'a>, events: Seq<Part1ColdStorageEvent>,
    result: Part1MainHeaderResult<'a>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_resolved_run(input, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_main_quantization_reserved(input),
{
    reveal(part1_main_resolved_run);
    reveal(part1_main_header_after_components);
    if part1_finish_main_quantizations(input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc).is_ok() {
        if let Some((bitmap, after_bitmap)) = part1_main_bitmap_run(input, events) {
            part1_bitmap_projection(0, input.raw.progression, input.style.layers, &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, events, bitmap, after_bitmap);
            if bitmap.is_ok() { if let Ok(ctx) = part1_main_resolved_prepare(input) {
        if let Some((graph, after)) = part1_resolved_graph_run(ResolvedCopyRole::Main, ctx.mct, after_bitmap) {
            part1_resolved_graph_projection(ResolvedCopyRole::Main, ctx.mct, after_bitmap, graph, after);
        }
            }}
        }
    }
}

pub(crate) proof fn part1_main_resolved_error<'a>(
    initial: Part1CodestreamReader<'a>, input: Part1MainQuantizationInput<'a>,
    ctx: Part1MainResolvedInput<'a>, error: crate::DecodeError,
)
    requires part1_prepare_main_quantization(initial) == Ok(input),
        part1_main_resolved_prepare(input) == Ok(ctx),
        part1_resolved_graph_result(ResolvedCopyRole::Main, ctx.mct, Err(error)),
    ensures part1_cold_layout_result(initial, Err(error)),
{
    reveal(part1_main_resolved_run);
    reveal(part1_resolved_graph_result);
    let graph_calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_resolved_graph_run(ResolvedCopyRole::Main, ctx.mct, calls) == Some((Err(error), Seq::empty()));
    let bitmap = part1_main_bitmap_calls(input);
    part1_bitmap_normal(0, input.raw.progression, input.style.layers, &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, graph_calls);
    let storage = part1_main_quantization_normal_calls(Ok(input));
    let before = part1_prepare_main_progression_normal(initial);
    let last = bitmap + graph_calls;
    let calls = before + storage + last;
    assert(calls =~= before + (storage + last));
    assert(part1_prepare_main_progression_run(initial, calls) == Some((Ok(input), storage + last)));
    if storage.len() > 0 { assert((storage + last).drop_first() =~= last); }
    else { assert(storage + last =~= last); }
    reveal(part1_cold_layout_result);
    assert(part1_layout_with_cold_storage(initial, calls) == Some((Err(error), Seq::empty())));
}

pub(crate) open spec fn part1_tile_payload_copy_requests(raw: Part1TileHeaderAccumulator) -> Seq<Part1MctCopyRequest> {
    part1_part2_role_requests(true, part1_part2_copy_requests(raw.part2_extensions))
}

pub(crate) open spec fn part1_tile_after_window_run<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, transform: Option<Seq<Part2MctStage>>,
    end: usize, data: Seq<u8>, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Part1TilePartResult, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    let normal = part1_tile_part_after_window(reader, raw, tile, configuration, transform, end, data, lengths, headers);
    if normal.0.is_err() { Some((normal, events)) } else {
        match part1_mct_copy_run(part1_tile_payload_copy_requests(raw), events) {
            None => None, Some((Err(error), rest)) => Some(((Err(error), normal.1), rest)),
            Some((Ok(()), rest)) => Some((normal, rest)),
        }
    }
}

pub(crate) proof fn part1_tile_after_window_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, transform: Option<Seq<Part2MctStage>>,
    end: usize, data: Seq<u8>, lengths: Part1PacketLengths, headers: Part1PackedHeaders, tail: Seq<Part1ColdStorageEvent>,
)
    ensures ({
        let normal = part1_tile_part_after_window(reader, raw, tile, configuration, transform, end, data, lengths, headers);
        let calls = if normal.0.is_ok() { part1_mct_copy_normal_calls(part1_tile_payload_copy_requests(raw)) } else { Seq::empty() };
        part1_tile_after_window_run(reader, raw, tile, configuration, transform, end, data, lengths, headers, calls + tail)
            == Some((normal, tail))
    }),
{
    if part1_tile_part_after_window(reader, raw, tile, configuration, transform, end, data, lengths, headers).0.is_ok() {
        part1_mct_copy_normal(part1_tile_payload_copy_requests(raw), tail);
    } else { assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail); }
}

pub(crate) proof fn part1_tile_after_window_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, transform: Option<Seq<Part2MctStage>>,
    end: usize, data: Seq<u8>, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>, result: (Part1TilePartResult, Part1CodestreamReader<'a>),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_after_window_run(reader, raw, tile, configuration, transform, end, data, lengths, headers, events) == Some((result, rest)),
    ensures part1_tile_after_window_run(reader, raw, tile, configuration, transform, end, data, lengths, headers, events + tail) == Some((result, rest + tail)),
{
    let normal = part1_tile_part_after_window(reader, raw, tile, configuration, transform, end, data, lengths, headers);
    if normal.0.is_ok() {
        if let Some((copied, after)) = part1_mct_copy_run(part1_tile_payload_copy_requests(raw), events) {
            part1_mct_copy_frame(part1_tile_payload_copy_requests(raw), events, copied, after, tail);
        }
    }
}

pub(crate) proof fn part1_tile_after_window_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, transform: Option<Seq<Part2MctStage>>,
    end: usize, data: Seq<u8>, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>, result: (Part1TilePartResult, Part1CodestreamReader<'a>), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_after_window_run(reader, raw, tile, configuration, transform, end, data, lengths, headers, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_part_after_window(reader, raw, tile, configuration, transform, end, data, lengths, headers),
{
    let normal = part1_tile_part_after_window(reader, raw, tile, configuration, transform, end, data, lengths, headers);
    if normal.0.is_ok() {
        if let Some((copied, after)) = part1_mct_copy_run(part1_tile_payload_copy_requests(raw), events) {
            part1_mct_copy_projection(part1_tile_payload_copy_requests(raw), events, copied, after);
        }
    }
}

pub(crate) open spec fn part1_tile_after_configuration_run<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Part1TilePartResult, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    match part1_bitmap_run(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, events) {
        None => None, Some((Err(error), rest)) => Some(((Err(error), reader), rest)),
        Some((Ok(()), rest)) => part1_tile_after_bitmap_run(reader, raw, tile, configuration, lengths, headers, rest),
    }
}
pub(crate) open spec fn part1_tile_after_bitmap_run<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Part1TilePartResult, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    match part1_resolved_graph_run(ResolvedCopyRole::Tile, raw.mct_parameters, events) {
            None => None, Some((Err(error), rest)) => Some(((Err(error), reader), rest)),
            Some((Ok(transform), rest)) => {
                let window = part1_tile_data_window(reader, reader.position, tile.0, tile.1);
                match window.0 {
                    Err(error) => Some(((Err(error), window.1), rest)),
                    Ok((end, data)) => part1_tile_after_window_run(window.1, raw, tile, configuration,
                        transform, end, data, lengths, headers, rest),
                }
            },
    }
}

pub(crate) open spec fn part1_tile_after_configuration_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
) -> Seq<Part1ColdStorageEvent> {
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    part1_bitmap_calls(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits) +
    if part1_validate_progression_changes(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits).is_err() {
        Seq::empty()
    } else {
        part1_mct_copy_normal_calls(part1_resolved_graph_requests(ResolvedCopyRole::Tile, raw.mct_parameters))
            + if part1_tile_part_after_configuration(reader, raw, tile, configuration, lengths, headers).0.is_ok() {
                part1_mct_copy_normal_calls(part1_tile_payload_copy_requests(raw))
            } else { Seq::empty() }
    }
}

pub(crate) proof fn part1_tile_after_configuration_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_tile_after_configuration_run(reader, raw, tile, configuration, lengths, headers,
        part1_tile_after_configuration_calls(reader, raw, tile, configuration, lengths, headers) + tail)
            == Some((part1_tile_part_after_configuration(reader, raw, tile, configuration, lengths, headers), tail)),
{
    reveal(part1_tile_part_after_configuration);
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    let bitmap = part1_bitmap_calls(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits);
    let later = if part1_validate_progression_changes(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits).is_ok() {
        part1_mct_copy_normal_calls(part1_resolved_graph_requests(ResolvedCopyRole::Tile, raw.mct_parameters)) +
        if part1_tile_part_after_configuration(reader, raw, tile, configuration, lengths, headers).0.is_ok() {
            part1_mct_copy_normal_calls(part1_tile_payload_copy_requests(raw))
        } else { Seq::empty() }
    } else { Seq::empty() };
    part1_bitmap_normal(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, later + tail);
    assert((bitmap + later) + tail =~= bitmap + (later + tail));
    if part1_validate_progression_changes(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits).is_ok() {
        let last = if part1_tile_part_after_configuration(reader, raw, tile, configuration, lengths, headers).0.is_ok() {
            part1_mct_copy_normal_calls(part1_tile_payload_copy_requests(raw))
        } else { Seq::empty() };
        let first = part1_mct_copy_normal_calls(part1_resolved_graph_requests(ResolvedCopyRole::Tile, raw.mct_parameters));
        assert((first + last) + tail =~= first + (last + tail));
        part1_resolved_graph_normal(ResolvedCopyRole::Tile, raw.mct_parameters, last + tail);
        if let Ok(transform) = part1_mct_graph(raw.mct_parameters) {
            let window = part1_tile_data_window(reader, reader.position, tile.0, tile.1);
            if let Ok((end, data)) = window.0 {
                part1_tile_after_window_normal(window.1, raw, tile, configuration, transform, end, data, lengths, headers, tail);
            }
        }
    }
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
}

pub(crate) proof fn part1_tile_after_configuration_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>, result: (Part1TilePartResult, Part1CodestreamReader<'a>),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_after_configuration_run(reader, raw, tile, configuration, lengths, headers, events) == Some((result, rest)),
    ensures part1_tile_after_configuration_run(reader, raw, tile, configuration, lengths, headers, events + tail) == Some((result, rest + tail)),
{
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    if let Some((bitmap, after_bitmap)) = part1_bitmap_run(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, events) {
        part1_bitmap_frame(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, events, bitmap, after_bitmap, tail);
        if bitmap.is_ok() {
        if let Some((graph, after)) = part1_resolved_graph_run(ResolvedCopyRole::Tile, raw.mct_parameters, after_bitmap) {
            part1_resolved_graph_frame(ResolvedCopyRole::Tile, raw.mct_parameters, after_bitmap, graph, after, tail);
            if let Ok(transform) = graph {
                let window = part1_tile_data_window(reader, reader.position, tile.0, tile.1);
                if let Ok((end, data)) = window.0 {
                    part1_tile_after_window_frame(window.1, raw, tile, configuration, transform, end, data,
                        lengths, headers, after, result, rest, tail);
                }
                }
            }
        }
    }
}

pub(crate) proof fn part1_tile_after_configuration_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, tile: (usize, u32, u16, u8, u8),
    configuration: Part1TileComponentConfiguration, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    events: Seq<Part1ColdStorageEvent>, result: (Part1TilePartResult, Part1CodestreamReader<'a>),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_after_configuration_run(reader, raw, tile, configuration, lengths, headers, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_part_after_configuration(reader, raw, tile, configuration, lengths, headers),
{
    reveal(part1_tile_part_after_configuration);
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    if let Some((bitmap, after_bitmap)) = part1_bitmap_run(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, events) {
        part1_bitmap_projection(tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, events, bitmap, after_bitmap);
        if bitmap.is_ok() {
        if let Some((graph, after)) = part1_resolved_graph_run(ResolvedCopyRole::Tile, raw.mct_parameters, after_bitmap) {
            part1_resolved_graph_projection(ResolvedCopyRole::Tile, raw.mct_parameters, after_bitmap, graph, after);
            if let Ok(transform) = graph {
                let window = part1_tile_data_window(reader, reader.position, tile.0, tile.1);
                if let Ok((end, data)) = window.0 {
                    part1_tile_after_window_projection(window.1, raw, tile, configuration, transform, end, data,
                        lengths, headers, after, result, rest);
                }
                }
            }
        }
    }
}

pub(crate) open spec fn part1_tile_graph_prepare(
    input: Part1ColdTileInput<'_>, raw: Part1TileHeaderAccumulator, reader: Part1CodestreamReader<'_>,
) -> Result<Part1TileComponentConfiguration, crate::DecodeError> {
    match part1_finish_tile_components(input.components, raw.tile_coding_style, raw.tile_cod_seen,
        raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments, input.styles,
        input.quantizations, raw.part2_extensions, reader.limits) {
        Err(error) => Err(error),
        Ok(configuration) => {
            let styles = crate::codestream::tile_part_native_styles(configuration.0);
            match part1_validate_progression_changes(input.tile.0, raw.progression_changes,
                raw.tile_coding_style.layers, &styles, reader.limits) {
                Err(error) => Err(error), Ok(()) => Ok(configuration),
            }
        },
    }
}

pub(crate) proof fn part1_cold_tile_graph_error<'a>(
    input: Part1ColdTileInput<'a>, raw: Part1TileHeaderAccumulator, reader: Part1CodestreamReader<'a>, error: crate::DecodeError,
)
    requires part1_cold_tile_header(input) == (Ok(raw), reader),
        raw.pending_mct.len() == 0, raw.pending_mcc.len() == 0,
        part1_tile_graph_prepare(input, raw, reader).is_ok(),
        part1_resolved_graph_result(ResolvedCopyRole::Tile, raw.mct_parameters, Err(error)),
    ensures part1_cold_tile_part_result(input, (Err(error), reader)),
{
    reveal(part1_resolved_graph_result); reveal(part1_cold_tile_part_result);
    let graph_calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_resolved_graph_run(ResolvedCopyRole::Tile, raw.mct_parameters, calls) == Some((Err(error), Seq::empty()));
    let header_calls = part1_read_tile_progression_normal(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers);
    part1_tile_components_cold_normal(input.components, raw.tile_coding_style, raw.tile_cod_seen, raw.coc_segments,
        raw.qcd_segment, input.defaults.1, raw.qcc_segments, input.styles, input.quantizations, raw.part2_extensions, reader.limits);
    let components = part1_cold_tile_configuration_calls(input);
    let configuration = part1_tile_graph_prepare(input, raw, reader)->Ok_0;
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    let bitmap = part1_bitmap_calls(input.tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits);
    part1_bitmap_normal(input.tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, reader.limits, graph_calls);
    let calls = header_calls + components + bitmap + graph_calls;
    assert(calls =~= header_calls + (components + (bitmap + graph_calls)));
    assert(part1_cold_tile_part_run(input, calls) == Some(((Err(error), reader), Seq::empty())));
}

pub(crate) proof fn part1_cold_tile_payload_error<'a>(
    input: Part1ColdTileInput<'a>, raw: Part1TileHeaderAccumulator, reader: Part1CodestreamReader<'a>, error: crate::DecodeError,
)
    requires part1_cold_tile_header(input).0 == Ok(raw),
        part1_cold_tile_normal(input).0.is_ok(), part1_cold_tile_normal(input).1 == reader,
        part1_mct_copy_result(part1_tile_payload_copy_requests(raw), Err(error)),
    ensures part1_cold_tile_part_result(input, (Err(error), reader)),
{
    reveal(part1_mct_copy_result); reveal(part1_cold_tile_part_result);
    let header = part1_cold_tile_header(input);
    assert(raw.pending_mct.len() == 0 && raw.pending_mcc.len() == 0
        && part1_tile_graph_prepare(input, raw, header.1).is_ok()
        && part1_mct_graph(raw.mct_parameters).is_ok()
        && part1_cold_tile_normal(input) == part1_tile_part_after_configuration(
            header.1, raw, input.tile, part1_tile_graph_prepare(input, raw, header.1)->Ok_0,
            input.lengths, input.headers)) by {
        reveal(part1_cold_tile_normal); reveal(part1_read_tile_part); reveal(part1_finish_tile_part);
        reveal(part1_tile_part_after_configuration);
    }
    let payload_calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_tile_payload_copy_requests(raw), calls)
        == Some((Err(error), Seq::empty()));
    let before_header = part1_read_tile_progression_normal(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers);
    let components = part1_cold_tile_configuration_calls(input);
    part1_tile_components_cold_normal(input.components, raw.tile_coding_style, raw.tile_cod_seen, raw.coc_segments,
        raw.qcd_segment, input.defaults.1, raw.qcc_segments, input.styles, input.quantizations, raw.part2_extensions, header.1.limits);
    let graph = part1_mct_copy_normal_calls(part1_resolved_graph_requests(ResolvedCopyRole::Tile, raw.mct_parameters));
    part1_resolved_graph_normal(ResolvedCopyRole::Tile, raw.mct_parameters, payload_calls);
    let configuration = part1_tile_graph_prepare(input, raw, header.1)->Ok_0;
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    let bitmap = part1_bitmap_calls(input.tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, header.1.limits);
    part1_bitmap_normal(input.tile.0, raw.progression_changes, raw.tile_coding_style.layers, &styles, header.1.limits, graph + payload_calls);
    let calls = before_header + components + bitmap + graph + payload_calls;
    assert(calls =~= before_header + (components + (bitmap + (graph + payload_calls))));
    assert(part1_cold_tile_part_run(input, calls) == Some(((Err(error), reader), Seq::empty()))) by {
        reveal(part1_tile_part_after_configuration);
    }
}

}
