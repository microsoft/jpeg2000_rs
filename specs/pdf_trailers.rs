//! Explicit completion-stage trailer admission after actual packet execution.
use super::*;
verus! {
pub(crate) type Part2TrailerPacketOutput = (
    Result<(crate::packet::TilePacketDecode, u8), crate::DecodeError>,
    Seq<Part1PacketPrecinctState>,
);

pub(crate) open spec fn part2_trailer_packet_finish(
    params: Part1TilePacketParameters,
    decoded: (Result<(), crate::DecodeError>, Part1TilePacketExecution), discarded: u8,
) -> Part2TrailerPacketOutput {
    (match decoded.0 {
        Err(error) => Err(error),
        Ok(()) => part2_tile_trailer_finish(params, decoded.1.progress, discarded).0,
    }, decoded.1.precincts)
}

pub(crate) open spec fn part2_trailer_packet_after_progress_run(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    input: Part1TilePacketPreparation, progress: Part1TilePacketProgress,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerPacketOutput> {
    let params = part2_packet_parameters(parts, grid, input, selection, limits);
    part2_jpip_snapshot_bind(
        part2_tile_plane_calls_run(params, Part1TilePacketExecution { progress, precincts }, events),
        |decoded: (Result<(), crate::DecodeError>, Part1TilePacketExecution), rest|
            Some((Ok(part2_trailer_packet_finish(params, decoded, discarded)), rest)))
}

pub(crate) open spec fn part2_trailer_packet_run(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerPacketOutput> {
    match part2_packet_input_run(parts, grid, precincts, selection, limits, events) {
        None => None,
        Some((Err(error), rest)) => Some((Ok((Err(error), precincts)), rest)),
        Some((Ok(input), rest)) => match part2_progress_initial_run(
            part2_packet_parameters(parts, grid, input, selection, limits), rest) {
            None => None,
            Some((Err(error), tail)) => Some((Ok((Err(error), precincts)), tail)),
            Some((Ok(progress), tail)) => part2_trailer_packet_after_progress_run(
                parts, grid, precincts, selection, limits, discarded, input, progress, tail),
        },
    }
}

pub(crate) open spec fn part2_trailer_packet_result(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    result: Part2TrailerPacketOutput,
) -> bool {
    part2_cold_framed(
        |events| part2_trailer_packet_run(parts, grid, precincts, selection, limits, discarded, events),
        Ok(result))
}

pub(crate) open spec fn part2_trailer_packet_value(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
) -> Part2TrailerPacketOutput {
    match part1_progression_tile_input_owned(parts, grid, precincts, selection, limits) {
        Err(error) => (Err(error), precincts),
        Ok(input) => {
            let params = part2_packet_parameters(parts, grid, input, selection, limits);
            match part1_tile_progress_initial(params) {
                Err(error) => (Err(error), precincts),
                Ok(progress) => part2_trailer_packet_finish(
                    params, part1_tile_run(params, Part1TilePacketExecution { progress, precincts }), discarded),
            }
        },
    }
}

pub(crate) proof fn part2_trailer_packet_input_error(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8, error: crate::DecodeError,
)
    requires part2_packet_input_result(parts, grid, precincts, selection, limits, Err(error)),
    ensures part2_trailer_packet_result(parts, grid, precincts, selection, limits, discarded, (Err(error), precincts)),
{
    reveal(part2_packet_input_result);
    let before = |events| part2_packet_input_run(parts, grid, precincts, selection, limits, events);
    let prefix = part2_cold_witness(before, Err(error));
    let root = |events| part2_trailer_packet_run(parts, grid, precincts, selection, limits, discarded, events);
    assert forall|tail| root(prefix + tail) == Some((Ok((Err(error), precincts)), tail)) by {
        part2_cold_prefix_at(before, prefix, Err(error), tail);
    }
    assert(part2_cold_prefix(root, prefix, Ok((Err(error), precincts))));
    part2_decode_eta(root, Ok((Err(error), precincts)));
}

pub(crate) proof fn part2_trailer_packet_progress_error(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    input: Part1TilePacketPreparation, error: crate::DecodeError,
)
    requires part2_packet_input_result(parts, grid, precincts, selection, limits, Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts, grid, input, selection, limits), Err(error)),
    ensures part2_trailer_packet_result(parts, grid, precincts, selection, limits, discarded, (Err(error), precincts)),
{
    reveal(part2_packet_input_result); reveal(part2_progress_initial_result);
    let before = |events| part2_packet_input_run(parts, grid, precincts, selection, limits, events);
    let after = |events| part2_progress_initial_run(part2_packet_parameters(parts, grid, input, selection, limits), events);
    let first = part2_cold_witness(before, Ok(input));
    let second = part2_cold_witness(after, Err(error));
    let prefix = first + second;
    let root = |events| part2_trailer_packet_run(parts, grid, precincts, selection, limits, discarded, events);
    assert forall|tail| root(prefix + tail) == Some((Ok((Err(error), precincts)), tail)) by {
        assert(prefix + tail =~= first + (second + tail));
        part2_cold_prefix_at(before, first, Ok(input), second + tail);
        part2_cold_prefix_at(after, second, Err(error), tail);
    }
    assert(part2_cold_prefix(root, prefix, Ok((Err(error), precincts))));
    part2_decode_eta(root, Ok((Err(error), precincts)));
}

pub(crate) proof fn part2_trailer_packet_actual(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    input: Part1TilePacketPreparation, progress: Part1TilePacketProgress,
    decoded: (Result<(), crate::DecodeError>, Part1TilePacketExecution),
)
    requires part2_packet_input_result(parts, grid, precincts, selection, limits, Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts, grid, input, selection, limits), Ok(progress)),
        part2_plane_tile_run_result(part2_packet_parameters(parts, grid, input, selection, limits),
            Part1TilePacketExecution { progress, precincts }, decoded),
    ensures part2_trailer_packet_result(parts, grid, precincts, selection, limits, discarded,
        part2_trailer_packet_finish(part2_packet_parameters(parts, grid, input, selection, limits), decoded, discarded)),
{
    reveal(part2_packet_input_result); reveal(part2_progress_initial_result);
    let params = part2_packet_parameters(parts, grid, input, selection, limits);
    let initial = Part1TilePacketExecution { progress, precincts };
    let before = |events| part2_packet_input_run(parts, grid, precincts, selection, limits, events);
    let after = |events| part2_progress_initial_run(params, events);
    let child = |events| part2_tile_plane_calls_run(params, initial, events);
    let first = part2_cold_witness(before, Ok(input));
    let second = part2_cold_witness(after, Ok(progress));
    part2_tile_plane_calls_observed(params, initial, decoded);
    let third = part2_cold_witness(child, Ok(decoded));
    let prefix = (first + second) + third;
    let output = part2_trailer_packet_finish(params, decoded, discarded);
    let root = |events| part2_trailer_packet_run(parts, grid, precincts, selection, limits, discarded, events);
    assert forall|tail| root(prefix + tail) == Some((Ok(output), tail)) by {
        assert(prefix + tail =~= first + (second + (third + tail)));
        part2_cold_prefix_at(before, first, Ok(input), second + (third + tail));
        part2_cold_prefix_at(after, second, Ok(progress), third + tail);
        part2_cold_prefix_at(child, third, Ok(decoded), tail);
    }
    assert(part2_cold_prefix(root, prefix, Ok(output)));
    part2_decode_eta(root, Ok(output));
}

pub(crate) proof fn part2_trailer_packet_normal(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
)
    ensures part2_trailer_packet_result(parts, grid, precincts, selection, limits, discarded,
        part2_trailer_packet_value(parts, grid, precincts, selection, limits, discarded)),
{
    part2_packet_input_normal(parts, grid, precincts, selection, limits);
    match part1_progression_tile_input_owned(parts, grid, precincts, selection, limits) {
        Err(error) => part2_trailer_packet_input_error(parts, grid, precincts, selection, limits, discarded, error),
        Ok(input) => {
            let params = part2_packet_parameters(parts, grid, input, selection, limits);
            part2_progress_initial_normal(params);
            match part1_tile_progress_initial(params) {
                Err(error) => part2_trailer_packet_progress_error(parts, grid, precincts, selection, limits, discarded, input, error),
                Ok(progress) => {
                    let initial = Part1TilePacketExecution { progress, precincts };
                    part2_plane_tile_run_normal(params, initial);
                    part2_trailer_packet_actual(parts, grid, precincts, selection, limits, discarded,
                        input, progress, part1_tile_run(params, initial));
                },
            }
        },
    }
}

pub(crate) open spec fn part2_trailer_packet_projection(
    result: Part2TrailerPacketOutput,
) -> Result<((crate::packet::TilePacketDecode, u8), Seq<Part1PacketPrecinctState>), crate::DecodeError> {
    match result.0 { Err(error) => Err(error), Ok(decoded) => Ok((decoded, result.1)) }
}

pub(crate) open spec fn part2_trailer_packet_value_run(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<((crate::packet::TilePacketDecode, u8), Seq<Part1PacketPrecinctState>)> {
    match part2_trailer_packet_run(parts, grid, precincts, selection, limits, discarded, events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(result), rest)) => Some((part2_trailer_packet_projection(result), rest)),
    }
}

pub(crate) proof fn part2_trailer_packet_value_actual(
    parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, precincts: Seq<Part1PacketPrecinctState>,
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, discarded: u8,
    result: Part2TrailerPacketOutput,
)
    requires part2_trailer_packet_result(parts, grid, precincts, selection, limits, discarded, result),
    ensures part2_cold_framed(
        |events| part2_trailer_packet_value_run(parts, grid, precincts, selection, limits, discarded, events),
        part2_trailer_packet_projection(result)),
{
    let before = |events| part2_trailer_packet_run(parts, grid, precincts, selection, limits, discarded, events);
    let prefix = part2_cold_witness(before, Ok(result));
    let root = |events| part2_trailer_packet_value_run(parts, grid, precincts, selection, limits, discarded, events);
    assert forall|tail| root(prefix + tail) == Some((part2_trailer_packet_projection(result), tail)) by {
        part2_cold_prefix_at(before, prefix, Ok(result), tail);
    }
    assert(part2_cold_prefix(root, prefix, part2_trailer_packet_projection(result)));
}

pub(crate) open spec fn part2_trailer_extract_output(
    effect: Part2ExtractionTileEffect, discarded: u8,
) -> Result<(Part2DecodedTileComponents, u8), crate::DecodeError> {
    match effect.0 {
        Err(error) => Err(error),
        Ok(()) => Ok((Part2DecodedTileComponents { prepared: effect.1, mct_work: effect.2 }, discarded)),
    }
}

pub(crate) open spec fn part2_trailer_extract_run(
    plan: Part2ProgressionTilePlan, first: Part2OwnedTilePart, size: &crate::codestream::ImageSize,
    standard: (bool, bool), limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>,
    work: u64, precincts: Seq<Part1PacketPrecinctState>, discarded: u8,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodedTileComponents, u8)> {
    part2_jpip_snapshot_bind(
        part2_extraction_tile_calls_run(prepared, plan.components, part2_precinct_decoder_planes(precincts),
            first.component_coding_styles, part2_owned_kernel_registry(first.part2_extensions),
            crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
            first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits), events),
        |effect: Part2ExtractionTileEffect, rest| Some((part2_trailer_extract_output(effect, discarded), rest)))
}

pub(crate) proof fn part2_trailer_extract_actual(
    plan: Part2ProgressionTilePlan, first: Part2OwnedTilePart, size: &crate::codestream::ImageSize,
    standard: (bool, bool), limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>,
    work: u64, precincts: Seq<Part1PacketPrecinctState>, discarded: u8, effect: Part2ExtractionTileEffect,
)
    requires part2_extraction_tile_result(prepared, plan.components, part2_precinct_decoder_planes(precincts),
        first.component_coding_styles, part2_owned_kernel_registry(first.part2_extensions),
        crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
        crate::limits::resource_decoded_bytes_limit(limits), effect),
    ensures part2_cold_framed(
        |events| part2_trailer_extract_run(plan, first, size, standard, limits, prepared, work, precincts, discarded, events),
        part2_trailer_extract_output(effect, discarded)),
{
    let planes = part2_precinct_decoder_planes(precincts);
    let kernels = part2_owned_kernel_registry(first.part2_extensions);
    part2_extraction_tile_calls_observed(prepared, plan.components, planes, first.component_coding_styles, kernels,
        crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
        first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
        crate::limits::resource_decoded_bytes_limit(limits), effect);
    part2_cold_pure(part2_trailer_extract_output(effect, discarded));
    part2_cold_bind(
        |events| part2_extraction_tile_calls_run(prepared, plan.components, planes, first.component_coding_styles, kernels,
            crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
            first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits), events),
        |value: Part2ExtractionTileEffect, rest| Some((part2_trailer_extract_output(value, discarded), rest)),
        Ok(effect), part2_trailer_extract_output(effect, discarded));
}

pub(crate) open spec fn part2_trailer_planned_run(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool), counts: Seq<u8>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, discarded: u8,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodedTileComponents, u8)> {
    part2_jpip_snapshot_bind(
        part2_trailer_packet_value_run(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, events),
        |decoded: ((crate::packet::TilePacketDecode, u8), Seq<Part1PacketPrecinctState>), rest|
            part2_trailer_extract_run(plan, first, size, standard, limits, prepared, work, decoded.1, decoded.0.1, rest))
}

pub(crate) open spec fn part2_trailer_planned_result(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool), counts: Seq<u8>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, discarded: u8,
    result: Result<(Part2DecodedTileComponents, u8), crate::DecodeError>,
) -> bool {
    part2_cold_framed(
        |events| part2_trailer_planned_run(plan, parts, first, size, standard, counts, limits, prepared, work, discarded, events),
        result)
}

pub(crate) open spec fn part2_trailer_planned_value(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool), counts: Seq<u8>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, discarded: u8,
) -> Result<(Part2DecodedTileComponents, u8), crate::DecodeError> {
    let decoded = part2_trailer_packet_value(parts, plan.grid, plan.precincts, Some(counts), limits, discarded);
    match decoded.0 {
        Err(error) => Err(error),
        Ok((_, discarded)) => part2_trailer_extract_output(
            part2_reconstruct_planned_tile(prepared, plan.components, part2_precinct_decoder_planes(decoded.1),
                first.component_coding_styles, part2_owned_kernel_registry(first.part2_extensions),
                crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
                first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
                crate::limits::resource_decoded_bytes_limit(limits)), discarded),
    }
}

pub(crate) proof fn part2_trailer_planned_packet_error(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool), counts: Seq<u8>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, discarded: u8,
    error: crate::DecodeError, after: Seq<Part1PacketPrecinctState>,
)
    requires part2_trailer_packet_result(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, (Err(error), after)),
    ensures part2_trailer_planned_result(plan, parts, first, size, standard, counts, limits, prepared, work, discarded, Err(error)),
{
    part2_trailer_packet_value_actual(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, (Err(error), after));
    part2_cold_bind(
        |events| part2_trailer_packet_value_run(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, events),
        |decoded: ((crate::packet::TilePacketDecode, u8), Seq<Part1PacketPrecinctState>), rest|
            part2_trailer_extract_run(plan, first, size, standard, limits, prepared, work, decoded.1, decoded.0.1, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_trailer_planned_extract_actual(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool), counts: Seq<u8>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, discarded: u8,
    decoded: crate::packet::TilePacketDecode, after: Seq<Part1PacketPrecinctState>, total: u8,
    effect: Part2ExtractionTileEffect,
)
    requires part2_trailer_packet_result(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, (Ok((decoded, total)), after)),
        part2_extraction_tile_result(prepared, plan.components, part2_precinct_decoder_planes(after),
            first.component_coding_styles, part2_owned_kernel_registry(first.part2_extensions),
            crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
            first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
            crate::limits::resource_decoded_bytes_limit(limits), effect),
    ensures part2_trailer_planned_result(plan, parts, first, size, standard, counts, limits, prepared, work, discarded,
        part2_trailer_extract_output(effect, total)),
{
    part2_trailer_packet_value_actual(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, (Ok((decoded, total)), after));
    part2_trailer_extract_actual(plan, first, size, standard, limits, prepared, work, after, total, effect);
    part2_decode_eta(
        |events| part2_trailer_extract_run(plan, first, size, standard, limits, prepared, work, after, total, events),
        part2_trailer_extract_output(effect, total));
    part2_cold_bind(
        |events| part2_trailer_packet_value_run(parts, plan.grid, plan.precincts, Some(counts), limits, discarded, events),
        |result: ((crate::packet::TilePacketDecode, u8), Seq<Part1PacketPrecinctState>), rest|
            part2_trailer_extract_run(plan, first, size, standard, limits, prepared, work, result.1, result.0.1, rest),
        Ok(((decoded, total), after)), part2_trailer_extract_output(effect, total));
}

pub(crate) proof fn part2_trailer_planned_normal(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool), counts: Seq<u8>,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64, discarded: u8,
)
    ensures part2_trailer_planned_result(plan, parts, first, size, standard, counts, limits, prepared, work, discarded,
        part2_trailer_planned_value(plan, parts, first, size, standard, counts, limits, prepared, work, discarded)),
{
    part2_trailer_packet_normal(parts, plan.grid, plan.precincts, Some(counts), limits, discarded);
    let decoded = part2_trailer_packet_value(parts, plan.grid, plan.precincts, Some(counts), limits, discarded);
    match decoded.0 {
        Err(error) => part2_trailer_planned_packet_error(plan, parts, first, size, standard, counts, limits, prepared, work, discarded, error, decoded.1),
        Ok((packet, total)) => {
            let planes = part2_precinct_decoder_planes(decoded.1);
            let kernels = part2_owned_kernel_registry(first.part2_extensions);
            part2_extraction_tile_normal(prepared, plan.components, planes, first.component_coding_styles, kernels,
                crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
                first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
                crate::limits::resource_decoded_bytes_limit(limits));
            let effect = part2_reconstruct_planned_tile(prepared, plan.components, planes, first.component_coding_styles, kernels,
                crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
                first.multiple_component_transform, standard, work, crate::limits::resource_work_limit(limits),
                crate::limits::resource_decoded_bytes_limit(limits));
            part2_trailer_planned_extract_actual(plan, parts, first, size, standard, counts, limits, prepared, work, discarded,
                packet, decoded.1, total, effect);
        },
    }
}

pub(crate) open spec fn part2_trailer_tile_output(
    counters: (u64, u64, u64), result: Result<(Part2DecodedTileComponents, u8), crate::DecodeError>,
) -> Result<(Part2DecodedLayoutTile, u8), crate::DecodeError> {
    match result {
        Err(error) => Err(error),
        Ok((decoded, discarded)) => Ok((Part2DecodedLayoutTile {
            prepared: decoded.prepared, counters, mct_work: decoded.mct_work,
        }, discarded)),
    }
}

pub(crate) open spec fn part2_trailer_tile_after_plan_run(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, metadata: Part2TileDecodeMetadata,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, plan: Part2ProgressionTilePlan, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodedLayoutTile, u8)> {
    match part2_planned_tile_accounting(plan, Some(metadata.resolution_counts), initial, limits) {
        Err(error) => Some((Err(error), events)),
        Ok(counters) => part2_jpip_snapshot_bind(
            part2_trailer_planned_run(plan, parts, metadata.first, size, metadata.standard, metadata.resolution_counts,
                limits, prepared, work, discarded, events),
            |decoded: (Part2DecodedTileComponents, u8), rest|
                Some((part2_trailer_tile_output(counters, Ok(decoded)), rest))),
    }
}

pub(crate) open spec fn part2_trailer_tile_after_metadata_run(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, metadata: Part2TileDecodeMetadata, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodedLayoutTile, u8)> {
    part2_jpip_snapshot_bind(
        part2_grid_plan_run(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
            metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
            (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits, events),
        |plan: Part2ProgressionTilePlan, rest|
            part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, plan, rest))
}

pub(crate) open spec fn part2_trailer_tile_run(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part2DecodedLayoutTile, u8)> {
    part2_jpip_snapshot_bind(
        part2_tile_metadata_run(parts, crate::codestream::image_size_component_count(size), Some(discard), events),
        |metadata: Part2TileDecodeMetadata, rest|
            part2_trailer_tile_after_metadata_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata, rest))
}

pub(crate) open spec fn part2_trailer_tile_result(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, result: Result<(Part2DecodedLayoutTile, u8), crate::DecodeError>,
) -> bool {
    part2_cold_framed(
        |events| part2_trailer_tile_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, events), result)
}

pub(crate) open spec fn part2_trailer_tile_after_plan_value(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, metadata: Part2TileDecodeMetadata,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, plan: Part2ProgressionTilePlan,
) -> Result<(Part2DecodedLayoutTile, u8), crate::DecodeError> {
    match part2_planned_tile_accounting(plan, Some(metadata.resolution_counts), initial, limits) {
        Err(error) => Err(error),
        Ok(counters) => part2_trailer_tile_output(counters,
            part2_trailer_planned_value(plan, parts, metadata.first, size, metadata.standard, metadata.resolution_counts,
                limits, prepared, work, discarded)),
    }
}

pub(crate) open spec fn part2_trailer_tile_after_metadata_value(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, metadata: Part2TileDecodeMetadata,
) -> Result<(Part2DecodedLayoutTile, u8), crate::DecodeError> {
    match part2_progression_tile_plan_owned(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
        metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
        (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits) {
        Err(error) => Err(error),
        Ok(plan) => part2_trailer_tile_after_plan_value(size, parts, metadata, limits, prepared, initial, work, discarded, plan),
    }
}

pub(crate) open spec fn part2_trailer_tile_value(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8,
) -> Result<(Part2DecodedLayoutTile, u8), crate::DecodeError> {
    match part2_tile_decode_metadata_owned(parts, crate::codestream::image_size_component_count(size), Some(discard)) {
        Err(error) => Err(error),
        Ok(metadata) => part2_trailer_tile_after_metadata_value(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata),
    }
}

pub(crate) proof fn part2_trailer_tile_metadata_actual(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, metadata: Result<Part2TileDecodeMetadata, crate::DecodeError>,
    result: Result<(Part2DecodedLayoutTile, u8), crate::DecodeError>,
)
    requires part2_tile_metadata_result(parts, crate::codestream::image_size_component_count(size), Some(discard), metadata),
        match metadata {
            Err(error) => result == Err(error),
            Ok(value) => part2_cold_framed(
                |events| part2_trailer_tile_after_metadata_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, value, events), result),
        },
    ensures part2_trailer_tile_result(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, result),
{
    part2_tile_metadata_frames(parts, crate::codestream::image_size_component_count(size), Some(discard), metadata);
    if let Ok(value) = metadata {
        part2_decode_eta(
            |events| part2_trailer_tile_after_metadata_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, value, events), result);
    }
    part2_cold_bind(
        |events| part2_tile_metadata_run(parts, crate::codestream::image_size_component_count(size), Some(discard), events),
        |value: Part2TileDecodeMetadata, rest|
            part2_trailer_tile_after_metadata_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, value, rest),
        metadata, result);
}

pub(crate) proof fn part2_trailer_tile_plan_actual(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, metadata: Part2TileDecodeMetadata, plan: Result<Part2ProgressionTilePlan, crate::DecodeError>,
    result: Result<(Part2DecodedLayoutTile, u8), crate::DecodeError>,
)
    requires part2_grid_plan_result(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
        metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
        (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits, plan),
        match plan {
            Err(error) => result == Err(error),
            Ok(value) => part2_cold_framed(
                |events| part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, value, events), result),
        },
    ensures part2_cold_framed(
        |events| part2_trailer_tile_after_metadata_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata, events), result),
{
    part2_grid_plan_frames(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
        metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
        (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits, plan);
    if let Ok(value) = plan {
        part2_decode_eta(
            |events| part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, value, events), result);
    }
    part2_cold_bind(
        |events| part2_grid_plan_run(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
            metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
            (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits, events),
        |value: Part2ProgressionTilePlan, rest|
            part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, value, rest),
        plan, result);
}

pub(crate) proof fn part2_trailer_tile_planned_actual(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, metadata: Part2TileDecodeMetadata,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, plan: Part2ProgressionTilePlan, counters: (u64, u64, u64),
    result: Result<(Part2DecodedTileComponents, u8), crate::DecodeError>,
)
    requires part2_planned_tile_accounting(plan, Some(metadata.resolution_counts), initial, limits) == Ok(counters),
        part2_trailer_planned_result(plan, parts, metadata.first, size, metadata.standard, metadata.resolution_counts, limits, prepared, work, discarded, result),
    ensures part2_cold_framed(
        |events| part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, plan, events),
        part2_trailer_tile_output(counters, result)),
{
    if let Ok(value) = result { part2_cold_pure(part2_trailer_tile_output(counters, Ok(value))); }
    part2_cold_bind(
        |events| part2_trailer_planned_run(plan, parts, metadata.first, size, metadata.standard, metadata.resolution_counts, limits, prepared, work, discarded, events),
        |value: (Part2DecodedTileComponents, u8), rest| Some((part2_trailer_tile_output(counters, Ok(value)), rest)),
        result, part2_trailer_tile_output(counters, result));
}

pub(crate) proof fn part2_trailer_tile_after_plan_normal(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, metadata: Part2TileDecodeMetadata,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, plan: Part2ProgressionTilePlan,
)
    ensures part2_cold_framed(
        |events| part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, plan, events),
        part2_trailer_tile_after_plan_value(size, parts, metadata, limits, prepared, initial, work, discarded, plan)),
{
    match part2_planned_tile_accounting(plan, Some(metadata.resolution_counts), initial, limits) {
        Err(error) => part2_cold_pure::<(Part2DecodedLayoutTile, u8)>(Err(error)),
        Ok(counters) => {
            part2_trailer_planned_normal(plan, parts, metadata.first, size, metadata.standard, metadata.resolution_counts, limits, prepared, work, discarded);
            part2_trailer_tile_planned_actual(size, parts, metadata, limits, prepared, initial, work, discarded, plan, counters,
                part2_trailer_planned_value(plan, parts, metadata.first, size, metadata.standard, metadata.resolution_counts, limits, prepared, work, discarded));
        },
    }
}

pub(crate) proof fn part2_trailer_tile_account_error(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, metadata: Part2TileDecodeMetadata,
    limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, plan: Part2ProgressionTilePlan, error: crate::DecodeError,
)
    requires part2_planned_tile_accounting(plan, Some(metadata.resolution_counts), initial, limits) == Err(error),
    ensures part2_cold_framed(
        |events| part2_trailer_tile_after_plan_run(size, parts, metadata, limits, prepared, initial, work, discarded, plan, events), Err(error)),
{
    part2_cold_pure::<(Part2DecodedLayoutTile, u8)>(Err(error));
}

pub(crate) proof fn part2_trailer_tile_after_metadata_normal(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8, metadata: Part2TileDecodeMetadata,
)
    ensures part2_cold_framed(
        |events| part2_trailer_tile_after_metadata_run(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata, events),
        part2_trailer_tile_after_metadata_value(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata)),
{
    part2_grid_plan_normal(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
        metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
        (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits);
    let plan = part2_progression_tile_plan_owned(size, metadata.first.coding_style, &metadata.first.component_coding_styles,
        metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, discard),
        (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps), true), limits);
    if let Ok(value) = plan {
        part2_trailer_tile_after_plan_normal(size, parts, metadata, limits, prepared, initial, work, discarded, value);
    }
    part2_trailer_tile_plan_actual(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata, plan,
        part2_trailer_tile_after_metadata_value(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata));
}

pub(crate) proof fn part2_trailer_tile_normal(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    discard: u8, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64),
    work: u64, discarded: u8,
)
    ensures part2_trailer_tile_result(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded,
        part2_trailer_tile_value(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded)),
{
    part2_tile_metadata_normal(parts, crate::codestream::image_size_component_count(size), Some(discard));
    let metadata = part2_tile_decode_metadata_owned(parts, crate::codestream::image_size_component_count(size), Some(discard));
    if let Ok(value) = metadata {
        part2_trailer_tile_after_metadata_normal(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, value);
    }
    part2_trailer_tile_metadata_actual(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded, metadata,
        part2_trailer_tile_value(size, tile, parts, caps, discard, limits, prepared, initial, work, discarded));
}

pub type Part2TrailerReconstructed = (Part1DecodedImageModel, crate::TileTrailerRecoveryReport);
pub type Part2TrailerTyped = (Part1DecodedTypedImage, crate::TileTrailerRecoveryReport);

pub(crate) open spec fn part2_trailer_reported(
    image: Result<Part1DecodedImageModel, crate::DecodeError>, discarded: u8,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match image {
        Err(error) => Err(error),
        Ok(image) => Ok((image, crate::TileTrailerRecoveryReport { discarded_tile_trailer_bytes: discarded })),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_trailer_selected_value(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits,
    index: nat, before: Part2DecodedLayoutTile, discarded: u8,
) -> Result<Part2TrailerReconstructed, crate::DecodeError>
    decreases if index < tiles.len() { (tiles.len() - index) as nat } else { 0nat },
{
    if index >= tiles.len() {
        part2_trailer_reported(
            part2_assemble_prepared(crate::image::assembly_size_view(size), before.prepared, Some((region, discard)),
                crate::limits::resource_decoded_bytes_limit(limits)), discarded)
    } else {
        match part2_collect_tile_parts(parts, tiles[index as int]) {
            Err(error) => Err(error),
            Ok(selected) => match part2_trailer_tile_value(size, tiles[index as int], selected, caps, discard,
                limits, before.prepared, before.counters, before.mct_work, discarded) {
                Err(error) => Err(error),
                Ok((after, total)) => part2_trailer_selected_value(size, parts, caps, tiles, region, discard, limits, index + 1, after, total),
            },
        }
    }
}

pub(crate) open spec fn part2_trailer_assembly_run(size:Part1AssemblySize,prepared:Seq<Part1AssemblyTile>,region:[u32;4],discard:u8,maximum:u64,discarded:u8,
    single_tile:bool,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2TrailerReconstructed> {
    part2_jpip_snapshot_bind(part2_owned_prepared_selected_run(size,prepared,region,discard,maximum,single_tile,events),
        |image:Part1DecodedImageModel,rest|Some((part2_trailer_reported(Ok(image),discarded),rest)))
}
pub(crate) proof fn part2_trailer_assembly_observed(size:Part1AssemblySize,prepared:Seq<Part1AssemblyTile>,region:[u32;4],discard:u8,maximum:u64,discarded:u8,
    single_tile:bool,result:Result<Part1DecodedImageModel,crate::DecodeError>)
    requires part2_owned_prepared_selected_result(size,prepared,region,discard,maximum,single_tile,result),
    ensures part2_cold_framed(|events|part2_trailer_assembly_run(size,prepared,region,discard,maximum,discarded,single_tile,events),part2_trailer_reported(result,discarded)),
{
    if let Ok(image)=result{part2_cold_pure(part2_trailer_reported(Ok(image),discarded));}
    part2_cold_bind(|events|part2_owned_prepared_selected_run(size,prepared,region,discard,maximum,single_tile,events),
        |image:Part1DecodedImageModel,rest|Some((part2_trailer_reported(Ok(image),discarded),rest)),result,part2_trailer_reported(result,discarded));
}
#[verifier::opaque]
pub(crate) open spec fn part2_trailer_selected_run(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits,
    index: nat, before: Part2DecodedLayoutTile, discarded: u8, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed>
    decreases if index < tiles.len() { (tiles.len() - index) as nat } else { 0nat },
{
    if index >= tiles.len() {
        part2_trailer_assembly_run(crate::image::assembly_size_view(size),before.prepared,region,discard,crate::limits::resource_decoded_bytes_limit(limits),discarded,tiles.len()==1,events)
    } else {
        part2_jpip_snapshot_bind(part2_collected_parts_run(parts, tiles[index as int], events),
            |selected: Seq<Part2OwnedTilePart>, rest| part2_jpip_snapshot_bind(
                part2_trailer_tile_run(size, tiles[index as int], selected, caps, discard, limits,
                    before.prepared, before.counters, before.mct_work, discarded, rest),
                |after: (Part2DecodedLayoutTile, u8), tail|
                    part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after.0, after.1, tail)))
    }
}

pub(crate) proof fn part2_trailer_selected_step(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits,
    index: nat, before: Part2DecodedLayoutTile, discarded: u8,
)
    requires index < tiles.len(),
    ensures forall|events| #[trigger] part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index, before, discarded, events)
        == part2_jpip_snapshot_bind(part2_collected_parts_run(parts, tiles[index as int], events),
            |selected: Seq<Part2OwnedTilePart>, rest| part2_jpip_snapshot_bind(
            part2_trailer_tile_run(size, tiles[index as int], selected, caps, discard, limits,
                before.prepared, before.counters, before.mct_work, discarded, rest),
            |after: (Part2DecodedLayoutTile, u8), tail|
                part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after.0, after.1, tail))),
{
    reveal_with_fuel(part2_trailer_selected_run, 1);
}

pub(crate) proof fn part2_trailer_selected_normal(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits,
    index: nat, before: Part2DecodedLayoutTile, discarded: u8,
)
    ensures part2_cold_framed(
        |events| part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index, before, discarded, events),
        part2_trailer_selected_value(size, parts, caps, tiles, region, discard, limits, index, before, discarded)),
    decreases if index < tiles.len() { (tiles.len() - index) as nat } else { 0nat },
{
    reveal_with_fuel(part2_trailer_selected_run, 1); reveal_with_fuel(part2_trailer_selected_value, 1);
    let result = part2_trailer_selected_value(size, parts, caps, tiles, region, discard, limits, index, before, discarded);
    if index >= tiles.len() {
        let size=crate::image::assembly_size_view(size);let maximum=crate::limits::resource_decoded_bytes_limit(limits);
        let single_tile=tiles.len()==1;
        part2_owned_prepared_selected_normal(size,before.prepared,region,discard,maximum,single_tile);
        part2_trailer_assembly_observed(size,before.prepared,region,discard,maximum,discarded,single_tile,part2_assemble_prepared(size,before.prepared,Some((region,discard)),maximum));
        part2_decode_eta(|events|part2_trailer_assembly_run(size,before.prepared,region,discard,maximum,discarded,single_tile,events),result);
    } else {
        let collected = part2_collect_tile_parts(parts, tiles[index as int]);
        part2_collected_parts_normal(parts, tiles[index as int]);
        match collected {
            Err(_) => part2_cold_pure::<Part2TrailerReconstructed>(result),
            Ok(selected) => {
                let tile = tiles[index as int];
                part2_trailer_tile_normal(size, tile, selected, caps, discard, limits, before.prepared, before.counters, before.mct_work, discarded);
                let decoded = part2_trailer_tile_value(size, tile, selected, caps, discard, limits, before.prepared, before.counters, before.mct_work, discarded);
                if let Ok((after, total)) = decoded {
                    part2_trailer_selected_normal(size, parts, caps, tiles, region, discard, limits, index + 1, after, total);
                    part2_decode_eta(
                        |events| part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after, total, events),
                        part2_trailer_selected_value(size, parts, caps, tiles, region, discard, limits, index + 1, after, total));
                }
                part2_cold_bind(
                    |events| part2_trailer_tile_run(size, tile, selected, caps, discard, limits, before.prepared, before.counters, before.mct_work, discarded, events),
                    |after: (Part2DecodedLayoutTile, u8), rest|
                        part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after.0, after.1, rest),
                    decoded, result);
                part2_decode_eta(|events| part2_jpip_snapshot_bind(
                    part2_trailer_tile_run(size, tile, selected, caps, discard, limits,
                        before.prepared, before.counters, before.mct_work, discarded, events),
                    |after: (Part2DecodedLayoutTile, u8), rest|
                        part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after.0, after.1, rest)),
                    result);
            },
        }
        part2_cold_bind(|events| part2_collected_parts_run(parts, tiles[index as int], events),
            |selected: Seq<Part2OwnedTilePart>, rest| part2_jpip_snapshot_bind(
                part2_trailer_tile_run(size, tiles[index as int], selected, caps, discard, limits,
                    before.prepared, before.counters, before.mct_work, discarded, rest),
                |after: (Part2DecodedLayoutTile, u8), tail|
                    part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after.0, after.1, tail)),
            collected, result);
        part2_decode_eta(|events| part2_jpip_snapshot_bind(part2_collected_parts_run(parts, tiles[index as int], events),
            |selected: Seq<Part2OwnedTilePart>, rest| part2_jpip_snapshot_bind(
                part2_trailer_tile_run(size, tiles[index as int], selected, caps, discard, limits,
                    before.prepared, before.counters, before.mct_work, discarded, rest),
                |after: (Part2DecodedLayoutTile, u8), tail|
                    part2_trailer_selected_run(size, parts, caps, tiles, region, discard, limits, index + 1, after.0, after.1, tail))),
            result);
    }
}

pub(crate) open spec fn part2_trailer_after_selection_run(
    input: Part2DecoderLayoutInput, selection: Part2ValidatedSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed> {
    if selection.1.len() != 4 { Some((Err(part1_block_placement_error(false)), events)) }
    else {
        let initial = Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 };
        part2_jpip_snapshot_bind(
            part2_prepare_tile_index_run(input.parts, part2_index_tile_slots(&input.size), selection.0.len(), events),
            |_: (), rest| part2_trailer_selected_run(&input.size, input.parts, input.capabilities, selection.0,
                [selection.1[0], selection.1[1], selection.1[2], selection.1[3]], selection.2, limits, 0, initial, 0, rest))
    }
}

pub(crate) open spec fn part2_trailer_layout_run(
    input: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed> {
    match part2_decoder_execution_admission(input) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(
            part2_validate_selection_run(crate::codestream::selection_geometry_view(&input.size), requested, events),
            |selection: Part2ValidatedSelection, rest| part2_trailer_after_selection_run(input, selection, limits, rest)),
    }
}

pub(crate) open spec fn part2_trailer_layout_value(
    input: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part2_decoder_execution_admission(input) {
        Err(error) => Err(error),
        Ok(()) => match part2_validate_selection(crate::codestream::selection_geometry_view(&input.size), requested) {
            Err(error) => Err(error),
            Ok(selection) => if selection.1.len() != 4 { Err(part1_block_placement_error(false)) }
                else {
                    let initial = Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 };
                    part2_trailer_selected_value(&input.size, input.parts, input.capabilities, selection.0,
                        [selection.1[0], selection.1[1], selection.1[2], selection.1[3]], selection.2, limits, 0, initial, 0)
                },
        },
    }
}

pub(crate) open spec fn part2_trailer_layout_result(
    input: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    result: Result<Part2TrailerReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_trailer_layout_run(input, requested, limits, events), result)
}

pub(crate) proof fn part2_trailer_layout_normal(
    input: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_trailer_layout_result(input, requested, limits, part2_trailer_layout_value(input, requested, limits)),
{
    let result = part2_trailer_layout_value(input, requested, limits);
    match part2_decoder_execution_admission(input) {
        Err(_) => part2_cold_pure::<Part2TrailerReconstructed>(result),
        Ok(()) => {
            let size = crate::codestream::selection_geometry_view(&input.size);
            let selected = part2_validate_selection(size, requested);
            part2_validate_selection_normal(size, requested);
            match selected {
                Err(_) => part2_cold_pure::<Part2TrailerReconstructed>(result),
                Ok(selection) => if selection.1.len() != 4 {
                    part2_cold_pure::<Part2TrailerReconstructed>(result);
                } else {
                    let initial = Part2DecodedLayoutTile { prepared: Seq::empty(), counters: (0, 0, 0), mct_work: 0 };
                    let region = [selection.1[0], selection.1[1], selection.1[2], selection.1[3]];
                    part2_trailer_selected_normal(&input.size, input.parts, input.capabilities, selection.0, region, selection.2, limits, 0, initial, 0);
                    part2_decode_eta(
                        |events| part2_trailer_selected_run(&input.size, input.parts, input.capabilities, selection.0, region, selection.2, limits, 0, initial, 0, events), result);
                    part2_index_prefix_normal(input.parts, part2_index_tile_slots(&input.size), selection.0.len(),
                        |events| part2_trailer_selected_run(&input.size, input.parts, input.capabilities,
                            selection.0, region, selection.2, limits, 0, initial, 0, events), result);
                    part2_decode_eta(|events| part2_trailer_after_selection_run(input, selection, limits, events), result);
                },
            }
            let child = |events| part2_validate_selection_run(size, requested, events);
            let next = |selection: Part2ValidatedSelection, rest| part2_trailer_after_selection_run(input, selection, limits, rest);
            part2_cold_bind(child, next, selected, result);
            part2_decode_eta(|events| part2_jpip_snapshot_bind(child(events), next), result);
        },
    }
}

pub(crate) open spec fn part2_trailer_raw_typed_finish(
    bytes: usize, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, decoded: Part2TrailerReconstructed,
) -> Result<Part2TrailerTyped, crate::DecodeError> {
    match part2_typed_decode_finish(bytes, source, Some(requested), limits, decoded.0) {
        Err(error) => Err(error), Ok(image) => Ok((image, decoded.1)),
    }
}

pub(crate) open spec fn part2_trailer_raw_reconstructed_finish(
    bytes: usize, source: Part2DecoderLayoutInput, decoded: Part2TrailerReconstructed,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part2_reconstructed_decode_finish(bytes, source, decoded.0) {
        Err(error) => Err(error), Ok(image) => Ok((image, decoded.1)),
    }
}
pub(crate) open spec fn part2_trailer_raw_typed_finish_run(bytes:usize,source:Part2DecoderLayoutInput,requested:Part2DecodeSelection,
    limits:&crate::ResourceLimits,decoded:Part2TrailerReconstructed,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2TrailerTyped> {
    part2_jpip_snapshot_bind(part2_typed_decode_finish_run(bytes,source,Some(requested),limits,decoded.0,events),
        |image:Part1DecodedTypedImage,rest|Some((Ok((image,decoded.1)),rest)))
}
pub(crate) proof fn part2_trailer_raw_typed_finish_normal(bytes:usize,source:Part2DecoderLayoutInput,requested:Part2DecodeSelection,limits:&crate::ResourceLimits,decoded:Part2TrailerReconstructed)
    ensures part2_cold_framed(|events|part2_trailer_raw_typed_finish_run(bytes,source,requested,limits,decoded,events),part2_trailer_raw_typed_finish(bytes,source,requested,limits,decoded)),
{
    let typed=part2_typed_decode_finish(bytes,source,Some(requested),limits,decoded.0);
    part2_typed_decode_finish_normal(bytes,source,Some(requested),limits,decoded.0);
    if let Ok(image)=typed{part2_cold_pure(Ok((image,decoded.1)));}
    part2_cold_bind(|events|part2_typed_decode_finish_run(bytes,source,Some(requested),limits,decoded.0,events),
        |image:Part1DecodedTypedImage,rest|Some((Ok((image,decoded.1)),rest)),typed,part2_trailer_raw_typed_finish(bytes,source,requested,limits,decoded));
}

pub(crate) open spec fn part2_trailer_raw_typed_after_parse(
    bytes: usize, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerTyped> {
    let source = part2_decoder_input_from_raw(parsed);
    part2_jpip_snapshot_bind(part2_trailer_layout_run(source, requested, limits, events),
        |decoded: Part2TrailerReconstructed, rest|part2_trailer_raw_typed_finish_run(bytes,source,requested,limits,decoded,rest))
}

pub(crate) open spec fn part2_trailer_raw_reconstructed_after_parse(
    bytes: usize, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed> {
    let source = part2_decoder_input_from_raw(parsed);
    part2_jpip_snapshot_bind(part2_trailer_layout_run(source, requested, limits, events),
        |decoded: Part2TrailerReconstructed, rest|
            Some((part2_trailer_raw_reconstructed_finish(bytes, source, decoded), rest)))
}

pub(crate) open spec fn part2_trailer_raw_typed_run(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerTyped> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 12, 0, events),
        |parsed: Part1CompleteLayout, rest|
            part2_trailer_raw_typed_after_parse(input.len() as usize, parsed, requested, limits, rest))
}

pub(crate) open spec fn part2_trailer_raw_reconstructed_run(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 12, 0, events),
        |parsed: Part1CompleteLayout, rest|
            part2_trailer_raw_reconstructed_after_parse(input.len() as usize, parsed, requested, limits, rest))
}

pub closed spec fn part2_trailer_raw_typed_result(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    result: Result<Part2TrailerTyped, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_trailer_raw_typed_run(input, requested, limits, events), result)
}

pub closed spec fn part2_trailer_raw_reconstructed_result(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    result: Result<Part2TrailerReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_trailer_raw_reconstructed_run(input, requested, limits, events), result)
}

pub(crate) open spec fn part2_trailer_raw_typed_layout_value(
    bytes: usize, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerTyped, crate::DecodeError> {
    match part2_trailer_layout_value(source, requested, limits) {
        Err(error) => Err(error), Ok(decoded) => part2_trailer_raw_typed_finish(bytes, source, requested, limits, decoded),
    }
}

pub(crate) open spec fn part2_trailer_raw_reconstructed_layout_value(
    bytes: usize, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part2_trailer_layout_value(source, requested, limits) {
        Err(error) => Err(error), Ok(decoded) => part2_trailer_raw_reconstructed_finish(bytes, source, decoded),
    }
}

pub closed spec fn part2_trailer_raw_typed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerTyped, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_trailer_raw_typed_layout_value(input.len() as usize, part2_decoder_input_from_raw(parsed), requested, limits),
    }
}

pub closed spec fn part2_trailer_raw_reconstructed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_trailer_raw_reconstructed_layout_value(input.len() as usize, part2_decoder_input_from_raw(parsed), requested, limits),
    }
}

pub(crate) proof fn part2_trailer_raw_value_unfold(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_trailer_raw_typed_value(input, requested, limits) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_trailer_raw_typed_layout_value(input.len() as usize, part2_decoder_input_from_raw(parsed), requested, limits),
    },
        part2_trailer_raw_reconstructed_value(input, requested, limits) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_trailer_raw_reconstructed_layout_value(input.len() as usize, part2_decoder_input_from_raw(parsed), requested, limits),
    },
{}

pub(crate) proof fn part2_trailer_raw_parse_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part1_parse_layout_cold_result(input, limits, Err(error)),
    ensures part2_trailer_raw_typed_result(input, requested, limits, Err(error)),
        part2_trailer_raw_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_trailer_raw_typed_result); reveal(part2_trailer_raw_reconstructed_result);
    part2_cold_parse_actual(input, limits, 12, 0, Err(error));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 12, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_trailer_raw_typed_after_parse(input.len() as usize, parsed, requested, limits, rest),
        Err(error), Err(error));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 12, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_trailer_raw_reconstructed_after_parse(input.len() as usize, parsed, requested, limits, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_trailer_raw_layout_actual(
    input: Seq<u8>, parsed: Part1CompleteLayout, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    decoded: Result<Part2TrailerReconstructed, crate::DecodeError>,
)
    requires part1_parse_layout_cold_result(input, limits, Ok(parsed)),
        part2_trailer_layout_result(part2_decoder_input_from_raw(parsed), requested, limits, decoded),
    ensures part2_trailer_raw_typed_result(input, requested, limits, match decoded {
        Err(error) => Err(error), Ok(value) => part2_trailer_raw_typed_finish(input.len() as usize, part2_decoder_input_from_raw(parsed), requested, limits, value),
    }),
        part2_trailer_raw_reconstructed_result(input, requested, limits, match decoded {
            Err(error) => Err(error), Ok(value) => part2_trailer_raw_reconstructed_finish(input.len() as usize, part2_decoder_input_from_raw(parsed), value),
        }),
{
    reveal(part2_trailer_raw_typed_result); reveal(part2_trailer_raw_reconstructed_result);
    let source = part2_decoder_input_from_raw(parsed);
    let typed = match decoded { Err(error) => Err(error), Ok(value) => part2_trailer_raw_typed_finish(input.len() as usize, source, requested, limits, value) };
    let wide = match decoded { Err(error) => Err(error), Ok(value) => part2_trailer_raw_reconstructed_finish(input.len() as usize, source, value) };
    if let Ok(value) = decoded {
        part2_trailer_raw_typed_finish_normal(input.len() as usize,source,requested,limits,value);
        part2_decode_eta(|events|part2_trailer_raw_typed_finish_run(input.len() as usize,source,requested,limits,value,events),
            part2_trailer_raw_typed_finish(input.len() as usize,source,requested,limits,value));
        part2_cold_pure(part2_trailer_raw_reconstructed_finish(input.len() as usize, source, value));
    }
    part2_cold_bind(|events| part2_trailer_layout_run(source, requested, limits, events),
        |value: Part2TrailerReconstructed, rest|part2_trailer_raw_typed_finish_run(input.len() as usize,source,requested,limits,value,rest),
        decoded, typed);
    part2_cold_bind(|events| part2_trailer_layout_run(source, requested, limits, events),
        |value: Part2TrailerReconstructed, rest| Some((part2_trailer_raw_reconstructed_finish(input.len() as usize, source, value), rest)),
        decoded, wide);
    part2_decode_eta(|events| part2_trailer_raw_typed_after_parse(input.len() as usize, parsed, requested, limits, events), typed);
    part2_decode_eta(|events| part2_trailer_raw_reconstructed_after_parse(input.len() as usize, parsed, requested, limits, events), wide);
    part2_cold_parse_actual(input, limits, 12, 0, Ok(parsed));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 12, 0, events),
        |value: Part1CompleteLayout, rest| part2_trailer_raw_typed_after_parse(input.len() as usize, value, requested, limits, rest), Ok(parsed), typed);
    part2_cold_bind(|events| part2_cold_parse(input, limits, 12, 0, events),
        |value: Part1CompleteLayout, rest| part2_trailer_raw_reconstructed_after_parse(input.len() as usize, value, requested, limits, rest), Ok(parsed), wide);
}

pub(crate) proof fn part2_trailer_raw_conversion_error(input:Seq<u8>,parsed:Part1CompleteLayout,requested:Part2DecodeSelection,
    limits:&crate::ResourceLimits,decoded:Part2TrailerReconstructed,error:crate::DecodeError)
    requires part1_parse_layout_cold_result(input,limits,Ok(parsed)),
        part2_trailer_layout_result(part2_decoder_input_from_raw(parsed),requested,limits,Ok(decoded)),
        part2_typed_layout_result(part2_decoder_input_from_raw(parsed),decoded.0,requested.2,limits,Err(error)),
    ensures part2_trailer_raw_typed_result(input,requested,limits,Err(error)),
{
    reveal(part2_trailer_raw_typed_result);
    let source=part2_decoder_input_from_raw(parsed);let bytes=input.len() as usize;
    part2_typed_decode_finish_error(bytes,source,Some(requested),limits,decoded.0,error);
    part2_decode_eta(|events|part2_typed_decode_finish_run(bytes,source,Some(requested),limits,decoded.0,events),Err(error));
    part2_cold_bind(|events|part2_typed_decode_finish_run(bytes,source,Some(requested),limits,decoded.0,events),
        |image:Part1DecodedTypedImage,rest|Some((Ok((image,decoded.1)),rest)),Err(error),Err::<Part2TrailerTyped,_>(error));
    part2_decode_eta(|events|part2_trailer_raw_typed_finish_run(bytes,source,requested,limits,decoded,events),Err(error));
    part2_cold_bind(|events|part2_trailer_layout_run(source,requested,limits,events),
        |value:Part2TrailerReconstructed,rest|part2_trailer_raw_typed_finish_run(bytes,source,requested,limits,value,rest),Ok(decoded),Err(error));
    part2_decode_eta(|events|part2_trailer_raw_typed_after_parse(bytes,parsed,requested,limits,events),Err(error));
    part2_cold_parse_actual(input,limits,12,0,Ok(parsed));
    part2_cold_bind(|events|part2_cold_parse(input,limits,12,0,events),
        |value:Part1CompleteLayout,rest|part2_trailer_raw_typed_after_parse(bytes,value,requested,limits,rest),Ok(parsed),Err(error));
}
pub(crate) proof fn part2_trailer_raw_normal(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_trailer_raw_typed_result(input, requested, limits, part2_trailer_raw_typed_value(input, requested, limits)),
        part2_trailer_raw_reconstructed_result(input, requested, limits, part2_trailer_raw_reconstructed_value(input, requested, limits)),
{
    part2_trailer_raw_value_unfold(input, requested, limits);
    part1_parse_layout_cold_normal(input, limits);
    match part1_parse_layout(input, limits) {
        Err(error) => part2_trailer_raw_parse_error(input, requested, limits, error),
        Ok(parsed) => {
            let source = part2_decoder_input_from_raw(parsed);
            part2_trailer_layout_normal(source, requested, limits);
            part2_trailer_raw_layout_actual(input, parsed, requested, limits, part2_trailer_layout_value(source, requested, limits));
        },
    }
}

pub(crate) open spec fn part2_trailer_jp2_typed_finish(
    inspected: Part2RawInspectedContainer, limits: &crate::ResourceLimits, decoded: Part2TrailerTyped,
) -> Result<Part2TrailerTyped, crate::DecodeError> {
    match part2_single_output(inspected, limits, decoded.0) {
        Err(error) => Err(error), Ok(image) => Ok((image, decoded.1)),
    }
}

pub(crate) open spec fn part2_trailer_jp2_typed_finish_run(inspected:Part2RawInspectedContainer,limits:&crate::ResourceLimits,decoded:Part2TrailerTyped,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2TrailerTyped> {
    part2_jpip_snapshot_bind(part2_single_output_run(inspected,limits,decoded.0,events),
        |image:Part1DecodedTypedImage,rest|Some((Ok((image,decoded.1)),rest)))
}
pub(crate) proof fn part2_trailer_jp2_typed_finish_normal(inspected:Part2RawInspectedContainer,limits:&crate::ResourceLimits,decoded:Part2TrailerTyped)
    ensures part2_cold_framed(|events|part2_trailer_jp2_typed_finish_run(inspected,limits,decoded,events),part2_trailer_jp2_typed_finish(inspected,limits,decoded)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2TrailerTyped>|
            (forall|events| #[trigger] other(events)==part2_trailer_jp2_typed_finish_run(inspected,limits,decoded,events)) ==> #[trigger] part2_cold_framed(other,part2_trailer_jp2_typed_finish(inspected,limits,decoded)),
{
    let mapped=part2_single_output(inspected,limits,decoded.0);part2_single_output_normal(inspected,limits,decoded.0);
    if let Ok(value)=mapped{part2_cold_pure(Ok((value,decoded.1)));}
    part2_cold_bind(|events|part2_single_output_run(inspected,limits,decoded.0,events),
        |image:Part1DecodedTypedImage,rest|Some((Ok((image,decoded.1)),rest)),mapped,part2_trailer_jp2_typed_finish(inspected,limits,decoded));
    part2_decode_eta(|events|part2_trailer_jp2_typed_finish_run(inspected,limits,decoded,events),part2_trailer_jp2_typed_finish(inspected,limits,decoded));
}
pub(crate) open spec fn part2_trailer_jp2_reconstructed_finish(
    inspected: Part2RawInspectedContainer, decoded: Part2TrailerReconstructed,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part2_jp2_reconstructed_output(inspected, decoded.0) {
        Err(error) => Err(error), Ok(image) => Ok((image, decoded.1)),
    }
}

pub(crate) open spec fn part2_trailer_jp2_typed_after_inspection(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerTyped> {
    match part2_single_profile(inspected, false) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(
            part2_trailer_raw_typed_run(inspected.0.streams[0].1, requested, limits, events),
            |decoded: Part2TrailerTyped, rest|part2_trailer_jp2_typed_finish_run(inspected,limits,decoded,rest)),
    }
}

pub(crate) open spec fn part2_trailer_jp2_reconstructed_after_inspection(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed> {
    match part2_single_profile(inspected, false) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(
            part2_trailer_raw_reconstructed_run(inspected.0.streams[0].1, requested, limits, events),
            |decoded: Part2TrailerReconstructed, rest| Some((part2_trailer_jp2_reconstructed_finish(inspected, decoded), rest))),
    }
}

pub(crate) open spec fn part2_trailer_jp2_typed_run(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerTyped> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest| part2_trailer_jp2_typed_after_inspection(inspected, requested, limits, rest))
}

pub(crate) open spec fn part2_trailer_jp2_reconstructed_run(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2TrailerReconstructed> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest| part2_trailer_jp2_reconstructed_after_inspection(inspected, requested, limits, rest))
}

pub closed spec fn part2_trailer_jp2_typed_result(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    result: Result<Part2TrailerTyped, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_trailer_jp2_typed_run(input, requested, limits, events), result)
}

pub closed spec fn part2_trailer_jp2_reconstructed_result(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    result: Result<Part2TrailerReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_trailer_jp2_reconstructed_run(input, requested, limits, events), result)
}

pub(crate) open spec fn part2_trailer_jp2_typed_inspected_value(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerTyped, crate::DecodeError> {
    match part2_single_profile(inspected, false) {
        Err(error) => Err(error),
        Ok(()) => match part2_trailer_raw_typed_value(inspected.0.streams[0].1, requested, limits) {
            Err(error) => Err(error), Ok(decoded) => part2_trailer_jp2_typed_finish(inspected, limits, decoded),
        },
    }
}

pub(crate) open spec fn part2_trailer_jp2_reconstructed_inspected_value(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part2_single_profile(inspected, false) {
        Err(error) => Err(error),
        Ok(()) => match part2_trailer_raw_reconstructed_value(inspected.0.streams[0].1, requested, limits) {
            Err(error) => Err(error), Ok(decoded) => part2_trailer_jp2_reconstructed_finish(inspected, decoded),
        },
    }
}

pub closed spec fn part2_trailer_jp2_typed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerTyped, crate::DecodeError> {
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error),
        Ok(inspected) => part2_trailer_jp2_typed_inspected_value(inspected, requested, limits),
    }
}

pub closed spec fn part2_trailer_jp2_reconstructed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2TrailerReconstructed, crate::DecodeError> {
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error),
        Ok(inspected) => part2_trailer_jp2_reconstructed_inspected_value(inspected, requested, limits),
    }
}

pub(crate) proof fn part2_trailer_jp2_value_unfold(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_trailer_jp2_typed_value(input, requested, limits) == match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error), Ok(inspected) => part2_trailer_jp2_typed_inspected_value(inspected, requested, limits),
    },
        part2_trailer_jp2_reconstructed_value(input, requested, limits) == match part2_parse_and_inspect_container_mode(input, limits, true) {
            Err(error) => Err(error), Ok(inspected) => part2_trailer_jp2_reconstructed_inspected_value(inspected, requested, limits),
        },
{}

pub(crate) proof fn part2_trailer_jp2_inspection_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Err(error)),
    ensures part2_trailer_jp2_typed_result(input, requested, limits, Err(error)),
        part2_trailer_jp2_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_trailer_jp2_typed_result); reveal(part2_trailer_jp2_reconstructed_result);
    part2_single_inspection_actual(input, limits, false, Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest| part2_trailer_jp2_typed_after_inspection(inspected, requested, limits, rest),
        Err(error), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest| part2_trailer_jp2_reconstructed_after_inspection(inspected, requested, limits, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_trailer_jp2_profile_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)), part2_single_profile(inspected, false) == Err(error),
    ensures part2_trailer_jp2_typed_result(input, requested, limits, Err(error)),
        part2_trailer_jp2_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_trailer_jp2_typed_result); reveal(part2_trailer_jp2_reconstructed_result);
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_pure::<Part2TrailerTyped>(Err(error));
    part2_cold_pure::<Part2TrailerReconstructed>(Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest| part2_trailer_jp2_typed_after_inspection(value, requested, limits, rest),
        Ok(inspected), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest| part2_trailer_jp2_reconstructed_after_inspection(value, requested, limits, rest),
        Ok(inspected), Err(error));
}

pub(crate) proof fn part2_trailer_jp2_typed_actual(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer, decoded: Result<Part2TrailerTyped, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)), part2_single_profile(inspected, false) == Ok(()),
        part2_trailer_raw_typed_result(inspected.0.streams[0].1, requested, limits, decoded),
    ensures part2_trailer_jp2_typed_result(input, requested, limits, match decoded {
        Err(error) => Err(error), Ok(value) => part2_trailer_jp2_typed_finish(inspected, limits, value),
    }),
{
    reveal(part2_trailer_jp2_typed_result); reveal(part2_trailer_raw_typed_result);
    let result = match decoded { Err(error) => Err(error), Ok(value) => part2_trailer_jp2_typed_finish(inspected, limits, value) };
    if let Ok(value) = decoded {part2_trailer_jp2_typed_finish_normal(inspected,limits,value);}
    part2_cold_bind(|events| part2_trailer_raw_typed_run(inspected.0.streams[0].1, requested, limits, events),
        |value: Part2TrailerTyped, rest|part2_trailer_jp2_typed_finish_run(inspected,limits,value,rest), decoded, result);
    part2_decode_eta(|events| part2_trailer_jp2_typed_after_inspection(inspected, requested, limits, events), result);
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest| part2_trailer_jp2_typed_after_inspection(value, requested, limits, rest), Ok(inspected), result);
}

pub(crate) proof fn part2_trailer_jp2_output_error(input:Seq<u8>,requested:Part2DecodeSelection,limits:&crate::ResourceLimits,
    inspected:Part2RawInspectedContainer,decoded:Part2TrailerTyped,error:crate::DecodeError)
    requires part2_inspection_cold_result(input,limits,true,Ok(inspected)),part2_single_profile(inspected,false)==Ok(()),
        part2_trailer_raw_typed_result(inspected.0.streams[0].1,requested,limits,Ok(decoded)),
        part2_output_storage_result(Part2OutputStorageContext {image:decoded.0,header:part2_raw_associated_header(inspected.0.header).0,
            components:crate::limits::resource_component_limit(limits),maximum:crate::limits::resource_decoded_bytes_limit(limits)},Err(error)),
    ensures part2_trailer_jp2_typed_result(input,requested,limits,Err(error)),
{
    reveal(part2_trailer_jp2_typed_result);reveal(part2_trailer_raw_typed_result);
    part2_single_inspection_actual(input,limits,false,Ok(inspected));
    part2_apply_output_observed(decoded.0,part2_raw_associated_header(inspected.0.header).0,
        crate::limits::resource_component_limit(limits),crate::limits::resource_decoded_bytes_limit(limits),Err(error));
    part2_decode_eta(|events|part2_single_output_run(inspected,limits,decoded.0,events),Err(error));
    part2_cold_bind(|events|part2_single_output_run(inspected,limits,decoded.0,events),
        |image:Part1DecodedTypedImage,rest|Some((Ok((image,decoded.1)),rest)),Err(error),Err::<Part2TrailerTyped,_>(error));
    part2_decode_eta(|events|part2_trailer_jp2_typed_finish_run(inspected,limits,decoded,events),Err(error));
    part2_cold_bind(|events|part2_trailer_raw_typed_run(inspected.0.streams[0].1,requested,limits,events),
        |decoded:Part2TrailerTyped,rest|part2_trailer_jp2_typed_finish_run(inspected,limits,decoded,rest),Ok(decoded),Err(error));
    part2_decode_eta(|events|part2_trailer_jp2_typed_after_inspection(inspected,requested,limits,events),Err(error));
    part2_cold_bind(|events|part2_single_inspection_run(input,limits,false,events),
        |value:Part2RawInspectedContainer,rest|part2_trailer_jp2_typed_after_inspection(value,requested,limits,rest),Ok(inspected),Err(error));
}
pub(crate) proof fn part2_trailer_jp2_reconstructed_actual(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer, decoded: Result<Part2TrailerReconstructed, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)), part2_single_profile(inspected, false) == Ok(()),
        part2_trailer_raw_reconstructed_result(inspected.0.streams[0].1, requested, limits, decoded),
    ensures part2_trailer_jp2_reconstructed_result(input, requested, limits, match decoded {
        Err(error) => Err(error), Ok(value) => part2_trailer_jp2_reconstructed_finish(inspected, value),
    }),
{
    reveal(part2_trailer_jp2_reconstructed_result); reveal(part2_trailer_raw_reconstructed_result);
    let result = match decoded { Err(error) => Err(error), Ok(value) => part2_trailer_jp2_reconstructed_finish(inspected, value) };
    if let Ok(value) = decoded { part2_cold_pure(part2_trailer_jp2_reconstructed_finish(inspected, value)); }
    part2_cold_bind(|events| part2_trailer_raw_reconstructed_run(inspected.0.streams[0].1, requested, limits, events),
        |value: Part2TrailerReconstructed, rest| Some((part2_trailer_jp2_reconstructed_finish(inspected, value), rest)), decoded, result);
    part2_decode_eta(|events| part2_trailer_jp2_reconstructed_after_inspection(inspected, requested, limits, events), result);
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest| part2_trailer_jp2_reconstructed_after_inspection(value, requested, limits, rest), Ok(inspected), result);
}

pub(crate) proof fn part2_trailer_jp2_normal(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_trailer_jp2_typed_result(input, requested, limits, part2_trailer_jp2_typed_value(input, requested, limits)),
        part2_trailer_jp2_reconstructed_result(input, requested, limits, part2_trailer_jp2_reconstructed_value(input, requested, limits)),
{
    part2_trailer_jp2_value_unfold(input, requested, limits);
    part2_single_inspection_normal(input, limits, false);
    part2_inspection_cold_normal(input, limits, true);
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => part2_trailer_jp2_inspection_error(input, requested, limits, error),
        Ok(inspected) => match part2_single_profile(inspected, false) {
            Err(error) => part2_trailer_jp2_profile_error(input, requested, limits, inspected, error),
            Ok(()) => {
                let stream = inspected.0.streams[0].1;
                part2_trailer_raw_normal(stream, requested, limits);
                part2_trailer_jp2_typed_actual(input, requested, limits, inspected, part2_trailer_raw_typed_value(stream, requested, limits));
                part2_trailer_jp2_reconstructed_actual(input, requested, limits, inspected, part2_trailer_raw_reconstructed_value(stream, requested, limits));
            },
        },
    }
}
}
