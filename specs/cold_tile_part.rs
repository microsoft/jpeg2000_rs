//! Complete tile-reader state around the reached quantization reservation.

use super::*;

verus! {

pub(crate) struct Part1ColdTileInput<'a> {
    pub reader: Part1CodestreamReader<'a>,
    pub tile: (usize, u32, u16, u8, u8),
    pub defaults: (Part1ParsedCodingStyle, Part2Quantization),
    pub styles: (u16, Seq<Part1ParsedCodingStyle>),
    pub quantizations: (u16, Seq<Part2Quantization>),
    pub roi: Seq<u8>,
    pub progression: Seq<crate::codestream::ProgressionChange>,
    pub mct: Part1MctParameters,
    pub extensions: Part2OwnedExtensions,
    pub components: u16,
    pub lengths: Part1PacketLengths,
    pub headers: Part1PackedHeaders,
}

pub(crate) open spec fn part1_cold_tile_normal(input: Part1ColdTileInput<'_>)
    -> (Part1TilePartResult, Part1CodestreamReader<'_>) {
    part1_read_tile_part(input.reader, input.tile, input.defaults, input.styles, input.quantizations,
        input.roi, input.progression, input.mct, input.extensions, input.components, input.lengths, input.headers)
}

pub(crate) open spec fn part1_cold_tile_header(input: Part1ColdTileInput<'_>)
    -> (Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'_>) {
    part1_read_tile_header(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers)
}

pub(crate) open spec fn part1_cold_tile_header_input(input: Part1ColdTileInput<'_>) -> Part1ColdTileHeaderInput<'_> {
    Part1ColdTileHeaderInput {
        reader: input.reader, raw: part1_tile_header_initial(input.reader.position, input.defaults.0,
            input.roi, input.progression, input.mct, input.extensions),
        components: input.components, index: input.tile.3, lengths: input.lengths, headers: input.headers,
    }
}

pub(crate) open spec fn part1_cold_tile_header_run(
    input: Part1ColdTileInput<'_>, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'_>), Seq<Part1ColdStorageEvent>)> {
    part1_read_tile_progression_run(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers, events)
}

pub(crate) open spec fn part1_cold_tile_components(
    input: Part1ColdTileInput<'_>, raw: Part1TileHeaderAccumulator, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Part1TileComponentConfiguration, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    part1_tile_components_cold_run(input.components, raw.tile_coding_style, raw.tile_cod_seen,
        raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments,
        input.styles, input.quantizations, raw.part2_extensions, part1_cold_tile_header(input).1.limits, events)
}

pub(crate) open spec fn part1_cold_tile_part_run<'a>(
    input: Part1ColdTileInput<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Part1TilePartResult, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    match part1_cold_tile_header_run(input, events) {
        None => None,
        Some((header, rest)) => part1_cold_tile_part_after_header(input, header, rest),
    }
}

pub(crate) open spec fn part1_cold_tile_part_after_header<'a>(
    input: Part1ColdTileInput<'a>,
    header: (Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>),
    events: Seq<Part1ColdStorageEvent>,
) -> Option<((Part1TilePartResult, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    match header.0 {
        Err(error) => Some(((Err(error), header.1), events)),
        Ok(raw) => if raw.pending_mct.len() != 0 || raw.pending_mcc.len() != 0 {
            Some(((Err(part1_codestream_malformed(
                header.1.position, crate::MalformedKind::MissingRequiredStructure)), header.1), events))
        } else {
            match part1_cold_tile_components(input, raw, events) {
                None => None,
                Some((Err(error), rest)) => Some(((Err(error), header.1), rest)),
                Some((Ok(configuration), rest)) => Some((part1_tile_part_after_configuration(
                    header.1, raw, input.tile, configuration, input.lengths, input.headers), rest)),
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_tile_part_result<'a>(
    input: Part1ColdTileInput<'a>, result: (Part1TilePartResult, Part1CodestreamReader<'a>),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>|
        part1_cold_tile_part_run(input, events) == Some((result, Seq::empty()))
}

pub(crate) open spec fn part1_cold_tile_part_normal_calls(input: Part1ColdTileInput<'_>)
    -> Seq<Part1ColdStorageEvent> {
    part1_read_tile_progression_calls(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers)
        + part1_cold_tile_configuration_calls(input)
}

pub(crate) open spec fn part1_cold_tile_configuration_calls(input: Part1ColdTileInput<'_>)
    -> Seq<Part1ColdStorageEvent> {
    match part1_cold_tile_header(input).0 {
        Err(_) => Seq::empty(),
        Ok(raw) => if raw.pending_mct.len() != 0 || raw.pending_mcc.len() != 0 { Seq::empty() } else {
            part1_tile_components_normal_calls(input.components, raw.tile_coding_style, raw.tile_cod_seen,
                raw.coc_segments, raw.qcd_segment, input.defaults.1, input.styles,
                raw.part2_extensions, part1_cold_tile_header(input).1.limits)
        },
    }
}

pub(crate) proof fn part1_cold_tile_part_normal(input: Part1ColdTileInput<'_>)
    ensures part1_cold_tile_part_result(input, part1_cold_tile_normal(input)),
        forall|tail: Seq<Part1ColdStorageEvent>|
            part1_cold_tile_part_run(input, part1_cold_tile_part_normal_calls(input) + tail)
                == Some((part1_cold_tile_normal(input), tail)),
{
    reveal(part1_cold_tile_part_result);
    reveal(part1_cold_tile_normal);
    reveal(part1_cold_tile_header);
    reveal(part1_cold_tile_components);
    reveal(part1_read_tile_part);
    reveal(part1_finish_tile_part);
    let first = part1_read_tile_progression_normal(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers);
    let header = part1_cold_tile_header(input);
    let events = match header.0 {
        Err(_) => Seq::empty(),
        Ok(raw) => if raw.pending_mct.len() != 0 || raw.pending_mcc.len() != 0 { Seq::empty() } else {
            part1_tile_components_cold_normal(input.components, raw.tile_coding_style, raw.tile_cod_seen,
                raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments,
                input.styles, input.quantizations, raw.part2_extensions, header.1.limits);
            part1_tile_components_normal_calls(input.components, raw.tile_coding_style, raw.tile_cod_seen,
                raw.coc_segments, raw.qcd_segment, input.defaults.1, input.styles,
                raw.part2_extensions, header.1.limits)
        },
    };
    assert(events + Seq::<Part1ColdStorageEvent>::empty() =~= events);
    assert(part1_cold_tile_header_run(input, first + events) == Some((header, events)));
    assert(part1_cold_tile_part_run(input, first + events) == Some((part1_cold_tile_normal(input), Seq::empty())));
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_cold_tile_part_run(input, part1_cold_tile_part_normal_calls(input) + tail)
            == Some((part1_cold_tile_normal(input), tail)) by {
        part1_cold_tile_part_frame(input, first + events, tail, part1_cold_tile_normal(input), Seq::empty());
        assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
    }
}

pub(crate) proof fn part1_cold_tile_part_refused<'a>(
    input: Part1ColdTileInput<'a>, raw: Part1TileHeaderAccumulator,
    reader: Part1CodestreamReader<'a>, error: crate::DecodeError,
)
    requires part1_cold_tile_header(input) == (Ok(raw), reader),
        raw.pending_mct.len() == 0, raw.pending_mcc.len() == 0,
        part1_tile_components_cold_result(input.components, raw.tile_coding_style, raw.tile_cod_seen,
            raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments,
            input.styles, input.quantizations, raw.part2_extensions, reader.limits, Err(error)),
    ensures part1_cold_tile_part_result(input, (Err(error), reader)),
{
    reveal(part1_cold_tile_part_result);
    reveal(part1_cold_tile_header);
    reveal(part1_cold_tile_components);
    reveal(part1_tile_components_cold_result);
    assert(part1_cold_tile_header(input).1.limits == reader.limits);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_tile_components_cold_run(input.components, raw.tile_coding_style, raw.tile_cod_seen,
            raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments,
            input.styles, input.quantizations, raw.part2_extensions, reader.limits, calls)
                == Some((Err(error), Seq::empty()));
    assert(part1_cold_tile_components(input, raw, calls) == Some((Err(error), Seq::empty())));
    let first = part1_read_tile_progression_normal(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers);
    assert(part1_cold_tile_part_run(input, first + calls) == Some(((Err(error), reader), Seq::empty())));
}

pub(crate) proof fn part1_cold_tile_part_calls<'a>(
    input: Part1ColdTileInput<'a>, result: (Part1TilePartResult, Part1CodestreamReader<'a>),
)
    requires part1_cold_tile_part_result(input, result),
    ensures exists|calls: Seq<Part1ColdStorageEvent>|
        part1_cold_tile_part_run(input, calls) == Some((result, Seq::empty())),
{
    reveal(part1_cold_tile_part_result);
}

pub(crate) proof fn part1_cold_tile_part_frame<'a>(
    input: Part1ColdTileInput<'a>, events: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
    result: (Part1TilePartResult, Part1CodestreamReader<'a>), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_tile_part_run(input, events) == Some((result, rest)),
    ensures part1_cold_tile_part_run(input, events + tail) == Some((result, rest + tail)),
{
    if let Some((header, after_header)) = part1_cold_tile_header_run(input, events) {
        part1_read_tile_progression_frame(input.reader, input.defaults.0, input.roi, input.progression,
            input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers,
            events, header, after_header, tail);
        if let Ok(raw) = header.0 {
            part1_read_tile_progression_projection(input.reader, input.defaults.0, input.roi, input.progression,
                input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers,
                events, header, after_header);
            if raw.pending_mct.len() == 0 && raw.pending_mcc.len() == 0 {
                if let Some((configuration, after)) = part1_cold_tile_components(input, raw, after_header) {
                part1_tile_components_cold_frame(input.components, raw.tile_coding_style, raw.tile_cod_seen,
                    raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments,
                    input.styles, input.quantizations, raw.part2_extensions, header.1.limits,
                    after_header, tail, configuration, after);
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_tile_part_projection<'a>(
    input: Part1ColdTileInput<'a>, events: Seq<Part1ColdStorageEvent>,
    result: (Part1TilePartResult, Part1CodestreamReader<'a>), rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_cold_tile_part_run(input, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_cold_tile_normal(input),
{
    reveal(part1_read_tile_part);
    reveal(part1_finish_tile_part);
    if let Some((header, after_header)) = part1_cold_tile_header_run(input, events) {
        part1_read_tile_progression_projection(input.reader, input.defaults.0, input.roi, input.progression,
            input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers,
            events, header, after_header);
        if let Ok(raw) = header.0 {
            if raw.pending_mct.len() == 0 && raw.pending_mcc.len() == 0 {
                if let Some((configuration, after)) = part1_cold_tile_components(input, raw, after_header) {
                part1_tile_components_cold_projection(input.components, raw.tile_coding_style, raw.tile_cod_seen,
                    raw.coc_segments, raw.qcd_segment, input.defaults.1, raw.qcc_segments,
                    input.styles, input.quantizations,                     raw.part2_extensions, header.1.limits, after_header, configuration, after);
                }
            }
        }
    }
}

pub(crate) proof fn part1_cold_tile_header_error<'a>(
    input: Part1ColdTileInput<'a>, error: crate::DecodeError, reader: Part1CodestreamReader<'a>,
)
    requires part1_read_tile_progression_result(part1_cold_tile_header_input(input), (Err(error), reader)),
    ensures part1_cold_tile_part_result(input, (Err(error), reader)),
{
    reveal(part1_read_tile_progression_result);
    reveal(part1_cold_tile_part_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_read_tile_progression_root_run(part1_cold_tile_header_input(input), calls)
            == Some(((Err(error), reader), Seq::empty()));
    assert(part1_cold_tile_header_run(input, calls) == Some(((Err(error), reader), Seq::empty())));
    assert(part1_cold_tile_part_run(input, calls) == Some(((Err(error), reader), Seq::empty())));
}

}
