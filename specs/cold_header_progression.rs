//! POC allocation responses inside the actual main/tile header traversals.

use super::*;

verus! {

pub(crate) open spec fn part1_main_progression_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    if segment.marker == 0xff5f && !raw.poc_seen {
        let changed = Part1MainHeaderAccumulator { poc_seen: true, ..raw };
        match part1_poc_cold_run(12, segment, raw.image_size.components, events) {
            None => None,
            Some((Err(error), rest)) => Some(((Err(error), reader, changed), rest)),
            Some((Ok(progression), rest)) => Some(((Ok(()), reader,
                Part1MainHeaderAccumulator { progression, ..changed }), rest)),
        }
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_main_payload(reader, raw, segment, events)
    } else if part1_p2_marker(segment.marker) { part1_p2_main_run(reader, raw, segment, events) }
    else if segment.marker == 0xff50 || segment.marker == 0xff56 || segment.marker == 0xff59 { part1_profile_main_run(reader, raw, segment, events) }
    else { Some((part1_main_header_payload(reader, raw, segment), events)) }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_progression_continuation<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    input_length: usize, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1MainQuantizationPreparation<'a>, Seq<Part1ColdStorageEvent>)>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    match admitted.0 {
        Err(error) => Some((Err(error), events)),
        Ok(None) => Some((part1_main_quantization_finish(admitted.1, changed), events)),
        Ok(Some(segment)) => match part1_main_progression_payload(admitted.1, changed, segment, events) {
            None => None,
            Some((step, rest)) => match step.0 {
                Err(error) => Some((Err(error), rest)),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    Some((Err(part1_codestream_malformed(
                        step.1.position, crate::MalformedKind::InvalidMarkerLength)), rest))
                } else { part1_main_progression_continuation(step.1, step.2, input_length, rest) },
            },
        },
    }
}

pub(crate) open spec fn part1_prepare_main_progression_run<'a>(
    reader: Part1CodestreamReader<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1MainQuantizationPreparation<'a>, Seq<Part1ColdStorageEvent>)> {
    let prologue = part1_parse_layout_prologue(reader);
    match prologue.0 {
        Err(error) => Some((Err(error), events)),
        Ok((size, r_siz, start)) => part1_main_progression_continuation(prologue.1,
            part1_main_header_initial(size, r_siz, start), prologue.1.input.len() as usize, events),
    }
}

pub(crate) open spec fn part1_tile_progression_payload<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        let changed = Part1TileHeaderAccumulator { poc_seen: true, ..raw };
        match part1_poc_cold_run(13, segment, components, events) {
            None => None,
            Some((Err(error), rest)) => Some(((Err(error), reader, changed), rest)),
            Some((Ok(progression_changes), rest)) => Some(((Ok(()), reader,
                Part1TileHeaderAccumulator { progression_changes, ..changed }), rest)),
        }
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_tile_payload(reader, raw, segment, components, events)
    } else if part1_p2_marker(segment.marker) { part1_p2_tile_run(reader, raw, segment, components, events) }
    else { Some((part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers), events)) }
}

pub(crate) open spec fn part1_tile_progression_dispatch<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    let changed = Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58),
        ..raw
    };
    part1_tile_progression_payload(reader, changed, segment, components, tile_part_index, lengths, headers, events)
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_progression_traversal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    components: u16, tile_part_index: u8, lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    input_length: usize, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), Seq<Part1ColdStorageEvent>)>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_tile_header_segment(reader);
    match admitted.0 {
        Err(error) => Some(((Err(error), admitted.1, raw), events)),
        Ok(None) => Some(((Ok(()), admitted.1,
            Part1TileHeaderAccumulator { tile_header_end: reader.position, ..raw }), events)),
        Ok(Some(segment)) => match part1_tile_progression_dispatch(
            admitted.1, raw, segment, components, tile_part_index, lengths, headers, events) {
            None => None,
            Some((step, rest)) => match step.0 {
                Err(_) => Some((step, rest)),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    Some(((Err(part1_codestream_malformed(
                        step.1.position, crate::MalformedKind::InvalidTilePart)), step.1, step.2), rest))
                } else { part1_tile_progression_traversal(
                    step.1, step.2, components, tile_part_index, lengths, headers, input_length, rest) },
            },
        },
    }
}

pub(crate) open spec fn part1_read_tile_progression_run<'a>(
    reader: Part1CodestreamReader<'a>, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    match part1_tile_progression_traversal(reader,
        part1_tile_header_initial(reader.position, style, roi, progression, mct, extensions),
        components, tile_part_index, lengths, headers, reader.input.len() as usize, events) {
        None => None,
        Some((result, rest)) => Some(((match result.0 {
            Err(error) => Err(error), Ok(()) => Ok(result.2),
        }, result.1), rest)),
    }
}

pub(crate) open spec fn part1_main_progression_payload_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
) -> Seq<Part1ColdStorageEvent> {
    if segment.marker == 0xff5f && !raw.poc_seen {
        part1_poc_normal_calls(12, segment, raw.image_size.components)
    } else if part1_p2_marker(segment.marker) { part1_p2_main_calls(reader, raw, segment) }
    else if segment.marker == 0xff50 || segment.marker == 0xff56 || segment.marker == 0xff59 { part1_profile_main_calls(raw, segment) }
    else { part1_fresh_main_calls(reader, raw, segment) }
}

pub(crate) proof fn part1_main_progression_payload_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_main_progression_payload(reader, raw, segment,
        part1_main_progression_payload_calls(reader, raw, segment) + tail)
            == Some((part1_main_header_payload(reader, raw, segment), tail)),
{
    reveal(part1_main_header_payload);
    if segment.marker == 0xff5f && !raw.poc_seen {
        part1_poc_cold_normal(12, segment, raw.image_size.components, tail);
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_main_normal(reader, raw, segment, tail);
    } else if part1_p2_marker(segment.marker) {
        part1_p2_main_normal(reader, raw, segment, tail);
    } else if segment.marker == 0xff50 || segment.marker == 0xff56 || segment.marker == 0xff59 {
        part1_profile_main_normal(reader, raw, segment, tail);
    } else { assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail); }
}

pub(crate) proof fn part1_main_progression_continuation_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, input_length: usize,
) -> (calls: Seq<Part1ColdStorageEvent>)
    ensures calls == part1_main_progression_continuation_calls(reader, raw, input_length),
        forall|tail: Seq<Part1ColdStorageEvent>|
        part1_main_progression_continuation(reader, raw, input_length, calls + tail)
            == Some((part1_main_quantization_continuation(reader, raw, input_length), tail)),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_main_progression_continuation, 1);
    reveal_with_fuel(part1_main_quantization_continuation, 1);
    reveal_with_fuel(part1_main_progression_continuation_calls, 1);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    match admitted.0 {
        Err(_) => Seq::empty(),
        Ok(None) => Seq::empty(),
        Ok(Some(segment)) => {
            let first = part1_main_progression_payload_calls(admitted.1, changed, segment);
            let step = part1_main_header_payload(admitted.1, changed, segment);
            let rest = if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_main_progression_continuation_normal(step.1, step.2, input_length)
            } else { Seq::empty() };
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_main_progression_continuation(reader, raw, input_length, (first + rest) + tail)
                    == Some((part1_main_quantization_continuation(reader, raw, input_length), tail)) by {
                assert((first + rest) + tail =~= first + (rest + tail));
                part1_main_progression_payload_normal(admitted.1, changed, segment, rest + tail);
                reveal_with_fuel(part1_main_progression_continuation, 1);
                reveal_with_fuel(part1_main_quantization_continuation, 1);
            }
            first + rest
        },
    }
}

pub(crate) proof fn part1_prepare_main_progression_normal(reader: Part1CodestreamReader<'_>)
    -> (calls: Seq<Part1ColdStorageEvent>)
    ensures calls == part1_prepare_main_progression_calls(reader),
        forall|tail: Seq<Part1ColdStorageEvent>|
        part1_prepare_main_progression_run(reader, calls + tail)
            == Some((part1_prepare_main_quantization(reader), tail)),
{
    let prologue = part1_parse_layout_prologue(reader);
    match prologue.0 {
        Err(_) => Seq::empty(),
        Ok((size, r_siz, start)) => part1_main_progression_continuation_normal(prologue.1,
            part1_main_header_initial(size, r_siz, start), prologue.1.input.len() as usize),
    }
}

pub(crate) open spec fn part1_tile_progression_payload_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1TileHeaderAccumulator, segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
) -> Seq<Part1ColdStorageEvent> {
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        part1_poc_normal_calls(13, segment, components)
    } else if part1_p2_marker(segment.marker) { part1_p2_tile_calls(reader, raw, segment, components) }
    else { part1_fresh_tile_calls(reader, raw, segment, components) }
}

pub(crate) proof fn part1_tile_progression_payload_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers,
        part1_tile_progression_payload_calls(reader, raw, segment, components, tile_part_index) + tail)
            == Some((part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers), tail)),
{
    reveal(part1_tile_header_payload);
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        part1_poc_cold_normal(13, segment, components, tail);
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_tile_normal(reader, raw, segment, components, tail);
    } else if part1_p2_marker(segment.marker) {
        part1_p2_tile_normal(reader, raw, segment, components, tail);
    } else { assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail); }
}

pub(crate) proof fn part1_tile_progression_dispatch_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_tile_progression_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers,
        part1_tile_progression_payload_calls(reader, raw, segment, components, tile_part_index) + tail)
            == Some((part1_tile_header_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers), tail)),
{
    reveal(part1_tile_header_dispatch);
    let changed = Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58),
        ..raw
    };
    part1_tile_progression_payload_normal(reader, changed, segment, components, tile_part_index, lengths, headers, tail);
}

pub(crate) proof fn part1_tile_progression_traversal_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, input_length: usize,
) -> (calls: Seq<Part1ColdStorageEvent>)
    ensures calls == part1_tile_progression_traversal_calls(
            reader, raw, components, tile_part_index, lengths, headers, input_length),
        forall|tail: Seq<Part1ColdStorageEvent>|
        part1_tile_progression_traversal(reader, raw, components, tile_part_index, lengths, headers, input_length, calls + tail)
            == Some((part1_tile_header_traversal(reader, raw, components, tile_part_index, lengths, headers, input_length), tail)),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_tile_progression_traversal, 1);
    reveal_with_fuel(part1_tile_header_traversal, 1);
    reveal_with_fuel(part1_tile_progression_traversal_calls, 1);
    let admitted = part1_read_tile_header_segment(reader);
    match admitted.0 {
        Err(_) => Seq::empty(),
        Ok(None) => Seq::empty(),
        Ok(Some(segment)) => {
            let first = part1_tile_progression_payload_calls(admitted.1, raw, segment, components, tile_part_index);
            let step = part1_tile_header_dispatch(admitted.1, raw, segment, components, tile_part_index, lengths, headers);
            let rest = if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_tile_progression_traversal_normal(
                    step.1, step.2, components, tile_part_index, lengths, headers, input_length)
            } else { Seq::empty() };
            assert forall|tail: Seq<Part1ColdStorageEvent>|
                part1_tile_progression_traversal(reader, raw, components, tile_part_index, lengths, headers,
                    input_length, (first + rest) + tail)
                    == Some((part1_tile_header_traversal(
                        reader, raw, components, tile_part_index, lengths, headers, input_length), tail)) by {
                assert((first + rest) + tail =~= first + (rest + tail));
                part1_tile_progression_dispatch_normal(admitted.1, raw, segment, components, tile_part_index,
                    lengths, headers, rest + tail);
                reveal_with_fuel(part1_tile_progression_traversal, 1);
                reveal_with_fuel(part1_tile_header_traversal, 1);
            }
            first + rest
        },
    }
}

pub(crate) proof fn part1_read_tile_progression_normal<'a>(
    reader: Part1CodestreamReader<'a>, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
) -> (calls: Seq<Part1ColdStorageEvent>)
    ensures calls == part1_read_tile_progression_calls(
            reader, style, roi, progression, mct, extensions, components, tile_part_index, lengths, headers),
        forall|tail: Seq<Part1ColdStorageEvent>|
        part1_read_tile_progression_run(reader, style, roi, progression, mct, extensions,
            components, tile_part_index, lengths, headers, calls + tail)
            == Some((part1_read_tile_header(reader, style, roi, progression, mct, extensions,
                components, tile_part_index, lengths, headers), tail)),
{
    reveal(part1_read_tile_header);
    part1_tile_progression_traversal_normal(reader,
        part1_tile_header_initial(reader.position, style, roi, progression, mct, extensions),
        components, tile_part_index, lengths, headers, reader.input.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_progression_continuation_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1MainHeaderAccumulator, input_length: usize,
) -> Seq<Part1ColdStorageEvent>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    match admitted.0 {
        Err(_) => Seq::empty(),
        Ok(None) => Seq::empty(),
        Ok(Some(segment)) => {
            let step = part1_main_header_payload(admitted.1, changed, segment);
            part1_main_progression_payload_calls(admitted.1, changed, segment) +
                if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                    part1_main_progression_continuation_calls(step.1, step.2, input_length)
                } else { Seq::empty() }
        },
    }
}

pub(crate) open spec fn part1_prepare_main_progression_calls(reader: Part1CodestreamReader<'_>)
    -> Seq<Part1ColdStorageEvent> {
    let prologue = part1_parse_layout_prologue(reader);
    match prologue.0 {
        Err(_) => Seq::empty(),
        Ok((size, r_siz, start)) => part1_main_progression_continuation_calls(prologue.1,
            part1_main_header_initial(size, r_siz, start), prologue.1.input.len() as usize),
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_progression_traversal_calls(
    reader: Part1CodestreamReader<'_>, raw: Part1TileHeaderAccumulator, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, input_length: usize,
) -> Seq<Part1ColdStorageEvent>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_tile_header_segment(reader);
    match admitted.0 {
        Err(_) => Seq::empty(),
        Ok(None) => Seq::empty(),
        Ok(Some(segment)) => {
            let step = part1_tile_header_dispatch(admitted.1, raw, segment, components, tile_part_index, lengths, headers);
            part1_tile_progression_payload_calls(admitted.1, raw, segment, components, tile_part_index) +
                if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                    part1_tile_progression_traversal_calls(
                        step.1, step.2, components, tile_part_index, lengths, headers, input_length)
                } else { Seq::empty() }
        },
    }
}

pub(crate) open spec fn part1_read_tile_progression_calls<'a>(
    reader: Part1CodestreamReader<'a>, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
) -> Seq<Part1ColdStorageEvent> {
    part1_tile_progression_traversal_calls(reader,
        part1_tile_header_initial(reader.position, style, roi, progression, mct, extensions),
        components, tile_part_index, lengths, headers, reader.input.len() as usize)
}

pub(crate) proof fn part1_main_progression_payload_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_progression_payload(reader, raw, segment, events) == Some((result, rest)),
    ensures part1_main_progression_payload(reader, raw, segment, events + tail) == Some((result, rest + tail)),
{
    if segment.marker == 0xff5f && !raw.poc_seen {
        if let Some((parsed, after)) = part1_poc_cold_run(12, segment, raw.image_size.components, events) {
            part1_poc_cold_frame(12, segment, raw.image_size.components, events, parsed, after, tail);
        }
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_main_frame(reader, raw, segment, events, result, rest, tail);
    } else if part1_p2_marker(segment.marker) {
        part1_p2_main_frame(reader, raw, segment, events, result, rest, tail);
    } else if segment.marker == 0xff50 || segment.marker == 0xff56 || segment.marker == 0xff59 {
        part1_profile_main_frame(reader, raw, segment, events, result, rest, tail);
    }
}

pub(crate) proof fn part1_main_progression_payload_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, segment: Part1CodestreamSegment,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1MainHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_progression_payload(reader, raw, segment, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_main_header_payload(reader, raw, segment),
{
    reveal(part1_main_header_payload);
    if segment.marker == 0xff5f && !raw.poc_seen {
        if let Some((parsed, after)) = part1_poc_cold_run(12, segment, raw.image_size.components, events) {
            part1_poc_cold_projection(12, segment, raw.image_size.components, events, parsed, after);
        }
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_main_projection(reader, raw, segment, events, result, rest);
    } else if part1_p2_marker(segment.marker) {
        part1_p2_main_projection(reader, raw, segment, events, result, rest);
    } else if segment.marker == 0xff50 || segment.marker == 0xff56 || segment.marker == 0xff59 {
        part1_profile_main_projection(reader, raw, segment, events, result, rest);
    }
}

pub(crate) proof fn part1_main_progression_continuation_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, input_length: usize,
    events: Seq<Part1ColdStorageEvent>, result: Part1MainQuantizationPreparation<'a>,
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_progression_continuation(reader, raw, input_length, events) == Some((result, rest)),
    ensures part1_main_progression_continuation(reader, raw, input_length, events + tail) == Some((result, rest + tail)),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_main_progression_continuation, 1);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    if let Ok(Some(segment)) = admitted.0 {
        if let Some((step, after)) = part1_main_progression_payload(admitted.1, changed, segment, events) {
            part1_main_progression_payload_frame(admitted.1, changed, segment, events, step, after, tail);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_main_progression_continuation_frame(step.1, step.2, input_length, after, result, rest, tail);
            }
        }
    }
}

pub(crate) proof fn part1_main_progression_continuation_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, input_length: usize,
    events: Seq<Part1ColdStorageEvent>, result: Part1MainQuantizationPreparation<'a>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_progression_continuation(reader, raw, input_length, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_main_quantization_continuation(reader, raw, input_length),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_main_progression_continuation, 1);
    reveal_with_fuel(part1_main_quantization_continuation, 1);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    if let Ok(Some(segment)) = admitted.0 {
        if let Some((step, after)) = part1_main_progression_payload(admitted.1, changed, segment, events) {
            part1_main_progression_payload_projection(admitted.1, changed, segment, events, step, after);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_main_progression_continuation_projection(step.1, step.2, input_length, after, result, rest);
            }
        }
    }
}

pub(crate) proof fn part1_prepare_main_progression_frame<'a>(
    reader: Part1CodestreamReader<'a>, events: Seq<Part1ColdStorageEvent>,
    result: Part1MainQuantizationPreparation<'a>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_prepare_main_progression_run(reader, events) == Some((result, rest)),
    ensures part1_prepare_main_progression_run(reader, events + tail) == Some((result, rest + tail)),
{
    let prologue = part1_parse_layout_prologue(reader);
    if let Ok((size, r_siz, start)) = prologue.0 {
        part1_main_progression_continuation_frame(prologue.1, part1_main_header_initial(size, r_siz, start),
            prologue.1.input.len() as usize, events, result, rest, tail);
    }
}

pub(crate) proof fn part1_prepare_main_progression_projection<'a>(
    reader: Part1CodestreamReader<'a>, events: Seq<Part1ColdStorageEvent>,
    result: Part1MainQuantizationPreparation<'a>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_prepare_main_progression_run(reader, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_prepare_main_quantization(reader),
{
    let prologue = part1_parse_layout_prologue(reader);
    if let Ok((size, r_siz, start)) = prologue.0 {
        part1_main_progression_continuation_projection(prologue.1, part1_main_header_initial(size, r_siz, start),
            prologue.1.input.len() as usize, events, result, rest);
    }
}

pub(crate) open spec fn part1_cold_main_prefix_at<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    prefix: Seq<Part1ColdStorageEvent>,
) -> bool {
    forall|tail: Seq<Part1ColdStorageEvent>|
        #[trigger] part1_prepare_main_progression_run(initial, prefix + tail)
            == part1_main_progression_continuation(
                reader, raw, part1_parse_layout_prologue(initial).1.input.len() as usize, tail)
}

#[verifier::opaque]
pub(crate) open spec fn part1_cold_main_prefix<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
) -> bool {
    exists|prefix: Seq<Part1ColdStorageEvent>|
        #[trigger] part1_cold_main_prefix_at(initial, reader, raw, prefix)
}

pub(crate) proof fn part1_cold_main_start<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
)
    requires match part1_parse_layout_prologue(initial) {
        (Ok((size, r_siz, start)), after) => reader == after && raw == part1_main_header_initial(size, r_siz, start),
        _ => false,
    },
    ensures part1_cold_main_prefix(initial, reader, raw),
{
    reveal(part1_cold_main_prefix);
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_prepare_main_progression_run(initial, Seq::empty() + tail)
            == part1_main_progression_continuation(
                reader, raw, part1_parse_layout_prologue(initial).1.input.len() as usize, tail) by {
        assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
    }
    assert(part1_cold_main_prefix_at(initial, reader, raw, Seq::empty()));
}

pub(crate) proof fn part1_cold_main_advance<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    next: Part1CodestreamReader<'a>, changed: Part1MainHeaderAccumulator,
)
    requires part1_cold_main_prefix(initial, reader, raw),
        match part1_read_main_header_segment(reader, raw.segments) {
            (Ok(Some(segment)), after, segments) =>
                part1_main_header_payload(after, Part1MainHeaderAccumulator { segments, ..raw }, segment)
                    == (Ok(()), next, changed),
            _ => false,
        },
        part1_parser_progress(reader.position, next.position, part1_parse_layout_prologue(initial).1.input.len() as usize),
    ensures part1_cold_main_prefix(initial, next, changed),
{
    reveal(part1_cold_main_prefix);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>|
        part1_cold_main_prefix_at(initial, reader, raw, prefix);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    if let Ok(Some(segment)) = admitted.0 {
        let before = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
        let calls = part1_main_progression_payload_calls(admitted.1, before, segment);
        assert forall|tail: Seq<Part1ColdStorageEvent>|
            part1_prepare_main_progression_run(initial, (prefix + calls) + tail)
                == part1_main_progression_continuation(
                    next, changed, part1_parse_layout_prologue(initial).1.input.len() as usize, tail) by {
            assert((prefix + calls) + tail =~= prefix + (calls + tail));
            part1_main_progression_payload_normal(admitted.1, before, segment, tail);
            reveal_with_fuel(part1_main_progression_continuation, 1);
        }
        assert(part1_cold_main_prefix_at(initial, next, changed, prefix + calls));
    }
}

pub(crate) proof fn part1_cold_main_poc_error<'a>(
    initial: Part1CodestreamReader<'a>, reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
    segment: Part1CodestreamSegment, error: crate::DecodeError,
)
    requires part1_cold_main_prefix(initial, reader, raw),
        part1_read_main_header_segment(reader, raw.segments).0 == Ok(Some(segment)),
        segment.marker == 0xff5f, !raw.poc_seen,
        part1_parse_poc_storage_result(segment, raw.image_size.components, Err(error)),
    ensures part1_cold_layout_result(initial, Err(error)),
{
    reveal(part1_cold_main_prefix);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>|
        part1_cold_main_prefix_at(initial, reader, raw, prefix);
    let calls = part1_poc_cold_observed(12, segment, raw.image_size.components, Err(error));
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    reveal_with_fuel(part1_main_progression_continuation, 1);
    assert(part1_prepare_main_progression_run(initial, prefix + calls) == Some((Err(error), Seq::empty())));
    reveal(part1_cold_layout_result);
    assert(part1_layout_with_cold_storage(initial, prefix + calls) == Some((Err(error), Seq::empty())));
}

pub(crate) proof fn part1_tile_progression_payload_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, events)
        == Some((result, rest)),
    ensures part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, events + tail)
        == Some((result, rest + tail)),
{
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        if let Some((parsed, after)) = part1_poc_cold_run(13, segment, components, events) {
            part1_poc_cold_frame(13, segment, components, events, parsed, after, tail);
        }
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_tile_frame(reader, raw, segment, components, events, result, rest, tail);
    } else if part1_p2_marker(segment.marker) {
        part1_p2_tile_frame(reader, raw, segment, components, events, result, rest, tail);
    }
}

pub(crate) proof fn part1_tile_progression_payload_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, events)
        == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers),
{
    reveal(part1_tile_header_payload);
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        if let Some((parsed, after)) = part1_poc_cold_run(13, segment, components, events) {
            part1_poc_cold_projection(13, segment, components, events, parsed, after);
        }
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_tile_projection(reader, raw, segment, components, events, result, rest);
    } else if part1_p2_marker(segment.marker) {
        part1_p2_tile_projection(reader, raw, segment, components, events, result, rest);
    }
}

pub(crate) proof fn part1_tile_progression_dispatch_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_progression_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers, events)
        == Some((result, rest)),
    ensures part1_tile_progression_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers, events + tail)
        == Some((result, rest + tail)),
{
    part1_tile_progression_payload_frame(reader, Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58), ..raw
    }, segment, components, tile_part_index, lengths, headers, events, result, rest, tail);
}

pub(crate) proof fn part1_tile_progression_dispatch_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_progression_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers, events)
        == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_header_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers),
{
    reveal(part1_tile_header_dispatch);
    part1_tile_progression_payload_projection(reader, Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58), ..raw
    }, segment, components, tile_part_index, lengths, headers, events, result, rest);
}

pub(crate) proof fn part1_tile_progression_traversal_frame<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    components: u16, tile_part_index: u8, lengths: Part1PacketLengths, headers: Part1PackedHeaders, input_length: usize,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_progression_traversal(reader, raw, components, tile_part_index, lengths, headers, input_length, events)
        == Some((result, rest)),
    ensures part1_tile_progression_traversal(reader, raw, components, tile_part_index, lengths, headers, input_length, events + tail)
        == Some((result, rest + tail)),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_tile_progression_traversal, 1);
    let admitted = part1_read_tile_header_segment(reader);
    if let Ok(Some(segment)) = admitted.0 {
        if let Some((step, after)) = part1_tile_progression_dispatch(
            admitted.1, raw, segment, components, tile_part_index, lengths, headers, events) {
            part1_tile_progression_dispatch_frame(admitted.1, raw, segment, components, tile_part_index,
                lengths, headers, events, step, after, tail);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_tile_progression_traversal_frame(step.1, step.2, components, tile_part_index,
                    lengths, headers, input_length, after, result, rest, tail);
            }
        }
    }
}

pub(crate) proof fn part1_tile_progression_traversal_projection<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    components: u16, tile_part_index: u8, lengths: Part1PacketLengths, headers: Part1PackedHeaders, input_length: usize,
    events: Seq<Part1ColdStorageEvent>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_progression_traversal(reader, raw, components, tile_part_index, lengths, headers, input_length, events)
        == Some((result, rest)), result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_tile_header_traversal(reader, raw, components, tile_part_index, lengths, headers, input_length),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_tile_progression_traversal, 1);
    reveal_with_fuel(part1_tile_header_traversal, 1);
    let admitted = part1_read_tile_header_segment(reader);
    if let Ok(Some(segment)) = admitted.0 {
        if let Some((step, after)) = part1_tile_progression_dispatch(
            admitted.1, raw, segment, components, tile_part_index, lengths, headers, events) {
            part1_tile_progression_dispatch_projection(
                admitted.1, raw, segment, components, tile_part_index, lengths, headers, events, step, after);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_tile_progression_traversal_projection(step.1, step.2, components, tile_part_index,
                    lengths, headers, input_length, after, result, rest);
            }
        }
    }
}

pub(crate) proof fn part1_read_tile_progression_frame<'a>(
    reader: Part1CodestreamReader<'a>, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_read_tile_progression_run(reader, style, roi, progression, mct, extensions,
        components, tile_part_index, lengths, headers, events) == Some((result, rest)),
    ensures part1_read_tile_progression_run(reader, style, roi, progression, mct, extensions,
        components, tile_part_index, lengths, headers, events + tail) == Some((result, rest + tail)),
{
    let raw = part1_tile_header_initial(reader.position, style, roi, progression, mct, extensions);
    if let Some((step, after)) = part1_tile_progression_traversal(
        reader, raw, components, tile_part_index, lengths, headers, reader.input.len() as usize, events) {
        part1_tile_progression_traversal_frame(reader, raw, components, tile_part_index,
            lengths, headers, reader.input.len() as usize, events, step, after, tail);
    }
}

pub(crate) proof fn part1_read_tile_progression_projection<'a>(
    reader: Part1CodestreamReader<'a>, style: Part1ParsedCodingStyle, roi: Seq<u8>,
    progression: Seq<crate::codestream::ProgressionChange>, mct: Part1MctParameters,
    extensions: Part2OwnedExtensions, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, events: Seq<Part1ColdStorageEvent>,
    result: (Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>),
    rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_read_tile_progression_run(reader, style, roi, progression, mct, extensions,
        components, tile_part_index, lengths, headers, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_read_tile_header(reader, style, roi, progression, mct, extensions,
        components, tile_part_index, lengths, headers),
{
    reveal(part1_read_tile_header);
    let raw = part1_tile_header_initial(reader.position, style, roi, progression, mct, extensions);
    if let Some((step, after)) = part1_tile_progression_traversal(
        reader, raw, components, tile_part_index, lengths, headers, reader.input.len() as usize, events) {
        part1_tile_progression_traversal_projection(reader, raw, components, tile_part_index,
            lengths, headers, reader.input.len() as usize, events, step, after);
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_progression_payload_result<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_tile_progression_payload(
        reader, raw, segment, components, tile_part_index, lengths, headers, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_tile_progression_payload_normal_result<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
)
    ensures part1_tile_progression_payload_result(reader, raw, segment, components, tile_part_index, lengths, headers,
        part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers)),
{
    reveal(part1_tile_progression_payload_result);
    part1_tile_progression_payload_normal(reader, raw, segment, components, tile_part_index, lengths, headers, Seq::empty());
    let calls = part1_tile_progression_payload_calls(reader, raw, segment, components, tile_part_index);
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
}

pub(crate) proof fn part1_tile_progression_payload_error<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, error: crate::DecodeError,
)
    requires segment.marker == 0xff5f, !raw.poc_seen,
        part1_parse_poc_storage_result(segment, components, Err(error)),
    ensures part1_tile_progression_payload_result(reader, raw, segment, components, 0, lengths, headers,
        (Err(error), reader, Part1TileHeaderAccumulator { poc_seen: true, ..raw })),
{
    reveal(part1_tile_progression_payload_result);
    let calls = part1_poc_cold_observed(13, segment, components, Err(error));
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_poc_cold_run(13, segment, components, calls) == Some((Err(error), Seq::empty())));
    assert(part1_tile_progression_payload(reader, raw, segment, components, 0, lengths, headers, calls)
        == Some(((Err(error), reader, Part1TileHeaderAccumulator { poc_seen: true, ..raw }), Seq::empty())));
}

pub(crate) proof fn part1_tile_progression_payload_normal_rule<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
)
    ensures forall|result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator)|
        result == part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers)
            ==> #[trigger] part1_tile_progression_payload_result(
                reader, raw, segment, components, tile_part_index, lengths, headers, result),
{
    part1_tile_progression_payload_normal_result(reader, raw, segment, components, tile_part_index, lengths, headers);
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_progression_dispatch_result<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_tile_progression_dispatch(
        reader, raw, segment, components, tile_part_index, lengths, headers, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_tile_progression_dispatch_observed<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
)
    requires part1_tile_progression_payload_result(reader, Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58),
        ..raw }, segment, components, tile_part_index, lengths, headers, result),
    ensures part1_tile_progression_dispatch_result(reader, raw, segment, components, tile_part_index, lengths, headers, result),
{
    reveal(part1_tile_progression_payload_result);
    reveal(part1_tile_progression_dispatch_result);
    let before = Part1TileHeaderAccumulator {
        has_functional_header_marker: raw.has_functional_header_marker || (segment.marker != 0xff64 && segment.marker != 0xff58), ..raw };
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_tile_progression_payload(
        reader, before, segment, components, tile_part_index, lengths, headers, calls) == Some((result, Seq::empty()));
    assert(part1_tile_progression_dispatch(reader, raw, segment, components, tile_part_index, lengths, headers, calls)
        == Some((result, Seq::empty())));
}

pub(crate) struct Part1ColdTileHeaderInput<'a> {
    pub reader: Part1CodestreamReader<'a>,
    pub raw: Part1TileHeaderAccumulator,
    pub components: u16,
    pub index: u8,
    pub lengths: Part1PacketLengths,
    pub headers: Part1PackedHeaders,
}

pub(crate) open spec fn part1_tile_progression_root_run<'a>(
    input: Part1ColdTileHeaderInput<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator), Seq<Part1ColdStorageEvent>)> {
    part1_tile_progression_traversal(input.reader, input.raw, input.components, input.index,
        input.lengths, input.headers, input.reader.input.len() as usize, events)
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_progression_result<'a>(
    input: Part1ColdTileHeaderInput<'a>,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_tile_progression_root_run(input, events) == Some((result, Seq::empty()))
}

pub(crate) open spec fn part1_tile_progression_prefix_at<'a>(
    input: Part1ColdTileHeaderInput<'a>, reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    prefix: Seq<Part1ColdStorageEvent>,
) -> bool {
    forall|tail: Seq<Part1ColdStorageEvent>|
        #[trigger] part1_tile_progression_root_run(input, prefix + tail)
            == part1_tile_progression_traversal(reader, raw, input.components, input.index,
                input.lengths, input.headers, input.reader.input.len() as usize, tail)
}

#[verifier::opaque]
pub(crate) open spec fn part1_tile_progression_prefix<'a>(
    input: Part1ColdTileHeaderInput<'a>, reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
) -> bool {
    exists|prefix: Seq<Part1ColdStorageEvent>| #[trigger] part1_tile_progression_prefix_at(input, reader, raw, prefix)
}

pub(crate) proof fn part1_tile_progression_start(input: Part1ColdTileHeaderInput<'_>)
    ensures part1_tile_progression_prefix(input, input.reader, input.raw),
{
    reveal(part1_tile_progression_prefix);
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_tile_progression_root_run(input, Seq::empty() + tail)
            == part1_tile_progression_traversal(input.reader, input.raw, input.components, input.index,
                input.lengths, input.headers, input.reader.input.len() as usize, tail) by {
        assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
    }
    assert(part1_tile_progression_prefix_at(input, input.reader, input.raw, Seq::empty()));
}

pub(crate) proof fn part1_tile_progression_finish<'a>(
    input: Part1ColdTileHeaderInput<'a>, reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
)
    requires part1_tile_progression_prefix(input, reader, raw),
        !matches!(part1_read_tile_header_segment(reader).0, Ok(Some(_))),
    ensures part1_tile_progression_result(input, match part1_read_tile_header_segment(reader) {
        (Err(error), after) => (Err(error), after, raw),
        (Ok(None), after) => (Ok(()), after, Part1TileHeaderAccumulator { tile_header_end: reader.position, ..raw }),
        _ => (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidMarker)), reader, raw),
    }),
{
    reveal(part1_tile_progression_prefix);
    reveal(part1_tile_progression_result);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_tile_progression_prefix_at(input, reader, raw, prefix);
    assert(prefix + Seq::<Part1ColdStorageEvent>::empty() =~= prefix);
    reveal_with_fuel(part1_tile_progression_traversal, 1);
    let result = match part1_read_tile_header_segment(reader) {
        (Err(error), after) => (Err(error), after, raw),
        (Ok(None), after) => (Ok(()), after, Part1TileHeaderAccumulator { tile_header_end: reader.position, ..raw }),
        _ => (Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidMarker)), reader, raw),
    };
    assert(part1_tile_progression_root_run(input, prefix) == Some((result, Seq::empty())));
}

pub(crate) proof fn part1_tile_progression_step<'a>(
    input: Part1ColdTileHeaderInput<'a>, reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment,
    step: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
)
    requires part1_tile_progression_prefix(input, reader, raw),
        part1_read_tile_header_segment(reader).0 == Ok(Some(segment)),
        part1_tile_progression_dispatch_result(part1_read_tile_header_segment(reader).1, raw, segment,
            input.components, input.index, input.lengths, input.headers, step),
    ensures if step.0.is_err() { part1_tile_progression_result(input, step) }
        else if part1_parser_progress(reader.position, step.1.position, input.reader.input.len() as usize) {
            part1_tile_progression_prefix(input, step.1, step.2)
        } else { part1_tile_progression_result(input,
            (Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidTilePart)), step.1, step.2)) },
{
    reveal(part1_tile_progression_prefix);
    reveal(part1_tile_progression_dispatch_result);
    reveal(part1_tile_progression_result);
    let prefix = choose|prefix: Seq<Part1ColdStorageEvent>| part1_tile_progression_prefix_at(input, reader, raw, prefix);
    let admitted = part1_read_tile_header_segment(reader);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_tile_progression_dispatch(admitted.1, raw, segment, input.components, input.index, input.lengths,
            input.headers, calls) == Some((step, Seq::empty()));
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_tile_progression_root_run(input, (prefix + calls) + tail)
            == if step.0.is_err() { Some((step, tail)) }
            else if part1_parser_progress(reader.position, step.1.position, input.reader.input.len() as usize) {
                part1_tile_progression_traversal(step.1, step.2, input.components, input.index,
                    input.lengths, input.headers, input.reader.input.len() as usize, tail)
            } else { Some(((Err(part1_codestream_malformed(
                step.1.position, crate::MalformedKind::InvalidTilePart)), step.1, step.2), tail)) } by {
        assert((prefix + calls) + tail =~= prefix + (calls + tail));
        part1_tile_progression_dispatch_frame(admitted.1, raw, segment, input.components, input.index,
            input.lengths, input.headers, calls, step, Seq::empty(), tail);
        assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
        reveal_with_fuel(part1_tile_progression_traversal, 1);
    }
    assert((prefix + calls) + Seq::<Part1ColdStorageEvent>::empty() =~= prefix + calls);
    if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input.reader.input.len() as usize) {
        assert(part1_tile_progression_prefix_at(input, step.1, step.2, prefix + calls));
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_read_tile_progression_result<'a>(
    input: Part1ColdTileHeaderInput<'a>,
    result: (Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>),
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_read_tile_progression_root_run(input, events) == Some((result, Seq::empty()))
}

pub(crate) open spec fn part1_read_tile_progression_root_run<'a>(
    input: Part1ColdTileHeaderInput<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<((Result<Part1TileHeaderAccumulator, crate::DecodeError>, Part1CodestreamReader<'a>), Seq<Part1ColdStorageEvent>)> {
    match part1_tile_progression_root_run(input, events) {
        Some((step, rest)) => Some(((match step.0 { Ok(()) => Ok(step.2), Err(error) => Err(error) }, step.1), rest)),
        None => None,
    }
}

pub(crate) proof fn part1_read_tile_progression_observed<'a>(
    input: Part1ColdTileHeaderInput<'a>,
    step: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
)
    requires part1_tile_progression_result(input, step),
    ensures part1_read_tile_progression_result(input,
        (match step.0 { Ok(()) => Ok(step.2), Err(error) => Err(error) }, step.1)),
{
    reveal(part1_read_tile_progression_result);
    reveal(part1_tile_progression_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_tile_progression_root_run(input, calls)
        == Some((step, Seq::empty()));
    assert(part1_read_tile_progression_root_run(input, calls)
        == Some(((match step.0 { Ok(()) => Ok(step.2), Err(error) => Err(error) }, step.1), Seq::empty())));
}

pub(crate) open spec fn part1_tile_progression_payload_storage<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, reserved: bool,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator) {
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        let changed = Part1TileHeaderAccumulator { poc_seen: true, ..raw };
        match part1_parse_poc_storage(segment, components, reserved) {
            Err(error) => (Err(error), reader, changed),
            Ok(progression_changes) => (Ok(()), reader, Part1TileHeaderAccumulator { progression_changes, ..changed }),
        }
    } else { part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers) }
}

pub(crate) open spec fn part1_tile_progression_payload_storage_result<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
) -> bool {
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        exists|reserved: bool| result == part1_tile_progression_payload_storage(
            reader, raw, segment, components, tile_part_index, lengths, headers, reserved)
    } else if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_tile_result(reader, raw, segment, components, result)
    } else if part1_p2_marker(segment.marker) {
        part1_p2_tile_result(reader, raw, segment, components, result)
    } else { result == part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers) }
}

pub(crate) proof fn part1_tile_progression_payload_storage_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
)
    ensures part1_tile_progression_payload_storage_result(reader, raw, segment, components, tile_part_index, lengths, headers,
        part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers)),
{
    reveal(part1_tile_header_payload);
    if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        part1_fresh_tile_normal_result(reader, raw, segment, components);
    }
    if part1_p2_marker(segment.marker) { part1_p2_tile_normal_result(reader, raw, segment, components); }
    assert(part1_tile_progression_payload_storage(reader, raw, segment, components, tile_part_index, lengths, headers, true)
        == part1_tile_header_payload(reader, raw, segment, components, tile_part_index, lengths, headers));
}

pub(crate) proof fn part1_tile_progression_payload_storage_error<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders, error: crate::DecodeError,
)
    requires segment.marker == 0xff5f, !raw.poc_seen,
        part1_parse_poc_storage_result(segment, components, Err(error)),
    ensures part1_tile_progression_payload_storage_result(reader, raw, segment, components, 0, lengths, headers,
        (Err(error), reader, Part1TileHeaderAccumulator { poc_seen: true, ..raw })),
{
    let reserved = choose|reserved: bool| part1_parse_poc_storage(segment, components, reserved) == Err(error);
    assert(part1_tile_progression_payload_storage(reader, raw, segment, components, 0, lengths, headers, reserved)
        == (Err(error), reader, Part1TileHeaderAccumulator { poc_seen: true, ..raw }));
}

pub(crate) proof fn part1_tile_progression_payload_storage_observed<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16, tile_part_index: u8,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part1TileHeaderAccumulator),
)
    requires part1_tile_progression_payload_storage_result(
        reader, raw, segment, components, tile_part_index, lengths, headers, result),
    ensures part1_tile_progression_payload_result(
        reader, raw, segment, components, tile_part_index, lengths, headers, result),
{
    reveal(part1_tile_progression_payload_result);
    if part1_p2_marker(segment.marker) {
        reveal(part1_p2_tile_result);
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_tile_run(reader, raw, segment, components, calls) == Some((result, Seq::empty()));
        assert(part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, calls) == Some((result, Seq::empty())));
        return;
    }
    if segment.marker == 0xff74 || segment.marker == 0xff75 || segment.marker == 0xff77 {
        reveal(part1_fresh_tile_result);
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_fresh_tile_payload(reader, raw, segment, components, calls) == Some((result, Seq::empty()));
        assert(part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, calls) == Some((result, Seq::empty())));
        return;
    }
    if !(segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0) {
        assert(result == part1_tile_progression_payload_storage(
            reader, raw, segment, components, tile_part_index, lengths, headers, true));
    }
    let reserved = choose|reserved: bool| result == part1_tile_progression_payload_storage(
        reader, raw, segment, components, tile_part_index, lengths, headers, reserved);
    if segment.marker == 0xff5f && !raw.poc_seen && tile_part_index == 0 {
        let parsed = part1_parse_poc_storage(segment, components, reserved);
        part1_parse_poc_storage_observed(segment, components, reserved, parsed);
        let calls = part1_poc_cold_observed(13, segment, components, parsed);
        assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
        assert(part1_poc_cold_run(13, segment, components, calls) == Some((parsed, Seq::empty())));
        assert(part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, calls)
            == Some((result, Seq::empty())));
    } else {
        assert(part1_tile_progression_payload(reader, raw, segment, components, tile_part_index, lengths, headers, Seq::empty())
            == Some((result, Seq::empty())));
    }
}

pub(crate) proof fn part1_tile_progression_payload_storage_leaf<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1TileHeaderAccumulator,
    segment: Part1CodestreamSegment, components: u16,
    lengths: Part1PacketLengths, headers: Part1PackedHeaders,
    parsed: Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>,
)
    requires segment.marker == 0xff5f, !raw.poc_seen,
        part1_parse_poc_storage_result(segment, components, parsed),
    ensures part1_tile_progression_payload_storage_result(reader, raw, segment, components, 0, lengths, headers,
        match parsed {
            Err(error) => (Err(error), reader, Part1TileHeaderAccumulator { poc_seen: true, ..raw }),
            Ok(progression_changes) => (Ok(()), reader,
                Part1TileHeaderAccumulator { progression_changes, poc_seen: true, ..raw }),
        }),
{
    let reserved = choose|reserved: bool| part1_parse_poc_storage(segment, components, reserved) == parsed;
    let result = match parsed {
        Err(error) => (Err(error), reader, Part1TileHeaderAccumulator { poc_seen: true, ..raw }),
        Ok(progression_changes) => (Ok(()), reader,
            Part1TileHeaderAccumulator { progression_changes, poc_seen: true, ..raw }),
    };
    assert(part1_tile_progression_payload_storage(reader, raw, segment, components, 0, lengths, headers, reserved) == result);
}

}
