//! Input-derived cutpoint before the first component-quantization reservation.

use super::*;

verus! {

pub(crate) open spec fn part1_quantization_owner_copy_result(
    source: (u16, Seq<crate::codestream::Quantization>),
    result: Result<crate::codestream::ComponentQuantizations, crate::DecodeError>,
) -> bool {
    match result {
        Err(error) => source.1.len() > 0 && error == crate::DecodeError::AllocationFailed,
        Ok(owner) => crate::codestream::quantization_owner_view(&owner) == source,
    }
}

pub(crate) struct Part1MainQuantizationInput<'a> {
    pub reader: Part1CodestreamReader<'a>,
    pub raw: Part1MainHeaderAccumulator,
    pub frames: Seq<(usize, usize)>,
    pub header: Seq<u8>,
    pub style: Part1ParsedCodingStyle,
    pub quantization: Part2Quantization,
    pub styles: (u16, Seq<Part1ParsedCodingStyle>),
}

pub(crate) type Part1MainQuantizationPreparation<'a> =
    Result<Part1MainQuantizationInput<'a>, crate::DecodeError>;

#[verifier::opaque]
pub(crate) open spec fn part1_main_quantization_after_depths<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
) -> Part1MainQuantizationPreparation<'a> {
    match part1_parse_ppm_frames(raw.ppm, raw.ppm_fragments, reader.limits) {
        Err(error) => Err(error),
        Ok(frames) => if raw.start > reader.position || reader.position > reader.input.len() {
            Err(part1_codestream_malformed(reader.position, crate::MalformedKind::InvalidPackedPacketHeader))
        } else {
            let header = reader.input.subrange(raw.start as int, reader.position as int);
            match raw.coding_style {
                None => Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure)),
                Some(style) => match raw.qcd {
                    None => Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure)),
                    Some(segment) => match part1_parse_qcd_payload(segment.offset, segment.payload, style) {
                        Err(error) => Err(error),
                        Ok(quantization) => match part1_finish_main_styles(
                            raw.image_size.components, style, raw.coc, reader.limits, raw.extensions) {
                            Err(error) => Err(error),
                            Ok(styles) => Ok(Part1MainQuantizationInput {
                                reader, raw, frames, header, style, quantization, styles }),
                        },
                    },
                },
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_quantization_finish<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
) -> Part1MainQuantizationPreparation<'a> {
    if raw.pending_mct.len() != 0 || raw.pending_mcc.len() != 0 {
        Err(part1_codestream_malformed(reader.position, crate::MalformedKind::MissingRequiredStructure))
    } else if raw.plm.len() != 0 && super::part1_incomplete_plm_offset(raw.plm.last()).is_some() {
        Err(part1_codestream_malformed(super::part1_incomplete_plm_offset(raw.plm.last())->Some_0,
            crate::MalformedKind::InvalidMarkerLength))
    } else {
        let depths = part1_apply_component_depths(raw.image_size, raw.extensions.depths, reader.position);
        match depths.0 {
            Err(error) => Err(error),
            Ok(()) => part1_main_quantization_after_depths(
                reader, Part1MainHeaderAccumulator { image_size: depths.1, ..raw }),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_main_quantization_continuation<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, input_length: usize,
) -> Part1MainQuantizationPreparation<'a>
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    match admitted.0 {
        Err(error) => Err(error),
        Ok(None) => part1_main_quantization_finish(admitted.1, changed),
        Ok(Some(segment)) => {
            let step = part1_main_header_payload(admitted.1, changed, segment);
            match step.0 {
                Err(error) => Err(error),
                Ok(()) => if !part1_parser_progress(reader.position, step.1.position, input_length) {
                    Err(part1_codestream_malformed(step.1.position, crate::MalformedKind::InvalidMarkerLength))
                } else { part1_main_quantization_continuation(step.1, step.2, input_length) },
            }
        },
    }
}

pub(crate) open spec fn part1_prepare_main_quantization(reader: Part1CodestreamReader<'_>)
    -> Part1MainQuantizationPreparation<'_> {
    let prologue = part1_parse_layout_prologue(reader);
    match prologue.0 {
        Err(error) => Err(error),
        Ok((size, r_siz, start)) => part1_main_quantization_continuation(prologue.1,
            part1_main_header_initial(size, r_siz, start), prologue.1.input.len() as usize),
    }
}

pub(crate) open spec fn part1_main_quantization_normal_complete<'a>(
    prepared: Part1MainQuantizationPreparation<'a>,
) -> Part1MainHeaderResult<'a> {
    match prepared {
        Err(error) => Err(error),
        Ok(input) => match part1_finish_main_quantizations(
            input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc) {
            Err(error) => Err(error),
            Ok(quantizations) => part1_main_header_after_components(input.reader, input.raw,
                input.frames, input.header, input.style, input.quantization, input.styles, quantizations),
        },
    }
}

pub(crate) proof fn part1_main_quantization_finish_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator,
)
    ensures part1_main_quantization_normal_complete(part1_main_quantization_finish(reader, raw))
        == part1_finish_main_header(reader, raw),
{
    reveal(part1_main_quantization_finish);
    reveal(part1_main_quantization_after_depths);
    reveal(part1_finish_main_header);
    reveal(part1_main_header_after_depths);
}

pub(crate) proof fn part1_main_quantization_continuation_normal<'a>(
    reader: Part1CodestreamReader<'a>, raw: Part1MainHeaderAccumulator, input_length: usize,
)
    ensures part1_main_quantization_normal_complete(
        part1_main_quantization_continuation(reader, raw, input_length))
            == part1_main_header_continuation(reader, raw, input_length),
    decreases if reader.position <= input_length { input_length as int - reader.position as int } else { 0 },
{
    reveal_with_fuel(part1_main_quantization_continuation, 1);
    reveal_with_fuel(part1_main_header_continuation, 1);
    let admitted = part1_read_main_header_segment(reader, raw.segments);
    let changed = Part1MainHeaderAccumulator { segments: admitted.2, ..raw };
    match admitted.0 {
        Err(_) => {},
        Ok(None) => part1_main_quantization_finish_normal(admitted.1, changed),
        Ok(Some(segment)) => {
            let step = part1_main_header_payload(admitted.1, changed, segment);
            if step.0.is_ok() && part1_parser_progress(reader.position, step.1.position, input_length) {
                part1_main_quantization_continuation_normal(step.1, step.2, input_length);
            }
        },
    }
}

pub(crate) proof fn part1_main_quantization_normal(reader: Part1CodestreamReader<'_>)
    ensures part1_main_quantization_normal_complete(part1_prepare_main_quantization(reader))
        == part1_read_main_header(reader),
{
    reveal(part1_read_main_header);
    let prologue = part1_parse_layout_prologue(reader);
    if let Ok((size, r_siz, start)) = prologue.0 {
        part1_main_quantization_continuation_normal(prologue.1,
            part1_main_header_initial(size, r_siz, start), prologue.1.input.len() as usize);
    }
}

pub(crate) open spec fn part1_quantization_storage_request(
    site: u8, elements: usize, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<(), crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    if events.len() == 0 { None } else {
        let response = events[0];
        if response.site != site || response.elements != elements { None }
        else { Some((if response.succeeded { Ok(()) } else {
            Err(crate::DecodeError::AllocationFailed) }, events.drop_first())) }
    }
}

pub(crate) open spec fn part1_main_quantization_reserved<'a>(
    input: Part1MainQuantizationInput<'a>,
) -> Part1MainHeaderResult<'a> {
    match part1_finish_main_quantizations(
        input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc) {
        Err(error) => Err(error),
        Ok(quantizations) => part1_main_header_after_components(input.reader, input.raw,
            input.frames, input.header, input.style, input.quantization, input.styles, quantizations),
    }
}

pub(crate) open spec fn part1_main_quantization_cold_complete<'a>(
    prepared: Part1MainQuantizationPreparation<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1MainHeaderResult<'a>, Seq<Part1ColdStorageEvent>)> {
    match prepared {
        Err(error) => Some((Err(error), events)),
        Ok(input) => if input.raw.image_size.components == 0 || input.raw.image_size.components > 64 {
            part1_main_resolved_run(input, events)
        } else {
            match part1_quantization_storage_request(8, input.raw.image_size.components as usize, events) {
                None => None,
                Some((Err(error), rest)) => Some((Err(error), rest)),
                Some((Ok(()), rest)) => part1_main_resolved_run(input, rest),
            }
        },
    }
}

pub(crate) open spec fn part1_main_header_cold_run<'a>(
    reader: Part1CodestreamReader<'a>, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Part1MainHeaderResult<'a>, Seq<Part1ColdStorageEvent>)> {
    match part1_prepare_main_progression_run(reader, events) {
        None => None,
        Some((prepared, rest)) => part1_main_quantization_cold_complete(prepared, rest),
    }
}

pub(crate) open spec fn part1_main_quantization_normal_calls(
    prepared: Part1MainQuantizationPreparation<'_>,
) -> Seq<Part1ColdStorageEvent> {
    match prepared {
        Err(_) => Seq::empty(),
        Ok(input) => if input.raw.image_size.components == 0 || input.raw.image_size.components > 64 {
            Seq::empty()
        } else {
            seq![Part1ColdStorageEvent {
                site: 8, elements: input.raw.image_size.components as usize, succeeded: true }]
        },
    }
}

pub(crate) proof fn part1_main_header_cold_normal<'a>(
    reader: Part1CodestreamReader<'a>, tail: Seq<Part1ColdStorageEvent>,
)
    ensures part1_main_header_cold_run(reader,
        part1_main_header_normal_calls(reader) + tail)
            == Some((part1_read_main_header(reader), tail)),
{
    part1_main_quantization_normal(reader);
    let first = part1_prepare_main_progression_normal(reader);
    let quantization = part1_main_quantization_normal_calls(part1_prepare_main_quantization(reader));
    let graph = part1_main_resolved_calls(part1_prepare_main_quantization(reader));
    let last = quantization + graph;
    assert(part1_main_header_normal_calls(reader) =~= first + last);
    assert((first + last) + tail =~= first + (last + tail));
    assert(part1_prepare_main_progression_run(reader, first + (last + tail))
        == Some((part1_prepare_main_quantization(reader), last + tail)));
    match part1_prepare_main_quantization(reader) {
        Err(_) => { assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail); },
        Ok(input) => {
            part1_main_resolved_normal(input, tail);
            assert((quantization + graph) + tail =~= quantization + (graph + tail));
            if quantization.len() == 0 { assert(quantization + (graph + tail) =~= graph + tail); }
            else { assert((quantization + (graph + tail)).drop_first() =~= graph + tail); }
        },
    }
}

pub(crate) proof fn part1_main_header_cold_projection<'a>(
    reader: Part1CodestreamReader<'a>, events: Seq<Part1ColdStorageEvent>,
    result: Part1MainHeaderResult<'a>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_header_cold_run(reader, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_read_main_header(reader),
{
    part1_main_quantization_normal(reader);
    if let Some((prepared, after)) = part1_prepare_main_progression_run(reader, events) {
        part1_prepare_main_progression_projection(reader, events, prepared, after);
        if let Ok(input) = prepared {
            if input.raw.image_size.components == 0 || input.raw.image_size.components > 64 {
                part1_main_resolved_projection(input, after, result, rest);
            } else if let Some((copied, after_quantization)) = part1_quantization_storage_request(
                8, input.raw.image_size.components as usize, after) {
                assert(copied == Ok(()));
                part1_main_resolved_projection(input, after_quantization, result, rest);
            }
        }
    }
}

pub(crate) proof fn part1_main_header_cold_frame<'a>(
    reader: Part1CodestreamReader<'a>, events: Seq<Part1ColdStorageEvent>,
    result: Part1MainHeaderResult<'a>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
)
    requires part1_main_header_cold_run(reader, events) == Some((result, rest)),
    ensures part1_main_header_cold_run(reader, events + tail) == Some((result, rest + tail)),
{
    if let Some((prepared, after)) = part1_prepare_main_progression_run(reader, events) {
        part1_prepare_main_progression_frame(reader, events, prepared, after, tail);
        if after.len() > 0 { assert((after + tail).drop_first() =~= after.drop_first() + tail); }
        if let Ok(input) = prepared {
            if input.raw.image_size.components == 0 || input.raw.image_size.components > 64 {
                part1_main_resolved_frame(input, after, result, rest, tail);
            } else if let Some((copied, after_quantization)) = part1_quantization_storage_request(
                8, input.raw.image_size.components as usize, after) {
                if copied.is_ok() { part1_main_resolved_frame(input, after_quantization, result, rest, tail); }
            }
        }
    }
}

pub(crate) open spec fn part1_main_header_normal_calls(reader: Part1CodestreamReader<'_>)
    -> Seq<Part1ColdStorageEvent> {
    part1_prepare_main_progression_calls(reader)
        + part1_main_quantization_normal_calls(part1_prepare_main_quantization(reader))
        + part1_main_resolved_calls(part1_prepare_main_quantization(reader))
}

}
