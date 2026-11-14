//! Compressed-byte typed and strict reconstruction composition, without native-layout banks.

use super::*;

verus! {

pub(crate) type Part2ColdRun<T> =
    Option<(Result<T, crate::DecodeError>, Seq<Part2JpipSnapshotEvent>)>;

pub(crate) open spec fn part2_cold_prefix<T>(
    run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    prefix: Seq<Part2JpipSnapshotEvent>,
    result: Result<T, crate::DecodeError>,
) -> bool {
    forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] run(prefix + tail) == Some((result, tail))
}

pub(crate) open spec fn part2_cold_framed<T>(
    run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    result: Result<T, crate::DecodeError>,
) -> bool {
    exists|prefix: Seq<Part2JpipSnapshotEvent>| #[trigger] part2_cold_prefix(run, prefix, result)
}

pub(crate) proof fn part2_cold_prefix_at<T>(
    run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    prefix: Seq<Part2JpipSnapshotEvent>, result: Result<T, crate::DecodeError>,
    tail: Seq<Part2JpipSnapshotEvent>,
)
    requires part2_cold_prefix(run, prefix, result),
    ensures run(prefix + tail) == Some((result, tail)),
{
    reveal(part2_cold_prefix);
}

pub(crate) proof fn part2_cold_witness<T>(
    run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    result: Result<T, crate::DecodeError>,
) -> (prefix: Seq<Part2JpipSnapshotEvent>)
    requires part2_cold_framed(run, result),
    ensures part2_cold_prefix(run, prefix, result),
        run(prefix) == Some((result, Seq::empty())),
        forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] run(prefix + tail) == Some((result, tail)),
{
    let prefix = choose|prefix: Seq<Part2JpipSnapshotEvent>| #[trigger] part2_cold_prefix(run, prefix, result);
    part2_cold_prefix_at(run, prefix, result, Seq::empty());
    assert(prefix + Seq::empty() =~= prefix);
    prefix
}

pub(crate) open spec fn part2_cold_parse(
    input: Seq<u8>, limits: &crate::ResourceLimits, phase: u8, index: usize,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1CompleteLayout> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipSnapshotEvent::Parse { phase: actual, index: at, calls } =>
                if actual != phase || at != index { None } else {
                    match part1_parse_layout_with_cold_storage(input, limits, calls) {
                        Some((result, rest)) => if rest.len() == 0 {
                            Some((result, events.drop_first()))
                        } else { None },
                        None => None,
                    }
                },
            _ => None,
        }
    }
}

pub(crate) proof fn part2_cold_parse_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, phase: u8, index: usize,
    result: Part1CompleteLayoutResult,
)
    requires part1_parse_layout_cold_result(input, limits, result),
    ensures part2_cold_framed(
        |events| part2_cold_parse(input, limits, phase, index, events), result),
{
    part1_parse_layout_cold_calls(input, limits, result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_parse_layout_with_cold_storage(input, limits, calls) == Some((result, Seq::empty()));
    let prefix = seq![Part2JpipSnapshotEvent::Parse { phase, index, calls }];
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_cold_parse(input, limits, phase, index, prefix + tail)
            == Some((result, tail)) by {
        assert((prefix + tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(
        |events| part2_cold_parse(input, limits, phase, index, events), prefix, result));
}

pub(crate) proof fn part2_cold_pure<T>(result: Result<T, crate::DecodeError>)
    ensures part2_cold_framed(|events| Some((result, events)), result),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events) == Some((result, events)))
                ==> #[trigger] part2_cold_framed(run, result),
{
    let prefix: Seq<Part2JpipSnapshotEvent> = Seq::empty();
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        prefix + tail == tail by {};
    assert(part2_cold_prefix(|events| Some((result, events)), prefix, result));
    assert forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
        (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events) == Some((result, events)))
            implies #[trigger] part2_cold_framed(run, result) by {
        assert(part2_cold_prefix(run, prefix, result));
    }
}

pub(crate) proof fn part2_cold_framed_extensional<T>(
    first: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    second: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>,
    result: Result<T, crate::DecodeError>,
)
    requires part2_cold_framed(first, result),
        forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] second(events) == first(events),
    ensures part2_cold_framed(second, result),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events) == second(events))
                ==> #[trigger] part2_cold_framed(run, result),
{
    assert(first =~= second);
    let prefix = choose|prefix: Seq<Part2JpipSnapshotEvent>| #[trigger] part2_cold_prefix(first, prefix, result);
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] second(prefix + tail) == Some((result, tail)) by {};
    assert(part2_cold_prefix(second, prefix, result));
    assert forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
        (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events) == second(events))
            implies #[trigger] part2_cold_framed(run, result) by {
        assert forall|tail: Seq<Part2JpipSnapshotEvent>|
            #[trigger] run(prefix + tail) == Some((result, tail)) by {};
        assert(part2_cold_prefix(run, prefix, result));
    }
}

pub(crate) proof fn part2_cold_bind<A, B>(
    first: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<A>,
    next: spec_fn(A, Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>,
    intermediate: Result<A, crate::DecodeError>, result: Result<B, crate::DecodeError>,
)
    requires part2_cold_framed(first, intermediate),
        match intermediate {
            Err(error) => result == Err(error),
            Ok(value) => part2_cold_framed(|events| next(value, events), result),
        },
    ensures part2_cold_framed(
        |events| part2_jpip_snapshot_bind(first(events), next), result),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>|
            (forall|events: Seq<Part2JpipSnapshotEvent>|
                #[trigger] run(events) == part2_jpip_snapshot_bind(first(events), next))
                ==> #[trigger] part2_cold_framed(run, result),
{
    let prefix = part2_cold_witness(first, intermediate);
    match intermediate {
        Err(error) => {
            assert forall|tail: Seq<Part2JpipSnapshotEvent>|
                #[trigger] part2_jpip_snapshot_bind(first(prefix + tail), next)
                    == Some((result, tail)) by {};
            assert(part2_cold_prefix(
                |events| part2_jpip_snapshot_bind(first(events), next), prefix, result));
        },
        Ok(value) => {
            let next_run = |events| next(value, events);
            let suffix = part2_cold_witness(next_run, result);
            assert forall|tail: Seq<Part2JpipSnapshotEvent>|
                #[trigger] part2_jpip_snapshot_bind(first((prefix + suffix) + tail), next)
                    == Some((result, tail)) by {
                assert((prefix + suffix) + tail =~= prefix + (suffix + tail));
                part2_cold_prefix_at(first, prefix, intermediate, suffix + tail);
                part2_cold_prefix_at(next_run, suffix, result, tail);
                assert(first((prefix + suffix) + tail) == Some((Ok(value), suffix + tail)));
                assert(next(value, suffix + tail) == Some((result, tail)));
            }
            assert(part2_cold_prefix(
                |events| part2_jpip_snapshot_bind(first(events), next), prefix + suffix, result));
        },
    }
    assert forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<B>|
        (forall|events: Seq<Part2JpipSnapshotEvent>|
            #[trigger] run(events) == part2_jpip_snapshot_bind(first(events), next))
            implies #[trigger] part2_cold_framed(run, result) by {
        part2_cold_framed_extensional(
            |events| part2_jpip_snapshot_bind(first(events), next), run, result);
    }
}

pub(crate) open spec fn part2_cold_parse_finish<T>(
    parsed: Part1CompleteLayoutResult,
    finish: spec_fn(Part1CompleteLayout) -> Result<T, crate::DecodeError>,
) -> Result<T, crate::DecodeError> {
    match parsed { Err(error) => Err(error), Ok(layout) => finish(layout) }
}

pub(crate) proof fn part2_cold_parse_then_actual<T>(
    input: Seq<u8>, limits: &crate::ResourceLimits, phase: u8, index: usize,
    parsed: Part1CompleteLayoutResult,
    finish: spec_fn(Part1CompleteLayout) -> Result<T, crate::DecodeError>,
)
    requires part1_parse_layout_cold_result(input, limits, parsed),
    ensures part2_cold_framed(
        |events| part2_jpip_snapshot_bind(part2_cold_parse(input, limits, phase, index, events),
            |layout: Part1CompleteLayout, rest| Some((finish(layout), rest))),
        part2_cold_parse_finish(parsed, finish)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<T>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_jpip_snapshot_bind(part2_cold_parse(input, limits, phase, index, events),
                    |layout: Part1CompleteLayout, rest| Some((finish(layout), rest))))
                ==> #[trigger] part2_cold_framed(run, part2_cold_parse_finish(parsed, finish)),
{
    part2_cold_parse_actual(input, limits, phase, index, parsed);
    if let Ok(layout) = parsed { part2_cold_pure(finish(layout)); }
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, phase, index, events),
        |layout: Part1CompleteLayout, rest| Some((finish(layout), rest)),
        parsed, match parsed { Err(error) => Err(error), Ok(layout) => finish(layout) });
}

pub(crate) open spec fn part2_cold_info(
    input: Seq<u8>, limits: &crate::ResourceLimits, phase: u8, index: usize,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2RawCodestreamInfo> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipSnapshotEvent::Parse { phase: actual, index: at, calls } =>
                if actual != phase || at != index { None } else {
                    match part1_parse_info_with_cold_storage(input, limits, calls) {
                        Some((result, rest)) => if rest.len() == 0 {
                            Some((result, events.drop_first()))
                        } else { None },
                        None => None,
                    }
                },
            _ => None,
        }
    }
}

pub(crate) proof fn part2_cold_info_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, phase: u8, index: usize,
    result: Result<Part2RawCodestreamInfo, crate::DecodeError>,
)
    requires part1_parse_info_cold_result(input, limits, result),
    ensures part2_cold_framed(
        |events| part2_cold_info(input, limits, phase, index, events), result),
{
    part1_parse_info_cold_calls(input, limits, result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>|
        part1_parse_info_with_cold_storage(input, limits, calls) == Some((result, Seq::empty()));
    let prefix = seq![Part2JpipSnapshotEvent::Parse { phase, index, calls }];
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_cold_info(input, limits, phase, index, prefix + tail)
            == Some((result, tail)) by {
        assert((prefix + tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(
        |events| part2_cold_info(input, limits, phase, index, events), prefix, result));
}

pub(crate) proof fn part2_cold_info_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, phase: u8, index: usize,
)
    ensures part2_cold_framed(
        |events| part2_cold_info(input, limits, phase, index, events), part1_parse_info(input, limits)),
{
    part1_parse_layout_cold_normal(input, limits);
    part1_parse_info_cold_projection(input, limits, part1_parse_layout(input, limits));
    part1_parse_info_unfold(input, limits);
    part2_cold_info_actual(input, limits, phase, index, part1_parse_info(input, limits));
}

pub(crate) open spec fn part2_decode_raw_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 2, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested), rest)))
}

pub closed spec fn part2_decode_raw_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
    result: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_decode_raw_cold_run(input, limits, requested, events), result)
}

pub(crate) proof fn part2_decode_raw_cold_frames(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
    result: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_decode_raw_cold_result(input, limits, requested, result),
    ensures part2_cold_framed(|events| part2_decode_raw_cold_run(input, limits, requested, events), result),
{
    reveal(part2_decode_raw_cold_result);
}

pub(crate) open spec fn part2_decode_raw_value_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedTypedImage> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 2, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_typed_layout_value_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested), rest)))
}

pub(crate) open spec fn part2_decode_raw_value_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
    result: Result<Part1DecodedTypedImage, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_decode_raw_value_cold_run(input, limits, requested, events), result)
}

pub(crate) proof fn part2_decode_raw_cold_to_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
    result: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_decode_raw_cold_result(input, limits, requested, result),
    ensures part2_decode_raw_value_cold_result(input, limits,
        match requested { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) }, result),
{
    part2_decode_raw_cold_frames(input, limits, requested, result);
    let selected = match requested { None => None, Some(value) => Some(crate::options::decode_selection_view(value)) };
    let run = |events| part2_decode_raw_value_cold_run(input, limits, selected, events);
    part2_cold_framed_extensional(
        |events| part2_decode_raw_cold_run(input, limits, requested, events),
        run, result);
    let prefix = part2_cold_witness(run, result);
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_decode_raw_value_cold_run(input, limits, selected, prefix + tail)
            == Some((result, tail)) by {
        part2_cold_prefix_at(run, prefix, result, tail);
    }
    assert(part2_cold_prefix(
        |events| part2_decode_raw_value_cold_run(input, limits, selected, events), prefix, result));
}

pub(crate) proof fn part2_decode_raw_value_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
)
    ensures part2_decode_raw_value_cold_result(input, limits, requested,
        part2_decode_raw_codestream_value(input, limits, requested)),
{
    reveal(part2_decode_raw_codestream_value);
    part1_parse_layout_cold_normal(input, limits);
    part2_cold_parse_then_actual(input, limits, 2, 0, part1_parse_layout(input, limits),
        |layout: Part1CompleteLayout| part2_decode_typed_layout_value_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested));
}

pub(crate) proof fn part2_decode_raw_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
)
    ensures part2_decode_raw_cold_result(
        input, limits, requested, part2_decode_raw_codestream(input, limits, requested)),
{
    reveal(part2_decode_raw_cold_result);
    part1_parse_layout_cold_normal(input, limits);
    let parsed = part1_parse_layout(input, limits);
    part2_cold_parse_actual(input, limits, 2, 0, parsed);
    if let Ok(layout) = parsed {
        part2_cold_pure(part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested));
    }
    part2_decode_raw_codestream_unfold(input, limits, requested);
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 2, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested), rest)),
        parsed, part2_decode_raw_codestream(input, limits, requested));
}

pub(crate) proof fn part2_decode_raw_cold_parse_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
    error: crate::DecodeError,
)
    requires part1_parse_layout_cold_result(input, limits, Err(error)),
    ensures part2_decode_raw_cold_result(input, limits, requested, Err(error)),
{
    reveal(part2_decode_raw_cold_result);
    part2_cold_parse_actual(input, limits, 2, 0, Err(error));
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 2, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested), rest)),
        Err(error), Err(error));
}

pub(crate) open spec fn part2_decode_reconstructed_cold_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 8, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_reconstructed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits), rest)))
}

pub closed spec fn part2_decode_reconstructed_cold_result(
    input: Seq<u8>, limits: &crate::ResourceLimits,
    result: Result<Part1DecodedImageModel, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_decode_reconstructed_cold_run(input, limits, events), result)
}

pub(crate) proof fn part2_decode_reconstructed_cold_frames(
    input: Seq<u8>, limits: &crate::ResourceLimits, result: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part2_decode_reconstructed_cold_result(input, limits, result),
    ensures part2_cold_framed(|events| part2_decode_reconstructed_cold_run(input, limits, events), result),
{
    reveal(part2_decode_reconstructed_cold_result);
}

pub(crate) proof fn part2_decode_reconstructed_cold_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_decode_reconstructed_cold_result(
        input, limits, part2_decode_raw_reconstructed_codestream(input, limits)),
{
    reveal(part2_decode_reconstructed_cold_result);
    part1_parse_layout_cold_normal(input, limits);
    let parsed = part1_parse_layout(input, limits);
    part2_cold_parse_actual(input, limits, 8, 0, parsed);
    if let Ok(layout) = parsed {
        part2_cold_pure(part2_decode_reconstructed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits));
    }
    part2_decode_raw_reconstructed_codestream_unfold(input, limits);
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 8, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_reconstructed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits), rest)),
        parsed, part2_decode_raw_reconstructed_codestream(input, limits));
}

pub(crate) proof fn part2_decode_reconstructed_cold_parse_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part1_parse_layout_cold_result(input, limits, Err(error)),
    ensures part2_decode_reconstructed_cold_result(input, limits, Err(error)),
{
    reveal(part2_decode_reconstructed_cold_result);
    part2_cold_parse_actual(input, limits, 8, 0, Err(error));
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 8, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_decode_reconstructed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits), rest)),
        Err(error), Err(error));
}

pub open spec fn part1_validate_reconstructed_output_components(
    components: Seq<Part1DecodedComponentModel>, component: nat,
) -> Result<(), crate::DecodeError>
    decreases components.len() - component,
{
    if component >= components.len() { Ok(()) } else {
        let output = components[component as int];
        if !part1_component_output_shape_valid(output.0, output.1, output.4.len() as usize) {
            Err(part1_block_placement_error(false))
        } else { part1_validate_reconstructed_output_components(components, component + 1) }
    }
}

pub open spec fn part1_validate_reconstructed_output_shape(
    input_bytes: usize, tile_parts: usize, expected_components: u16, image: Part1DecodedImageModel,
) -> Result<(), crate::DecodeError> {
    if !part1_decode_output_shape_valid(
        input_bytes, tile_parts, expected_components, image.4.len() as usize, image.0, image.1,
    ) { Err(part1_block_placement_error(false)) }
    else { part1_validate_reconstructed_output_components(image.4, 0) }
}

pub(crate) open spec fn part2_validate_reconstruction_transforms(
    input: Part2DecoderLayoutInput,
) -> Result<(), crate::DecodeError> {
    if input.main_extensions.nonlinear.len() != 0
        || exists |i: int| 0 <= i < input.parts.len()
            && input.parts[i].part2_extensions.nonlinear.len() != 0
    {
        Err(crate::DecodeError::UnsupportedFeature {
            feature: "nonlinear transforms on reconstruction samples",
        })
    } else { Ok(()) }
}

pub(crate) open spec fn part2_decode_reconstructed_layout_input(
    input_bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_decode_layout_input(input, limits) {
        Err(error) => Err(error),
        Ok(image) => match part2_validate_reconstruction_transforms(input) {
            Err(error) => Err(error),
            Ok(()) => match part1_validate_reconstructed_output_shape(
                input_bytes, input.parts.len() as usize, input.size.components, image,
            ) {
                Err(error) => Err(error), Ok(()) => Ok(image),
            },
        },
    }
}

pub closed spec fn part2_decode_raw_codestream(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
    }
}

pub(crate) proof fn part2_decode_raw_codestream_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<&crate::DecodeSelection>,
)
    ensures part2_decode_raw_codestream(input, limits, requested) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_typed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
    },
{
}

pub(crate) closed spec fn part2_decode_raw_codestream_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: Option<Part2DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_typed_layout_value_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, requested),
    }
}

pub(crate) proof fn part2_decode_raw_codestream_selection_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, requested: &crate::DecodeSelection,
)
    ensures part2_decode_raw_codestream(input, limits, Some(requested))
        == part2_decode_raw_codestream_value(input, limits, Some(crate::options::decode_selection_view(requested))),
{
    reveal(part2_decode_raw_codestream);
    reveal(part2_decode_raw_codestream_value);
}

pub(crate) proof fn part2_decode_raw_codestream_selection_none(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_decode_raw_codestream(input, limits, None)
        == part2_decode_raw_codestream_value(input, limits, None),
{
    reveal(part2_decode_raw_codestream);
    reveal(part2_decode_raw_codestream_value);
}

pub closed spec fn part2_decode_raw_reconstructed_codestream(
    input: Seq<u8>, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_decode_reconstructed_layout_input(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits),
    }
}

pub(crate) proof fn part2_decode_raw_reconstructed_codestream_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits,
)
    ensures part2_decode_raw_reconstructed_codestream(input, limits)
        == match part1_parse_layout(input, limits) {
            Err(error) => Err(error),
            Ok(layout) => part2_decode_reconstructed_layout_input(
                input.len() as usize, part2_decoder_input_from_raw(layout), limits),
        },
{
}

}
