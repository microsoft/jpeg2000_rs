//! Actual selected raw reconstruction without an intermediate typed image.
use super::*;
verus! {
pub(crate) open spec fn part2_selected_reconstruction_layout_run(
    bytes: usize, input: Part2DecoderLayoutInput, limits: &crate::ResourceLimits,
    selected: Part2DecodeSelection, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_layout_decode_run(input, Some(selected), limits, events),
        |image: Part1DecodedImageModel, rest|
            Some((part2_reconstructed_decode_finish(bytes, input, image), rest)))
}

pub(crate) open spec fn part2_selected_reconstruction_value_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, selected: Part2DecodeSelection,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 10, 0, events),
        |layout: Part1CompleteLayout, rest| part2_selected_reconstruction_layout_run(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits,
            selected, rest))
}

pub(crate) open spec fn part2_selected_reconstruction_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_selected_reconstruction_value_run(
        input, limits, crate::options::decode_selection_view(selection), events)
}

pub closed spec fn part2_selected_reconstruction_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    result: Result<Part1DecodedImageModel, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_selected_reconstruction_run(input, limits, selection, events), result)
}

pub(crate) open spec fn part2_selected_reconstruction_selected_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, selected: Part2DecodeSelection,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(layout) => {
            let source = part2_decoder_input_from_raw(layout);
            match part2_decode_layout_selected_value_input(
                source, selected, limits) {
                Err(error) => Err(error),
                Ok(image) => part2_reconstructed_decode_finish(input.len() as usize, source, image),
            }
        },
    }
}

pub closed spec fn part2_selected_reconstruction_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    part2_selected_reconstruction_selected_value(input, limits, crate::options::decode_selection_view(selection))
}

pub(crate) proof fn part2_selected_reconstruction_value_frames(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    result: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part2_selected_reconstruction_result(input, limits, selection, result),
    ensures part2_cold_framed(
        |events| part2_selected_reconstruction_value_run(
            input, limits, crate::options::decode_selection_view(selection), events), result),
{
    reveal(part2_selected_reconstruction_result);
    part2_cold_framed_extensional(
        |events| part2_selected_reconstruction_run(input, limits, selection, events),
        |events| part2_selected_reconstruction_value_run(
            input, limits, crate::options::decode_selection_view(selection), events), result);
}

pub(crate) proof fn part2_selected_reconstruction_value_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, selected: Part2DecodeSelection,
)
    ensures part2_cold_framed(
        |events| part2_selected_reconstruction_value_run(input, limits, selected, events),
        part2_selected_reconstruction_selected_value(input, limits, selected)),
{
    let parsed = part1_parse_layout(input, limits);
    part1_parse_layout_cold_normal(input, limits);
    part2_cold_parse_actual(input, limits, 10, 0, parsed);
    if let Ok(layout) = parsed {
        let source = part2_decoder_input_from_raw(layout);
        let decoded = part2_decode_layout_selected_value_input(source, selected, limits);
        part2_layout_decode_normal(source, Some(selected), limits);
        reveal(part2_layout_decode_result);
        if let Ok(image) = decoded {
            part2_cold_pure(part2_reconstructed_decode_finish(input.len() as usize, source, image));
        }
        part2_cold_bind(
            |events| part2_layout_decode_run(source, Some(selected), limits, events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_reconstructed_decode_finish(input.len() as usize, source, image), rest)),
            decoded, part2_selected_reconstruction_selected_value(input, limits, selected));
    }
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 10, 0, events),
        |layout: Part1CompleteLayout, rest| part2_selected_reconstruction_layout_run(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, selected, rest),
        parsed, part2_selected_reconstruction_selected_value(input, limits, selected));
}

pub(crate) proof fn part2_selected_reconstruction_value_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
)
    ensures part2_selected_reconstruction_value(input, limits, selection) ==
        match part1_parse_layout(input, limits) {
            Err(error) => Err(error),
            Ok(layout) => {
                let source = part2_decoder_input_from_raw(layout);
                match part2_decode_layout_selected_value_input(
                    source, crate::options::decode_selection_view(selection), limits) {
                    Err(error) => Err(error),
                    Ok(image) => part2_reconstructed_decode_finish(input.len() as usize, source, image),
                }
            },
        },
        part2_selected_reconstruction_value(input, limits, selection)
            == part2_selected_reconstruction_selected_value(
                input, limits, crate::options::decode_selection_view(selection)),
{}

pub(crate) proof fn part2_selected_reconstruction_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
)
    ensures part2_selected_reconstruction_result(
        input, limits, selection, part2_selected_reconstruction_value(input, limits, selection)),
{
    reveal(part2_selected_reconstruction_result);
    part2_selected_reconstruction_value_unfold(input, limits, selection);
    let parsed = part1_parse_layout(input, limits);
    let selected = crate::options::decode_selection_view(selection);
    part1_parse_layout_cold_normal(input, limits);
    part2_cold_parse_actual(input, limits, 10, 0, parsed);
    if let Ok(layout) = parsed {
        let source = part2_decoder_input_from_raw(layout);
        let decoded = part2_decode_layout_selected_value_input(source, selected, limits);
        part2_layout_decode_normal(source, Some(selected), limits);
        reveal(part2_layout_decode_result);
        if let Ok(image) = decoded {
            part2_cold_pure(part2_reconstructed_decode_finish(input.len() as usize, source, image));
        }
        part2_cold_bind(
            |events| part2_layout_decode_run(source, Some(selected), limits, events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_reconstructed_decode_finish(input.len() as usize, source, image), rest)),
            decoded, part2_selected_reconstruction_value(input, limits, selection));
    }
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 10, 0, events),
        |layout: Part1CompleteLayout, rest| part2_selected_reconstruction_layout_run(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, selected, rest),
        parsed, part2_selected_reconstruction_value(input, limits, selection));
}

pub(crate) proof fn part2_selected_reconstruction_parse_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    error: crate::DecodeError,
)
    requires part1_parse_layout_cold_result(input, limits, Err(error)),
    ensures part2_selected_reconstruction_result(input, limits, selection, Err(error)),
{
    reveal(part2_selected_reconstruction_result);
    part2_cold_parse_actual(input, limits, 10, 0, Err(error));
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 10, 0, events),
        |layout: Part1CompleteLayout, rest| part2_selected_reconstruction_layout_run(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits,
            crate::options::decode_selection_view(selection), rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_selected_reconstruction_layout_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    error: crate::DecodeError,
)
    requires part1_parse_layout(input, limits).is_ok(),
        part1_parse_layout_cold_result(input, limits, part1_parse_layout(input, limits)),
        match part1_parse_layout(input, limits) {
            Err(_) => false,
            Ok(layout) => part2_layout_decode_result(part2_decoder_input_from_raw(layout),
                Some(crate::options::decode_selection_view(selection)), limits, Err(error)),
        },
    ensures part2_selected_reconstruction_result(input, limits, selection, Err(error)),
{
    reveal(part2_selected_reconstruction_result); reveal(part2_layout_decode_result);
    let parsed = part1_parse_layout(input, limits);
    let selected = crate::options::decode_selection_view(selection);
    part2_cold_parse_actual(input, limits, 10, 0, parsed);
    if let Ok(layout) = parsed {
        let source = part2_decoder_input_from_raw(layout);
        part2_cold_bind(
            |events| part2_layout_decode_run(source, Some(selected), limits, events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_reconstructed_decode_finish(input.len() as usize, source, image), rest)),
            Err(error), Err(error));
    }
    part2_cold_bind(
        |events| part2_cold_parse(input, limits, 10, 0, events),
        |layout: Part1CompleteLayout, rest| part2_selected_reconstruction_layout_run(
            input.len() as usize, part2_decoder_input_from_raw(layout), limits, selected, rest),
        parsed, Err(error));
}

pub(crate) open spec fn part2_selected_jp2_reconstruction_after_inspection(
    inspected: Part2RawInspectedContainer, limits: &crate::ResourceLimits,
    selection: &crate::DecodeSelection, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    match part2_single_profile(inspected, false) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(
            part2_selected_reconstruction_run(inspected.0.streams[0].1, limits, selection, events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_jp2_reconstructed_output(inspected, image), rest))),
    }
}

pub(crate) open spec fn part2_selected_jp2_reconstruction_run(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part1DecodedImageModel> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_selected_jp2_reconstruction_after_inspection(inspected, limits, selection, rest))
}

pub closed spec fn part2_selected_jp2_reconstruction_result(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    result: Result<Part1DecodedImageModel, crate::DecodeError>,
) -> bool {
    part2_cold_framed(
        |events| part2_selected_jp2_reconstruction_run(input, limits, selection, events), result)
}

pub closed spec fn part2_selected_jp2_reconstruction_value(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_single_profile(inspected, false) {
            Err(error) => Err(error),
            Ok(()) => match part2_selected_reconstruction_value(
                inspected.0.streams[0].1, limits, selection) {
                Err(error) => Err(error),
                Ok(image) => part2_jp2_reconstructed_output(inspected, image),
            },
        },
    }
}

pub(crate) proof fn part2_selected_jp2_reconstruction_value_unfold(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
)
    ensures part2_selected_jp2_reconstruction_value(input, limits, selection) ==
        match part2_parse_and_inspect_container_mode(input, limits, true) {
            Err(error) => Err(error),
            Ok(inspected) => match part2_single_profile(inspected, false) {
                Err(error) => Err(error),
                Ok(()) => match part2_selected_reconstruction_value(
                    inspected.0.streams[0].1, limits, selection) {
                    Err(error) => Err(error),
                    Ok(image) => part2_jp2_reconstructed_output(inspected, image),
                },
            },
        },
{}

pub(crate) proof fn part2_selected_jp2_reconstruction_normal(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
)
    ensures part2_selected_jp2_reconstruction_result(input, limits, selection,
        part2_selected_jp2_reconstruction_value(input, limits, selection)),
{
    reveal(part2_selected_jp2_reconstruction_result);
    part2_selected_jp2_reconstruction_value_unfold(input, limits, selection);
    let inspected = part2_parse_and_inspect_container_mode(input, limits, true);
    part2_single_inspection_normal(input, limits, false);
    if let Ok(value) = inspected {
        match part2_single_profile(value, false) {
            Err(error) => { part2_cold_pure::<Part1DecodedImageModel>(Err(error)); },
            Ok(()) => {
                let decoded = part2_selected_reconstruction_value(
                    value.0.streams[0].1, limits, selection);
                part2_selected_reconstruction_normal(value.0.streams[0].1, limits, selection);
                reveal(part2_selected_reconstruction_result);
                if let Ok(image) = decoded {
                    part2_cold_pure(part2_jp2_reconstructed_output(value, image));
                }
                part2_cold_bind(
                    |events| part2_selected_reconstruction_run(
                        value.0.streams[0].1, limits, selection, events),
                    |image: Part1DecodedImageModel, rest|
                        Some((part2_jp2_reconstructed_output(value, image), rest)),
                    decoded, match decoded {
                        Err(error) => Err(error), Ok(image) => part2_jp2_reconstructed_output(value, image),
                    });
            },
        }
    }
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_selected_jp2_reconstruction_after_inspection(value, limits, selection, rest),
        inspected, part2_selected_jp2_reconstruction_value(input, limits, selection));
}

pub(crate) proof fn part2_selected_jp2_reconstruction_inspection_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Err(error)),
    ensures part2_selected_jp2_reconstruction_result(input, limits, selection, Err(error)),
{
    reveal(part2_selected_jp2_reconstruction_result);
    part2_single_inspection_actual(input, limits, false, Err(error));
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_selected_jp2_reconstruction_after_inspection(inspected, limits, selection, rest),
        Err(error), Err(error));
}

pub(crate) proof fn part2_selected_jp2_reconstruction_profile_error(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    inspected: Part2RawInspectedContainer, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Err(error),
    ensures part2_selected_jp2_reconstruction_result(input, limits, selection, Err(error)),
{
    reveal(part2_selected_jp2_reconstruction_result);
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_pure::<Part1DecodedImageModel>(Err(error));
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_selected_jp2_reconstruction_after_inspection(value, limits, selection, rest),
        Ok(inspected), Err(error));
}

pub(crate) proof fn part2_selected_jp2_reconstruction_image_actual(
    input: Seq<u8>, limits: &crate::ResourceLimits, selection: &crate::DecodeSelection,
    inspected: Part2RawInspectedContainer,
    decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Ok(()),
        part2_selected_reconstruction_result(inspected.0.streams[0].1, limits, selection, decoded),
    ensures part2_selected_jp2_reconstruction_result(input, limits, selection, match decoded {
        Err(error) => Err(error), Ok(image) => part2_jp2_reconstructed_output(inspected, image),
    }),
{
    reveal(part2_selected_jp2_reconstruction_result);
    reveal(part2_selected_reconstruction_result);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_jp2_reconstructed_output(inspected, image),
    };
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    if let Ok(image) = decoded { part2_cold_pure(part2_jp2_reconstructed_output(inspected, image)); }
    part2_cold_bind(
        |events| part2_selected_reconstruction_run(inspected.0.streams[0].1, limits, selection, events),
        |image: Part1DecodedImageModel, rest|
            Some((part2_jp2_reconstructed_output(inspected, image), rest)),
        decoded, result);
    part2_cold_bind(
        |events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_selected_jp2_reconstruction_after_inspection(value, limits, selection, rest),
        Ok(inspected), result);
}
}
