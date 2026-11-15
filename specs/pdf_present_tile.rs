//! Sole-present-tile selection and logical intended-canvas accounting.
use super::*;
verus! {
pub(crate) open spec fn part2_present_tile_index(
    input: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
) -> Result<Option<u16>, crate::DecodeError> {
    if !matches!(requested.0, Part2TileSelection::All) || requested.1.is_some() {
        Ok(None)
    } else {
        match part2_selection_tile_count(crate::codestream::selection_geometry_view(&input.size)) {
            Err(error) => Err(error),
            Ok(count) => if count <= 1 || input.parts.len() == 0 { Ok(None) }
                else if forall|i: int| 0 <= i < input.parts.len()
                    ==> #[trigger] input.parts[i].tile_index == input.parts[0].tile_index {
                    Ok(Some(input.parts[0].tile_index))
                } else { Ok(None) },
        }
    }
}

pub(crate) open spec fn part2_present_tile_effective(
    tile: Option<u16>, requested: Part2DecodeSelection,
) -> Option<Part2DecodeSelection> {
    match tile {
        None => None,
        Some(index) => Some((Part2TileSelection::Index(index), None, requested.2)),
    }
}

pub(crate) open spec fn part2_present_tile_requested(
    tile: Option<u16>, requested: Part2DecodeSelection,
) -> Part2DecodeSelection {
    match part2_present_tile_effective(tile, requested) {
        None => requested, Some(selected) => selected,
    }
}

pub(crate) open spec fn part2_present_ceil_scale(
    value: u64, divisor: u64,
) -> Result<u64, crate::DecodeError> {
    if divisor == 0 { Err(part1_block_placement_error(true)) } else {
        let total = value as nat / divisor as nat
            + if value as nat % divisor as nat == 0 { 0nat } else { 1nat };
        if total > u64::MAX { Err(part1_block_placement_error(true)) } else { Ok(total as u64) }
    }
}

pub(crate) open spec fn part2_present_canvas_bytes(
    size: Part2SelectionGeometry, discard: u8, components: usize,
) -> Result<u64, crate::DecodeError> {
    if discard >= 64 { Err(part1_block_placement_error(true)) } else {
        let scale = 1u64 << discard;
        let x0 = size.2 as u64;
        let y0 = size.3 as u64;
        let x1 = size.2 as nat + size.0 as nat;
        let y1 = size.3 as nat + size.1 as nat;
        if x1 > u64::MAX || y1 > u64::MAX { Err(part1_block_placement_error(true)) } else {
            match (part2_present_ceil_scale(x1 as u64, scale), part2_present_ceil_scale(x0, scale),
                part2_present_ceil_scale(y1 as u64, scale), part2_present_ceil_scale(y0, scale)) {
                (Ok(right), Ok(left), Ok(bottom), Ok(top)) => if right < left || bottom < top {
                    Err(part1_block_placement_error(true))
                } else {
                    let pixels = (right - left) as nat * (bottom - top) as nat;
                    let samples = pixels * components as nat;
                    let bytes = samples * 8;
                    if pixels > u64::MAX || components > u64::MAX || samples > u64::MAX || bytes > u64::MAX {
                        Err(part1_block_placement_error(true))
                    } else { Ok(bytes as u64) }
                },
                _ => Err(part1_block_placement_error(true)),
            }
        }
    }
}

pub(crate) open spec fn part2_present_tile_report(
    size: Part2SelectionGeometry, requested: Part2DecodeSelection, tile: Option<u16>,
    components: usize, limits: &crate::ResourceLimits,
) -> Result<crate::decode::PresentTileRecoveryReport, crate::DecodeError> {
    let bytes = if tile.is_some() {
        match part2_present_canvas_bytes(size, requested.2, components) {
            Err(error) => Err(error),
            Ok(actual) => if actual > crate::limits::resource_decoded_bytes_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::DecodedBytes,
                    limit: crate::limits::resource_decoded_bytes_limit(limits), actual })
            } else { Ok(Some(actual)) },
        }
    } else { Ok(None) };
    match bytes {
        Err(error) => Err(error),
        Ok(bytes) => Ok(crate::decode::PresentTileRecoveryReport {
            selected_present_tile: tile, canvas_width: size.0, canvas_height: size.1,
            canvas_x_origin: size.2, canvas_y_origin: size.3, discard_levels: requested.2,
            full_canvas_sample_bytes: bytes,
        }),
    }
}

pub(crate) type Part2PresentTyped = (Part1DecodedTypedImage, crate::decode::PresentTileRecoveryReport);
pub(crate) type Part2PresentReconstructed = (Part1DecodedImageModel, crate::decode::PresentTileRecoveryReport);

pub(crate) open spec fn part2_present_typed_finish(
    source: Part2DecoderLayoutInput, requested: Part2DecodeSelection, tile: Option<u16>,
    image: Part1DecodedTypedImage, limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part2_present_tile_report(crate::codestream::selection_geometry_view(&source.size),
        requested, tile, image.1.len() as usize, limits) {
        Err(error) => Err(error), Ok(report) => Ok((image, report)),
    }
}

pub(crate) open spec fn part2_present_reconstructed_finish(
    source: Part2DecoderLayoutInput, requested: Part2DecodeSelection, tile: Option<u16>,
    image: Part1DecodedImageModel, limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part2_present_tile_report(crate::codestream::selection_geometry_view(&source.size),
        requested, tile, image.4.len() as usize, limits) {
        Err(error) => Err(error), Ok(report) => Ok((image, report)),
    }
}

pub(crate) open spec fn part2_present_raw_typed_after_layout(
    input: Seq<u8>, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentTyped> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Some((Err(error), events)),
        Ok(tile) => part2_jpip_snapshot_bind(
            part2_decode_raw_value_cold_run(input, limits,
                Some(part2_present_tile_requested(tile, requested)), events),
            |image: Part1DecodedTypedImage, rest|
                Some((part2_present_typed_finish(source, requested, tile, image, limits), rest))),
    }
}

pub(crate) open spec fn part2_present_raw_reconstructed_after_layout(
    input: Seq<u8>, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentReconstructed> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Some((Err(error), events)),
        Ok(tile) => part2_jpip_snapshot_bind(
            part2_selected_reconstruction_value_run(input, limits,
                part2_present_tile_requested(tile, requested), events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_present_reconstructed_finish(source, requested, tile, image, limits), rest))),
    }
}

pub(crate) open spec fn part2_present_raw_typed_run(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentTyped> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 11, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_present_raw_typed_after_layout(
            input, part2_decoder_input_from_raw(parsed), requested, limits, rest))
}

pub(crate) open spec fn part2_present_raw_reconstructed_run(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentReconstructed> {
    part2_jpip_snapshot_bind(part2_cold_parse(input, limits, 11, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_present_raw_reconstructed_after_layout(
            input, part2_decoder_input_from_raw(parsed), requested, limits, rest))
}

pub closed spec fn part2_present_raw_typed_result(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PresentTyped, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_present_raw_typed_run(input, requested, limits, events), result)
}

pub closed spec fn part2_present_raw_reconstructed_result(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PresentReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_present_raw_reconstructed_run(input, requested, limits, events), result)
}

pub(crate) open spec fn part2_present_raw_typed_layout_value(
    input: Seq<u8>, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Err(error),
        Ok(tile) => match part2_decode_raw_codestream_value(
            input, limits, Some(part2_present_tile_requested(tile, requested))) {
            Err(error) => Err(error),
            Ok(image) => part2_present_typed_finish(source, requested, tile, image, limits),
        },
    }
}

pub(crate) open spec fn part2_present_raw_reconstructed_layout_value(
    input: Seq<u8>, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Err(error),
        Ok(tile) => match part2_selected_reconstruction_selected_value(
            input, limits, part2_present_tile_requested(tile, requested)) {
            Err(error) => Err(error),
            Ok(image) => part2_present_reconstructed_finish(source, requested, tile, image, limits),
        },
    }
}

pub closed spec fn part2_present_raw_typed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_present_raw_typed_layout_value(input, part2_decoder_input_from_raw(parsed), requested, limits),
    }
}

pub closed spec fn part2_present_raw_reconstructed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_present_raw_reconstructed_layout_value(input, part2_decoder_input_from_raw(parsed), requested, limits),
    }
}

pub(crate) proof fn part2_present_raw_value_unfold(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_present_raw_typed_value(input, requested, limits) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_present_raw_typed_layout_value(input, part2_decoder_input_from_raw(parsed), requested, limits),
    },
    part2_present_raw_reconstructed_value(input, requested, limits) == match part1_parse_layout(input, limits) {
        Err(error) => Err(error),
        Ok(parsed) => part2_present_raw_reconstructed_layout_value(input, part2_decoder_input_from_raw(parsed), requested, limits),
    },
{}

pub(crate) proof fn part2_present_raw_parse_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    error: crate::DecodeError,
)
    requires part1_parse_layout_cold_result(input, limits, Err(error)),
    ensures part2_present_raw_typed_result(input, requested, limits, Err(error)),
        part2_present_raw_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_present_raw_typed_result); reveal(part2_present_raw_reconstructed_result);
    part2_cold_parse_actual(input, limits, 11, 0, Err(error));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 11, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_present_raw_typed_after_layout(
            input, part2_decoder_input_from_raw(parsed), requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 11, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_present_raw_reconstructed_after_layout(
            input, part2_decoder_input_from_raw(parsed), requested, limits, rest), Err(error), Err(error));
}

pub(crate) proof fn part2_present_raw_choice_error(
    input: Seq<u8>, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part1_parse_layout(input, limits) == Ok(parsed),
        part1_parse_layout_cold_result(input, limits, Ok(parsed)),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Err(error),
    ensures part2_present_raw_typed_result(input, requested, limits, Err(error)),
        part2_present_raw_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_present_raw_typed_result); reveal(part2_present_raw_reconstructed_result);
    part2_cold_parse_actual(input, limits, 11, 0, Ok(parsed));
    part2_cold_pure::<Part2PresentTyped>(Err(error));
    part2_cold_pure::<Part2PresentReconstructed>(Err(error));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_raw_typed_after_layout(
            input, part2_decoder_input_from_raw(raw), requested, limits, rest), Ok(parsed), Err(error));
    part2_cold_bind(|events| part2_cold_parse(input, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_raw_reconstructed_after_layout(
            input, part2_decoder_input_from_raw(raw), requested, limits, rest), Ok(parsed), Err(error));
}

pub(crate) proof fn part2_present_raw_typed_actual(
    input: Seq<u8>, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    tile: Option<u16>, limits: &crate::ResourceLimits,
    decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part1_parse_layout(input, limits) == Ok(parsed),
        part1_parse_layout_cold_result(input, limits, Ok(parsed)),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Ok(tile),
        part2_decode_raw_value_cold_result(input, limits, Some(part2_present_tile_requested(tile, requested)), decoded),
    ensures part2_present_raw_typed_result(input, requested, limits, match decoded {
        Err(error) => Err(error),
        Ok(image) => part2_present_typed_finish(part2_decoder_input_from_raw(parsed), requested, tile, image, limits),
    }),
{
    reveal(part2_present_raw_typed_result);
    let source = part2_decoder_input_from_raw(parsed);
    let selected = Some(part2_present_tile_requested(tile, requested));
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_present_typed_finish(source, requested, tile, image, limits),
    };
    part2_cold_parse_actual(input, limits, 11, 0, Ok(parsed));
    if let Ok(image) = decoded { part2_cold_pure(part2_present_typed_finish(source, requested, tile, image, limits)); }
    part2_cold_bind(|events| part2_decode_raw_value_cold_run(input, limits, selected, events),
        |image: Part1DecodedTypedImage, rest|
            Some((part2_present_typed_finish(source, requested, tile, image, limits), rest)),
        decoded, result);
    part2_cold_bind(|events| part2_cold_parse(input, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_raw_typed_after_layout(
            input, part2_decoder_input_from_raw(raw), requested, limits, rest),
        Ok(parsed), result);
}

pub(crate) proof fn part2_present_raw_reconstructed_actual(
    input: Seq<u8>, parsed: Part1CompleteLayout, requested: Part2DecodeSelection,
    tile: Option<u16>, limits: &crate::ResourceLimits,
    decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part1_parse_layout(input, limits) == Ok(parsed),
        part1_parse_layout_cold_result(input, limits, Ok(parsed)),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Ok(tile),
        part2_cold_framed(|events| part2_selected_reconstruction_value_run(input, limits,
            part2_present_tile_requested(tile, requested), events), decoded),
    ensures part2_present_raw_reconstructed_result(input, requested, limits, match decoded {
        Err(error) => Err(error),
        Ok(image) => part2_present_reconstructed_finish(part2_decoder_input_from_raw(parsed), requested, tile, image, limits),
    }),
{
    reveal(part2_present_raw_reconstructed_result);
    let source = part2_decoder_input_from_raw(parsed);
    let selected = part2_present_tile_requested(tile, requested);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_present_reconstructed_finish(source, requested, tile, image, limits),
    };
    part2_cold_parse_actual(input, limits, 11, 0, Ok(parsed));
    if let Ok(image) = decoded { part2_cold_pure(part2_present_reconstructed_finish(source, requested, tile, image, limits)); }
    part2_cold_bind(|events| part2_selected_reconstruction_value_run(input, limits, selected, events),
        |image: Part1DecodedImageModel, rest|
            Some((part2_present_reconstructed_finish(source, requested, tile, image, limits), rest)),
        decoded, result);
    part2_cold_bind(|events| part2_cold_parse(input, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_raw_reconstructed_after_layout(
            input, part2_decoder_input_from_raw(raw), requested, limits, rest),
        Ok(parsed), result);
}

pub(crate) proof fn part2_present_raw_normal(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_present_raw_typed_result(input, requested, limits, part2_present_raw_typed_value(input, requested, limits)),
        part2_present_raw_reconstructed_result(input, requested, limits, part2_present_raw_reconstructed_value(input, requested, limits)),
{
    part2_present_raw_value_unfold(input, requested, limits);
    part1_parse_layout_cold_normal(input, limits);
    match part1_parse_layout(input, limits) {
        Err(error) => { part2_present_raw_parse_error(input, requested, limits, error); },
        Ok(parsed) => match part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) {
            Err(error) => { part2_present_raw_choice_error(input, parsed, requested, limits, error); },
            Ok(tile) => {
                let selected = part2_present_tile_requested(tile, requested);
                part2_decode_raw_value_cold_normal(input, limits, Some(selected));
                part2_present_raw_typed_actual(input, parsed, requested, tile, limits,
                    part2_decode_raw_codestream_value(input, limits, Some(selected)));
                part2_selected_reconstruction_value_normal(input, limits, selected);
                part2_present_raw_reconstructed_actual(input, parsed, requested, tile, limits,
                    part2_selected_reconstruction_selected_value(input, limits, selected));
            },
        },
    }
}

pub(crate) open spec fn part2_present_jp2_typed_finish(
    inspected: Part2RawInspectedContainer, source: Part2DecoderLayoutInput,
    requested: Part2DecodeSelection, tile: Option<u16>,
    image: Part1DecodedTypedImage, limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part2_single_output(inspected, limits, image) {
        Err(error) => Err(error),
        Ok(mapped) => part2_present_typed_finish(source, requested, tile, mapped, limits),
    }
}

pub(crate) open spec fn part2_present_jp2_reconstructed_finish(
    inspected: Part2RawInspectedContainer, source: Part2DecoderLayoutInput,
    requested: Part2DecodeSelection, tile: Option<u16>,
    image: Part1DecodedImageModel, limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part2_jp2_reconstructed_output(inspected, image) {
        Err(error) => Err(error),
        Ok(mapped) => part2_present_reconstructed_finish(source, requested, tile, mapped, limits),
    }
}

pub(crate) open spec fn part2_present_jp2_typed_after_layout(
    inspected: Part2RawInspectedContainer, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentTyped> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Some((Err(error), events)),
        Ok(tile) => part2_jpip_snapshot_bind(
            part2_decode_raw_value_cold_run(inspected.0.streams[0].1, limits,
                Some(part2_present_tile_requested(tile, requested)), events),
            |image: Part1DecodedTypedImage, rest|
                Some((part2_present_jp2_typed_finish(inspected, source, requested, tile, image, limits), rest))),
    }
}

pub(crate) open spec fn part2_present_jp2_reconstructed_after_layout(
    inspected: Part2RawInspectedContainer, source: Part2DecoderLayoutInput, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentReconstructed> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Some((Err(error), events)),
        Ok(tile) => part2_jpip_snapshot_bind(
            part2_selected_reconstruction_value_run(inspected.0.streams[0].1, limits,
                part2_present_tile_requested(tile, requested), events),
            |image: Part1DecodedImageModel, rest|
                Some((part2_present_jp2_reconstructed_finish(inspected, source, requested, tile, image, limits), rest))),
    }
}

pub(crate) open spec fn part2_present_jp2_typed_after_inspection(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentTyped> {
    match part2_single_profile(inspected, false) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(part2_cold_parse(inspected.0.streams[0].1, limits, 11, 0, events),
            |parsed: Part1CompleteLayout, rest| part2_present_jp2_typed_after_layout(
                inspected, part2_decoder_input_from_raw(parsed), requested, limits, rest)),
    }
}

pub(crate) open spec fn part2_present_jp2_reconstructed_after_inspection(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentReconstructed> {
    match part2_single_profile(inspected, false) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => part2_jpip_snapshot_bind(part2_cold_parse(inspected.0.streams[0].1, limits, 11, 0, events),
            |parsed: Part1CompleteLayout, rest| part2_present_jp2_reconstructed_after_layout(
                inspected, part2_decoder_input_from_raw(parsed), requested, limits, rest)),
    }
}

pub(crate) open spec fn part2_present_jp2_typed_run(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentTyped> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_present_jp2_typed_after_inspection(inspected, requested, limits, rest))
}

pub(crate) open spec fn part2_present_jp2_reconstructed_run(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2PresentReconstructed> {
    part2_jpip_snapshot_bind(part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_present_jp2_reconstructed_after_inspection(inspected, requested, limits, rest))
}

pub closed spec fn part2_present_jp2_typed_result(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PresentTyped, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_present_jp2_typed_run(input, requested, limits, events), result)
}

pub closed spec fn part2_present_jp2_reconstructed_result(
    input: Seq<u8>, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, result: Result<Part2PresentReconstructed, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_present_jp2_reconstructed_run(input, requested, limits, events), result)
}

pub(crate) open spec fn part2_present_jp2_typed_layout_value(
    inspected: Part2RawInspectedContainer, source: Part2DecoderLayoutInput,
    requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Err(error),
        Ok(tile) => match part2_decode_raw_codestream_value(
            inspected.0.streams[0].1, limits, Some(part2_present_tile_requested(tile, requested))) {
            Err(error) => Err(error),
            Ok(image) => part2_present_jp2_typed_finish(inspected, source, requested, tile, image, limits),
        },
    }
}

pub(crate) open spec fn part2_present_jp2_reconstructed_layout_value(
    inspected: Part2RawInspectedContainer, source: Part2DecoderLayoutInput,
    requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part2_present_tile_index(source, requested) {
        Err(error) => Err(error),
        Ok(tile) => match part2_selected_reconstruction_selected_value(
            inspected.0.streams[0].1, limits, part2_present_tile_requested(tile, requested)) {
            Err(error) => Err(error),
            Ok(image) => part2_present_jp2_reconstructed_finish(inspected, source, requested, tile, image, limits),
        },
    }
}

pub(crate) open spec fn part2_present_jp2_typed_inspected_value(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part2_single_profile(inspected, false) {
        Err(error) => Err(error),
        Ok(()) => match part1_parse_layout(inspected.0.streams[0].1, limits) {
            Err(error) => Err(error),
            Ok(parsed) => part2_present_jp2_typed_layout_value(inspected, part2_decoder_input_from_raw(parsed), requested, limits),
        },
    }
}

pub(crate) open spec fn part2_present_jp2_reconstructed_inspected_value(
    inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part2_single_profile(inspected, false) {
        Err(error) => Err(error),
        Ok(()) => match part1_parse_layout(inspected.0.streams[0].1, limits) {
            Err(error) => Err(error),
            Ok(parsed) => part2_present_jp2_reconstructed_layout_value(inspected, part2_decoder_input_from_raw(parsed), requested, limits),
        },
    }
}

pub closed spec fn part2_present_jp2_typed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentTyped, crate::DecodeError> {
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error),
        Ok(inspected) => part2_present_jp2_typed_inspected_value(inspected, requested, limits),
    }
}

pub closed spec fn part2_present_jp2_reconstructed_value(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part2PresentReconstructed, crate::DecodeError> {
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => Err(error),
        Ok(inspected) => part2_present_jp2_reconstructed_inspected_value(inspected, requested, limits),
    }
}

pub(crate) proof fn part2_present_jp2_value_unfold(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_present_jp2_typed_value(input, requested, limits) ==
        match part2_parse_and_inspect_container_mode(input, limits, true) {
            Err(error) => Err(error),
            Ok(inspected) => part2_present_jp2_typed_inspected_value(inspected, requested, limits),
        },
        part2_present_jp2_reconstructed_value(input, requested, limits) ==
        match part2_parse_and_inspect_container_mode(input, limits, true) {
            Err(error) => Err(error),
            Ok(inspected) => part2_present_jp2_reconstructed_inspected_value(inspected, requested, limits),
        },
{}

pub(crate) proof fn part2_present_jp2_inspection_error(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
    error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Err(error)),
    ensures part2_present_jp2_typed_result(input, requested, limits, Err(error)),
        part2_present_jp2_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_present_jp2_typed_result); reveal(part2_present_jp2_reconstructed_result);
    part2_single_inspection_actual(input, limits, false, Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_present_jp2_typed_after_inspection(inspected, requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |inspected: Part2RawInspectedContainer, rest|
            part2_present_jp2_reconstructed_after_inspection(inspected, requested, limits, rest), Err(error), Err(error));
}

pub(crate) proof fn part2_present_jp2_profile_error(
    input: Seq<u8>, inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Err(error),
    ensures part2_present_jp2_typed_result(input, requested, limits, Err(error)),
        part2_present_jp2_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_present_jp2_typed_result); reveal(part2_present_jp2_reconstructed_result);
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_pure::<Part2PresentTyped>(Err(error));
    part2_cold_pure::<Part2PresentReconstructed>(Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_typed_after_inspection(value, requested, limits, rest), Ok(inspected), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_reconstructed_after_inspection(value, requested, limits, rest), Ok(inspected), Err(error));
}

pub(crate) proof fn part2_present_jp2_layout_error(
    input: Seq<u8>, inspected: Part2RawInspectedContainer, requested: Part2DecodeSelection,
    limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Ok(()),
        part1_parse_layout_cold_result(inspected.0.streams[0].1, limits, Err(error)),
    ensures part2_present_jp2_typed_result(input, requested, limits, Err(error)),
        part2_present_jp2_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_present_jp2_typed_result); reveal(part2_present_jp2_reconstructed_result);
    let bytes = inspected.0.streams[0].1;
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_parse_actual(bytes, limits, 11, 0, Err(error));
    part2_cold_bind(|events| part2_cold_parse(bytes, limits, 11, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_present_jp2_typed_after_layout(
            inspected, part2_decoder_input_from_raw(parsed), requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_cold_parse(bytes, limits, 11, 0, events),
        |parsed: Part1CompleteLayout, rest| part2_present_jp2_reconstructed_after_layout(
            inspected, part2_decoder_input_from_raw(parsed), requested, limits, rest), Err(error), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_typed_after_inspection(value, requested, limits, rest), Ok(inspected), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_reconstructed_after_inspection(value, requested, limits, rest), Ok(inspected), Err(error));
}

pub(crate) proof fn part2_present_jp2_choice_error(
    input: Seq<u8>, inspected: Part2RawInspectedContainer, parsed: Part1CompleteLayout,
    requested: Part2DecodeSelection, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Ok(()),
        part1_parse_layout(inspected.0.streams[0].1, limits) == Ok(parsed),
        part1_parse_layout_cold_result(inspected.0.streams[0].1, limits, Ok(parsed)),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Err(error),
    ensures part2_present_jp2_typed_result(input, requested, limits, Err(error)),
        part2_present_jp2_reconstructed_result(input, requested, limits, Err(error)),
{
    reveal(part2_present_jp2_typed_result); reveal(part2_present_jp2_reconstructed_result);
    let bytes = inspected.0.streams[0].1;
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_parse_actual(bytes, limits, 11, 0, Ok(parsed));
    part2_cold_pure::<Part2PresentTyped>(Err(error));
    part2_cold_pure::<Part2PresentReconstructed>(Err(error));
    part2_cold_bind(|events| part2_cold_parse(bytes, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_jp2_typed_after_layout(
            inspected, part2_decoder_input_from_raw(raw), requested, limits, rest), Ok(parsed), Err(error));
    part2_cold_bind(|events| part2_cold_parse(bytes, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_jp2_reconstructed_after_layout(
            inspected, part2_decoder_input_from_raw(raw), requested, limits, rest), Ok(parsed), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_typed_after_inspection(value, requested, limits, rest), Ok(inspected), Err(error));
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_reconstructed_after_inspection(value, requested, limits, rest), Ok(inspected), Err(error));
}

pub(crate) proof fn part2_present_jp2_typed_actual(
    input: Seq<u8>, inspected: Part2RawInspectedContainer, parsed: Part1CompleteLayout,
    requested: Part2DecodeSelection, tile: Option<u16>, limits: &crate::ResourceLimits,
    decoded: Result<Part1DecodedTypedImage, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Ok(()),
        part1_parse_layout(inspected.0.streams[0].1, limits) == Ok(parsed),
        part1_parse_layout_cold_result(inspected.0.streams[0].1, limits, Ok(parsed)),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Ok(tile),
        part2_decode_raw_value_cold_result(inspected.0.streams[0].1, limits,
            Some(part2_present_tile_requested(tile, requested)), decoded),
    ensures part2_present_jp2_typed_result(input, requested, limits, match decoded {
        Err(error) => Err(error),
        Ok(image) => part2_present_jp2_typed_finish(
            inspected, part2_decoder_input_from_raw(parsed), requested, tile, image, limits),
    }),
{
    reveal(part2_present_jp2_typed_result);
    let bytes = inspected.0.streams[0].1;
    let source = part2_decoder_input_from_raw(parsed);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_present_jp2_typed_finish(inspected, source, requested, tile, image, limits),
    };
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_parse_actual(bytes, limits, 11, 0, Ok(parsed));
    if let Ok(image) = decoded { part2_cold_pure(part2_present_jp2_typed_finish(inspected, source, requested, tile, image, limits)); }
    part2_cold_bind(
        |events| part2_decode_raw_value_cold_run(bytes, limits, Some(part2_present_tile_requested(tile, requested)), events),
        |image: Part1DecodedTypedImage, rest|
            Some((part2_present_jp2_typed_finish(inspected, source, requested, tile, image, limits), rest)),
        decoded, result);
    part2_cold_bind(|events| part2_cold_parse(bytes, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_jp2_typed_after_layout(
            inspected, part2_decoder_input_from_raw(raw), requested, limits, rest), Ok(parsed), result);
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_typed_after_inspection(value, requested, limits, rest), Ok(inspected), result);
}

pub(crate) proof fn part2_present_jp2_reconstructed_actual(
    input: Seq<u8>, inspected: Part2RawInspectedContainer, parsed: Part1CompleteLayout,
    requested: Part2DecodeSelection, tile: Option<u16>, limits: &crate::ResourceLimits,
    decoded: Result<Part1DecodedImageModel, crate::DecodeError>,
)
    requires part2_inspection_cold_result(input, limits, true, Ok(inspected)),
        part2_single_profile(inspected, false) == Ok(()),
        part1_parse_layout(inspected.0.streams[0].1, limits) == Ok(parsed),
        part1_parse_layout_cold_result(inspected.0.streams[0].1, limits, Ok(parsed)),
        part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) == Ok(tile),
        part2_cold_framed(|events| part2_selected_reconstruction_value_run(inspected.0.streams[0].1,
            limits, part2_present_tile_requested(tile, requested), events), decoded),
    ensures part2_present_jp2_reconstructed_result(input, requested, limits, match decoded {
        Err(error) => Err(error),
        Ok(image) => part2_present_jp2_reconstructed_finish(
            inspected, part2_decoder_input_from_raw(parsed), requested, tile, image, limits),
    }),
{
    reveal(part2_present_jp2_reconstructed_result);
    let bytes = inspected.0.streams[0].1;
    let source = part2_decoder_input_from_raw(parsed);
    let result = match decoded {
        Err(error) => Err(error), Ok(image) => part2_present_jp2_reconstructed_finish(inspected, source, requested, tile, image, limits),
    };
    part2_single_inspection_actual(input, limits, false, Ok(inspected));
    part2_cold_parse_actual(bytes, limits, 11, 0, Ok(parsed));
    if let Ok(image) = decoded { part2_cold_pure(part2_present_jp2_reconstructed_finish(inspected, source, requested, tile, image, limits)); }
    part2_cold_bind(
        |events| part2_selected_reconstruction_value_run(bytes, limits, part2_present_tile_requested(tile, requested), events),
        |image: Part1DecodedImageModel, rest|
            Some((part2_present_jp2_reconstructed_finish(inspected, source, requested, tile, image, limits), rest)),
        decoded, result);
    part2_cold_bind(|events| part2_cold_parse(bytes, limits, 11, 0, events),
        |raw: Part1CompleteLayout, rest| part2_present_jp2_reconstructed_after_layout(
            inspected, part2_decoder_input_from_raw(raw), requested, limits, rest), Ok(parsed), result);
    part2_cold_bind(|events| part2_single_inspection_run(input, limits, false, events),
        |value: Part2RawInspectedContainer, rest|
            part2_present_jp2_reconstructed_after_inspection(value, requested, limits, rest), Ok(inspected), result);
}

pub(crate) proof fn part2_present_jp2_normal(
    input: Seq<u8>, requested: Part2DecodeSelection, limits: &crate::ResourceLimits,
)
    ensures part2_present_jp2_typed_result(input, requested, limits, part2_present_jp2_typed_value(input, requested, limits)),
        part2_present_jp2_reconstructed_result(input, requested, limits, part2_present_jp2_reconstructed_value(input, requested, limits)),
{
    part2_present_jp2_value_unfold(input, requested, limits);
    part2_inspection_cold_normal(input, limits, true);
    match part2_parse_and_inspect_container_mode(input, limits, true) {
        Err(error) => { part2_present_jp2_inspection_error(input, requested, limits, error); },
        Ok(inspected) => match part2_single_profile(inspected, false) {
            Err(error) => { part2_present_jp2_profile_error(input, inspected, requested, limits, error); },
            Ok(()) => {
                let bytes = inspected.0.streams[0].1;
                part1_parse_layout_cold_normal(bytes, limits);
                match part1_parse_layout(bytes, limits) {
                    Err(error) => { part2_present_jp2_layout_error(input, inspected, requested, limits, error); },
                    Ok(parsed) => match part2_present_tile_index(part2_decoder_input_from_raw(parsed), requested) {
                        Err(error) => { part2_present_jp2_choice_error(input, inspected, parsed, requested, limits, error); },
                        Ok(tile) => {
                            let selected = part2_present_tile_requested(tile, requested);
                            part2_decode_raw_value_cold_normal(bytes, limits, Some(selected));
                            part2_present_jp2_typed_actual(input, inspected, parsed, requested, tile, limits,
                                part2_decode_raw_codestream_value(bytes, limits, Some(selected)));
                            part2_selected_reconstruction_value_normal(bytes, limits, selected);
                            part2_present_jp2_reconstructed_actual(input, inspected, parsed, requested, tile, limits,
                                part2_selected_reconstruction_selected_value(bytes, limits, selected));
                        },
                    },
                }
            },
        },
    }
}
}
