use super::{DecodedImage, TypedImage, apply_jp2_output, arithmetic_overflow, codestream, jp2};
use crate::{DecodeError, DecodeOptions, DecodeSelection, Resource, ResourceLimits, TileSelection};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// What was selected automatically, and the full original SIZ canvas.
///
/// The returned image retains its own genuine crop/origin/grid. The canvas is
/// metadata, not decoded pixels. A checked byte count bounds full-resolution
/// eight-byte output planes at the requested reduction when recovery is used;
/// it is not a global live-allocation or arbitrary renderer-memory measurement.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct PresentTileRecoveryReport {
    pub selected_present_tile: Option<u16>,
    pub canvas_width: u32,
    pub canvas_height: u32,
    pub canvas_x_origin: u32,
    pub canvas_y_origin: u32,
    pub discard_levels: u8,
    pub full_canvas_sample_bytes: Option<u64>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct PresentTileRecoveredImage {
    pub image: TypedImage,
    pub report: PresentTileRecoveryReport,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct PresentTileRecoveredReconstructedImage {
    pub image: DecodedImage,
    pub report: PresentTileRecoveryReport,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn present_optional_selection_view(value: Option<DecodeSelection>)
        -> Option<crate::specs::Part2DecodeSelection> {
        match value {
            None => None, Some(selection) => Some(crate::options::decode_selection_value_view(selection)),
        }
    }

    pub open spec fn present_typed_outcome(value: Result<PresentTileRecoveredImage, DecodeError>)
        -> Result<crate::specs::Part2PresentTyped, DecodeError> {
        match value {
            Err(error) => Err(error),
            Ok(value) => Ok((crate::image::typed_image_value_view(value.image), value.report)),
        }
    }

    pub open spec fn present_reconstructed_outcome(value: Result<PresentTileRecoveredReconstructedImage, DecodeError>)
        -> Result<crate::specs::Part2PresentReconstructed, DecodeError> {
        match value {
            Err(error) => Err(error),
            Ok(value) => Ok((crate::image::decoded_image_view(value.image), value.report)),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_present_tile_index(
        codestream::decoder_layout_input_view(layout), crate::options::decode_selection_view(requested)),
))]
pub(super) fn automatic_tile(
    layout: &codestream::CodestreamLayout<'_>,
    requested: &DecodeSelection,
) -> Result<Option<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_input_fields(layout);
        reveal(codestream::tile_parts_owned_view);
    }
    if !matches!(requested.tile_selection(), TileSelection::All)
        || requested.region().is_some()
        || layout.info.image_size.tile_count()? <= 1
    {
        return Ok(None);
    }
    let Some(first) = layout.tile_parts.first() else {
        return Ok(None);
    };
    let tile = first.tile_index;
    let mut index = 1_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(&layout.info.image_size);
        codestream::selection_geometry_known_fields(&codestream::decoder_layout_input_view(layout).size);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= index <= layout.tile_parts.len(),
            matches!(crate::options::decode_selection_view(requested).0, crate::specs::Part2TileSelection::All),
            crate::options::decode_selection_view(requested).1.is_none(),
            match crate::specs::part2_selection_tile_count(
                codestream::selection_geometry_view(&codestream::decoder_layout_input_view(layout).size)) {
                Ok(count) => count > 1, Err(_) => false,
            },
            tile == layout.tile_parts@[0].tile_index,
            codestream::decoder_layout_input_view(layout).parts
                == codestream::tile_parts_owned_view(layout.tile_parts@),
            codestream::decoder_layout_input_view(layout).size == layout.info.image_size,
            forall|i: int| 0 <= i < index ==> layout.tile_parts@[i].tile_index == tile,
        decreases layout.tile_parts.len() - index,
    ))]
    while index < layout.tile_parts.len() {
        #[cfg(verus_keep_ghost)]
        proof! { codestream::tile_part_owned_tile_known(&layout.tile_parts@[index as int]); }
        if layout.tile_parts[index].tile_index != tile {
            #[cfg(verus_keep_ghost)]
            proof! {
                codestream::tile_part_owned_tile_known(&layout.tile_parts@[0]);
                let ghost source = codestream::decoder_layout_input_view(layout);
                assert(source.parts[index as int].tile_index != source.parts[0].tile_index);
            }
            return Ok(None);
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(Some(tile))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures present_optional_selection_view(result) == crate::specs::part2_present_tile_effective(
        tile, crate::options::decode_selection_view(requested)),
))]
pub(super) fn effective_selection(
    tile: Option<u16>,
    requested: &DecodeSelection,
) -> Option<DecodeSelection> {
    tile.map(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeSelection =>
            ensures crate::options::decode_selection_value_view(result)
                == (crate::specs::Part2TileSelection::Index(index), None, crate::options::decode_selection_view(requested).2),
        ))]
        |index| crate::options::selection_from_parts(
            TileSelection::Index(index), None, requested.discard_levels()),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_present_ceil_scale(value, divisor),
))]
fn ceil_scale(value: u64, divisor: u64) -> Result<u64, DecodeError> {
    if divisor == 0 {
        return Err(arithmetic_overflow());
    }
    let remainder = value % divisor;
    (value / divisor)
        .checked_add(if remainder == 0 { 0 } else { 1 })
        .ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_present_canvas_bytes(
        codestream::selection_geometry_view(size), discard, components),
))]
fn canvas_sample_bytes(
    size: &codestream::ImageSize,
    discard: u8,
    components: usize,
) -> Result<u64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::selection_geometry_known_fields(size); }
    if discard >= u64::BITS as u8 {
        return Err(arithmetic_overflow());
    }
    let scale = 1_u64 << discard;
    let x0 = u64::from(size.x_origin);
    let y0 = u64::from(size.y_origin);
    let x1 = x0
        .checked_add(u64::from(size.width))
        .ok_or_else(arithmetic_overflow)?;
    let y1 = y0
        .checked_add(u64::from(size.height))
        .ok_or_else(arithmetic_overflow)?;
    let width = ceil_scale(x1, scale)?
        .checked_sub(ceil_scale(x0, scale)?)
        .ok_or_else(arithmetic_overflow)?;
    let height = ceil_scale(y1, scale)?
        .checked_sub(ceil_scale(y0, scale)?)
        .ok_or_else(arithmetic_overflow)?;
    let pixels = width.checked_mul(height).ok_or_else(arithmetic_overflow)?;
    let count = u64::try_from(components).map_err(|_| arithmetic_overflow())?;
    let samples = pixels.checked_mul(count).ok_or_else(arithmetic_overflow)?;
    samples.checked_mul(8).ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_present_tile_report(
        codestream::selection_geometry_view(size), crate::options::decode_selection_view(requested),
        selected_present_tile, components, limits),
))]
pub(super) fn finish_report(
    size: &codestream::ImageSize,
    requested: &DecodeSelection,
    selected_present_tile: Option<u16>,
    components: usize,
    limits: &ResourceLimits,
) -> Result<PresentTileRecoveryReport, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::selection_geometry_known_fields(size); }
    let full_canvas_sample_bytes = if selected_present_tile.is_some() {
        let actual = canvas_sample_bytes(size, requested.discard_levels(), components)?;
        if actual > limits.maximum_decoded_bytes() {
            return Err(DecodeError::limit(
                Resource::DecodedBytes,
                limits.maximum_decoded_bytes(),
                actual,
            ));
        }
        Some(actual)
    } else {
        None
    };
    Ok(PresentTileRecoveryReport {
        selected_present_tile,
        canvas_width: size.width,
        canvas_height: size.height,
        canvas_x_origin: size.x_origin,
        canvas_y_origin: size.y_origin,
        discard_levels: requested.discard_levels(),
        full_canvas_sample_bytes,
    })
}

/// Decode raw input, selecting a sole supplied tile only for an unbounded
/// full-image request. Explicit tiles/regions keep ordinary selection semantics.
/// Missing pixels are never allocated or relabeled as decoded data.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_present_raw_typed_result(input@,
        crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options),
        present_typed_outcome(result)),
        present_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            present_typed_outcome(result) == crate::specs::part2_present_raw_typed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_codestream_recover_present_tile_selected(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PresentTileRecoveredImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_present_raw_value_unfold(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_present_raw_normal(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let parsed = codestream::parse_layout(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_present_raw_parse_error(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); codestream::decoder_layout_input_fields(&layout); }
    let chosen = automatic_tile(&layout, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = chosen {
            if let Ok(raw) = crate::specs::part1_parse_layout(input@, crate::options::decode_options_limits(options)) {
                crate::specs::part2_present_raw_choice_error(input@, raw,
                    crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
            }
        }
    }
    let tile = chosen?;
    let adjusted = effective_selection(tile, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    let decoded = super::decode_codestream_selected(input, options, selected);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_raw_cold_to_value(input@, crate::options::decode_options_limits(options),
            Some(selected), crate::image::decoded_typed_image_outcome(decoded));
        crate::specs::part2_decode_raw_value_matches_reference(
            input@, crate::options::decode_options_limits(options), Some(selected));
        if let Ok(raw) = crate::specs::part1_parse_layout(input@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_present_raw_typed_actual(input@, raw,
                crate::options::decode_selection_view(requested), tile, crate::options::decode_options_limits(options),
                crate::image::decoded_typed_image_outcome(decoded));
        }
    }
    let image = decoded?;
    let report = finish_report(
        &layout.info.image_size,
        requested,
        tile,
        image.components().len(),
        options.limits(),
    )?;
    Ok(PresentTileRecoveredImage { image, report })
}

/// Recover the same raw tile selection while preserving centered fractions.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_present_raw_reconstructed_result(input@,
        crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options),
        present_reconstructed_outcome(result)),
        present_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            present_reconstructed_outcome(result) == crate::specs::part2_present_raw_reconstructed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_codestream_reconstructed_recover_present_tile_selected(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PresentTileRecoveredReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_present_raw_value_unfold(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_present_raw_normal(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let parsed = codestream::parse_layout(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_present_raw_parse_error(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); codestream::decoder_layout_input_fields(&layout); }
    let chosen = automatic_tile(&layout, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = chosen {
            if let Ok(raw) = crate::specs::part1_parse_layout(input@, crate::options::decode_options_limits(options)) {
                crate::specs::part2_present_raw_choice_error(input@, raw,
                    crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
            }
        }
    }
    let tile = chosen?;
    let adjusted = effective_selection(tile, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    let decoded = super::decode_codestream_reconstructed_selected(input, options, selected);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_selected_reconstruction_value_frames(input@, crate::options::decode_options_limits(options),
            selected, crate::image::decoded_image_outcome(decoded));
        crate::specs::part2_selected_reconstruction_value_unfold(
            input@, crate::options::decode_options_limits(options), selected);
        if let Ok(raw) = crate::specs::part1_parse_layout(input@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_present_raw_reconstructed_actual(input@, raw,
                crate::options::decode_selection_view(requested), tile, crate::options::decode_options_limits(options),
                crate::image::decoded_image_outcome(decoded));
        }
    }
    let image = decoded?;
    let report = finish_report(
        &layout.info.image_size,
        requested,
        tile,
        image.components().len(),
        options.limits(),
    )?;
    Ok(PresentTileRecoveredReconstructedImage { image, report })
}

/// Recover a JP2 sole tile without bypassing any container/output processing.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_present_jp2_typed_result(input@,
        crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options),
        present_typed_outcome(result)),
        present_typed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            present_typed_outcome(result) == crate::specs::part2_present_jp2_typed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_recover_present_tile_selected(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PresentTileRecoveredImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_present_jp2_value_unfold(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_present_jp2_normal(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let inspected_result = jp2::parse_and_inspect_for_display(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = inspected_result {
            crate::specs::part2_present_jp2_inspection_error(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let inspected = inspected_result?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    let profile = super::api::validate_jp2_display_profile(inspected.file());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = profile {
            crate::specs::part2_present_jp2_profile_error(input@, jp2::raw_inspected_container_view(&inspected),
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    profile?;
    let source = inspected.file().codestream(0)?.data();
    let parsed = codestream::parse_layout(source, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_present_jp2_layout_error(input@, jp2::raw_inspected_container_view(&inspected),
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); codestream::decoder_layout_input_fields(&layout); }
    let chosen = automatic_tile(&layout, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = chosen {
            if let Ok(raw) = crate::specs::part1_parse_layout(source@, crate::options::decode_options_limits(options)) {
                crate::specs::part2_present_jp2_choice_error(input@, jp2::raw_inspected_container_view(&inspected),
                    raw, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
            }
        }
    }
    let tile = chosen?;
    let adjusted = effective_selection(tile, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    let decoded_result = super::decode_codestream_selected(source, options, selected);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_decode_raw_cold_to_value(source@, crate::options::decode_options_limits(options),
            Some(selected), crate::image::decoded_typed_image_outcome(decoded_result));
        crate::specs::part2_decode_raw_value_matches_reference(
            source@, crate::options::decode_options_limits(options), Some(selected));
        if let Ok(raw) = crate::specs::part1_parse_layout(source@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_present_jp2_typed_actual(input@, jp2::raw_inspected_container_view(&inspected),
                raw, crate::options::decode_selection_view(requested), tile, crate::options::decode_options_limits(options),
                crate::image::decoded_typed_image_outcome(decoded_result));
        }
    }
    let decoded = decoded_result?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost output_source=crate::image::typed_image_value_view(decoded);}
    let output = apply_jp2_output(decoded, inspected.file().header(), options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=output {
            if let Ok(raw)=crate::specs::part1_parse_layout(source@,crate::options::decode_options_limits(options)) {
                crate::specs::part2_present_jp2_output_error(input@,jp2::raw_inspected_container_view(&inspected),raw,
                    crate::options::decode_selection_view(requested),tile,crate::options::decode_options_limits(options),output_source,error);
            }
        }
    }
    let image = output?;
    let report = finish_report(
        &layout.info.image_size,
        requested,
        tile,
        image.components().len(),
        options.limits(),
    )?;
    Ok(PresentTileRecoveredImage { image, report })
}

/// Recover JP2 tile selection in the strict centered output domain.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_present_jp2_reconstructed_result(input@,
        crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options),
        present_reconstructed_outcome(result)),
        present_reconstructed_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            present_reconstructed_outcome(result) == crate::specs::part2_present_jp2_reconstructed_value(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_reconstructed_recover_present_tile_selected(
    input: &[u8],
    options: &DecodeOptions,
    requested: &DecodeSelection,
) -> Result<PresentTileRecoveredReconstructedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::decoder_layout_errors_known();
        crate::specs::part2_present_jp2_value_unfold(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
        crate::specs::part2_present_jp2_normal(input@,
            crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options));
    }
    let inspected_result = jp2::parse_and_inspect_for_display(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = inspected_result {
            crate::specs::part2_present_jp2_inspection_error(input@,
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let inspected = inspected_result?;
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected)); }
    let profile = super::api::validate_jp2_display_profile(inspected.file());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = profile {
            crate::specs::part2_present_jp2_profile_error(input@, jp2::raw_inspected_container_view(&inspected),
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    profile?;
    let stream = inspected.file().codestream(0)?;
    let source = stream.data();
    let parsed = codestream::parse_layout(source, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = parsed {
            crate::specs::part2_present_jp2_layout_error(input@, jp2::raw_inspected_container_view(&inspected),
                crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
        }
    }
    let layout = parsed?;
    #[cfg(verus_keep_ghost)]
    proof! { codestream::decoder_layout_input_matches_raw(&layout); codestream::decoder_layout_input_fields(&layout); }
    let chosen = automatic_tile(&layout, requested);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error) = chosen {
            if let Ok(raw) = crate::specs::part1_parse_layout(source@, crate::options::decode_options_limits(options)) {
                crate::specs::part2_present_jp2_choice_error(input@, jp2::raw_inspected_container_view(&inspected),
                    raw, crate::options::decode_selection_view(requested), crate::options::decode_options_limits(options), error);
            }
        }
    }
    let tile = chosen?;
    let adjusted = effective_selection(tile, requested);
    let selected = match &adjusted {
        None => requested,
        Some(value) => value,
    };
    let decoded_result = super::decode_codestream_reconstructed_selected(source, options, selected);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_selected_reconstruction_value_frames(source@, crate::options::decode_options_limits(options),
            selected, crate::image::decoded_image_outcome(decoded_result));
        crate::specs::part2_selected_reconstruction_value_unfold(
            source@, crate::options::decode_options_limits(options), selected);
        if let Ok(raw) = crate::specs::part1_parse_layout(source@, crate::options::decode_options_limits(options)) {
            crate::specs::part2_present_jp2_reconstructed_actual(input@, jp2::raw_inspected_container_view(&inspected),
                raw, crate::options::decode_selection_view(requested), tile, crate::options::decode_options_limits(options),
                crate::image::decoded_image_outcome(decoded_result));
        }
    }
    let image = decoded_result?;
    super::api::validate_jp2_reconstruction_output(inspected.file().header())?;
    if let Some(association) = stream.codestream_header() {
        let header = association
            .parsed_header()
            .ok_or(DecodeError::UnsupportedFeature {
                feature: "unparsed JPX header on reconstruction samples",
            })?;
        super::api::validate_jp2_reconstruction_output(header)?;
    }
    let report = finish_report(
        &layout.info.image_size,
        requested,
        tile,
        image.components().len(),
        options.limits(),
    )?;
    Ok(PresentTileRecoveredReconstructedImage { image, report })
}
