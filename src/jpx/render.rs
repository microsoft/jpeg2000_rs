//! Public rendering entry points, supplied layers, and canvas assembly.
use super::compositing::composite_placed_layer;
use super::inspection::{effective_layer_count, ensure_jpx, inspect_file};
use super::layer_decode::decode_effective_layer;
use super::resources::{
    arithmetic_overflow, charge_layer_bytes, checked_area, enforce_limit, invalid_layer,
};
use super::timeline::select_frame_instructions;
use super::{
    ConvertedColorSpace, ConvertedImage, DecodeError, DecodeOptions, Jp2File, JpxFrameInfo,
    JpxInspection, JpxInstructionInfo, OwnedLayer, Resource, ResourceLimits, SuppliedLayer, jp2,
};
#[cfg(verus_keep_ghost)]
use super::{
    collected_layers_result, composition_source_view, frame_views, inspection_composition_view,
    instruction_views, layer_owned_planes_push, owned_layer_outcome, placement_views,
    placement_views_push, raw_jpx_file_known, raw_jpx_geometries_known,
    raw_jpx_inspection_outcome_known, raw_jpx_render_metadata_known, supplied_views,
    supplied_views_push,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Renders one layer while retaining its straight/premultiplied sample representation.
/// The alpha channel records that representation; frame/composition output is straight alpha.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_render_raw_jpx_layer(
        input@, layer_index, crate::options::decode_options_limits(options)),
))]
pub fn render_jpx_layer(
    input: &[u8],
    layer_index: usize,
    options: &DecodeOptions,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_render_raw_jpx_layer_unfold(input@, layer_index, crate::options::decode_options_limits(options));
    }
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! {
        jp2::raw_render_file_known(jp2::raw_inspected_file_reference(&inspected));
        jp2::raw_jpx_inspection_parts_known(jp2::raw_inspected_file_reference(&inspected));
    }
    ensure_jpx(inspected.file())?;
    decode_effective_layer(inspected.file(), layer_index, options)?.into_image()
}

pub fn render_jpx_composition(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<ConvertedImage, DecodeError> {
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    let file = inspected.file();
    ensure_jpx(file)?;
    let metadata = inspect_file(file, inspected.codestreams(), options.limits())?;
    let has_frames = match metadata.composition() {
        Some(composition) => !composition.frames().is_empty(),
        None => false,
    };
    if has_frames {
        return render_inspected_frame(file, &metadata, 0, options);
    }
    let (width, height) = composition_dimensions(&metadata, options.limits())?;
    let mut layers = Vec::new();
    let layer_count = effective_layer_count(file);
    let mut layer_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant layer_index <= layer_count,
            decreases layer_count - layer_index,
        )
    )]
    while layer_index < layer_count {
        layers.push((
            decode_effective_layer(file, layer_index, options)?,
            JpxInstructionInfo {
                layer_index,
                target_x: 0,
                target_y: 0,
                target_width: metadata.layer(layer_index)?.width(),
                target_height: metadata.layer(layer_index)?.height(),
                source_x: 0,
                source_y: 0,
                source_width: 0,
                source_height: 0,
                persistent: true,
                next_reuse: 0,
            },
        ));
        layer_index = layer_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    render_decoded_layers(
        width,
        height,
        &layers,
        options.limits().maximum_decoded_bytes(),
        options.limits(),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_render_raw_jpx_frame(
        input@, frame_index, crate::options::decode_options_limits(options)),
))]
pub fn render_jpx_frame(
    input: &[u8],
    frame_index: usize,
    options: &DecodeOptions,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_render_raw_jpx_frame_unfold(input@, frame_index, crate::options::decode_options_limits(options));
        raw_jpx_inspection_outcome_known();
    }
    let inspected = jp2::parse_and_inspect(input, options.limits())?;
    let file = inspected.file();
    #[cfg(verus_keep_ghost)]
    proof! {
        jp2::raw_render_file_known(file);
        jp2::raw_jpx_inspection_parts_known(file);
        raw_jpx_file_known(file);
        raw_jpx_geometries_known(jp2::raw_inspected_native_infos(&inspected));
    }
    ensure_jpx(file)?;
    let metadata = inspect_file(file, inspected.codestreams(), options.limits())?;
    #[cfg(verus_keep_ghost)]
    proof! { raw_jpx_render_metadata_known(&metadata); }
    render_inspected_frame(file, &metadata, frame_index, options)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::color::converted_image_result(result) == crate::specs::part2_render_inspected_source_frame(
        jp2::jpx_file_decode_view(file), jp2::source_file_layer_configs(file), inspection_composition_view(metadata),
        requested_frame, crate::options::decode_options_limits(options)),
))]
pub(super) fn render_inspected_frame(
    file: &Jp2File<'_>,
    metadata: &JpxInspection,
    requested_frame: usize,
    options: &DecodeOptions,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = jp2::jpx_file_decode_view(file);
        let ghost layers = jp2::source_file_layer_configs(file);
        let ghost limits = crate::options::decode_options_limits(options);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_render_inspected_source_frame);
    }
    let composition = metadata
        .composition()
        .ok_or(DecodeError::FrameIndexOutOfRange {
            index: requested_frame,
            frames: 0,
        })?;
    let instructions = select_frame_instructions(
        composition.frames(),
        composition.loop_count(),
        requested_frame,
    )?;
    let mut supplied = Vec::new();
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost selected = instruction_views(instructions@); }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_frame_source_supplies);
        assert(supplied_views(supplied@) =~= Seq::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= instructions.len(),
                selected == instruction_views(instructions@),
                input == jp2::jpx_file_decode_view(file),
                layers == jp2::source_file_layer_configs(file),
                limits == crate::options::decode_options_limits(options),
            invariant_except_break
                crate::specs::part2_frame_source_supplies(input, layers, selected, limits, index as nat)
                    == (supplied_views(supplied@), false),
            ensures supplied_views(supplied@)
                == crate::specs::part2_frame_source_supplies(input, layers, selected, limits, selected.len()).0,
            decreases instructions.len() - index,
        )
    )]
    while index < instructions.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_frame_source_supplies_step(input, layers, selected, limits, index as nat);
        }
        let instruction = instructions[index];
        let outcome = decode_effective_layer(file, instruction.layer_index(), options);
        let failed = outcome.is_err();
        #[cfg(verus_keep_ghost)]
        proof! {
            supplied_views_push(supplied@, (instruction.layer_index, Some(outcome)));
        }
        supplied.push((instruction.layer_index, Some(outcome)));
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_frame_source_supplies(input, layers, selected, limits, index as nat + 1)
                == (supplied_views(supplied@), failed));
        }
        if failed {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_frame_source_supplies_stopped(
                    input, layers, selected, limits, index as nat + 1, selected.len());
            }
            break;
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    render_normalized_frame(
        composition.width(),
        composition.height(),
        composition.frames(),
        composition.loop_count(),
        requested_frame,
        supplied,
        options.limits().maximum_decoded_bytes(),
        options.limits(),
    )
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (owned_layer_outcome(result), supplied_views(final(supplied)@))
            == crate::specs::part2_take_supplied_layer(supplied_views(old(supplied)@), reference),
    )
)]
fn take_supplied_layer(
    supplied: &mut [SuppliedLayer],
    reference: usize,
) -> Result<OwnedLayer, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = supplied_views(supplied@); }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= supplied.len(), supplied_views(supplied@) == input,
                input == supplied_views(old(supplied)@),
                crate::specs::part2_supply_search(input, reference, 0) == crate::specs::part2_supply_search(input, reference, index as nat),
            decreases supplied.len() - index,
        )
    )]
    while index < supplied.len() {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_supply_search_step(input, reference, index as nat); }
        if supplied[index].0 == reference && supplied[index].1.is_some() {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::specs::part2_supply_search(input, reference, 0) == Some(index as nat));
            }
            let outcome = supplied[index].1.take().ok_or_else(invalid_layer)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(supplied_views(supplied@) =~= input.update(index as int, (reference, None)));
                assert(owned_layer_outcome(outcome) == input[index as int].1.unwrap());
                assert((owned_layer_outcome(outcome), supplied_views(supplied@))
                    == crate::specs::part2_take_supplied_layer(input, reference));
            }
            let layer = outcome?;
            return Ok(layer);
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_supply_search_step(input, reference, index as nat); }
    Err(invalid_layer())
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures collected_layers_result(result) == crate::specs::part2_collect_supplied_layers(
            instruction_views(instructions@), supplied_views(supplied@)),
    )
)]
fn collect_supplied_layers(
    instructions: &[JpxInstructionInfo],
    supplied: Vec<SuppliedLayer>,
) -> Result<Vec<(OwnedLayer, JpxInstructionInfo)>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = instruction_views(instructions@);
        let ghost bank = supplied_views(supplied@);
    }
    let mut available = supplied;
    let mut placements = Vec::new();
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_gather_base(input, bank);
        assert(placement_views(placements@) =~= Seq::<crate::specs::Part2Placement>::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= instructions.len(), input == instruction_views(instructions@),
                bank == supplied_views(supplied@),
                crate::specs::part2_gather_layers(input, bank, index as nat)
                    == (Ok(()), placement_views(placements@), supplied_views(available@)),
            decreases instructions.len() - index,
        )
    )]
    while index < instructions.len() {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_gather_step(input, bank, index as nat); }
        let instruction = instructions[index];
        let outcome = take_supplied_layer(&mut available, instruction.layer_index);
        #[cfg(verus_keep_ghost)]
        proof! {
            if outcome.is_err() {
                assert(crate::specs::part2_gather_layers(input, bank, index as nat + 1).0 == Err(outcome.err().unwrap()));
                crate::proofs::production_impl::production_gather_error(input, bank, index as nat + 1);
            }
        }
        let layer = outcome?;
        let placement = (layer, instruction);
        #[cfg(verus_keep_ghost)]
        proof! { placement_views_push(placements@, placement); }
        placements.push(placement);
        index += 1;
    }
    Ok(placements)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::color::converted_image_result(result) == crate::specs::part2_render_normalized_frame(
            width, height, frame_views(frames@), loop_count, requested_frame, supplied_views(supplied@),
            maximum_decoded_bytes, crate::limits::resource_work_limit(limits)),
    )
)]
pub(super) fn render_normalized_frame(
    width: u32,
    height: u32,
    frames: &[JpxFrameInfo],
    loop_count: u8,
    requested_frame: usize,
    supplied: Vec<SuppliedLayer>,
    maximum_decoded_bytes: u64,
    limits: &ResourceLimits,
) -> Result<ConvertedImage, DecodeError> {
    let instructions = select_frame_instructions(frames, loop_count, requested_frame)?;
    let placements = collect_supplied_layers(&instructions, supplied)?;
    render_decoded_layers(width, height, &placements, maximum_decoded_bytes, limits)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures crate::color::converted_image_result(result) == crate::specs::part2_render_layers(
            width, height, placement_views(layers@), maximum_decoded_bytes, crate::limits::resource_work_limit(limits),
        ),
    )
)]
pub(super) fn render_decoded_layers(
    width: u32,
    height: u32,
    layers: &[(OwnedLayer, JpxInstructionInfo)],
    maximum_decoded_bytes: u64,
    limits: &ResourceLimits,
) -> Result<ConvertedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost input = placement_views(layers@);
        let ghost initial = crate::specs::part2_render_initial(width, height, input);
        let ghost work_limit = crate::limits::resource_work_limit(limits);
    }
    if layers.is_empty() {
        return Err(invalid_layer());
    }
    let mut output_space = ConvertedColorSpace::Grayscale;
    let mut scan = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant scan <= layers.len(), input == placement_views(layers@),
                matches!(output_space, ConvertedColorSpace::Srgb)
                    <==> exists|i: int| 0 <= i < scan && #[trigger] input[i].0.2 == ConvertedColorSpace::Srgb,
            decreases layers.len() - scan,
        )
    )]
    while scan < layers.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(input[scan as int].0.2 == layers@[scan as int].0.color_space);
        }
        if matches!(layers[scan].0.color_space, ConvertedColorSpace::Srgb) {
            output_space = ConvertedColorSpace::Srgb;
        }
        scan += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output_space == crate::specs::part2_render_space(input));
        crate::proofs::production_impl::production_render_empty(width, height, input, initial, maximum_decoded_bytes, work_limit);
    }
    let color_count = if matches!(output_space, ConvertedColorSpace::Srgb) {
        3
    } else {
        1
    };
    let pixels = match checked_area(width, height) {
        Ok(pixels) => pixels,
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_render_error(width, height, input, initial, maximum_decoded_bytes, work_limit, 0);
            }
            return Err(error);
        }
    };
    let mut output_colors = Vec::with_capacity(color_count);
    let mut color = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant color <= color_count,
                input == placement_views(layers@),
                initial == crate::specs::part2_render_initial(width, height, input),
                crate::specs::part2_layer_area(width, height) == Ok(pixels),
                output_space == crate::specs::part2_render_space(input),
                color_count as nat == crate::specs::part2_layer_color_count(output_space),
                crate::specs::part2_composition_planes(output_colors@) == Seq::new(color as nat, |i: int| Seq::new(pixels as nat, |j: int| 0u16)),
            decreases color_count - color,
        )
    )]
    while color < color_count {
        let samples = vec![0_u16; pixels];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(samples@ =~= Seq::new(pixels as nat, |j: int| 0u16));
            layer_owned_planes_push(output_colors@, samples);
        }
        output_colors.push(samples);
        color += 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_composition_planes(output_colors@) =~= Seq::new(color as nat, |i: int| Seq::new(pixels as nat, |j: int| 0u16)));
        }
    }
    let mut output_alpha = vec![0_u16; pixels];
    let output_channels = (color_count as u64 + 1) * 2;
    let mut decoded_bytes = match (pixels as u64).checked_mul(output_channels) {
        Some(bytes) => bytes,
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_render_error(width, height, input, initial, maximum_decoded_bytes, work_limit, 0);
            }
            return Err(arithmetic_overflow());
        }
    };
    let mut work = pixels as u64;
    let mut layer_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant layer_index <= layers.len(),
                input == placement_views(layers@),
                initial == crate::specs::part2_render_initial(width, height, input),
                output_space == crate::specs::part2_render_space(input),
                work_limit == crate::limits::resource_work_limit(limits),
                crate::specs::part2_render_prefix(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat)
                    == (Ok(()), crate::specs::part2_composition_planes(output_colors@), output_alpha@, work as nat, decoded_bytes as nat),
            decreases layers.len() - layer_index,
        )
    )]
    while layer_index < layers.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost before = (Ok::<(), DecodeError>(()), crate::specs::part2_composition_planes(output_colors@), output_alpha@, work as nat, decoded_bytes as nat);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_render_step(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat);
        }
        let (layer, instruction) = &layers[layer_index];
        let charge = charge_layer_bytes(layer, &mut decoded_bytes, maximum_decoded_bytes);
        #[cfg(verus_keep_ghost)]
        proof! {
            if charge.is_err() {
                assert(crate::specs::part2_render_prefix(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat + 1)
                    == (charge, crate::specs::part2_composition_planes(output_colors@), output_alpha@, work as nat, decoded_bytes as nat));
                crate::proofs::production_impl::production_render_error(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat + 1);
            }
        }
        charge?;
        let outcome = composite_placed_layer(
            width,
            height,
            output_space,
            layer,
            *instruction,
            &mut output_colors,
            &mut output_alpha,
            &mut work,
            limits,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part2_render_step(width, height, output_space, input[layer_index as int], before,
                maximum_decoded_bytes, work_limit) == (outcome, crate::specs::part2_composition_planes(output_colors@), output_alpha@, work as nat, decoded_bytes as nat));
            assert(crate::specs::part2_render_prefix(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat + 1)
                == (outcome, crate::specs::part2_composition_planes(output_colors@), output_alpha@, work as nat, decoded_bytes as nat));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if outcome.is_err() {
                crate::proofs::production_impl::production_render_error(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat + 1);
            }
        }
        outcome?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(outcome == Ok(()));
            assert(crate::specs::part2_render_prefix(width, height, input, initial, maximum_decoded_bytes, work_limit, layer_index as nat + 1)
                == (Ok(()), crate::specs::part2_composition_planes(output_colors@), output_alpha@, work as nat, decoded_bytes as nat));
        }
        layer_index = layer_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    crate::color::from_composited(width, height, output_space, output_colors, output_alpha)
}

fn composition_dimensions(
    inspection: &JpxInspection,
    limits: &ResourceLimits,
) -> Result<(u32, u32), DecodeError> {
    let (width, height) = match inspection.composition() {
        Some(composition) => (composition.width(), composition.height()),
        None => {
            let mut width = 0_u32;
            let mut height = 0_u32;
            let layer_count = inspection.layers().len();
            let mut index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant index <= layer_count,
                    decreases layer_count - index,
                )
            )]
            while index < layer_count {
                let layer = inspection.layer(index)?;
                width = width.max(
                    layer
                        .horizontal_offset()
                        .checked_add(layer.width())
                        .ok_or_else(arithmetic_overflow)?,
                );
                height = height.max(
                    layer
                        .vertical_offset()
                        .checked_add(layer.height())
                        .ok_or_else(arithmetic_overflow)?,
                );
                index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            (width, height)
        }
    };
    if width == 0 || height == 0 {
        return Err(invalid_layer());
    }
    enforce_limit(
        Resource::Width,
        u64::from(limits.maximum_width()),
        u64::from(width),
    )?;
    enforce_limit(
        Resource::Height,
        u64::from(limits.maximum_height()),
        u64::from(height),
    )?;
    enforce_limit(
        Resource::Pixels,
        limits.maximum_pixels(),
        u64::from(width)
            .checked_mul(u64::from(height))
            .ok_or_else(arithmetic_overflow)?,
    )?;
    Ok((width, height))
}
