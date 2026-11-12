use super::{
    ArbitraryKernel, CodeBlockPlane, CodingStyle, ComponentTransform, DecodeError, DecodedImage,
    ImageSize, MalformedKind, PacketPrecinctDecoder, PlannedTileComponent, PrepareFold,
    PrepareWorking, PreparedTileComponent, ProgressionCodeBlockPlacement, ProgressionTilePlan,
    Resource, ResourceLimits, SignedMagnitude, SubbandGeometry, TileComponent,
    TransformComponentMut, WaveletBand, WaveletLevel, WaveletTransform, WorkingSubband,
    apply_multiple_component_transform_components, arithmetic_overflow, assemble_image,
    assemble_selected_image, checked_area_u32, checked_index, codestream, decode_prepared_image,
    invalid_decode, inverse_horizontal_5_3, inverse_horizontal_9_7, inverse_horizontal_arbitrary,
    inverse_level_5_3, inverse_level_9_7, inverse_level_arbitrary, inverse_quantize_magnitudes,
    inverse_vertical_5_3, inverse_vertical_9_7, inverse_vertical_arbitrary,
};
#[cfg(verus_keep_ghost)]
use super::{
    planned_components_view, prepare_cell_outcome, prepare_fold_outcome, prepare_plan_view,
    prepare_precincts_view, prepare_style_view, prepare_working_outcome,
    prepared_component_outcome, prepared_component_view, prepared_components_view,
    prepared_tiles_outcome, progression_reconstruction_view, working_bands_view,
    working_subband_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl PreparedTileComponent {
    pub const fn component(&self) -> u16 {
        self.component
    }

    pub const fn width(&self) -> u32 {
        self.width
    }

    pub const fn height(&self) -> u32 {
        self.height
    }

    pub const fn fraction_bits(&self) -> u8 {
        self.fraction_bits
    }

    pub fn samples(&self) -> &[i64] {
        &self.samples
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::image::assembly_tile_view(result) == crate::specs::part1_prepared_as_tile(prepared_component_view(*self)),
    ))]
    pub fn as_tile_component(&self) -> TileComponent<'_> {
        TileComponent {
            component: self.component,
            x: self.x,
            y: self.y,
            width: self.width,
            height: self.height,
            fraction_bits: self.fraction_bits,
            samples: &self.samples,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures
        (result, Seq::new((final(components)@.len() - old(components)@.len()) as nat, |index: int|
            crate::image::transform_component_mut_view(&final(components)@[old(components)@.len() as int + index])))
            == crate::specs::part2_mct_prepared_inputs(
                Seq::new(old(prepared)@.len(), |index: int| prepared_component_view(old(prepared)@[index])),
                codestream::image_size_component_count(size), codestream::image_size_component_infos(size)),
        final(components)@.len() == old(components)@.len()
            + crate::specs::part2_mct_prepared_inputs(
                Seq::new(old(prepared)@.len(), |index: int| prepared_component_view(old(prepared)@[index])),
                codestream::image_size_component_count(size), codestream::image_size_component_infos(size)).1.len(),
        final(components)@.take(old(components)@.len() as int) == old(components)@,
        final(prepared)@.len() == old(prepared)@.len(),
        forall |index: int| 0 <= index < old(prepared)@.len() ==>
            prepared_component_view(final(prepared)@[index])
                == if index < final(components)@.len() - old(components)@.len() {
                    (old(prepared)@[index].component, old(prepared)@[index].x, old(prepared)@[index].y,
                        old(prepared)@[index].width, old(prepared)@[index].height,
                        crate::image::transform_component_final_precision(&final(components)@[old(components)@.len() as int + index]),
                        crate::image::transform_component_final_samples(&final(components)@[old(components)@.len() as int + index]))
                } else { prepared_component_view(old(prepared)@[index]) },
    decreases prepared.len(),
))]
pub(super) fn collect_prepared_transform_components<'a>(
    prepared: &'a mut [PreparedTileComponent],
    size: &ImageSize,
    components: &mut Vec<TransformComponentMut<'a>>,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = prepared@; let ghost prefix = components@; }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost input = Seq::new(original.len(), |index: int| prepared_component_view(original[index])); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_mct_prepared_inputs, 1); }
    let Some((component, remaining)) = prepared.split_first_mut() else {
        return Ok(());
    };
    let info = size.component(component.component)?;
    components.push(TransformComponentMut {
        component: component.component,
        x: component.x,
        y: component.y,
        width: component.width,
        height: component.height,
        x_subsampling: info.x_subsampling,
        y_subsampling: info.y_subsampling,
        fraction_bits: &mut component.fraction_bits,
        samples: &mut component.samples,
    });
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost added = components@[prefix.len() as int]; }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost added_view = crate::image::transform_component_mut_view(&added);
        let ghost tail_input = Seq::new(remaining@.len(), |index: int| prepared_component_view(remaining@[index]));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(input.drop_first() =~= tail_input);
        assert(crate::specs::part2_mct_prepared_input(input[0], codestream::image_size_component_count(size),
            codestream::image_size_component_infos(size)) == Ok(added_view));
    }
    let result = collect_prepared_transform_components(remaining, size, components);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(components@[prefix.len() as int] == added);
        assert(components@.take(prefix.len() as int) =~= prefix);
        let tail = crate::specs::part2_mct_prepared_inputs(tail_input, codestream::image_size_component_count(size),
            codestream::image_size_component_infos(size));
        assert(components@.len() == prefix.len() + 1 + tail.1.len());
        assert(Seq::new((components@.len() - prefix.len()) as nat, |index: int|
            crate::image::transform_component_mut_view(&components@[prefix.len() as int + index]))
            =~= seq![added_view] + tail.1);
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result,
        Seq::new(final(prepared)@.len(), |index: int| prepared_component_view(final(prepared)@[index])),
        *final(work)) == crate::specs::part2_mct_prepared_tiles(
            Seq::new(old(prepared)@.len(), |index: int| prepared_component_view(old(prepared)@[index])),
            codestream::image_size_component_count(size), codestream::image_size_component_infos(size),
            codestream::multiple_component_transform_view(transform), *old(work),
            crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub(super) fn apply_tile_multiple_component_transform(
    prepared: &mut [PreparedTileComponent],
    size: &ImageSize,
    transform: &codestream::MultipleComponentTransform,
    limits: &ResourceLimits,
    work: &mut u64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost before = Seq::new(prepared@.len(), |index: int| prepared_component_view(prepared@[index]));
        let ghost initial_work = *work;
    }
    let mut components = Vec::with_capacity(prepared.len());
    let collected_result = collect_prepared_transform_components(prepared, size, &mut components);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_prepared_inputs_shape(
            before, codestream::image_size_component_count(size), codestream::image_size_component_infos(size));
    }
    match collected_result {
        Ok(()) => {}
        Err(error) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall |index: int| 0 <= index < components@.len() implies
                    crate::image::transform_component_final_samples(&components@[index])
                        == crate::image::transform_component_mut_view(&components@[index]).3
                        && crate::image::transform_component_final_precision(&components@[index])
                            == crate::image::transform_component_mut_view(&components@[index]).2 by {}
                assert(Seq::new(final(prepared)@.len(), |index: int| prepared_component_view(final(prepared)@[index])) =~= before);
            }
            return Err(error);
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(components@.len() == before.len()); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost collected = components@;
        let ghost input = Seq::new(components@.len(), |index: int| crate::image::transform_component_mut_view(&components@[index]));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_mct_unit_result(collected_result);
        assert(collected_result == Result::<(), DecodeError>::Ok(()));
        assert(crate::specs::part2_mct_prepared_inputs(before,
            codestream::image_size_component_count(size), codestream::image_size_component_infos(size)).0 == collected_result);
        assert(input =~= crate::specs::part2_mct_prepared_inputs(before,
            codestream::image_size_component_count(size), codestream::image_size_component_infos(size)).1);
        assert(crate::specs::part2_mct_prepared_inputs(before,
            codestream::image_size_component_count(size), codestream::image_size_component_infos(size)) == (Result::<(), DecodeError>::Ok(()), input));
    }
    let result =
        apply_multiple_component_transform_components(&mut components, transform, limits, work);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((result, Seq::new(components@.len(), |index: int| crate::image::transform_component_mut_view(&components@[index])), *work)
            == crate::specs::part2_mct_transform(input, codestream::multiple_component_transform_view(transform),
                initial_work, crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits)));
        assert forall |index: int| 0 <= index < components@.len() implies
            crate::image::transform_component_final_samples(&collected[index])
                == crate::image::transform_component_mut_view(&components@[index]).3
                && crate::image::transform_component_final_precision(&collected[index])
                    == crate::image::transform_component_mut_view(&components@[index]).2 by {}
        assert(Seq::new(final(prepared)@.len(), |index: int| prepared_component_view(final(prepared)@[index]))
            =~= crate::specs::part2_mct_prepared_result(before,
                Seq::new(components@.len(), |index: int| crate::image::transform_component_mut_view(&components@[index]))));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(destination)@) == crate::specs::part1_quantized_block_pixel(
        old(destination)@, source@, block_width, placement_x, placement_y, x, y,
    ),
))]
pub(super) fn write_quantized_pixel(
    destination: &mut WorkingSubband,
    source: &[i64],
    block_width: u32,
    placement_x: u32,
    placement_y: u32,
    x: u32,
    y: u32,
) -> Result<(), DecodeError> {
    let destination_index = checked_index(
        destination.width,
        placement_x.checked_add(x).ok_or_else(arithmetic_overflow)?,
        placement_y.checked_add(y).ok_or_else(arithmetic_overflow)?,
    )?;
    let source_index = checked_index(block_width, x, y)?;
    if destination_index >= destination.samples.len()
        || destination_index >= destination.visited.len()
        || source_index >= source.len()
        || destination.visited[destination_index]
    {
        return Err(invalid_decode());
    }
    destination.samples[destination_index] =
        *source.get(source_index).ok_or_else(invalid_decode)?;
    destination.visited[destination_index] = true;
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(destination)@) == crate::specs::part1_quantized_block_row(
        old(destination)@, source@, block_width, placement_x, placement_y, y, block_width as nat,
    ),
))]
pub(super) fn write_quantized_row(
    destination: &mut WorkingSubband,
    source: &[i64],
    block_width: u32,
    placement_x: u32,
    placement_y: u32,
    y: u32,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = destination@; }
    let mut x = 0_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant x <= block_width,
        original == old(destination)@,
        crate::specs::part1_quantized_block_row(
            original, source@, block_width, placement_x, placement_y, y, x as nat,
        ) == (Ok(()), destination@),
        decreases block_width - x,
    ))]
    while x < block_width {
        match write_quantized_pixel(
            destination,
            source,
            block_width,
            placement_x,
            placement_y,
            x,
            y,
        ) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_quantized_row_error_persists(
                        original, source@, block_width, placement_x, placement_y, y,
                        x as nat + 1, block_width as nat,
                    );
                }
                return Err(error);
            }
        }
        x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(destination)@) == crate::specs::part1_quantized_block_rows(
        old(destination)@, source@, block_width, placement_x, placement_y, block_height as nat,
    ),
))]
pub(super) fn write_quantized_block(
    destination: &mut WorkingSubband,
    source: &[i64],
    block_width: u32,
    block_height: u32,
    placement_x: u32,
    placement_y: u32,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = destination@; }
    let mut y = 0_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant y <= block_height,
        original == old(destination)@,
        crate::specs::part1_quantized_block_rows(
            original, source@, block_width, placement_x, placement_y, y as nat,
        ) == (Ok(()), destination@),
        decreases block_height - y,
    ))]
    while y < block_height {
        match write_quantized_row(
            destination,
            source,
            block_width,
            placement_x,
            placement_y,
            y,
        ) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_quantized_block_error_persists(
                        original, source@, block_width, placement_x, placement_y,
                        y as nat + 1, block_height as nat,
                    );
                }
                return Err(error);
            }
        }
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepared_component_outcome(result) == crate::specs::part1_prepare_standard_component(
        prepare_plan_view(plan), prepare_precincts_view(precincts@), prepare_style_view(coding_style),
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
    prepared_component_outcome(result) == crate::specs::part2_prepare_component(
        prepare_plan_view(plan), prepare_precincts_view(precincts@), prepare_style_view(coding_style), None,
        crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn prepare_tile_component(
    plan: &PlannedTileComponent,
    precincts: &[PacketPrecinctDecoder],
    coding_style: CodingStyle,
    limits: &ResourceLimits,
) -> Result<PreparedTileComponent, DecodeError> {
    prepare_tile_component_with_kernel(plan, precincts, coding_style, None, limits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepare_working_outcome(result) == crate::specs::part1_prepare_init_prefix(bands@, fraction, crate::limits::resource_decoded_bytes_limit(limits), selected as nat),
    result.is_ok() ==> result->Ok_0.bands.len() == selected,
))]
pub(super) fn initialize_prepare_working(
    bands: &[SubbandGeometry],
    selected: usize,
    fraction: u8,
    limits: &ResourceLimits,
) -> Result<PrepareWorking, DecodeError> {
    let mut working = PrepareWorking {
        bands: Vec::with_capacity(selected),
        bytes: 0,
    };
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_prepare_init_empty(bands@, fraction, crate::limits::resource_decoded_bytes_limit(limits));
        assert(working_bands_view(working.bands@) =~= Seq::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= selected, working.bands.len() == index,
        crate::specs::part1_prepare_init_prefix(bands@, fraction, crate::limits::resource_decoded_bytes_limit(limits), index as nat) == Ok(working@),
        decreases selected - index,
    ))]
    while index < selected {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_prepare_init_step(bands@, fraction, crate::limits::resource_decoded_bytes_limit(limits), index as nat); }
        let operation = append_prepare_subband(&mut working, bands, index, fraction, limits);
        match operation {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! { crate::proofs::production_impl::production_prepare_init_error(
                    bands@, fraction, crate::limits::resource_decoded_bytes_limit(limits), index as nat + 1, selected as nat, error);
                }
                return Err(error);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(operation.is_ok());
            assert(operation->Ok_0 == ());
            assert(operation == Ok(()));
        }
        index += 1;
    }
    Ok(working)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(working).bands.len() < usize::MAX,
    ensures (result, final(working)@) == crate::specs::part1_prepare_append_band(old(working)@, bands@, index, fraction, crate::limits::resource_decoded_bytes_limit(limits)),
    result.is_ok() ==> final(working).bands.len() == old(working).bands.len() + 1,
))]
pub(super) fn append_prepare_subband(
    working: &mut PrepareWorking,
    bands: &[SubbandGeometry],
    index: usize,
    fraction: u8,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let geometry = *bands.get(index).ok_or_else(invalid_decode)?;
    let length = checked_area_u32(geometry.width, geometry.height)?;
    let bytes = (length as u64)
        .checked_mul(9)
        .ok_or_else(arithmetic_overflow)?;
    working.bytes = working
        .bytes
        .checked_add(bytes)
        .ok_or_else(arithmetic_overflow)?;
    if working.bytes > limits.maximum_decoded_bytes() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: limits.maximum_decoded_bytes(),
            actual: working.bytes,
        });
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = working.bands@; }
    working.bands.push(WorkingSubband {
        width: geometry.width,
        height: geometry.height,
        fraction_bits: fraction,
        samples: vec![0_i64; length],
        visited: vec![false; length],
    });
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(working.bands@[working.bands.len() - 1].samples@ =~= Seq::new(length as nat, |i: int| 0i64));
        assert(working.bands@[working.bands.len() - 1].visited@ =~= Seq::new(length as nat, |i: int| false));
        assert(working_bands_view(working.bands@) =~= working_bands_view(before).push(working_subband_view(working.bands@[working.bands.len() - 1])));
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::transform::quantized_coefficients_outcome(result) == crate::specs::part1_prepare_collect_coefficients(crate::tier1::code_block_plane_view(plane)),
))]
pub(super) fn collect_prepare_coefficients(
    plane: &CodeBlockPlane,
) -> Result<Vec<SignedMagnitude>, DecodeError> {
    let count = usize::from(plane.width())
        .checked_mul(usize::from(plane.height()))
        .ok_or_else(arithmetic_overflow)?;
    let mut coefficients = Vec::with_capacity(count);
    let height = plane.height();
    let width = plane.width();
    let mut y = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::transform::representation_proofs::quantized_coefficients_fields(coefficients@);
        crate::proofs::production_impl::production_prepare_rows_empty(crate::tier1::code_block_plane_view(plane));
        assert(crate::transform::quantized_coefficients_view(coefficients@) =~= Seq::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant y <= height,
        width == crate::tier1::code_block_plane_view(plane).width,
        height == crate::tier1::code_block_plane_view(plane).height,
        count as nat == width as nat * height as nat,
        coefficients.len() as nat == y as nat * width as nat,
        crate::specs::part1_prepare_coefficient_rows(crate::tier1::code_block_plane_view(plane), y as nat) == Ok(crate::transform::quantized_coefficients_view(coefficients@)),
        decreases height - y,
    ))]
    while y < height {
        #[cfg(verus_keep_ghost)]
        proof! { crate::transform::representation_proofs::quantized_coefficients_fields(coefficients@); }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost row_start = crate::transform::quantized_coefficients_view(coefficients@); }
        let mut x = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_prepare_row_empty(crate::tier1::code_block_plane_view(plane), y, row_start); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant x <= width, y < height,
            width == crate::tier1::code_block_plane_view(plane).width,
            height == crate::tier1::code_block_plane_view(plane).height,
            count as nat == width as nat * height as nat,
            row_start.len() == y as nat * width as nat,
            coefficients.len() as nat == y as nat * width as nat + x as nat,
            crate::specs::part1_prepare_coefficient_rows(crate::tier1::code_block_plane_view(plane), y as nat) == Ok(row_start),
            crate::specs::part1_prepare_coefficient_row(crate::tier1::code_block_plane_view(plane), y, row_start, x as nat) == Ok(crate::transform::quantized_coefficients_view(coefficients@)),
            decreases width - x,
        ))]
        while x < width {
            #[cfg(verus_keep_ghost)]
            proof! { crate::proofs::production_impl::production_prepare_row_step(crate::tier1::code_block_plane_view(plane), y, row_start, x as nat); }
            let value = match collect_prepare_cell(plane, x, y) {
                Ok(value) => value,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_prepare_row_error(crate::tier1::code_block_plane_view(plane), y, row_start, x as nat + 1, width as nat, error);
                        crate::proofs::production_impl::production_prepare_rows_step(crate::tier1::code_block_plane_view(plane), y as nat);
                        crate::proofs::production_impl::production_prepare_rows_error(crate::tier1::code_block_plane_view(plane), y as nat + 1, height as nat, error);
                    }
                    return Err(error);
                }
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before_values = coefficients@; }
            coefficients.push(value);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::transform::representation_proofs::quantized_coefficients_fields(coefficients@);
                crate::transform::representation_proofs::quantized_coefficients_push(before_values, value);
            }
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_prepare_rows_step(crate::tier1::code_block_plane_view(plane), y as nat);
            assert(y as nat * width as nat + width as nat == (y as nat + 1) * width as nat) by(nonlinear_arith);
        }
        y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(coefficients)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepare_cell_outcome(result) == crate::specs::part1_prepare_signed_cell(crate::tier1::code_block_plane_view(plane), x, y),
))]
pub(super) fn collect_prepare_cell(
    plane: &CodeBlockPlane,
    x: u16,
    y: u16,
) -> Result<SignedMagnitude, DecodeError> {
    let coefficient = plane.coefficient(x, y)?;
    coefficient.signed_magnitude()
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(working)@) == crate::specs::part1_prepare_placement(
        old(working)@, bands@, prepare_precincts_view(precincts@), placement, reversible, crate::limits::resource_decoded_bytes_limit(limits),
    ),
    final(working).bands.len() == old(working).bands.len(),
))]
pub(super) fn place_prepare_block(
    working: &mut PrepareWorking,
    bands: &[SubbandGeometry],
    precincts: &[PacketPrecinctDecoder],
    placement: ProgressionCodeBlockPlacement,
    reversible: bool,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_prepare_placement); }
    if placement.subband_index >= working.bands.len() {
        return Ok(());
    }
    let geometry = *bands
        .get(placement.subband_index)
        .ok_or_else(invalid_decode)?;
    let precinct = precincts
        .get(placement.precinct_index)
        .ok_or_else(invalid_decode)?;
    let decoder = precinct.decoder(placement.decoder_index)?;
    let plane = decoder.plane();
    let width = u32::from(plane.width());
    let height = u32::from(plane.height());
    if placement
        .x
        .checked_add(width)
        .ok_or_else(arithmetic_overflow)?
        > geometry.width
        || placement
            .y
            .checked_add(height)
            .ok_or_else(arithmetic_overflow)?
            > geometry.height
    {
        return Err(invalid_decode());
    }
    let coefficients = collect_prepare_coefficients(plane)?;
    let quantized = inverse_quantize_magnitudes(
        &coefficients,
        geometry.quantization_step,
        geometry.dynamic_range,
        reversible,
        geometry.roi_shift,
        limits,
    )?;
    if quantized.fraction_bits() != if reversible { 0 } else { 16 } {
        return Err(invalid_decode());
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = working.bands@; }
    let destination = working
        .bands
        .get_mut(placement.subband_index)
        .ok_or_else(invalid_decode)?;
    let result = write_quantized_block(
        destination,
        quantized.samples(),
        width,
        height,
        placement.x,
        placement.y,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(working_bands_view(working.bands@) =~= working_bands_view(before).update(
            placement.subband_index as int, working_subband_view(working.bands@[placement.subband_index as int])));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_prepare_coverage(working_bands_view(bands@)),
))]
pub(super) fn validate_prepare_coverage(bands: &[WorkingSubband]) -> Result<(), DecodeError> {
    let mut band = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant band <= bands.len(),
        forall |b: int, i: int| 0 <= b < band && 0 <= i < bands@[b].visited.len() ==> bands@[b].visited@[i],
        decreases bands.len() - band,
    ))]
    while band < bands.len() {
        let subband = &bands[band];
        let mut sample = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant band < bands.len(), sample <= subband.visited.len(),
            subband == &bands@[band as int],
            forall |b: int, i: int| 0 <= b < band && 0 <= i < bands@[b].visited.len() ==> bands@[b].visited@[i],
            forall |i: int| 0 <= i < sample ==> subband.visited@[i],
            decreases subband.visited.len() - sample,
        ))]
        while sample < subband.visited.len() {
            if !subband.visited[sample] {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(working_bands_view(bands@)[band as int].4 == subband.visited@);
                    assert(!working_bands_view(bands@)[band as int].4[sample as int]);
                }
                return Err(invalid_decode());
            }
            sample += 1;
        }
        band += 1;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepared_component_outcome(result) == crate::specs::part2_prepare_component(
        prepare_plan_view(plan), prepare_precincts_view(precincts@), prepare_style_view(coding_style),
        crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits),
    ),
    kernel.is_none() ==> prepared_component_outcome(result) == crate::specs::part1_prepare_standard_component(
        prepare_plan_view(plan), prepare_precincts_view(precincts@), prepare_style_view(coding_style),
        crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn prepare_tile_component_with_kernel(
    plan: &PlannedTileComponent,
    precincts: &[PacketPrecinctDecoder],
    coding_style: CodingStyle,
    kernel: Option<&ArbitraryKernel>,
    limits: &ResourceLimits,
) -> Result<PreparedTileComponent, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_prepare_standard_component);
        reveal(crate::specs::part2_prepare_component);
    }
    if plan.subbands.is_empty() {
        return Err(invalid_decode());
    }
    let reversible = match coding_style.transform {
        WaveletTransform::Reversible5x3 => true,
        WaveletTransform::Irreversible9x7 => false,
        WaveletTransform::Arbitrary(_) => kernel.ok_or_else(invalid_decode)?.reversible(),
    };
    let expected_fraction_bits = if reversible { 0_u8 } else { 16_u8 };
    let selected_subbands =
        coding_style.subband_count_through_resolution(plan.output_resolution)?;
    if selected_subbands > plan.subbands.len() {
        return Err(invalid_decode());
    }
    let mut working = initialize_prepare_working(
        &plan.subbands,
        selected_subbands,
        expected_fraction_bits,
        limits,
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial_working = working@; }

    let mut placement_index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_prepare_placements_empty(
            initial_working, prepare_plan_view(plan), prepare_precincts_view(precincts@), reversible,
            crate::limits::resource_decoded_bytes_limit(limits),
        );
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant placement_index <= plan.placements.len(),
            working.bands.len() == selected_subbands,
            plan.subbands.len() > 0,
            selected_subbands <= plan.subbands.len(),
            expected_fraction_bits == crate::specs::part1_prepare_fraction(reversible),
            crate::specs::part1_subband_count_through_resolution(
                prepare_style_view(coding_style).1, prepare_style_view(coding_style).2, plan.output_resolution,
            ) == Ok(selected_subbands),
            crate::specs::part1_prepare_init_prefix(plan.subbands@, expected_fraction_bits, crate::limits::resource_decoded_bytes_limit(limits), selected_subbands as nat) == Ok(initial_working),
            kernel.is_none() ==> !matches!(coding_style.transform, WaveletTransform::Arbitrary(_)),
            kernel.is_none() ==> reversible == matches!(coding_style.transform, WaveletTransform::Reversible5x3),
            crate::specs::part2_prepare_reversible(prepare_style_view(coding_style), crate::transform::arbitrary_kernel_option(kernel)) == Ok(reversible),
            crate::specs::part1_prepare_placements(
                initial_working, prepare_plan_view(plan), prepare_precincts_view(precincts@), reversible,
                crate::limits::resource_decoded_bytes_limit(limits), placement_index as nat,
            ) == (Ok(()), working@),
            decreases plan.placements.len() - placement_index,
        )
    )]
    while placement_index < plan.placements.len() {
        let placement = *plan
            .placements
            .get(placement_index)
            .ok_or_else(invalid_decode)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_prepare_placements_step(
                initial_working, prepare_plan_view(plan), prepare_precincts_view(precincts@), reversible,
                crate::limits::resource_decoded_bytes_limit(limits), placement_index as nat,
            );
        }
        let operation = place_prepare_block(
            &mut working,
            &plan.subbands,
            precincts,
            placement,
            reversible,
            limits,
        );
        match operation {
            Ok(()) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(operation.is_ok());
                    assert(operation->Ok_0 == ());
                    assert(operation == Ok(()));
                }
            }
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_prepare_placements_error(
                        initial_working, prepare_plan_view(plan), prepare_precincts_view(precincts@), reversible,
                        crate::limits::resource_decoded_bytes_limit(limits), placement_index as nat + 1, plan.placements.len() as nat,
                    );
                    assert(crate::specs::part1_prepare_placements(
                        initial_working, prepare_plan_view(plan), prepare_precincts_view(precincts@), reversible,
                        crate::limits::resource_decoded_bytes_limit(limits), plan.placements.len() as nat,
                    ).0 == Err(error));
                    reveal(crate::specs::part1_prepare_standard_component);
                    reveal(crate::specs::part2_prepare_component);
                    assert(crate::specs::part2_prepare_component(
                        prepare_plan_view(plan), prepare_precincts_view(precincts@), prepare_style_view(coding_style),
                        crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits),
                    ) == Err(error));
                    assert(kernel.is_none() ==> crate::specs::part1_prepare_standard_component(
                        prepare_plan_view(plan), prepare_precincts_view(precincts@), prepare_style_view(coding_style),
                        crate::limits::resource_decoded_bytes_limit(limits),
                    ) == Err(error));
                }
                return Err(error);
            }
        }
        placement_index = placement_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    validate_prepare_coverage(&working.bands)?;

    let folded = reconstruct_prepare_working(
        &working.bands,
        plan,
        coding_style,
        reversible,
        kernel,
        limits,
    )?;
    finish_prepared_component(plan, folded, expected_fraction_bits)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepare_fold_outcome(result) == crate::specs::part2_prepare_reconstruct(
        working_bands_view(working@), prepare_plan_view(plan), prepare_style_view(coding_style), reversible,
        crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn reconstruct_prepare_working(
    working: &[WorkingSubband],
    plan: &PlannedTileComponent,
    coding_style: CodingStyle,
    reversible: bool,
    kernel: Option<&ArbitraryKernel>,
    limits: &ResourceLimits,
) -> Result<PrepareFold, DecodeError> {
    let ll = working.first().ok_or_else(invalid_decode)?;
    let mut folded = PrepareFold {
        width: ll.width,
        height: ll.height,
        samples: ll.samples.clone(),
        first_detail: 1,
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = folded@; }
    let mut resolution = 1_u8;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_prepare_kernel_fold_empty(initial, working_bands_view(working@), plan.subbands@, prepare_style_view(coding_style), reversible, crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits)); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= resolution as int <= plan.output_resolution as int + 1,
        working.len() > 0, ll == &working@[0],
        initial == (ll.width, ll.height, ll.samples@, 1usize),
        crate::specs::part2_prepare_fold(
            initial, working_bands_view(working@), plan.subbands@, prepare_style_view(coding_style), reversible,
            crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits), (resolution - 1) as nat,
        ) == Ok(folded@),
        decreases plan.output_resolution as int + 1 - resolution as int,
    ))]
    while resolution <= plan.output_resolution {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_prepare_kernel_fold_step(initial, working_bands_view(working@), plan.subbands@, prepare_style_view(coding_style), reversible, crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits), (resolution - 1) as nat);
            crate::proofs::production_impl::production_prepare_kernel_fold_error_guard(initial, working_bands_view(working@), plan.subbands@, prepare_style_view(coding_style), reversible, crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits), resolution as nat, plan.output_resolution as nat);
        }
        let direction = coding_style.direction_for_resolution(resolution)?;
        if matches!(direction, crate::codestream::DecompositionDirection::None) {
            resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
            continue;
        }
        folded = reconstruct_prepare_resolution(
            working, plan, folded, direction, reversible, kernel, limits,
        )?;
        if resolution == u8::MAX {
            return Err(arithmetic_overflow());
        }
        let modeled_resolution = crate::refinement::wavelet_next_resolution(resolution);
        resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
        if resolution != modeled_resolution {
            return Err(arithmetic_overflow());
        }
    }
    Ok(folded)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepare_fold_outcome(result) == crate::specs::part2_prepare_resolution(
        before@, working_bands_view(working@), plan.subbands@, direction, reversible,
        crate::transform::arbitrary_kernel_option(kernel), crate::limits::resource_decoded_bytes_limit(limits),
    ),
))]
pub(super) fn reconstruct_prepare_resolution(
    working: &[WorkingSubband],
    plan: &PlannedTileComponent,
    before: PrepareFold,
    direction: crate::codestream::DecompositionDirection,
    reversible: bool,
    kernel: Option<&ArbitraryKernel>,
    limits: &ResourceLimits,
) -> Result<PrepareFold, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_prepare_resolution);
        reveal(crate::specs::part2_kernel_inverse_horizontal);
        reveal(crate::specs::part2_kernel_inverse_vertical);
        reveal(crate::specs::part2_kernel_inverse_level);
    }
    let mut first_detail = before.first_detail;
    let reconstructed_width = before.width;
    let reconstructed_height = before.height;
    let reconstructed = before.samples;
    let expected_fraction_bits = if reversible { 0 } else { 16 };
    let detail = working.get(first_detail).ok_or_else(invalid_decode)?;
    if detail.fraction_bits != expected_fraction_bits {
        return Err(invalid_decode());
    }
    let geometry = *plan.subbands.get(first_detail).ok_or_else(invalid_decode)?;
    let low = WaveletBand {
        width: reconstructed_width,
        height: reconstructed_height,
        samples: &reconstructed,
    };
    let plane = match direction {
        crate::codestream::DecompositionDirection::Horizontal => {
            first_detail = first_detail
                .checked_add(crate::refinement::wavelet_detail_advance(1))
                .ok_or_else(arithmetic_overflow)?;
            let high = WaveletBand {
                width: detail.width,
                height: detail.height,
                samples: &detail.samples,
            };
            if let Some(kernel) = kernel {
                inverse_horizontal_arbitrary(
                    low,
                    high,
                    geometry.resolution_width,
                    geometry.low_pass_first_x,
                    kernel,
                    limits,
                )?
            } else if reversible {
                inverse_horizontal_5_3(
                    low,
                    high,
                    geometry.resolution_width,
                    geometry.low_pass_first_x,
                    limits,
                )?
            } else {
                inverse_horizontal_9_7(
                    low,
                    high,
                    geometry.resolution_width,
                    geometry.low_pass_first_x,
                    limits,
                )?
            }
        }
        crate::codestream::DecompositionDirection::Vertical => {
            first_detail = first_detail
                .checked_add(crate::refinement::wavelet_detail_advance(2))
                .ok_or_else(arithmetic_overflow)?;
            let high = WaveletBand {
                width: detail.width,
                height: detail.height,
                samples: &detail.samples,
            };
            if let Some(kernel) = kernel {
                inverse_vertical_arbitrary(
                    low,
                    high,
                    geometry.resolution_height,
                    geometry.low_pass_first_y,
                    kernel,
                    limits,
                )?
            } else if reversible {
                inverse_vertical_5_3(
                    low,
                    high,
                    geometry.resolution_height,
                    geometry.low_pass_first_y,
                    limits,
                )?
            } else {
                inverse_vertical_9_7(
                    low,
                    high,
                    geometry.resolution_height,
                    geometry.low_pass_first_y,
                    limits,
                )?
            }
        }
        crate::codestream::DecompositionDirection::TwoDimensional => {
            let lh = working
                .get(
                    first_detail
                        .checked_add(1)
                        .ok_or_else(arithmetic_overflow)?,
                )
                .ok_or_else(invalid_decode)?;
            let hh = working
                .get(
                    first_detail
                        .checked_add(2)
                        .ok_or_else(arithmetic_overflow)?,
                )
                .ok_or_else(invalid_decode)?;
            if lh.fraction_bits != expected_fraction_bits
                || hh.fraction_bits != expected_fraction_bits
            {
                return Err(invalid_decode());
            }
            first_detail = first_detail
                .checked_add(crate::refinement::wavelet_detail_advance(3))
                .ok_or_else(arithmetic_overflow)?;
            let level = WaveletLevel {
                ll: low,
                hl: WaveletBand {
                    width: detail.width,
                    height: detail.height,
                    samples: &detail.samples,
                },
                lh: WaveletBand {
                    width: lh.width,
                    height: lh.height,
                    samples: &lh.samples,
                },
                hh: WaveletBand {
                    width: hh.width,
                    height: hh.height,
                    samples: &hh.samples,
                },
                output_width: geometry.resolution_width,
                output_height: geometry.resolution_height,
                low_pass_first_x: geometry.low_pass_first_x,
                low_pass_first_y: geometry.low_pass_first_y,
            };
            if let Some(kernel) = kernel {
                inverse_level_arbitrary(level, kernel, limits)?
            } else if reversible {
                inverse_level_5_3(level, limits)?
            } else {
                inverse_level_9_7(level, limits)?
            }
        }
        crate::codestream::DecompositionDirection::None => {
            return Err(invalid_decode());
        }
    };
    if plane.fraction_bits() != expected_fraction_bits {
        return Err(invalid_decode());
    }
    copy_prepare_plane(plane, first_detail)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepare_fold_outcome(result) == crate::specs::part1_prepare_copy_plane(crate::transform::reconstructed_plane_view(plane), first_detail),
))]
pub(super) fn copy_prepare_plane(
    plane: crate::transform::ReconstructedPlane,
    first_detail: usize,
) -> Result<PrepareFold, DecodeError> {
    let reconstructed_width = plane.width();
    let reconstructed_height = plane.height();
    let plane_sample_count = plane.samples().len();
    let mut next_samples = Vec::with_capacity(plane_sample_count);
    let mut sample_index = 0_usize;
    #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant sample_index <= plane_sample_count,
                    plane_sample_count == crate::transform::reconstructed_plane_view(plane).3.len(),
                    reconstructed_width == crate::transform::reconstructed_plane_view(plane).0,
                    reconstructed_height == crate::transform::reconstructed_plane_view(plane).1,
                    next_samples@ == crate::transform::reconstructed_plane_view(plane).3.subrange(0, sample_index as int),
                decreases plane_sample_count - sample_index,
            )
        )]
    while sample_index < plane_sample_count {
        next_samples.push(
            *plane
                .samples()
                .get(sample_index)
                .ok_or_else(invalid_decode)?,
        );
        sample_index = sample_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(next_samples@ =~= crate::transform::reconstructed_plane_view(plane).3); }
    Ok(PrepareFold {
        width: reconstructed_width,
        height: reconstructed_height,
        samples: next_samples,
        first_detail,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepared_component_outcome(result) == crate::specs::part1_prepare_finish(prepare_plan_view(plan), fraction, folded@),
))]
pub(super) fn finish_prepared_component(
    plan: &PlannedTileComponent,
    folded: PrepareFold,
    fraction: u8,
) -> Result<PreparedTileComponent, DecodeError> {
    if folded.width != plan.width
        || folded.height != plan.height
        || folded.samples.len() != checked_area_u32(plan.width, plan.height)?
    {
        return Err(invalid_decode());
    }
    Ok(PreparedTileComponent {
        component: plan.component,
        x: plan.x,
        y: plan.y,
        width: plan.width,
        height: plan.height,
        fraction_bits: fraction,
        samples: folded.samples,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures prepared_tiles_outcome(result) == Ok(prepared_components_view(prepared@)),
))]
pub(super) fn prepared_tile_views<'a>(
    prepared: &'a [PreparedTileComponent],
) -> Result<Vec<TileComponent<'a>>, DecodeError> {
    let mut tiles = Vec::with_capacity(prepared.len());
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= prepared.len(),
        tiles@.len() == index,
        crate::image::assembly_tiles_view(tiles@) == prepared_components_view(prepared@).take(index as int),
        decreases prepared.len() - index,
    ))]
    while index < prepared.len() {
        let tile = prepared
            .get(index)
            .ok_or_else(invalid_decode)?
            .as_tile_component();
        #[cfg(verus_keep_ghost)]
        proof! { assert(crate::image::assembly_tile_view(tile) == prepared_components_view(prepared@)[index as int]); }
        tiles.push(tile);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::image::assembly_tiles_view(tiles@) =~= prepared_components_view(prepared@).take(index as int + 1));
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(prepared_components_view(prepared@).take(prepared@.len() as int) =~= prepared_components_view(prepared@)); }
    Ok(tiles)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_image_outcome(result) == crate::specs::part2_assemble_prepared(
        crate::image::assembly_size_view(size), prepared_components_view(prepared@), selection,
        crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub(super) fn assemble_prepared_components(
    size: &ImageSize,
    prepared: &[PreparedTileComponent],
    selection: Option<([u32; 4], u8)>,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    let tiles = prepared_tile_views(prepared)?;
    match selection {
        None => assemble_image(size, &tiles, limits),
        Some((region, levels)) => assemble_selected_image(size, &tiles, region, levels, limits),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::image::decoded_image_outcome(result) == crate::specs::part1_progression_prepared_image(
        crate::image::assembly_size_view(size), progression_reconstruction_view(plan).0, progression_reconstruction_view(plan).1,
        progression_reconstruction_view(plan).2, progression_reconstruction_view(plan).3, crate::limits::resource_decoded_bytes_limit(limits)),
))]
pub fn decode_progression_prepared_image(
    size: &ImageSize,
    plan: &ProgressionTilePlan,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost plans = planned_components_view(plan); let ghost precincts = prepare_precincts_view(plan.precincts@); }
    let mut prepared = Vec::with_capacity(plan.components.len());
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_reconstruct_components_empty(Seq::empty(), plans, precincts,
            plan.component_coding_styles, Seq::empty(), crate::limits::resource_decoded_bytes_limit(limits));
    }
    let mut component_index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component_index <= plan.components.len(),
            plans == planned_components_view(plan), precincts == prepare_precincts_view(plan.precincts@),
            crate::specs::part2_reconstruct_components_prefix(Seq::empty(), plans, precincts, plan.component_coding_styles,
                Seq::empty(), crate::limits::resource_decoded_bytes_limit(limits), component_index as nat)
                    == (Ok(()), prepared_components_view(prepared@)),
            decreases plan.components.len() - component_index,
        )
    )]
    while component_index < plan.components.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_reconstruct_components_step(Seq::empty(), plans, precincts, plan.component_coding_styles,
                Seq::empty(), crate::limits::resource_decoded_bytes_limit(limits), component_index as nat);
            crate::proofs::production_impl::production_reconstruct_components_error(Seq::empty(), plans, precincts, plan.component_coding_styles,
                Seq::empty(), crate::limits::resource_decoded_bytes_limit(limits), component_index as nat + 1, plans.len());
        }
        let component = plan
            .components
            .get(component_index)
            .ok_or_else(invalid_decode)?;
        let style = plan.component_coding_styles.style(component.component)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            if let WaveletTransform::Arbitrary(index) = style.transform {
                crate::proofs::production_impl::production_kernel_registry_empty(Seq::empty(), index);
            }
        }
        prepared.push(prepare_tile_component(
            component,
            &plan.precincts,
            style,
            limits,
        )?);
        component_index = component_index
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    let tile_components = prepared_tile_views(&prepared)?;
    let component_transform = if !plan.coding_style.multiple_component_transform {
        ComponentTransform::None
    } else {
        match plan.coding_style.transform {
            WaveletTransform::Reversible5x3 => ComponentTransform::Reversible,
            WaveletTransform::Irreversible9x7 => ComponentTransform::Irreversible,
            WaveletTransform::Arbitrary(_) => {
                return Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::MissingRequiredStructure,
                });
            }
        }
    };
    decode_prepared_image(size, &tile_components, component_transform, limits)
}
