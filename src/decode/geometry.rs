use super::{
    CodingStyle, ComponentCodingStyles, ComponentResolutionGeometry, DecodeError, ImageSize,
    MalformedKind, PacketGrid, Quantization, QuantizationStep, QuantizationStyle, ResourceLimits,
    SelectionError, SubbandGeometry, SubbandOrientation, arithmetic_overflow, ceil_div_u32,
    floor_div_u32, invalid_decode,
};
#[cfg(verus_keep_ghost)]
use super::{
    Resource, codestream, resolution_counts_outcome, resolution_geometry_style, subbands_outcome,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_resolution_geometry(
        codestream::selection_geometry_view(size), codestream::image_size_component_count(size),
        codestream::image_size_component_infos(size), resolution_geometry_style(coding_style),
        component, resolution, None,
    ),
))]
pub fn derive_component_resolution_geometry(
    size: &ImageSize,
    coding_style: CodingStyle,
    component: u16,
    resolution: u8,
) -> Result<ComponentResolutionGeometry, DecodeError> {
    derive_component_resolution_geometry_for(size, coding_style, component, resolution, None)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_resolution_geometry(
        codestream::selection_geometry_view(size), codestream::image_size_component_count(size),
        codestream::image_size_component_infos(size), resolution_geometry_style(coding_style),
        component, resolution, tile_index,
    ),
))]
pub(crate) fn derive_component_resolution_geometry_for(
    size: &ImageSize,
    coding_style: CodingStyle,
    component: u16,
    resolution: u8,
    tile_index: Option<u16>,
) -> Result<ComponentResolutionGeometry, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::resolution_selectors_known_fields(coding_style);
    }
    if resolution > coding_style.decomposition_levels {
        return Err(invalid_decode());
    }

    let component_bounds = component_coordinate_bounds(size, component, tile_index)?;
    let component_x0 = component_bounds[0];
    let component_y0 = component_bounds[1];
    let component_x1 = component_bounds[2];
    let component_y1 = component_bounds[3];
    let (scale_x, scale_y) = coding_style.resolution_downsampling(resolution)?;
    let resolution_x0 = ceil_div_u32(component_x0, scale_x)?;
    let resolution_y0 = ceil_div_u32(component_y0, scale_y)?;
    let resolution_x1 = ceil_div_u32(component_x1, scale_x)?;
    let resolution_y1 = ceil_div_u32(component_y1, scale_y)?;
    let width = resolution_x1
        .checked_sub(resolution_x0)
        .ok_or_else(arithmetic_overflow)?;
    let height = resolution_y1
        .checked_sub(resolution_y0)
        .ok_or_else(arithmetic_overflow)?;
    let code_block_width = u32::from(coding_style.code_block_width);
    let code_block_height = u32::from(coding_style.code_block_height);
    if code_block_width == 0 || code_block_height == 0 {
        return Err(invalid_decode());
    }
    let code_blocks_across = ceil_div_u32(resolution_x1, code_block_width)?
        .checked_sub(floor_div_u32(resolution_x0, code_block_width)?)
        .ok_or_else(arithmetic_overflow)?;
    let code_blocks_down = ceil_div_u32(resolution_y1, code_block_height)?
        .checked_sub(floor_div_u32(resolution_y0, code_block_height)?)
        .ok_or_else(arithmetic_overflow)?;
    let code_blocks_across = if width == 0 { 0 } else { code_blocks_across };
    let code_blocks_down = if height == 0 { 0 } else { code_blocks_down };
    let code_blocks = u64::from(code_blocks_across)
        .checked_mul(u64::from(code_blocks_down))
        .ok_or_else(arithmetic_overflow)?;
    let (precinct_x, precinct_y) = coding_style.precinct_exponents(resolution)?;
    if precinct_x > 31 || precinct_y > 31 {
        return Err(invalid_decode());
    }
    let precinct_width = 1_u32 << u32::from(precinct_x);
    let precinct_height = 1_u32 << u32::from(precinct_y);
    let precinct_x0 = floor_div_u32(resolution_x0, precinct_width)?;
    let precinct_y0 = floor_div_u32(resolution_y0, precinct_height)?;
    let precinct_x1 = ceil_div_u32(resolution_x1, precinct_width)?;
    let precinct_y1 = ceil_div_u32(resolution_y1, precinct_height)?;
    let precincts_across = precinct_x1
        .checked_sub(precinct_x0)
        .ok_or_else(arithmetic_overflow)?;
    let precincts_down = precinct_y1
        .checked_sub(precinct_y0)
        .ok_or_else(arithmetic_overflow)?;
    let precincts_across = if width == 0 { 0 } else { precincts_across };
    let precincts_down = if height == 0 { 0 } else { precincts_down };
    let precincts = u64::from(precincts_across)
        .checked_mul(u64::from(precincts_down))
        .ok_or_else(arithmetic_overflow)?;
    Ok(ComponentResolutionGeometry {
        component,
        resolution,
        width,
        height,
        subbands: if resolution == 0 { 1 } else { 3 },
        code_blocks_across,
        code_blocks_down,
        code_blocks,
        precincts_across,
        precincts_down,
        precincts,
    })
}

pub fn derive_packet_grid(
    size: &ImageSize,
    coding_style: CodingStyle,
    limits: &ResourceLimits,
) -> Result<PacketGrid, DecodeError> {
    derive_packet_grid_for(size, coding_style, limits, None)
}

pub(super) fn derive_packet_grid_for(
    size: &ImageSize,
    coding_style: CodingStyle,
    limits: &ResourceLimits,
    tile_index: Option<u16>,
) -> Result<PacketGrid, DecodeError> {
    let resolutions = coding_style
        .decomposition_levels
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let capacity = usize::from(size.components)
        .checked_mul(usize::from(resolutions))
        .ok_or_else(arithmetic_overflow)?;
    let mut precinct_counts = Vec::with_capacity(capacity);
    let mut total_code_blocks = 0_u64;
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= size.components,
            decreases size.components - component,
        )
    )]
    while component < size.components {
        let mut resolution = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant resolution <= resolutions,
                decreases resolutions - resolution,
            )
        )]
        while resolution < resolutions {
            let geometry = derive_component_resolution_geometry_for(
                size,
                coding_style,
                component,
                resolution,
                tile_index,
            )?;
            let subband_count = coding_style
                .subband_count_through_resolution(resolution)?
                .checked_sub(if resolution == 0 {
                    0
                } else {
                    coding_style.subband_count_through_resolution(
                        resolution.checked_sub(1).ok_or_else(arithmetic_overflow)?,
                    )?
                })
                .ok_or_else(arithmetic_overflow)?;
            total_code_blocks = total_code_blocks
                .checked_add(geometry.code_blocks)
                .ok_or_else(arithmetic_overflow)?;
            if total_code_blocks > limits.maximum_code_blocks() {
                return Err(DecodeError::limit(
                    crate::Resource::CodeBlocks,
                    limits.maximum_code_blocks(),
                    total_code_blocks,
                ));
            }

            precinct_counts.push(if subband_count == 0 {
                0
            } else {
                u32::try_from(geometry.precincts).map_err(|_| arithmetic_overflow())?
            });
            if resolution == u8::MAX {
                return Err(arithmetic_overflow());
            }
            let modeled_resolution = crate::refinement::wavelet_next_resolution(resolution);
            resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
            if resolution != modeled_resolution {
                return Err(arithmetic_overflow());
            }
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    PacketGrid::new(
        coding_style.layers,
        size.components,
        resolutions,
        precinct_counts,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures resolution_counts_outcome(result)
        == crate::specs::part2_component_resolution_counts(components, coding_styles, discard_levels),
))]
pub(crate) fn prepare_component_resolution_counts(
    components: u16,
    coding_styles: &ComponentCodingStyles,
    discard_levels: u8,
) -> Result<(u8, Vec<u8>, Vec<u8>), DecodeError> {
    let mut maximum_resolutions = 0_u8;
    let mut component_resolutions = Vec::with_capacity(usize::from(components));
    let mut selected_resolution_counts = Vec::with_capacity(usize::from(components));
    let mut component = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_component_resolution_counts_run); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant
                component <= components,
                crate::specs::part2_component_resolution_counts(components, coding_styles, discard_levels)
                    == crate::specs::part2_component_resolution_counts_run(
                        components, coding_styles, discard_levels, component, maximum_resolutions,
                        component_resolutions@, selected_resolution_counts@,
                    ),
            decreases components - component,
        )
    )]
    while component < components {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_component_resolution_counts_run); }
        let resolutions = coding_styles
            .style(component)?
            .decomposition_levels
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        maximum_resolutions = maximum_resolutions.max(resolutions);
        component_resolutions.push(resolutions);
        let selected_resolutions =
            resolutions
                .checked_sub(discard_levels)
                .ok_or(DecodeError::InvalidSelection {
                    reason: SelectionError::ReductionTooLarge,
                })?;
        if selected_resolutions == 0 {
            return Err(DecodeError::InvalidSelection {
                reason: SelectionError::ReductionTooLarge,
            });
        }
        selected_resolution_counts.push(selected_resolutions);
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_component_resolution_counts_run); }
    Ok((
        maximum_resolutions,
        component_resolutions,
        selected_resolution_counts,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::packet::packet_grid_outcome(result) == crate::specs::part2_packet_grid_from_components(
        size, coding_styles, layers, limits, tile_index, discard_levels,
    ),
))]
pub(crate) fn derive_packet_grid_for_components(
    size: &ImageSize,
    coding_styles: &ComponentCodingStyles,
    layers: u16,
    limits: &ResourceLimits,
    tile_index: Option<u16>,
    discard_levels: u8,
) -> Result<PacketGrid, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::selection_geometry_known_fields(size); }
    let (maximum_resolutions, component_resolutions, selected_resolution_counts) =
        prepare_component_resolution_counts(size.components, coding_styles, discard_levels)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost descriptors = (maximum_resolutions, component_resolutions@, selected_resolution_counts@);
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_packet_grid_components_run); }
    let capacity = usize::from(size.components)
        .checked_mul(usize::from(maximum_resolutions))
        .ok_or_else(arithmetic_overflow)?;
    let mut precinct_counts = Vec::with_capacity(capacity);
    let mut total_code_blocks = 0_u64;
    let mut component = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant
                component <= size.components,
                codestream::image_size_component_count(size) == size.components,
                descriptors == (maximum_resolutions, component_resolutions@, selected_resolution_counts@),
                crate::specs::part2_packet_grid_from_components(size, coding_styles, layers, limits, tile_index, discard_levels)
                    == crate::specs::part2_packet_grid_components_run(
                        size, coding_styles, layers, limits, tile_index, discard_levels,
                        descriptors, component, precinct_counts@, total_code_blocks,
                    ),
            decreases size.components - component,
        )
    )]
    while component < size.components {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_packet_grid_components_run); }
        let style = coding_styles.style(component)?;
        let resolutions = style
            .decomposition_levels
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        let mut resolution = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(codestream::component_coding_style_result(coding_styles, component) == Ok(style));
            assert(style.decomposition_levels < u8::MAX);
            assert(resolutions as int == style.decomposition_levels as int + 1);
            crate::proofs::production_impl::production_packet_grid_component_start(
                size, coding_styles, layers, limits, tile_index, discard_levels,
                descriptors, component, precinct_counts@, total_code_blocks, style, resolutions,
            );
            assert(crate::specs::part2_packet_grid_components_run(
                size, coding_styles, layers, limits, tile_index, discard_levels,
                descriptors, component, precinct_counts@, total_code_blocks,
            ) == crate::specs::part2_packet_grid_resolutions_run(
                size, coding_styles, layers, limits, tile_index, discard_levels,
                descriptors, component, style, resolutions, 0, precinct_counts@, total_code_blocks,
            ));
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    component < size.components,
                    codestream::image_size_component_count(size) == size.components,
                    resolution <= maximum_resolutions,
                    descriptors == (maximum_resolutions, component_resolutions@, selected_resolution_counts@),
                    crate::specs::part2_packet_grid_from_components(size, coding_styles, layers, limits, tile_index, discard_levels)
                        == crate::specs::part2_packet_grid_resolutions_run(
                            size, coding_styles, layers, limits, tile_index, discard_levels,
                            descriptors, component, style, resolutions, resolution,
                            precinct_counts@, total_code_blocks,
                        ),
                decreases maximum_resolutions - resolution,
            )
        )]
        while resolution < maximum_resolutions {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_packet_grid_resolutions_run); }
            if resolution < resolutions {
                let geometry = derive_component_resolution_geometry_for(
                    size, style, component, resolution, tile_index,
                )?;
                let subband_count = style
                    .subband_count_through_resolution(resolution)?
                    .checked_sub(if resolution == 0 {
                        0
                    } else {
                        style.subband_count_through_resolution(
                            resolution.checked_sub(1).ok_or_else(arithmetic_overflow)?,
                        )?
                    })
                    .ok_or_else(arithmetic_overflow)?;
                let selected_resolutions = resolutions.checked_sub(discard_levels).ok_or(
                    DecodeError::InvalidSelection {
                        reason: SelectionError::ReductionTooLarge,
                    },
                )?;
                if resolution < selected_resolutions {
                    total_code_blocks = total_code_blocks
                        .checked_add(geometry.code_blocks)
                        .ok_or_else(arithmetic_overflow)?;
                    if total_code_blocks > limits.maximum_code_blocks() {
                        return Err(DecodeError::LimitExceeded {
                            resource: crate::Resource::CodeBlocks,
                            limit: limits.maximum_code_blocks(),
                            actual: total_code_blocks,
                        });
                    }
                }
                precinct_counts.push(if subband_count == 0 {
                    0
                } else {
                    match u32::try_from(geometry.precincts) {
                        Ok(count) => count,
                        Err(_) => return Err(arithmetic_overflow()),
                    }
                });
            } else {
                precinct_counts.push(0);
            }
            resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_packet_grid_resolutions_run);
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_packet_grid_components_run); }
    crate::packet::packet_grid_new_with_selected_resolutions(
        layers,
        size.components,
        component_resolutions,
        precinct_counts,
        if discard_levels == 0 {
            None
        } else {
            Some(&selected_resolution_counts)
        },
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_quantization_step_at_index(
        codestream::quantization_view(quantization), resolution, index,
    ),
))]
pub(crate) fn quantization_step_at_index(
    quantization: &Quantization,
    resolution: u8,
    index: u16,
) -> Result<QuantizationStep, DecodeError> {
    match quantization.style() {
        QuantizationStyle::None | QuantizationStyle::ScalarExpounded => quantization.step(index),
        QuantizationStyle::ScalarDerived => {
            let base = quantization.step(0)?;
            Ok(QuantizationStep {
                exponent: base.exponent.saturating_sub(resolution.saturating_sub(1)),
                mantissa: base.mantissa,
            })
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_quantization_for_subband(
        codestream::quantization_view(quantization), resolution, orientation,
    ),
))]
pub fn quantization_step_for_subband(
    quantization: &Quantization,
    resolution: u8,
    orientation: SubbandOrientation,
) -> Result<(u16, QuantizationStep), DecodeError> {
    let orientation_index = if resolution == 0 {
        if !matches!(orientation, SubbandOrientation::Ll) {
            return Err(invalid_decode());
        }
        0_u16
    } else {
        let offset = match orientation {
            SubbandOrientation::Hl => 0_u16,
            SubbandOrientation::Lh => 1_u16,
            SubbandOrientation::Hh => 2_u16,
            SubbandOrientation::Ll => return Err(invalid_decode()),
        };
        let level = u16::from(resolution)
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
        let index = level.checked_mul(3).ok_or_else(arithmetic_overflow)?;
        let index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        index.checked_add(offset).ok_or_else(arithmetic_overflow)?
    };
    let step = quantization_step_at_index(quantization, resolution, orientation_index)?;
    Ok((orientation_index, step))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures subbands_outcome(result) == crate::specs::part2_component_subbands(
        size, coding_style, quantization, component, None, 0,
    ),
))]
pub fn derive_component_subbands(
    size: &ImageSize,
    coding_style: CodingStyle,
    quantization: &Quantization,
    component: u16,
) -> Result<Vec<SubbandGeometry>, DecodeError> {
    derive_component_subbands_for(size, coding_style, quantization, component, None, 0)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures subbands_outcome(result) == crate::specs::part2_component_subbands(
        size, coding_style, quantization, component, tile_index, roi_shift,
    ),
))]
pub(crate) fn derive_component_subbands_for(
    size: &ImageSize,
    coding_style: CodingStyle,
    quantization: &Quantization,
    component: u16,
    tile_index: Option<u16>,
    roi_shift: u8,
) -> Result<Vec<SubbandGeometry>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::resolution_selectors_known_fields(coding_style); }
    let info = size.component(component)?;
    let component_bounds = component_coordinate_bounds(size, component, tile_index)?;
    let expected_count = coding_style.subband_count();
    let mut subbands = Vec::with_capacity(usize::from(expected_count));
    let mut resolution = 0_u8;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_subband_vector_run); }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant
                resolution as int <= coding_style.decomposition_levels as int + 1,
                crate::specs::part2_component_subbands(size, coding_style, quantization, component, tile_index, roi_shift)
                    == crate::specs::part2_subband_vector_run(
                        coding_style, component_bounds, [info.precision, roi_shift],
                        codestream::quantization_view(quantization), expected_count, resolution, subbands@,
                    ),
            decreases coding_style.decomposition_levels as int + 1 - resolution as int,
        )
    )]
    while resolution <= coding_style.decomposition_levels {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_subband_vector_run); }
        subbands = derive_subband_resolution(
            coding_style,
            component_bounds,
            [info.precision, roi_shift],
            quantization,
            resolution,
            subbands,
        )?;
        resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_subband_vector_run); }
    if subbands.len() != usize::from(expected_count) {
        return Err(invalid_decode());
    }
    Ok(subbands)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures subbands_outcome(result) == crate::specs::part2_subband_resolution(
        coding_style, component_bounds, component_depth, codestream::quantization_view(quantization), resolution, before@,
    ),
))]
pub(crate) fn derive_subband_resolution(
    coding_style: CodingStyle,
    component_bounds: [u32; 4],
    component_depth: [u8; 2],
    quantization: &Quantization,
    resolution: u8,
    before: Vec<SubbandGeometry>,
) -> Result<Vec<SubbandGeometry>, DecodeError> {
    let component_x0 = component_bounds[0];
    let component_y0 = component_bounds[1];
    let component_x1 = component_bounds[2];
    let component_y1 = component_bounds[3];
    let mut subbands = before;
    let (scale_x, scale_y) = coding_style.resolution_downsampling(resolution)?;
    let resolution_x0 = ceil_div_u32(component_x0, scale_x)?;
    let resolution_y0 = ceil_div_u32(component_y0, scale_y)?;
    let resolution_x1 = ceil_div_u32(component_x1, scale_x)?;
    let resolution_y1 = ceil_div_u32(component_y1, scale_y)?;
    let resolution_width = resolution_x1
        .checked_sub(resolution_x0)
        .ok_or_else(arithmetic_overflow)?;
    let resolution_height = resolution_y1
        .checked_sub(resolution_y0)
        .ok_or_else(arithmetic_overflow)?;
    if resolution == 0 {
        subbands.push(make_subband_geometry(
            resolution,
            SubbandOrientation::Ll,
            [resolution_x0, resolution_y0, resolution_x1, resolution_y1],
            [resolution_width, resolution_height],
            [true, true],
            component_depth,
            quantization,
            0,
        )?);
    } else {
        let low_x0 = ceil_div_u32(resolution_x0, 2)?;
        let low_y0 = ceil_div_u32(resolution_y0, 2)?;
        let low_x1 = ceil_div_u32(resolution_x1, 2)?;
        let low_y1 = ceil_div_u32(resolution_y1, 2)?;
        let high_x0 = resolution_x0 / 2;
        let high_y0 = resolution_y0 / 2;
        let high_x1 = resolution_x1 / 2;
        let high_y1 = resolution_y1 / 2;
        let phase = [
            resolution_x0.is_multiple_of(2),
            resolution_y0.is_multiple_of(2),
        ];
        let direction = coding_style.direction_for_resolution(resolution)?;
        if matches!(
            direction,
            crate::codestream::DecompositionDirection::TwoDimensional
                | crate::codestream::DecompositionDirection::Horizontal
        ) {
            let index = match u16::try_from(subbands.len()) {
                Ok(index) => index,
                Err(_) => return Err(arithmetic_overflow()),
            };
            let y_bounds = if matches!(
                direction,
                crate::codestream::DecompositionDirection::TwoDimensional
            ) {
                [low_y0, low_y1]
            } else {
                [resolution_y0, resolution_y1]
            };
            subbands.push(make_subband_geometry(
                resolution,
                SubbandOrientation::Hl,
                [high_x0, y_bounds[0], high_x1, y_bounds[1]],
                [resolution_width, resolution_height],
                phase,
                component_depth,
                quantization,
                index,
            )?);
        }
        if matches!(
            direction,
            crate::codestream::DecompositionDirection::TwoDimensional
                | crate::codestream::DecompositionDirection::Vertical
        ) {
            let index = match u16::try_from(subbands.len()) {
                Ok(index) => index,
                Err(_) => return Err(arithmetic_overflow()),
            };
            let x_bounds = if matches!(
                direction,
                crate::codestream::DecompositionDirection::TwoDimensional
            ) {
                [low_x0, low_x1]
            } else {
                [resolution_x0, resolution_x1]
            };
            subbands.push(make_subband_geometry(
                resolution,
                SubbandOrientation::Lh,
                [x_bounds[0], high_y0, x_bounds[1], high_y1],
                [resolution_width, resolution_height],
                phase,
                component_depth,
                quantization,
                index,
            )?);
        }
        if matches!(
            direction,
            crate::codestream::DecompositionDirection::TwoDimensional
        ) {
            let index = match u16::try_from(subbands.len()) {
                Ok(index) => index,
                Err(_) => return Err(arithmetic_overflow()),
            };
            subbands.push(make_subband_geometry(
                resolution,
                SubbandOrientation::Hh,
                [high_x0, high_y0, high_x1, high_y1],
                [resolution_width, resolution_height],
                phase,
                component_depth,
                quantization,
                index,
            )?);
        }
    }
    Ok(subbands)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_make_subband_geometry(
        resolution, orientation, bounds, resolution_dimensions, low_pass_first, component_depth,
        codestream::quantization_view(quantization), quantization_index,
    ),
))]
pub(crate) fn make_subband_geometry(
    resolution: u8,
    orientation: SubbandOrientation,
    bounds: [u32; 4],
    resolution_dimensions: [u32; 2],
    low_pass_first: [bool; 2],
    component_depth: [u8; 2],
    quantization: &Quantization,
    quantization_index: u16,
) -> Result<SubbandGeometry, DecodeError> {
    let precision = component_depth[0];
    let roi_shift = component_depth[1];
    let gain = match orientation {
        SubbandOrientation::Ll => 0_u8,
        SubbandOrientation::Hl | SubbandOrientation::Lh => 1_u8,
        SubbandOrientation::Hh => 2_u8,
    };
    let dynamic_range = precision
        .checked_add(gain)
        .ok_or_else(arithmetic_overflow)?;
    if dynamic_range == 0 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidQuantization,
        });
    }
    let quantization_step =
        quantization_step_at_index(quantization, resolution, quantization_index)?;
    let significant_bitplanes = u16::from(quantization.guard_bits())
        .checked_add(u16::from(quantization_step.exponent))
        .ok_or_else(invalid_decode)?;
    let significant_bitplanes = significant_bitplanes
        .checked_sub(1)
        .ok_or_else(invalid_decode)?;
    let significant_bitplanes = significant_bitplanes
        .checked_add(u16::from(roi_shift))
        .ok_or_else(invalid_decode)?;
    if significant_bitplanes == 0 || significant_bitplanes > crate::tier1::MAX_TIER1_BITPLANES {
        return Err(invalid_decode());
    }
    Ok(SubbandGeometry {
        resolution,
        orientation,
        x0: bounds[0],
        y0: bounds[1],
        width: bounds[2]
            .checked_sub(bounds[0])
            .ok_or_else(arithmetic_overflow)?,
        height: bounds[3]
            .checked_sub(bounds[1])
            .ok_or_else(arithmetic_overflow)?,
        resolution_width: resolution_dimensions[0],
        resolution_height: resolution_dimensions[1],
        quantization_index,
        quantization_step,
        dynamic_range,
        significant_bitplanes,
        roi_shift,
        low_pass_first_x: low_pass_first[0],
        low_pass_first_y: low_pass_first[1],
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_component_coordinate_bounds(
        codestream::selection_geometry_view(size), codestream::image_size_component_count(size),
        codestream::image_size_component_infos(size), component, tile_index,
    ),
))]
pub(crate) fn component_coordinate_bounds(
    size: &ImageSize,
    component: u16,
    tile_index: Option<u16>,
) -> Result<[u32; 4], DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        codestream::selection_geometry_known_fields(size);
    }
    if let Some(tile_index) = tile_index {
        let bounds = size.tile_component_bounds(tile_index, component)?;
        return Ok([bounds.x0, bounds.y0, bounds.x1, bounds.y1]);
    }
    let info = size.component(component)?;
    let image_x1 = size
        .x_origin
        .checked_add(size.width)
        .ok_or_else(arithmetic_overflow)?;
    let image_y1 = size
        .y_origin
        .checked_add(size.height)
        .ok_or_else(arithmetic_overflow)?;
    let x0 = ceil_div_u32(size.x_origin, u32::from(info.x_subsampling))?;
    let y0 = ceil_div_u32(size.y_origin, u32::from(info.y_subsampling))?;
    let x1 = ceil_div_u32(image_x1, u32::from(info.x_subsampling))?;
    let y1 = ceil_div_u32(image_y1, u32::from(info.y_subsampling))?;
    Ok([x0, y0, x1, y1])
}
