use super::{
    CodingStyle, ComponentCodingStyles, ComponentPlanBuilder, ComponentQuantizations, DecodeError,
    ImageSize, PacketGrid, PacketPrecinctDecoder, PacketSubbandExecution, PlannedCodeBlocks,
    PlannedComponent, PlannedComponentMetadata, PlannedPrecinct, PlannedSubbandExecution,
    PlannedSubbandLattice, PlannedTileComponent, PrecinctPlanBuilder,
    ProgressionCodeBlockPlacement, ProgressionTilePlan, Quantization, ResolutionPlanMetadata,
    Resource, ResourceLimits, RoiShifts, SelectionError, SubbandGeometry, Tier1CodingStyle,
    arithmetic_overflow, ceil_div_u32, codestream, derive_component_resolution_geometry_for,
    derive_component_subbands_for, derive_packet_grid_for_components, floor_div_u32,
    invalid_decode,
};
#[cfg(verus_keep_ghost)]
use super::{
    Tier1CodeBlockDecoder, component_plan_builder_view, component_plan_metadata_outcome,
    component_plan_metadata_view, planned_codeblocks_outcome, planned_codeblocks_view,
    planned_component_outcome, planned_component_view, planned_precinct_outcome,
    planned_precinct_view, planned_subband_execution_outcome, planned_subband_execution_view,
    planned_subband_lattice_outcome, planned_subband_lattice_view, planning_components_view,
    planning_precincts_view, precinct_plan_builder_view, prepare_plan_view,
    progression_plan_outcome, progression_plan_view, resolution_plan_metadata_outcome,
    resolution_plan_metadata_view, tile_plan_buffers_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl PlannedTileComponent {
    pub fn subbands(&self) -> &[SubbandGeometry] {
        &self.subbands
    }

    pub fn placements(&self) -> &[ProgressionCodeBlockPlacement] {
        &self.placements
    }
}

impl ProgressionTilePlan {
    pub const fn tile_index(&self) -> u16 {
        self.tile_index
    }

    pub const fn grid(&self) -> &PacketGrid {
        &self.grid
    }

    pub fn precincts(&self) -> &[PacketPrecinctDecoder] {
        &self.precincts
    }

    pub fn precincts_mut(&mut self) -> &mut [PacketPrecinctDecoder] {
        &mut self.precincts
    }

    pub fn packet_execution(&mut self) -> (&PacketGrid, &mut [PacketPrecinctDecoder]) {
        (&self.grid, &mut self.precincts)
    }

    pub fn components(&self) -> &[PlannedTileComponent] {
        &self.components
    }
}

pub fn plan_progression_tile(
    size: &ImageSize,
    coding_style: CodingStyle,
    quantization: &Quantization,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePlan, DecodeError> {
    plan_progression_tile_at_with_roi(
        size,
        0,
        coding_style,
        quantization,
        &RoiShifts::none(),
        limits,
    )
}

pub fn plan_progression_tile_at(
    size: &ImageSize,
    tile_index: u16,
    coding_style: CodingStyle,
    quantization: &Quantization,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePlan, DecodeError> {
    plan_progression_tile_at_with_roi(
        size,
        tile_index,
        coding_style,
        quantization,
        &RoiShifts::none(),
        limits,
    )
}

pub fn plan_progression_tile_at_with_roi(
    size: &ImageSize,
    tile_index: u16,
    coding_style: CodingStyle,
    quantization: &Quantization,
    roi_shifts: &RoiShifts,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePlan, DecodeError> {
    let coding_styles = ComponentCodingStyles::uniform(size.components, coding_style)?;
    let quantizations = ComponentQuantizations::uniform(size.components, *quantization)?;
    plan_progression_tile_at_with_component_overrides(
        size,
        tile_index,
        coding_style,
        &coding_styles,
        &quantizations,
        roi_shifts,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures progression_plan_outcome(result) == crate::specs::part2_progression_tile_plan(
        size, coding_style, coding_styles, quantizations, roi_shifts, (tile_index, 0), (false, 74, false), limits,
    ),
))]
pub fn plan_progression_tile_at_with_component_overrides(
    size: &ImageSize,
    tile_index: u16,
    coding_style: CodingStyle,
    coding_styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi_shifts: &RoiShifts,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePlan, DecodeError> {
    plan_progression_tile_at_selected(
        size,
        tile_index,
        coding_style,
        coding_styles,
        quantizations,
        roi_shifts,
        0,
        false,
        74,
        false,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures component_plan_metadata_outcome(result) == crate::specs::part2_component_plan_metadata(
        size, coding_styles, quantizations, roi_shifts, component, selection, force_high_throughput,
    ),
))]
pub(crate) fn prepare_component_plan_metadata(
    size: &ImageSize,
    coding_styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi_shifts: &RoiShifts,
    component: u16,
    selection: (u16, u8),
    force_high_throughput: bool,
) -> Result<PlannedComponentMetadata, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::selection_geometry_known_fields(size); }
    let (tile_index, discard_levels) = selection;
    let component_coding_style = coding_styles.style(component)?;
    let output_resolution = component_coding_style
        .decomposition_levels
        .checked_sub(discard_levels)
        .ok_or(DecodeError::InvalidSelection {
            reason: SelectionError::ReductionTooLarge,
        })?;
    let component_quantization = quantizations.quantization(component)?;
    let mut tier1_style = component_coding_style.tier1_coding_style()?;
    if tier1_style.block_coding.uses_high_throughput() && force_high_throughput {
        tier1_style.set_force_high_throughput(true);
    }
    let bounds = size.tile_component_bounds(tile_index, component)?;
    let output_geometry = derive_component_resolution_geometry_for(
        size,
        component_coding_style,
        component,
        output_resolution,
        Some(tile_index),
    )?;
    let component_width = output_geometry.width;
    let component_height = output_geometry.height;
    let (scale_x, scale_y) = component_coding_style.resolution_downsampling(output_resolution)?;
    let info = size.component(component)?;
    let component_image_x0 = ceil_div_u32(size.x_origin, u32::from(info.x_subsampling))?;
    let component_image_y0 = ceil_div_u32(size.y_origin, u32::from(info.y_subsampling))?;
    let component_x = ceil_div_u32(bounds.x0, scale_x)?
        .checked_sub(ceil_div_u32(component_image_x0, scale_x)?)
        .ok_or_else(arithmetic_overflow)?;
    let component_y = ceil_div_u32(bounds.y0, scale_y)?
        .checked_sub(ceil_div_u32(component_image_y0, scale_y)?)
        .ok_or_else(arithmetic_overflow)?;
    let subbands = derive_component_subbands_for(
        size,
        component_coding_style,
        &component_quantization,
        component,
        Some(tile_index),
        roi_shifts.shift(component)?,
    )?;
    Ok(PlannedComponentMetadata {
        component_coding_style,
        output_resolution,
        tier1_style,
        bounds,
        component_width,
        component_height,
        component_x,
        component_y,
        subbands,
    })
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures progression_plan_outcome(result) == crate::specs::part2_progression_tile_plan(
        size, coding_style, coding_styles, quantizations, roi_shifts, (tile_index, discard_levels),
        (allow_multiple_ht_sets, ht_magnitude_bound, force_high_throughput), limits,
    ),
))]
pub(super) fn plan_progression_tile_at_selected(
    size: &ImageSize,
    tile_index: u16,
    coding_style: CodingStyle,
    coding_styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi_shifts: &RoiShifts,
    discard_levels: u8,
    allow_multiple_ht_sets: bool,
    ht_magnitude_bound: u8,
    force_high_throughput: bool,
    limits: &ResourceLimits,
) -> Result<ProgressionTilePlan, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::selection_geometry_known_fields(size); }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_progression_tile_plan(
        size, coding_style, coding_styles, quantizations, roi_shifts, (tile_index, discard_levels),
        (allow_multiple_ht_sets, ht_magnitude_bound, force_high_throughput), limits,
    ); }
    size.tile_bounds(tile_index)?;
    let grid = derive_packet_grid_for_components(
        size,
        coding_styles,
        coding_style.layers,
        limits,
        Some(tile_index),
        discard_levels,
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original_grid = crate::packet::packet_grid_view(&grid); }
    let mut precincts = Vec::new();
    let mut components = Vec::with_capacity(usize::from(size.components));
    let mut planned_code_blocks = 0_u64;
    let mut component = 0_u16;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(tile_plan_buffers_view);
        assert(planning_precincts_view(precincts@) =~= Seq::empty());
        assert(planning_components_view(components@) =~= Seq::empty());
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant component <= size.components,
                codestream::image_size_component_count(size) == size.components,
                crate::packet::packet_grid_view(&grid) == original_grid,
                goal == crate::specs::part2_progression_tile_plan(
                    size, coding_style, coding_styles, quantizations, roi_shifts, (tile_index, discard_levels),
                    (allow_multiple_ht_sets, ht_magnitude_bound, force_high_throughput), limits,
                ),
                goal == crate::specs::part2_tile_plan_components(
                    size, coding_style, coding_styles, codestream::quantization_owner_view(quantizations), roi_shifts, (tile_index, discard_levels),
                    (allow_multiple_ht_sets, ht_magnitude_bound, force_high_throughput), limits, original_grid,
                    component, tile_plan_buffers_view(precincts@, components@, planned_code_blocks),
                ),
            decreases size.components - component,
        )
    )]
    while component < size.components {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = tile_plan_buffers_view(precincts@, components@, planned_code_blocks); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_tile_plan_components, 1); }
        let planned = plan_tile_component(
            size,
            coding_styles,
            quantizations,
            roi_shifts,
            component,
            (tile_index, discard_levels),
            (
                allow_multiple_ht_sets,
                ht_magnitude_bound,
                force_high_throughput,
            ),
            precincts,
            planned_code_blocks,
            limits,
        )?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost row = planned_component_view(&planned); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(planned_component_view); reveal(tile_plan_buffers_view); }
        precincts = planned.precincts;
        planned_code_blocks = planned.planned_code_blocks;
        components.push(planned.component);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(planning_components_view(components@) =~= before.components.push(row.component));
        }
        component = component.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_tile_plan_components, 1);
        reveal(tile_plan_buffers_view);
        reveal(progression_plan_view);
    }
    Ok(ProgressionTilePlan {
        tile_index,
        coding_style,
        component_coding_styles: *coding_styles,
        grid,
        precincts,
        components,
    })
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures planned_component_outcome(result) == crate::specs::part2_planned_component(
        size, coding_styles, quantizations, roi_shifts, component, selection, policy,
        planning_precincts_view(precincts@), planned_code_blocks, limits,
    ),
))]
pub(crate) fn plan_tile_component(
    size: &ImageSize,
    coding_styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi_shifts: &RoiShifts,
    component: u16,
    selection: (u16, u8),
    policy: (bool, u8, bool),
    precincts: Vec<PacketPrecinctDecoder>,
    planned_code_blocks: u64,
    limits: &ResourceLimits,
) -> Result<PlannedComponent, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_planned_component(
        size, coding_styles, quantizations, roi_shifts, component, selection, policy,
        planning_precincts_view(precincts@), planned_code_blocks, limits,
    ); }
    let metadata = prepare_component_plan_metadata(
        size,
        coding_styles,
        quantizations,
        roi_shifts,
        component,
        selection,
        policy.2,
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost meta = component_plan_metadata_view(&metadata); }
    let mut builder = ComponentPlanBuilder {
        precincts,
        placements: Vec::new(),
        planned_code_blocks,
    };
    let mut resolution = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant resolution <= metadata.component_coding_style.decomposition_levels as int + 1,
            meta == component_plan_metadata_view(&metadata),
            goal == crate::specs::part2_planned_component(
                size, coding_styles, quantizations, roi_shifts, component, selection, policy,
                planning_precincts_view(precincts@), planned_code_blocks, limits,
            ),
            goal == crate::specs::part2_component_plan_resolutions(
                size, component, selection.0, meta, policy, limits, resolution as nat, component_plan_builder_view(&builder),
            ),
        decreases metadata.component_coding_style.decomposition_levels as int + 1 - resolution as int,
    ))]
    while resolution <= metadata.component_coding_style.decomposition_levels {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(component_plan_metadata_view);
            reveal(component_plan_builder_view);
            reveal_with_fuel(crate::specs::part2_component_plan_resolutions, 1);
        }
        let data = prepare_resolution_plan_metadata(
            size,
            metadata.component_coding_style,
            component,
            (selection.0, resolution),
            [metadata.bounds.x0, metadata.bounds.y0],
        )?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost resolution_data = resolution_plan_metadata_view(&data); }
        let mut precinct = 0_u32;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant precinct <= data.precincts_in_resolution,
                resolution <= metadata.component_coding_style.decomposition_levels,
                meta == component_plan_metadata_view(&metadata),
                resolution_data == resolution_plan_metadata_view(&data),
                goal == crate::specs::part2_planned_component(
                    size, coding_styles, quantizations, roi_shifts, component, selection, policy,
                    planning_precincts_view(precincts@), planned_code_blocks, limits,
                ),
                goal == match crate::specs::part2_component_plan_precincts(
                    component, resolution, meta, resolution_data, policy, limits, precinct as nat, component_plan_builder_view(&builder),
                ) {
                    Err(error) => Err(error),
                    Ok(after) => if resolution == u8::MAX { Err(crate::specs::part1_block_placement_error(true)) }
                        else { crate::specs::part2_component_plan_resolutions(
                            size, component, selection.0, meta, policy, limits, resolution as nat + 1, after) },
                },
            decreases data.precincts_in_resolution - precinct,
        ))]
        while precinct < data.precincts_in_resolution {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = component_plan_builder_view(&builder); }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(component_plan_metadata_view);
                reveal(resolution_plan_metadata_view);
                reveal(component_plan_builder_view);
                reveal_with_fuel(crate::specs::part2_component_plan_precincts, 1);
            }
            let origin = derive_planned_precinct_origin(
                data.first_precinct,
                data.geometry.precincts_across,
                precinct,
                data.band_size,
            )?;
            let planned = plan_packet_precinct(
                [origin[0], origin[1], data.band_size[0], data.band_size[1]],
                data.block_size,
                &metadata.subbands,
                (data.first_subband, data.subband_count),
                metadata.tier1_style,
                (policy.0, policy.1),
                (component, resolution, precinct, builder.precincts.len()),
                builder.placements,
                builder.planned_code_blocks,
                resolution <= metadata.output_resolution,
                limits,
            )?;
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost row = planned_precinct_view(&planned); }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(planned_precinct_view); }
            builder.placements = planned.placements;
            builder.planned_code_blocks = planned.planned_code_blocks;
            builder.precincts.push(planned.precinct);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(planning_precincts_view(builder.precincts@) =~= before.precincts.push(row.precinct));
                assert(crate::specs::part2_component_plan_precinct(
                    component, resolution, meta, resolution_data, policy, limits, precinct, before,
                ) == Ok(component_plan_builder_view(&builder)));
            }
            precinct = precinct.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(resolution_plan_metadata_view);
            reveal_with_fuel(crate::specs::part2_component_plan_precincts, 1);
        }
        resolution = resolution.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(component_plan_metadata_view);
        reveal(component_plan_builder_view);
        reveal(planned_component_view);
        reveal(prepare_plan_view);
        reveal_with_fuel(crate::specs::part2_component_plan_resolutions, 1);
    }
    Ok(PlannedComponent {
        component: PlannedTileComponent {
            component,
            x: metadata.component_x,
            y: metadata.component_y,
            width: metadata.component_width,
            height: metadata.component_height,
            output_resolution: metadata.output_resolution,
            subbands: metadata.subbands,
            placements: builder.placements,
        },
        precincts: builder.precincts,
        planned_code_blocks: builder.planned_code_blocks,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_planned_precinct_origin(first, across, precinct, band_size),
))]
pub(crate) fn derive_planned_precinct_origin(
    first: [u32; 2],
    across: u32,
    precinct: u32,
    band_size: [u32; 2],
) -> Result<[u32; 2], DecodeError> {
    let x = first[0]
        .checked_add(
            precinct
                .checked_rem(across)
                .ok_or_else(arithmetic_overflow)?,
        )
        .ok_or_else(arithmetic_overflow)?;
    let y = first[1]
        .checked_add(
            precinct
                .checked_div(across)
                .ok_or_else(arithmetic_overflow)?,
        )
        .ok_or_else(arithmetic_overflow)?;
    let band_x = x
        .checked_mul(band_size[0])
        .ok_or_else(arithmetic_overflow)?;
    let band_y = y
        .checked_mul(band_size[1])
        .ok_or_else(arithmetic_overflow)?;
    Ok([band_x, band_y])
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures resolution_plan_metadata_outcome(result) == crate::specs::part2_resolution_plan_metadata(
        size, style, component, selection, component_origin,
    ),
))]
pub(crate) fn prepare_resolution_plan_metadata(
    size: &ImageSize,
    style: CodingStyle,
    component: u16,
    selection: (u16, u8),
    component_origin: [u32; 2],
) -> Result<ResolutionPlanMetadata, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { codestream::resolution_selectors_known_fields(style); }
    let (tile, resolution) = selection;
    let geometry =
        derive_component_resolution_geometry_for(size, style, component, resolution, Some(tile))?;
    let first_subband = if resolution == 0 {
        0
    } else {
        style.subband_count_through_resolution(
            resolution.checked_sub(1).ok_or_else(arithmetic_overflow)?,
        )?
    };
    let subband_count = style
        .subband_count_through_resolution(resolution)?
        .checked_sub(first_subband)
        .ok_or_else(arithmetic_overflow)?;
    let precincts_in_resolution = if subband_count == 0 {
        0
    } else {
        match u32::try_from(geometry.precincts) {
            Ok(count) => count,
            Err(_) => return Err(arithmetic_overflow()),
        }
    };
    let (px, py) = style.precinct_exponents(resolution)?;
    if px > 31 || py > 31 {
        return Err(invalid_decode());
    }
    let scale = style.resolution_downsampling(resolution)?;
    let rx0 = ceil_div_u32(component_origin[0], scale.0)?;
    let ry0 = ceil_div_u32(component_origin[1], scale.1)?;
    let precinct_width = 1_u32 << u32::from(px);
    let precinct_height = 1_u32 << u32::from(py);
    let first_x = floor_div_u32(rx0, precinct_width)?;
    let first_y = floor_div_u32(ry0, precinct_height)?;
    let direction = if resolution == 0 {
        codestream::DecompositionDirection::None
    } else {
        style.direction_for_resolution(resolution)?
    };
    let split_x = matches!(
        direction,
        codestream::DecompositionDirection::Horizontal
            | codestream::DecompositionDirection::TwoDimensional
    );
    let split_y = matches!(
        direction,
        codestream::DecompositionDirection::Vertical
            | codestream::DecompositionDirection::TwoDimensional
    );
    let bx = if split_x {
        px.checked_sub(1).ok_or_else(invalid_decode)?
    } else {
        px
    };
    let by = if split_y {
        py.checked_sub(1).ok_or_else(invalid_decode)?
    } else {
        py
    };
    if bx > 31 || by > 31 {
        return Err(invalid_decode());
    }
    let band_width = 1_u32 << u32::from(bx);
    let band_height = 1_u32 << u32::from(by);
    let block_width = band_width.min(u32::from(style.code_block_width));
    let block_height = band_height.min(u32::from(style.code_block_height));
    if precinct_width == 0 || precinct_height == 0 || block_width == 0 || block_height == 0 {
        return Err(invalid_decode());
    }
    Ok(ResolutionPlanMetadata {
        geometry,
        first_subband,
        subband_count,
        precincts_in_resolution,
        first_precinct: [first_x, first_y],
        band_size: [band_width, band_height],
        block_size: [block_width, block_height],
    })
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures planned_precinct_outcome(result) == crate::specs::part2_planned_precinct(
        band, block_size, subbands@, range, style, policy, location, placements@, planned_code_blocks, selected, limits,
    ),
))]
pub(crate) fn plan_packet_precinct(
    band: [u32; 4],
    block_size: [u32; 2],
    subbands: &[SubbandGeometry],
    range: (usize, usize),
    style: Tier1CodingStyle,
    policy: (bool, u8),
    location: (u16, u8, u32, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    planned_code_blocks: u64,
    selected: bool,
    limits: &ResourceLimits,
) -> Result<PlannedPrecinct, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_planned_precinct(
        band, block_size, subbands@, range, style, policy, location, placements@, planned_code_blocks, selected, limits,
    ); }
    let mut builder = PrecinctPlanBuilder {
        executions: Vec::with_capacity(range.1),
        placements,
        decoder_index: 0,
        planned_code_blocks,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(precinct_plan_builder_view);
        assert(crate::packet::packet_executions_view(builder.executions@) =~= Seq::empty());
    }
    let mut local_subband = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant local_subband <= range.1,
            goal == crate::specs::part2_planned_precinct(
                band, block_size, subbands@, range, style, policy, location, placements@, planned_code_blocks, selected, limits,
            ),
            goal == crate::specs::part2_planned_precinct_rows(
                band, block_size, subbands@, range, style, policy, location, selected, limits,
                local_subband as nat, precinct_plan_builder_view(&builder),
            ),
        decreases range.1 - local_subband,
    ))]
    while local_subband < range.1 {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = precinct_plan_builder_view(&builder); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_planned_precinct_rows, 1); }
        let subband_index = range
            .0
            .checked_add(local_subband)
            .ok_or_else(arithmetic_overflow)?;
        let subband = *subbands.get(subband_index).ok_or_else(invalid_decode)?;
        let planned = plan_subband_execution(
            band,
            block_size,
            subband,
            style,
            policy,
            (location.3, subband_index, builder.decoder_index),
            builder.placements,
            builder.planned_code_blocks,
            selected,
            limits,
        )?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost row = planned_subband_execution_view(&planned); }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(precinct_plan_builder_view);
            reveal(planned_subband_execution_view);
        }
        builder.placements = planned.placements;
        builder.decoder_index = planned.decoder_index;
        builder.planned_code_blocks = planned.planned_code_blocks;
        if let Some(execution) = planned.execution {
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost execution_view = crate::packet::packet_execution_view(&execution); }
            builder.executions.push(execution);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row.execution == Some(execution_view));
                assert(crate::packet::packet_executions_view(builder.executions@)
                    =~= before.executions.push(execution_view));
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(row.execution.is_none());
                assert(crate::packet::packet_executions_view(builder.executions@) =~= before.executions);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(precinct_plan_builder_view);
            reveal(planned_subband_execution_view);
            assert(crate::specs::part2_planned_precinct_subband(
                band, block_size, subbands@, range.0, local_subband, style, policy, location.3, selected, limits, before,
            ) == Ok(precinct_plan_builder_view(&builder)));
        }
        local_subband = local_subband
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(crate::specs::part2_planned_precinct_rows, 1);
        reveal(precinct_plan_builder_view);
        reveal(planned_precinct_view);
    }
    let precinct = crate::packet::packet_precinct_from_subbands(
        location.0,
        location.1,
        location.2,
        style,
        builder.executions,
        limits,
    )?;
    Ok(PlannedPrecinct {
        precinct,
        placements: builder.placements,
        planned_code_blocks: builder.planned_code_blocks,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures planned_subband_lattice_outcome(result) == crate::specs::part2_planned_subband_lattice(band, block_size, subband),
))]
pub(crate) fn derive_planned_subband_lattice(
    band: [u32; 4],
    block_size: [u32; 2],
    subband: SubbandGeometry,
) -> Result<Option<PlannedSubbandLattice>, DecodeError> {
    let start_x = band[0].max(subband.x0);
    let start_y = band[1].max(subband.y0);
    let subband_x1 = subband
        .x0
        .checked_add(subband.width)
        .ok_or_else(arithmetic_overflow)?;
    let subband_y1 = subband
        .y0
        .checked_add(subband.height)
        .ok_or_else(arithmetic_overflow)?;
    if start_x >= subband_x1 || start_y >= subband_y1 {
        return Ok(None);
    }
    let end_x = band[0]
        .checked_add(band[2])
        .ok_or_else(arithmetic_overflow)?
        .min(subband_x1);
    let end_y = band[1]
        .checked_add(band[3])
        .ok_or_else(arithmetic_overflow)?
        .min(subband_y1);
    if start_x >= end_x || start_y >= end_y {
        return Ok(None);
    }
    let first_block_x = floor_div_u32(start_x, block_size[0])?;
    let first_block_y = floor_div_u32(start_y, block_size[1])?;
    let blocks_across = ceil_div_u32(end_x, block_size[0])?
        .checked_sub(first_block_x)
        .ok_or_else(arithmetic_overflow)?;
    let blocks_down = ceil_div_u32(end_y, block_size[1])?
        .checked_sub(first_block_y)
        .ok_or_else(arithmetic_overflow)?;
    Ok(Some(PlannedSubbandLattice {
        grid: [first_block_x, first_block_y, block_size[0], block_size[1]],
        clip: [start_x, start_y, end_x, end_y],
        blocks: [blocks_across, blocks_down],
    }))
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures planned_subband_execution_outcome(result) == crate::specs::part2_planned_subband_execution(
        band, block_size, subband, style, policy, indices, placements@, planned_code_blocks, selected, limits,
    ),
))]
pub(crate) fn plan_subband_execution(
    band: [u32; 4],
    block_size: [u32; 2],
    subband: SubbandGeometry,
    style: Tier1CodingStyle,
    policy: (bool, u8),
    indices: (usize, usize, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    planned_code_blocks: u64,
    selected: bool,
    limits: &ResourceLimits,
) -> Result<PlannedSubbandExecution, DecodeError> {
    let lattice = match derive_planned_subband_lattice(band, block_size, subband)? {
        None => {
            return Ok(PlannedSubbandExecution {
                execution: None,
                placements,
                decoder_index: indices.2,
                planned_code_blocks,
            });
        }
        Some(lattice) => lattice,
    };
    #[cfg(verus_keep_ghost)]
    proof! { reveal(planned_subband_lattice_view); }
    let planned = plan_codeblock_decoders(
        lattice.grid,
        lattice.clip,
        lattice.blocks,
        subband,
        style,
        policy,
        indices,
        placements,
        planned_code_blocks,
        selected,
        limits,
    )?;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(planned_codeblocks_view); reveal(planned_subband_execution_view); }
    let execution = PacketSubbandExecution {
        orientation: subband.orientation,
        code_blocks_across: lattice.blocks[0],
        code_blocks_down: lattice.blocks[1],
        maximum_zero_bitplanes: subband.significant_bitplanes,
        decoders: planned.decoders,
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::packet::packet_execution_known_fields(&execution); }
    Ok(PlannedSubbandExecution {
        execution: Some(execution),
        placements: planned.placements,
        decoder_index: planned.decoder_index,
        planned_code_blocks: planned.planned_code_blocks,
    })
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures planned_codeblocks_outcome(result) == crate::specs::part2_planned_codeblock_cell(
        grid, clip, block, subband, style, policy, indices, planned_codeblocks_view(&state),
    ),
))]
pub(crate) fn append_planned_codeblock(
    grid: [u32; 4],
    clip: [u32; 4],
    block: [u32; 2],
    subband: SubbandGeometry,
    style: Tier1CodingStyle,
    policy: (bool, u8),
    indices: (usize, usize),
    mut state: PlannedCodeBlocks,
) -> Result<PlannedCodeBlocks, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before = planned_codeblocks_view(&state); }
    let (x, y, width, height) = derive_planned_codeblock_geometry(grid, clip, block)?;
    let decoder = crate::tier1::tier1_configured_decoder(
        width,
        height,
        subband.significant_bitplanes,
        subband.orientation,
        style,
        policy.0,
        policy.1,
    )?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost decoded = crate::tier1::tier1_decoder_state(&decoder); }
    state.decoders.push(decoder);
    state.placements.push(ProgressionCodeBlockPlacement {
        precinct_index: indices.0,
        decoder_index: state.decoder_index,
        subband_index: indices.1,
        x: x.checked_sub(subband.x0).ok_or_else(arithmetic_overflow)?,
        y: y.checked_sub(subband.y0).ok_or_else(arithmetic_overflow)?,
    });
    state.decoder_index = state
        .decoder_index
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(planned_codeblocks_view);
        assert(state.decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder))
            =~= before.decoders.push(decoded));
    }
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures planned_codeblocks_outcome(result) == crate::specs::part2_planned_codeblocks(
        grid, clip, blocks, subband, style, policy, indices, placements@, planned_code_blocks, selected, limits,
    ),
))]
pub(crate) fn plan_codeblock_decoders(
    grid: [u32; 4],
    clip: [u32; 4],
    blocks: [u32; 2],
    subband: SubbandGeometry,
    style: Tier1CodingStyle,
    policy: (bool, u8),
    indices: (usize, usize, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    planned_code_blocks: u64,
    selected: bool,
    limits: &ResourceLimits,
) -> Result<PlannedCodeBlocks, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part2_planned_codeblocks(
        grid, clip, blocks, subband, style, policy, indices, placements@, planned_code_blocks, selected, limits,
    ); }
    let mut total = planned_code_blocks;
    let count = u64::from(blocks[0])
        .checked_mul(u64::from(blocks[1]))
        .ok_or_else(arithmetic_overflow)?;
    if selected {
        total = total.checked_add(count).ok_or_else(arithmetic_overflow)?;
        if total > limits.maximum_code_blocks() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlocks,
                limit: limits.maximum_code_blocks(),
                actual: total,
            });
        }
        if total > limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: total,
            });
        }
    }
    let capacity = match usize::try_from(count) {
        Ok(capacity) => capacity,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let mut state = PlannedCodeBlocks {
        decoders: Vec::with_capacity(capacity),
        placements,
        decoder_index: indices.2,
        planned_code_blocks: total,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(planned_codeblocks_view);
        assert(state.decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder))
            =~= Seq::empty());
    }
    let mut block_y = 0_u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant block_y <= blocks[1],
            goal == crate::specs::part2_planned_codeblocks(
                grid, clip, blocks, subband, style, policy, indices, placements@, planned_code_blocks, selected, limits,
            ),
            goal == crate::specs::part2_planned_codeblock_rows(
                grid, clip, blocks, subband, style, policy, (indices.0, indices.1),
                block_y as nat, planned_codeblocks_view(&state),
            ),
        decreases blocks[1] - block_y,
    ))]
    while block_y < blocks[1] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_planned_codeblock_rows, 1); }
        let mut block_x = 0_u32;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant block_x <= blocks[0], block_y < blocks[1],
                goal == crate::specs::part2_planned_codeblocks(
                    grid, clip, blocks, subband, style, policy, indices, placements@, planned_code_blocks, selected, limits,
                ),
                goal == match crate::specs::part2_planned_codeblock_columns(
                    grid, clip, blocks[0], subband, style, policy, (indices.0, indices.1),
                    block_y, block_x as nat, planned_codeblocks_view(&state),
                ) {
                    Err(error) => Err(error),
                    Ok(after) => crate::specs::part2_planned_codeblock_rows(
                        grid, clip, blocks, subband, style, policy, (indices.0, indices.1),
                        block_y as nat + 1, after,
                    ),
                },
            decreases blocks[0] - block_x,
        ))]
        while block_x < blocks[0] {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part2_planned_codeblock_columns, 1); }
            state = append_planned_codeblock(
                grid,
                clip,
                [block_x, block_y],
                subband,
                style,
                policy,
                (indices.0, indices.1),
                state,
            )?;
            block_x = block_x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_planned_codeblock_columns, 1); }
        block_y = block_y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_planned_codeblock_rows, 1); }
    Ok(state)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_planned_codeblock_geometry(grid, clip, block),
))]
pub(crate) fn derive_planned_codeblock_geometry(
    grid: [u32; 4],
    clip: [u32; 4],
    block: [u32; 2],
) -> Result<(u32, u32, u16, u16), DecodeError> {
    let index_x = grid[0]
        .checked_add(block[0])
        .ok_or_else(arithmetic_overflow)?;
    let nominal_x = index_x
        .checked_mul(grid[2])
        .ok_or_else(arithmetic_overflow)?;
    let index_y = grid[1]
        .checked_add(block[1])
        .ok_or_else(arithmetic_overflow)?;
    let nominal_y = index_y
        .checked_mul(grid[3])
        .ok_or_else(arithmetic_overflow)?;
    let x = nominal_x.max(clip[0]);
    let y = nominal_y.max(clip[1]);
    let nominal_x1 = nominal_x
        .checked_add(grid[2])
        .ok_or_else(arithmetic_overflow)?;
    let nominal_y1 = nominal_y
        .checked_add(grid[3])
        .ok_or_else(arithmetic_overflow)?;
    let width = nominal_x1
        .min(clip[2])
        .checked_sub(x)
        .ok_or_else(arithmetic_overflow)?;
    let width = match u16::try_from(width) {
        Ok(width) => width,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let height = nominal_y1
        .min(clip[3])
        .checked_sub(y)
        .ok_or_else(arithmetic_overflow)?;
    let height = match u16::try_from(height) {
        Ok(height) => height,
        Err(_) => return Err(arithmetic_overflow()),
    };
    Ok((x, y, width, height))
}
