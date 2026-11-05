verus! {
    pub(crate) proof fn decoder_execution_inputs_known(layout: &CodestreamLayout<'_>)
        ensures crate::specs::part2_decoder_execution_admission(codestream::decoder_layout_input_view(layout))
            == crate::specs::part2_validate_execution_layout(
                layout.info.image_size.components,
                execution_header_view(layout.info.component_coding_styles, &layout.info.part2_extensions),
                execution_tile_headers(layout.tile_parts@)),
    {
        codestream::decoder_layout_input_fields(layout);
        reveal(execution_header_view);
        reveal(execution_tile_headers);
        let input = codestream::decoder_layout_input_view(layout);
        assert(input.main_execution == execution_header_view(layout.info.component_coding_styles, &layout.info.part2_extensions));
        assert forall|index: int| 0 <= index < layout.tile_parts.len()
            implies #[trigger] crate::specs::part2_decoder_execution_tiles(input.parts)[index]
                == execution_tile_headers(layout.tile_parts@)[index] by {
            codestream::decoder_execution_header_fields(
                layout.tile_parts@[index].component_coding_styles, &layout.tile_parts@[index].part2_extensions);
        }
        assert(crate::specs::part2_decoder_execution_tiles(input.parts) =~= execution_tile_headers(layout.tile_parts@));
    }

    pub closed spec fn prepare_plan_view(plan: &PlannedTileComponent) -> crate::specs::Part1PreparePlan {
        crate::specs::Part1PreparePlan {
            component: plan.component, x: plan.x, y: plan.y, width: plan.width, height: plan.height,
            resolution: plan.output_resolution, subbands: plan.subbands@, placements: plan.placements@,
        }
    }

    pub closed spec fn prepare_style_view(style: CodingStyle) -> crate::specs::Part1PrepareStyle {
        let selector = crate::codestream::decomposition_selector_view(style);
        (style.transform, selector.0, selector.1)
    }

    pub open spec fn prepare_precincts_view(precincts: Seq<PacketPrecinctDecoder>) -> Seq<Seq<crate::specs::Tier1RawPlane>> {
        Seq::new(precincts.len(), |i: int| {
            let decoders = crate::packet::packet_precinct_decoders(&precincts[i]);
            Seq::new(decoders.len(), |j: int| crate::tier1::tier1_decoder_plane_view(&decoders[j]))
        })
    }

    pub proof fn planning_precinct_planes_known_fields(values: Seq<PacketPrecinctDecoder>)
        ensures prepare_precincts_view(values) == crate::specs::part2_precinct_decoder_planes(planning_precincts_view(values)),
    {
        assert forall |i: int| 0 <= i < values.len() implies
            prepare_precincts_view(values)[i]
                == crate::specs::part2_precinct_decoder_planes(planning_precincts_view(values))[i] by {
            crate::packet::packet_precinct_decoder_states(&values[i]);
            let decoders = crate::packet::packet_precinct_decoders(&values[i]);
            assert forall |j: int| 0 <= j < decoders.len() implies
                crate::tier1::tier1_decoder_plane_view(&decoders[j])
                    == crate::tier1::tier1_decoder_state(&decoders[j]).plane by {
                crate::tier1::tier1_decoder_plane_matches_state(&decoders[j]);
            }
            assert(prepare_precincts_view(values)[i]
                =~= crate::specs::part2_precinct_decoder_planes(planning_precincts_view(values))[i]);
        }
        assert(prepare_precincts_view(values) =~= crate::specs::part2_precinct_decoder_planes(planning_precincts_view(values)));
    }

    pub closed spec fn decoded_tile_components_view(value: &DecodedTileComponents) -> crate::specs::Part2DecodedTileComponents {
        crate::specs::Part2DecodedTileComponents { prepared: prepared_components_view(value.prepared@), mct_work: value.mct_work }
    }

    pub open spec fn decoded_tile_components_outcome(result: Result<DecodedTileComponents, DecodeError>)
        -> Result<crate::specs::Part2DecodedTileComponents, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(decoded_tile_components_view(&value)) }
    }

    pub closed spec fn prepared_component_view(value: PreparedTileComponent) -> crate::specs::Part1AssemblyTile {
        (value.component, value.x, value.y, value.width, value.height, value.fraction_bits, value.samples@)
    }

    pub open spec fn prepared_components_view(values: Seq<PreparedTileComponent>) -> Seq<crate::specs::Part1AssemblyTile> {
        Seq::new(values.len(), |index: int| prepared_component_view(values[index]))
    }

    pub open spec fn tile_mct_option(value: Option<&codestream::MultipleComponentTransform>) -> Option<Seq<crate::specs::Part2MctStage>> {
        match value { None => None, Some(transform) => Some(codestream::multiple_component_transform_view(transform)) }
    }

    pub open spec fn tile_part_mct_view(first: &TilePartPayload) -> Option<Seq<crate::specs::Part2MctStage>> {
        match first.multiple_component_transform {
            None => None,
            Some(transform) => Some(codestream::multiple_component_transform_view(&transform)),
        }
    }

    pub closed spec fn planned_components_view(plan: &ProgressionTilePlan) -> Seq<crate::specs::Part1PreparePlan> {
        Seq::new(plan.components@.len(), |index: int| prepare_plan_view(&plan.components@[index]))
    }

    pub closed spec fn progression_reconstruction_view(plan: &ProgressionTilePlan)
        -> (Seq<crate::specs::Part1PreparePlan>, Seq<Seq<crate::specs::Tier1RawPlane>>, ComponentCodingStyles, CodingStyle) {
        (planned_components_view(plan), prepare_precincts_view(plan.precincts@), plan.component_coding_styles, plan.coding_style)
    }

    spec fn prepared_tiles_outcome(result: Result<Vec<TileComponent<'_>>, DecodeError>)
        -> Result<Seq<crate::specs::Part1AssemblyTile>, DecodeError> {
        match result { Ok(tiles) => Ok(crate::image::assembly_tiles_view(tiles@)), Err(error) => Err(error) }
    }

    pub open spec fn prepared_component_outcome(result: Result<PreparedTileComponent, DecodeError>)
        -> Result<crate::specs::Part1AssemblyTile, DecodeError>
    {
        match result { Ok(value) => Ok(prepared_component_view(value)), Err(error) => Err(error) }
    }

    closed spec fn working_subband_view(value: WorkingSubband) -> crate::specs::Part1WorkingSubbandModel {
        (value.width, value.height, value.fraction_bits, value.samples@, value.visited@)
    }

    impl View for WorkingSubband {
        type V = crate::specs::Part1WorkingSubbandModel;

        closed spec fn view(&self) -> Self::V {
            working_subband_view(*self)
        }
    }

        closed spec fn working_bands_view(values: Seq<WorkingSubband>) -> Seq<crate::specs::Part1WorkingSubbandModel> {
            Seq::new(values.len(), |i: int| working_subband_view(values[i]))
        }

        impl View for PrepareWorking {
            type V = crate::specs::Part1PrepareWorking;
            closed spec fn view(&self) -> Self::V { (working_bands_view(self.bands@), self.bytes) }
        }

        closed spec fn prepare_working_outcome(result: Result<PrepareWorking, DecodeError>)
            -> Result<crate::specs::Part1PrepareWorking, DecodeError>
        {
            match result { Ok(value) => Ok(value@), Err(error) => Err(error) }
        }

        impl View for PrepareFold {
            type V = crate::specs::Part1PrepareFold;
            closed spec fn view(&self) -> Self::V { (self.width, self.height, self.samples@, self.first_detail) }
        }

        closed spec fn prepare_fold_outcome(result: Result<PrepareFold, DecodeError>)
            -> Result<crate::specs::Part1PrepareFold, DecodeError>
        {
            match result { Ok(value) => Ok(value@), Err(error) => Err(error) }
        }

        closed spec fn prepare_cell_outcome(result: Result<SignedMagnitude, DecodeError>)
            -> Result<crate::specs::Part1QuantizedCoefficient, DecodeError>
        {
            match result { Ok(value) => Ok((crate::magnitude::magnitude_limbs(value.magnitude), value.negative)), Err(error) => Err(error) }
        }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn planning_components_view(values: Seq<PlannedTileComponent>) -> Seq<crate::specs::Part1PreparePlan> {
        values.map_values(|value: PlannedTileComponent| prepare_plan_view(&value))
    }

    closed spec fn tile_plan_buffers_view(
        precincts: Seq<PacketPrecinctDecoder>, components: Seq<PlannedTileComponent>, total: u64,
    ) -> crate::specs::Part2TilePlanBuffers {
        crate::specs::Part2TilePlanBuffers {
            precincts: planning_precincts_view(precincts), components: planning_components_view(components),
            planned_code_blocks: total,
        }
    }

    pub closed spec fn progression_plan_view(value: &ProgressionTilePlan) -> crate::specs::Part2ProgressionTilePlan {
        crate::specs::Part2ProgressionTilePlan {
            tile: value.tile_index, coding_style: value.coding_style, coding_styles: value.component_coding_styles,
            grid: crate::packet::packet_grid_view(&value.grid), precincts: planning_precincts_view(value.precincts@),
            components: planning_components_view(value.components@),
        }
    }

    pub open spec fn progression_plan_outcome(result: Result<ProgressionTilePlan, DecodeError>)
        -> Result<crate::specs::Part2ProgressionTilePlan, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(progression_plan_view(&value)) }
    }

    pub closed spec fn planned_subband_lattice_view(value: PlannedSubbandLattice) -> crate::specs::Part2PlannedSubbandLattice {
        crate::specs::Part2PlannedSubbandLattice { grid: value.grid, clip: value.clip, blocks: value.blocks }
    }

    pub open spec fn planned_subband_lattice_outcome(result: Result<Option<PlannedSubbandLattice>, DecodeError>)
        -> Result<Option<crate::specs::Part2PlannedSubbandLattice>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(None) => Ok(None), Ok(Some(value)) => Ok(Some(planned_subband_lattice_view(value))) }
    }

    pub closed spec fn resolution_geometry_style(style: CodingStyle) -> crate::specs::Part2ResolutionStyle {
        let selector = codestream::decomposition_selector_view(style);
        (selector.0, selector.1, style.code_block_width, style.code_block_height,
            codestream::precinct_selector_view(style).1)
    }

    pub open spec fn resolution_counts_outcome(
        result: Result<(u8, Vec<u8>, Vec<u8>), DecodeError>,
    ) -> Result<crate::specs::Part2ComponentResolutionCounts, DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok(counts) => Ok((counts.0, counts.1@, counts.2@)),
        }
    }

    pub open spec fn subbands_outcome(result: Result<Vec<SubbandGeometry>, DecodeError>)
        -> Result<Seq<SubbandGeometry>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(values) => Ok(values@) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn planning_precincts_view(values: Seq<PacketPrecinctDecoder>) -> Seq<crate::specs::Part1PacketPrecinctState> {
        values.map_values(|value: PacketPrecinctDecoder| crate::packet::packet_precinct_view(&value))
    }

    closed spec fn component_plan_builder_view(value: &ComponentPlanBuilder) -> crate::specs::Part2ComponentPlanBuffers {
        crate::specs::Part2ComponentPlanBuffers {
            precincts: planning_precincts_view(value.precincts@), placements: value.placements@,
            planned_code_blocks: value.planned_code_blocks,
        }
    }

    pub closed spec fn planned_component_view(value: &PlannedComponent) -> crate::specs::Part2PlannedComponent {
        crate::specs::Part2PlannedComponent {
            component: prepare_plan_view(&value.component), precincts: planning_precincts_view(value.precincts@),
            planned_code_blocks: value.planned_code_blocks,
        }
    }

    pub open spec fn planned_component_outcome(result: Result<PlannedComponent, DecodeError>)
        -> Result<crate::specs::Part2PlannedComponent, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(planned_component_view(&value)) }
    }

    pub closed spec fn resolution_plan_metadata_view(value: &ResolutionPlanMetadata) -> crate::specs::Part2ResolutionPlanMetadata {
        crate::specs::Part2ResolutionPlanMetadata {
            geometry: value.geometry, first_subband: value.first_subband, subband_count: value.subband_count,
            precincts_in_resolution: value.precincts_in_resolution, first_precinct: value.first_precinct,
            band_size: value.band_size, block_size: value.block_size,
        }
    }

    pub open spec fn resolution_plan_metadata_outcome(result: Result<ResolutionPlanMetadata, DecodeError>)
        -> Result<crate::specs::Part2ResolutionPlanMetadata, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(resolution_plan_metadata_view(&value)) }
    }

    closed spec fn precinct_plan_builder_view(value: &PrecinctPlanBuilder) -> crate::specs::Part2PrecinctPlanBuilder {
        crate::specs::Part2PrecinctPlanBuilder {
            executions: crate::packet::packet_executions_view(value.executions@),
            placements: value.placements@, decoder_index: value.decoder_index,
            planned_code_blocks: value.planned_code_blocks,
        }
    }

    pub closed spec fn planned_precinct_view(value: &PlannedPrecinct) -> crate::specs::Part2PlannedPrecinct {
        crate::specs::Part2PlannedPrecinct {
            precinct: crate::packet::packet_precinct_view(&value.precinct),
            placements: value.placements@, planned_code_blocks: value.planned_code_blocks,
        }
    }

    pub open spec fn planned_precinct_outcome(result: Result<PlannedPrecinct, DecodeError>)
        -> Result<crate::specs::Part2PlannedPrecinct, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(planned_precinct_view(&value)) }
    }

    pub closed spec fn planned_subband_execution_view(value: &PlannedSubbandExecution) -> crate::specs::Part2PlannedSubbandExecution {
        crate::specs::Part2PlannedSubbandExecution {
            execution: match value.execution { None => None, Some(execution) => Some(crate::packet::packet_execution_view(&execution)) },
            placements: value.placements@, decoder_index: value.decoder_index,
            planned_code_blocks: value.planned_code_blocks,
        }
    }

    pub open spec fn planned_subband_execution_outcome(result: Result<PlannedSubbandExecution, DecodeError>)
        -> Result<crate::specs::Part2PlannedSubbandExecution, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(planned_subband_execution_view(&value)) }
    }

    pub closed spec fn planned_codeblocks_view(value: &PlannedCodeBlocks) -> crate::specs::Part2PlannedCodeBlocks {
        crate::specs::Part2PlannedCodeBlocks {
            decoders: value.decoders@.map_values(|decoder: Tier1CodeBlockDecoder| crate::tier1::tier1_decoder_state(&decoder)),
            placements: value.placements@, decoder_index: value.decoder_index,
            planned_code_blocks: value.planned_code_blocks,
        }
    }

    pub open spec fn planned_codeblocks_outcome(result: Result<PlannedCodeBlocks, DecodeError>)
        -> Result<crate::specs::Part2PlannedCodeBlocks, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(planned_codeblocks_view(&value)) }
    }

    pub closed spec fn component_plan_metadata_view(value: &PlannedComponentMetadata) -> crate::specs::Part2ComponentPlanMetadata {
        crate::specs::Part2ComponentPlanMetadata {
            coding_style: value.component_coding_style, output_resolution: value.output_resolution,
            tier1_style: value.tier1_style, bounds: value.bounds, width: value.component_width,
            height: value.component_height, x: value.component_x, y: value.component_y, subbands: value.subbands@,
        }
    }

    pub open spec fn component_plan_metadata_outcome(result: Result<PlannedComponentMetadata, DecodeError>)
        -> Result<crate::specs::Part2ComponentPlanMetadata, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(component_plan_metadata_view(&value)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn nonlinear_region_view(region: &NonlinearRegion<'_>) -> crate::specs::Part2NonlinearRegion {
        crate::specs::Part2NonlinearRegion {
            component: region.component, x0: region.x0, y0: region.y0, x1: region.x1, y1: region.y1,
            transform: codestream::owned_nonlinear_view(region.transform),
        }
    }

    pub(crate) open spec fn nonlinear_regions_view(regions: Seq<NonlinearRegion<'_>>) -> Seq<crate::specs::Part2NonlinearRegion> {
        regions.map_values(|region: NonlinearRegion<'_>| nonlinear_region_view(&region))
    }

    pub(crate) open spec fn nonlinear_regions_outcome(result: Result<Vec<NonlinearRegion<'_>>, DecodeError>)
        -> Result<Seq<crate::specs::Part2NonlinearRegion>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(regions) => Ok(nonlinear_regions_view(regions@)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn validated_selection_view(selection: ValidatedSelection) -> crate::specs::Part2ValidatedSelection {
        (selection.tiles@, selection.region@, selection.discard_levels)
    }

    closed spec fn color_selection_outcome(result: Result<(DecodeSelection, [u32; 4]), DecodeError>)
        -> Result<(crate::specs::Part2DecodeSelection, Seq<u32>), DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(output) => Ok((crate::options::decode_selection_value_view(output.0), output.1@)),
        }
    }

    closed spec fn selection_region_outcome(result: Result<[u32; 4], DecodeError>) -> Result<Seq<u32>, DecodeError> {
        match result { Err(error) => Err(error), Ok(region) => Ok(region@) }
    }

    pub closed spec fn associated_typed_outcome(result: Result<(TypedImage, Option<&jp2::Jp2Header>), DecodeError>)
        -> Result<(crate::specs::Part1DecodedTypedImage, Option<crate::specs::Part2AssociatedHeader>), DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(output) => Ok((crate::image::typed_image_value_view(output.0), jp2::associated_header_option(output.1))),
        }
    }

    closed spec fn selected_tiles_outcome(result: Result<Vec<u16>, DecodeError>) -> Result<Seq<u16>, DecodeError> {
        match result { Err(error) => Err(error), Ok(tiles) => Ok(tiles@) }
    }

    closed spec fn validated_selection_outcome(result: Result<ValidatedSelection, DecodeError>)
        -> Result<crate::specs::Part2ValidatedSelection, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(selection) => Ok(validated_selection_view(selection)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn tile_decode_metadata_view<'a, 'data>(value: &TileDecodeMetadata<'a, 'data>)
        -> crate::specs::Part2TileDecodeMetadata {
        crate::specs::Part2TileDecodeMetadata { first: codestream::tile_part_owned_view(value.first), standard: value.standard, resolution_counts: value.resolution_counts@ }
    }

    pub open spec fn tile_decode_metadata_outcome<'a, 'data>(result: Result<TileDecodeMetadata<'a, 'data>, DecodeError>)
        -> Result<crate::specs::Part2TileDecodeMetadata, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok(tile_decode_metadata_view(&value)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn resolution_counts_outcome_for_tile(result: Result<Vec<u8>, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match result { Err(error) => Err(error), Ok(counts) => Ok(counts@) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn decoded_layout_tile_view(value: &DecodedLayoutTile) -> crate::specs::Part2DecodedLayoutTile {
        crate::specs::Part2DecodedLayoutTile {
            prepared: prepared_components_view(value.prepared@), counters: value.counters, mct_work: value.mct_work,
        }
    }

    pub open spec fn decoded_layout_tile_outcome(result: Result<DecodedLayoutTile, DecodeError>)
        -> Result<crate::specs::Part2DecodedLayoutTile, DecodeError> {
        match result { Err(error) => Err(error), Ok(value) => Ok(decoded_layout_tile_view(&value)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn collected_tile_parts_outcome(result: Result<Vec<TilePartPayload<'_>>, DecodeError>)
        -> Result<Seq<crate::specs::Part2OwnedTilePart>, DecodeError> {
        match result { Err(error) => Err(error), Ok(parts) => Ok(codestream::tile_parts_owned_view(parts@)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn layout_accumulation_view(
        prepared: Seq<PreparedTileComponent>, counters: (u64, u64, u64), work: u64,
    ) -> crate::specs::Part2DecodedLayoutTile {
        crate::specs::Part2DecodedLayoutTile { prepared: prepared_components_view(prepared), counters, mct_work: work }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) closed spec fn execution_header_view(styles: ComponentCodingStyles, extensions: &codestream::Part2Extensions)
        -> crate::specs::Part2ExecutionHeader
    {
        (styles, codestream::part2_execution_registry(extensions), codestream::part2_kernel_registry(extensions),
            codestream::part2_component_depths(extensions))
    }

    pub(crate) closed spec fn execution_tile_headers(parts: Seq<TilePartPayload<'_>>) -> Seq<crate::specs::Part2ExecutionHeader> {
        Seq::new(parts.len(), |index: int|
            execution_header_view(parts[index].component_coding_styles, &parts[index].part2_extensions))
    }
}
