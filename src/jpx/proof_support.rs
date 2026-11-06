#[cfg(verus_keep_ghost)]
verus! {
    #[verifier::inline]
    spec fn inspection_layer_config(layer: &CompositingLayer) -> crate::specs::Part2InspectionLayerConfig {
        crate::specs::Part2InspectionLayerConfig {
            grid: (jp2::source_layer_geometry(layer).1, jp2::source_layer_geometry(layer).2),
            registrations: jp2::source_layer_registrations(layer),
            has_color_group: jp2::source_layer_color_group(layer).len() > 0,
            has_opacity_box: jp2::source_layer_opacity(layer).is_some(),
            nested_metadata_boxes: jp2::source_layer_nested_metadata(layer),
        }
    }

    #[verifier::inline]
    spec fn inspection_composition_config(composition: &jp2::Composition)
        -> crate::specs::Part2InspectionCompositionConfig
    {
        crate::specs::Part2InspectionCompositionConfig {
            width: composition.width, height: composition.height, loop_count: composition.loop_count,
            sets: timeline_set_views(composition), has_unknown_boxes: composition.has_unknown_boxes,
        }
    }

    #[verifier::inline]
    spec fn inspection_file_input(file: &Jp2File) -> crate::specs::Part2InspectionFileInput {
        let layers = jp2::source_file_layers(file);
        crate::specs::Part2InspectionFileInput {
            layers: Seq::new(layers.len(), |i: int| inspection_layer_config(&layers[i])),
            codestreams: jp2::jpx_file_decode_view(file).1.len() as usize,
            composition: match jp2::source_file_composition_reference(file) {
                None => None, Some(composition) => Some(inspection_composition_config(composition)),
            },
            metadata: jp2::source_file_metadata(file),
        }
    }

    #[verifier::inline]
    spec fn inspection_source_geometries(codestreams: Seq<crate::codestream::CodestreamInfo>) -> Seq<(u32, u32)> {
        Seq::new(codestreams.len(), |i: int| (codestreams[i].image_size.width, codestreams[i].image_size.height))
    }

    #[verifier::inline]
    spec fn inspected_layer_view(layer: &JpxLayerInfo) -> crate::specs::Part2LayerInspection {
        crate::specs::Part2LayerInspection {
            index: layer.index, codestream_indices: layer.codestream_indices@,
            grid: (layer.horizontal_grid_size, layer.vertical_grid_size),
            offset: (layer.horizontal_offset, layer.vertical_offset), geometry: (layer.width, layer.height),
            has_color_group: layer.has_color_group, has_opacity_box: layer.has_opacity_box,
            nested_metadata_boxes: layer.nested_metadata_boxes,
        }
    }

    #[verifier::inline]
    spec fn inspected_layers_view(layers: Seq<JpxLayerInfo>) -> Seq<crate::specs::Part2LayerInspection> {
        Seq::new(layers.len(), |i: int| inspected_layer_view(&layers[i]))
    }

    #[verifier::inline]
    spec fn inspected_composition_view(composition: &JpxCompositionInfo) -> crate::specs::Part2CompositionInspection {
        crate::specs::Part2CompositionInspection {
            source: composition_source_view(composition), instruction_sets: composition.instruction_sets,
            total_duration_milliseconds: composition.total_duration_milliseconds,
            has_unknown_boxes: composition.has_unknown_boxes,
        }
    }

    pub closed spec fn raw_jpx_inspection_outcome(result: Result<JpxInspection, DecodeError>)
        -> Result<crate::specs::Part2JpxInspection, DecodeError>
    {
        inspection_result(result)
    }

    proof fn raw_jpx_inspection_outcome_known()
        ensures forall|result: Result<JpxInspection, DecodeError>|
            raw_jpx_inspection_outcome(result) == inspection_result(result),
    {
        reveal(raw_jpx_inspection_outcome);
    }

    proof fn raw_jpx_composition_known(composition: &jp2::Composition)
        ensures inspection_composition_config(composition)
            == crate::specs::part2_raw_inspection_composition(jp2::raw_composition_view(composition)),
    {
        assert forall|i: int| #![auto] 0 <= i < composition.instruction_sets@.len() implies
            timeline_set_views(composition)[i]
                == crate::specs::part2_raw_timeline_sets(jp2::raw_composition_view(composition).3)[i] by {
            let instructions = composition.instruction_sets@[i].instructions@;
            assert(timeline_instruction_views(instructions) =~=
                Seq::new(instructions.len(), |j: int| crate::specs::part2_raw_timeline_instruction(instructions[j])));
        }
        assert(timeline_set_views(composition) =~=
            crate::specs::part2_raw_timeline_sets(jp2::raw_composition_view(composition).3));
    }

    proof fn raw_jpx_file_known(file: &Jp2File)
        ensures inspection_file_input(file) == crate::specs::part2_raw_inspection_file(jp2::raw_jp2_file_view(file)),
    {
        jp2::raw_jpx_inspection_parts_known(file);
        let layers = jp2::source_file_layers(file);
        assert forall|i: int| #![auto] 0 <= i < layers.len() implies
            inspection_layer_config(&layers[i])
                == crate::specs::part2_raw_inspection_layer(jp2::raw_compositing_layer_view(&layers[i])) by {
            jp2::raw_jpx_inspection_layer_known(&layers[i]);
        }
        assert(inspection_file_input(file).layers =~=
            crate::specs::part2_raw_inspection_file(jp2::raw_jp2_file_view(file)).layers);
        if let Some(composition) = jp2::source_file_composition_reference(file) {
            raw_jpx_composition_known(composition);
        }
    }

    proof fn raw_jpx_geometries_known(infos: Seq<crate::codestream::CodestreamInfo>)
        ensures inspection_source_geometries(infos)
            == crate::specs::part2_raw_inspection_geometries(jp2::raw_codestream_infos_view(infos)),
    {
        assert forall|i: int| #![auto] 0 <= i < infos.len() implies
            inspection_source_geometries(infos)[i]
                == crate::specs::part2_raw_inspection_geometries(jp2::raw_codestream_infos_view(infos))[i] by {
            crate::codestream::complete_codestream_info_known_fields(&infos[i]);
        }
        assert(inspection_source_geometries(infos)
            =~= crate::specs::part2_raw_inspection_geometries(jp2::raw_codestream_infos_view(infos)));
    }

    #[verifier::inline]
    spec fn inspection_result(result: Result<JpxInspection, DecodeError>)
        -> Result<crate::specs::Part2JpxInspection, DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(metadata) => Ok(crate::specs::Part2JpxInspection {
                layers: inspected_layers_view(metadata.layers@),
                composition: match &metadata.composition {
                    None => None, Some(composition) => Some(inspected_composition_view(composition)),
                },
                metadata: (metadata.metadata_boxes, metadata.metadata_depth),
            }),
        }
    }

    pub closed spec fn composition_source_frames(composition: &JpxCompositionInfo) -> Seq<JpxFrameInfo> {
        composition.frames@
    }

    pub closed spec fn instruction_source_layer_index(instruction: &JpxInstructionInfo) -> usize {
        instruction.layer_index
    }

    pub closed spec fn composition_source_view(composition: &JpxCompositionInfo) -> crate::specs::Part2FrameSourceConfig {
        (composition.width, composition.height, composition.loop_count, frame_views(composition.frames@))
    }

    pub closed spec fn inspection_composition_reference(metadata: &JpxInspection) -> Option<&JpxCompositionInfo> {
        match &metadata.composition { None => None, Some(composition) => Some(composition) }
    }

    pub open spec fn inspection_composition_view(metadata: &JpxInspection) -> Option<crate::specs::Part2FrameSourceConfig> {
        match inspection_composition_reference(metadata) {
            None => None, Some(composition) => Some(composition_source_view(composition)),
        }
    }

    proof fn supplied_views_push(supplied: Seq<SuppliedLayer>, value: SuppliedLayer)
        ensures supplied_views(supplied.push(value)) == supplied_views(supplied).push(
            (value.0, match value.1 { None => None, Some(outcome) => Some(owned_layer_outcome(outcome)) })),
    {
        assert(supplied_views(supplied.push(value)) =~= supplied_views(supplied).push(
            (value.0, match value.1 { None => None, Some(outcome) => Some(owned_layer_outcome(outcome)) })));
    }

    #[verifier::inline]
    spec fn general_source_views(sources: Seq<(TypedImage, u8, u8, u32, u32)>)
        -> Seq<crate::specs::Part2GeneralSource>
    {
        Seq::new(sources.len(), |i: int|
            (crate::image::typed_image_value_view(sources[i].0),
                sources[i].1, sources[i].2, sources[i].3, sources[i].4))
    }

    proof fn general_source_views_push(
        sources: Seq<(TypedImage, u8, u8, u32, u32)>,
        source: (TypedImage, u8, u8, u32, u32),
    )
        ensures general_source_views(sources.push(source)) == general_source_views(sources).push(
            (crate::image::typed_image_value_view(source.0), source.1, source.2, source.3, source.4)),
    {
        assert(general_source_views(sources.push(source)) =~= general_source_views(sources).push(
            (crate::image::typed_image_value_view(source.0), source.1, source.2, source.3, source.4)));
    }

    #[verifier::inline]
    spec fn timeline_instruction_view(instruction: CompositionInstruction) -> crate::specs::Part2TimelineInstruction {
        ((0, instruction.target_x, instruction.target_y, instruction.target_width, instruction.target_height,
            instruction.source_x, instruction.source_y, instruction.source_width, instruction.source_height,
            instruction.persistent, instruction.next_reuse), instruction.life)
    }

    #[verifier::inline]
    spec fn timeline_instruction_views(instructions: Seq<CompositionInstruction>) -> Seq<crate::specs::Part2TimelineInstruction> {
        Seq::new(instructions.len(), |i: int| timeline_instruction_view(instructions[i]))
    }

    #[verifier::inline]
    spec fn timeline_set_views(composition: &jp2::Composition) -> Seq<crate::specs::Part2TimelineSet> {
        Seq::new(composition.instruction_sets.len() as nat, |i: int|
            (composition.instruction_sets@[i].repeat, timeline_instruction_views(composition.instruction_sets@[i].instructions@)))
    }

    #[verifier::inline]
    spec fn timeline_state_view(state: &TimelineState) -> crate::specs::Part2TimelineState {
        (frame_views(state.frames@), state.assignments@, state.next_layer, state.instruction_index, state.milliseconds)
    }

    #[verifier::inline]
    spec fn timeline_step_result(result: Result<bool, DecodeError>, state: &TimelineState) -> crate::specs::Part2TimelineExecution {
        match result { Err(error) => Err(error), Ok(active) => Ok((active, timeline_state_view(state))) }
    }

    #[verifier::inline]
    spec fn timeline_frames_result(result: Result<Vec<JpxFrameInfo>, DecodeError>) -> Result<Seq<crate::specs::Part2Frame>, DecodeError> {
        match result { Err(error) => Err(error), Ok(frames) => Ok(frame_views(frames@)) }
    }

    #[verifier::inline]
    spec fn timeline_frame_result(result: Result<(), DecodeError>, frames: Seq<JpxFrameInfo>, time: u64)
        -> Result<(Seq<crate::specs::Part2Frame>, u64), DecodeError>
    {
        match result { Err(error) => Err(error), Ok(()) => Ok((frame_views(frames), time)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    #[verifier::inline]
    spec fn instruction_view(instruction: JpxInstructionInfo) -> crate::specs::Part2Instruction {
        (instruction.layer_index, instruction.target_x, instruction.target_y, instruction.target_width, instruction.target_height,
            instruction.source_x, instruction.source_y, instruction.source_width, instruction.source_height,
            instruction.persistent, instruction.next_reuse)
    }

    #[verifier::inline]
    spec fn instruction_views(instructions: Seq<JpxInstructionInfo>) -> Seq<crate::specs::Part2Instruction> {
        Seq::new(instructions.len(), |i: int| instruction_view(instructions[i]))
    }

    proof fn instruction_views_push(instructions: Seq<JpxInstructionInfo>, instruction: JpxInstructionInfo)
        ensures instruction_views(instructions.push(instruction)) == instruction_views(instructions).push(instruction_view(instruction)),
    {
        assert(instruction_views(instructions.push(instruction)) =~= instruction_views(instructions).push(instruction_view(instruction)));
    }

    #[verifier::inline]
    spec fn frame_views(frames: Seq<JpxFrameInfo>) -> Seq<crate::specs::Part2Frame> {
        Seq::new(frames.len(), |i: int| (frames[i].index, frames[i].start_milliseconds,
            frames[i].duration_milliseconds, frames[i].persistent, instruction_views(frames[i].instructions@)))
    }

    proof fn frame_views_push(frames: Seq<JpxFrameInfo>, frame: JpxFrameInfo)
        ensures frame_views(frames.push(frame)) == frame_views(frames).push(
            (frame.index, frame.start_milliseconds, frame.duration_milliseconds, frame.persistent, instruction_views(frame.instructions@))),
    {
        assert(frame_views(frames.push(frame)) =~= frame_views(frames).push(
            (frame.index, frame.start_milliseconds, frame.duration_milliseconds, frame.persistent, instruction_views(frame.instructions@))));
    }

    #[verifier::inline]
    spec fn frame_selection_result(result: Result<Vec<JpxInstructionInfo>, DecodeError>)
        -> Result<Seq<crate::specs::Part2Instruction>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(instructions) => Ok(instruction_views(instructions@)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    #[verifier::inline]
    spec fn layer_borrowed_planes(colors: Seq<&[u16]>) -> Seq<Seq<u16>> {
        Seq::new(colors.len(), |i: int| colors[i]@)
    }

    proof fn layer_borrowed_planes_push(colors: Seq<&[u16]>, samples: &[u16])
        ensures layer_borrowed_planes(colors.push(samples)) == layer_borrowed_planes(colors).push(samples@),
    {
        assert(layer_borrowed_planes(colors.push(samples)) =~= layer_borrowed_planes(colors).push(samples@));
    }

    proof fn layer_owned_planes_push(colors: Seq<Vec<u16>>, samples: Vec<u16>)
        ensures crate::specs::part2_composition_planes(colors.push(samples))
            == crate::specs::part2_composition_planes(colors).push(samples@),
    {
        assert(crate::specs::part2_composition_planes(colors.push(samples))
            =~= crate::specs::part2_composition_planes(colors).push(samples@));
    }

    #[verifier::inline]
    spec fn layer_color_slots(colors: Seq<Option<&[u16]>>) -> Seq<Option<Seq<u16>>> {
        Seq::new(colors.len(), |i: int| match colors[i] {
            Some(samples) => Some(samples@),
            None => None,
        })
    }

    #[verifier::inline]
    spec fn layer_alpha_planes(alphas: Seq<(&[u16], bool)>) -> Seq<crate::specs::Part2LayerAlpha> {
        Seq::new(alphas.len(), |i: int| (alphas[i].0@, alphas[i].1))
    }

    #[verifier::inline]
    spec fn layer_owned_alpha(alpha: Option<(Vec<u16>, bool)>) -> Option<crate::specs::Part2LayerAlpha> {
        match alpha {
            Some((samples, premultiplied)) => Some((samples@, premultiplied)),
            None => None,
        }
    }

    #[verifier::inline]
    spec fn owned_layer_view(layer: &OwnedLayer) -> crate::specs::Part2OwnedLayer {
        (layer.width, layer.height, layer.color_space,
            crate::specs::part2_composition_planes(layer.colors@), layer_owned_alpha(layer.alpha))
    }

    #[verifier::inline]
    spec fn layer_registration_view(registration: &jp2::CodestreamRegistration) -> crate::specs::Part2LayerRegistration {
        (registration.codestream_index, registration.horizontal_subsampling, registration.vertical_subsampling,
            registration.horizontal_offset, registration.vertical_offset)
    }

    #[verifier::inline]
    spec fn owned_layer_outcome(result: Result<OwnedLayer, DecodeError>) -> crate::specs::Part2OwnedLayerResult {
        match result {
            Err(error) => Err(error),
            Ok(layer) => Ok(owned_layer_view(&layer)),
        }
    }

    #[verifier::inline]
    spec fn supplied_views(supplied: Seq<SuppliedLayer>) -> Seq<crate::specs::Part2SuppliedLayer> {
        Seq::new(supplied.len(), |i: int| (supplied[i].0, match supplied[i].1 {
            None => None, Some(outcome) => Some(owned_layer_outcome(outcome)),
        }))
    }

    #[verifier::inline]
    spec fn collected_layers_result(result: Result<Vec<(OwnedLayer, JpxInstructionInfo)>, DecodeError>)
        -> Result<Seq<crate::specs::Part2Placement>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(placements) => Ok(placement_views(placements@)) }
    }

        #[verifier::inline]
        spec fn placement_view(placement: &(OwnedLayer, JpxInstructionInfo)) -> crate::specs::Part2Placement {
            let layer = &placement.0;
            let instruction = placement.1;
            ((layer.width, layer.height, layer.color_space, crate::specs::part2_composition_planes(layer.colors@),
                layer_owned_alpha(layer.alpha)),
                (instruction.layer_index, instruction.target_x, instruction.target_y, instruction.target_width, instruction.target_height,
                    instruction.source_x, instruction.source_y, instruction.source_width, instruction.source_height,
                    instruction.persistent, instruction.next_reuse))
        }

        #[verifier::inline]
        spec fn placement_views(placements: Seq<(OwnedLayer, JpxInstructionInfo)>) -> Seq<crate::specs::Part2Placement> {
            Seq::new(placements.len(), |i: int| placement_view(&placements[i]))
    }

    proof fn placement_views_push(placements: Seq<(OwnedLayer, JpxInstructionInfo)>, placement: (OwnedLayer, JpxInstructionInfo))
        ensures placement_views(placements.push(placement)) == placement_views(placements).push(placement_view(&placement)),
    {
        assert(placement_views(placements.push(placement)) =~= placement_views(placements).push(placement_view(&placement)));
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    #[verifier::inline]
    spec fn layer_channels_outcome(result: Result<LayerChannels<'_>, DecodeError>) -> crate::specs::Part2LayerInputResult {
        match result {
            Err(error) => Err(error),
            Ok(layer) => Ok((layer.width, layer.height, layer_borrowed_planes(layer.colors@), layer_owned_alpha(layer.alpha))),
        }
    }
}
