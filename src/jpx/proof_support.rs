#[cfg(verus_keep_ghost)]
verus! {
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
