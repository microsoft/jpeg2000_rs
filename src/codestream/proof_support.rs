#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn complete_codestream_info_view(value: &CodestreamInfo)
        -> (crate::specs::Part1LayoutMainFields, crate::specs::Part1ProfileMetadata, u32, u64)
    {
        (
            main_header_fields_view(&value.image_size, value.coding_style, &value.quantization,
                &value.component_coding_styles, &value.component_quantizations, &value.roi_shifts,
                &value.progression_changes, &value.multiple_component_transform, &value.part2_extensions,
                value.profile.r_siz, &value.profile.extended_capabilities, &value.profile.profile,
                &value.profile.corresponding_profile, value.main_header_segments),
            complete_codestream_profile_view(&value.profile), value.tile_parts, value.consumed_bytes,
        )
    }

    pub closed spec fn complete_codestream_info_outcome(value: Result<CodestreamInfo, DecodeError>)
        -> Result<(crate::specs::Part1LayoutMainFields, crate::specs::Part1ProfileMetadata, u32, u64), DecodeError>
    {
        match value { Err(error) => Err(error), Ok(info) => Ok(complete_codestream_info_view(&info)) }
    }

    pub closed spec fn complete_layout_outcome(value: Result<CodestreamLayout<'_>, DecodeError>)
        -> crate::specs::Part1CompleteLayoutResult
    {
        match value {
            Err(error) => Err(error),
            Ok(layout) => {
                let info = complete_codestream_info_view(&layout.info);
                Ok((info.0, info.1, info.2, info.3,
                    layout.tile_parts@.map_values(|part: TilePartPayload<'_>| tile_part_payload_view(&part))))
            },
        }
    }

    pub(crate) closed spec fn main_header_accumulator_view(
        size: &ImageSize, r_siz: u16, start: usize, segments: u64,
        style: Option<CodingStyle>, qcd: Option<Segment<'_>>,
        coc: Seq<Option<Segment<'_>>>, qcc: Seq<Option<Segment<'_>>>,
        roi: &RoiShifts, roi_seen: Seq<bool>,
        plm: Seq<PacketLengths<'_>>, next_plm: u16, plm_seen: bool,
        ppm: Seq<u8>, next_ppm: u16, ppm_fragments: u16,
        progression: &ProgressionChanges, poc_seen: bool,
        arrays: Seq<MctArray>, records: Seq<MctRecord>, order: &Option<Vec<u8>>,
        pending_mct: Seq<MctFragment>, completed_mct: Seq<u8>,
        pending_mcc: Seq<MccFragment>, completed_mcc: Seq<u8>,
        capabilities: &Option<ExtendedCapabilities>, profile: &Option<ProfileNumber>,
        corresponding_profile: &Option<ProfileNumber>, extensions: &Part2Extensions, next_tlm: u16,
    ) -> crate::specs::Part1MainHeaderAccumulator {
        crate::specs::Part1MainHeaderAccumulator {
            image_size: parsed_image_size_view(size), r_siz, start, segments,
            coding_style: match style { None => None, Some(style) => Some(parsed_coding_style_view(style)) },
            qcd: optional_segment_view(qcd), coc: segment_slots_view(coc), qcc: segment_slots_view(qcc),
            roi: roi_shifts_view(roi), roi_seen,
            plm: packet_length_groups_view(plm), next_plm, plm_seen, ppm, next_ppm, ppm_fragments,
            progression: progression_changes_view(progression), poc_seen,
            arrays: mct_arrays_view(arrays), records: mct_records_view(records),
            order: match order { None => None, Some(order) => Some(order@) },
            pending_mct: mct_pending_view(pending_mct), completed_mct,
            pending_mcc: mcc_pending_view(pending_mcc), completed_mcc,
            capabilities: optional_capabilities_view(capabilities),
            profile: optional_profile_number_view(profile),
            corresponding_profile: optional_profile_number_view(corresponding_profile),
            extensions: owned_extensions_view(extensions), next_tlm,
        }
    }

    pub(crate) closed spec fn main_header_fields_view(
        size: &ImageSize, style: CodingStyle, quantization: &Quantization,
        styles: &ComponentCodingStyles, quantizations: &ComponentQuantizations,
        roi: &RoiShifts, progression: &ProgressionChanges,
        transform: &Option<MultipleComponentTransform>, extensions: &Part2Extensions,
        r_siz: u16, capabilities: &Option<ExtendedCapabilities>,
        profile: &Option<ProfileNumber>, corresponding_profile: &Option<ProfileNumber>, segments: u64,
    ) -> crate::specs::Part1LayoutMainFields {
        crate::specs::Part1LayoutMainFields {
            image_size: parsed_image_size_view(size), coding_style: parsed_coding_style_view(style),
            quantization: quantization_view(quantization), styles: component_style_owner_view(styles),
            quantizations: parsed_quantization_owner_view(quantizations),
            roi: roi_shifts_view(roi), progression: progression_changes_view(progression),
            transform: match transform {
                None => None, Some(transform) => Some(multiple_component_transform_view(transform)),
            },
            extensions: owned_extensions_view(extensions), r_siz,
            capabilities: optional_capabilities_view(capabilities),
            profile: optional_profile_number_view(profile),
            corresponding_profile: optional_profile_number_view(corresponding_profile), segments,
        }
    }

    pub(crate) closed spec fn layout_main_header_outcome(result: Result<CodestreamLayout<'_>, DecodeError>)
        -> Result<crate::specs::Part1LayoutMainFields, DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(layout) => {
                let info = layout.info;
                Ok(main_header_fields_view(&info.image_size, info.coding_style, &info.quantization,
                    &info.component_coding_styles, &info.component_quantizations, &info.roi_shifts,
                    &info.progression_changes, &info.multiple_component_transform, &info.part2_extensions,
                    info.profile.r_siz, &info.profile.extended_capabilities, &info.profile.profile,
                    &info.profile.corresponding_profile, info.main_header_segments))
            },
        }
    }

    pub closed spec fn image_size_component_infos(size: &ImageSize) -> Seq<ComponentInfo> {
        size.component_info@
    }

    pub closed spec fn image_size_component_count(size: &ImageSize) -> u16 {
        size.components
    }

    pub closed spec fn selection_geometry_view(size: &ImageSize) -> crate::specs::Part2SelectionGeometry {
        (size.width, size.height, size.x_origin, size.y_origin, size.tile_width, size.tile_height,
            size.tile_x_origin, size.tile_y_origin, size.tiles_across, size.tiles_down)
    }

    pub(crate) closed spec fn parsed_image_size_view(size: &ImageSize) -> crate::specs::Part1ParsedImageSize {
        crate::specs::Part1ParsedImageSize {
            geometry: selection_geometry_view(size), components: size.components,
            uniform_bit_depth: size.uniform_bit_depth, uniform_signed: size.uniform_signed, infos: size.component_info@,
        }
    }

    pub(crate) proof fn selection_geometry_known_fields(size: &ImageSize)
        ensures selection_geometry_view(size)
            == (size.width, size.height, size.x_origin, size.y_origin, size.tile_width, size.tile_height,
                size.tile_x_origin, size.tile_y_origin, size.tiles_across, size.tiles_down),
            image_size_component_count(size) == size.components,
    {
        reveal(selection_geometry_view);
    }

    pub closed spec fn decomposition_selector_view(style: CodingStyle) -> (u8, Seq<DecompositionDirection>) {
        (style.decomposition_levels, style.decomposition_directions@)
    }

    pub closed spec fn precinct_selector_view(style: CodingStyle) -> (u8, Seq<(u8, u8)>) {
        (style.decomposition_levels, style.precinct_exponents@)
    }

    pub(crate) proof fn resolution_selectors_known_fields(style: CodingStyle)
        ensures
            decomposition_selector_view(style) == (style.decomposition_levels, style.decomposition_directions@),
            precinct_selector_view(style) == (style.decomposition_levels, style.precinct_exponents@),
    {
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn progression_change_contains(record: ProgressionChange, layer: u16, resolution: u8, component: u16) -> bool {
        layer < record.layer_end
            && resolution >= record.resolution_start && resolution < record.resolution_end
            && component >= record.component_start && component < record.component_end
    }

    pub closed spec fn progression_changes_view(changes: &ProgressionChanges) -> Seq<ProgressionChange> {
        changes.records@
    }

    pub open spec fn parsed_progression_outcome(value: Result<ProgressionChanges, DecodeError>)
        -> Result<Seq<ProgressionChange>, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(value) => Ok(progression_changes_view(&value)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) closed spec fn parsed_coding_style_view(style: CodingStyle) -> crate::specs::Part1ParsedCodingStyle {
        crate::specs::Part1ParsedCodingStyle {
            progression_order: style.progression_order, layers: style.layers,
            multiple_component_transform: style.multiple_component_transform,
            decomposition_levels: style.decomposition_levels, decomposition_structure: style.decomposition_structure,
            decomposition_directions: style.decomposition_directions@,
            code_block_width: style.code_block_width, code_block_height: style.code_block_height,
            code_block_style: style.code_block_style, transform: style.transform,
            precincts_defined: style.precincts_defined, sop_markers: style.sop_markers, eph_markers: style.eph_markers,
            precinct_exponents: style.precinct_exponents@,
        }
    }

    closed spec fn parsed_coding_style_outcome(result: Result<CodingStyle, DecodeError>)
        -> Result<crate::specs::Part1ParsedCodingStyle, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(style) => Ok(parsed_coding_style_view(style)) }
    }

    closed spec fn parsed_component_coding_style_outcome(result: Result<(u16, CodingStyle), DecodeError>)
        -> Result<(u16, crate::specs::Part1ParsedCodingStyle), DecodeError>
    {
        match result { Err(error) => Err(error), Ok((component, style)) => Ok((component, parsed_coding_style_view(style))) }
    }

    closed spec fn component_coding_style_payload_is_bounded(result: Result<ComponentCodingStylePayload, DecodeError>) -> bool {
        match result { Err(_) => true, Ok(prepared) => prepared.length <= 43 }
    }

    closed spec fn parsed_component_coding_style_payload_outcome(result: Result<ComponentCodingStylePayload, DecodeError>)
        -> Result<crate::specs::Part1CocPrepared, DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(prepared) => Ok(crate::specs::Part1CocPrepared {
                component: prepared.component,
                payload: prepared.payload@.subrange(0, prepared.length as int),
                decomposition_structure: prepared.decomposition_structure,
            }),
        }
    }

    pub closed spec fn component_style_owner_view(styles: &ComponentCodingStyles)
        -> (u16, Seq<crate::specs::Part1ParsedCodingStyle>)
    {
        (styles.components, styles.styles@.map_values(|style: CodingStyle| parsed_coding_style_view(style)))
    }

    closed spec fn parsed_style_owner_outcome(result: Result<ComponentCodingStyles, DecodeError>)
        -> Result<(u16, Seq<crate::specs::Part1ParsedCodingStyle>), DecodeError>
    {
        match result { Err(error) => Err(error), Ok(owner) => Ok(component_style_owner_view(&owner)) }
    }

    closed spec fn parsed_quantization_owner_view(owner: &ComponentQuantizations)
        -> (u16, Seq<crate::specs::Part2Quantization>)
    {
        (owner.components, owner.quantizations@.map_values(|value: Quantization| quantization_view(&value)))
    }

    closed spec fn parsed_quantization_owner_outcome(result: Result<ComponentQuantizations, DecodeError>)
        -> Result<(u16, Seq<crate::specs::Part2Quantization>), DecodeError>
    {
        match result { Err(error) => Err(error), Ok(owner) => Ok(parsed_quantization_owner_view(&owner)) }
    }

    closed spec fn segment_slots_view(segments: Seq<Option<Segment<'_>>>)
        -> Seq<Option<crate::specs::Part1CodestreamSegment>>
    {
        segments.map_values(|value: Option<Segment<'_>>| match value {
            None => None, Some(segment) => Some(segment_view(segment)),
        })
    }

    closed spec fn optional_segment_view(segment: Option<Segment<'_>>)
        -> Option<crate::specs::Part1CodestreamSegment>
    {
        match segment { None => None, Some(segment) => Some(segment_view(segment)) }
    }

    closed spec fn tile_component_configuration_outcome(
        result: Result<(ComponentCodingStyles, Quantization, ComponentQuantizations), DecodeError>,
    ) -> Result<(
        (u16, Seq<crate::specs::Part1ParsedCodingStyle>),
        crate::specs::Part2Quantization,
        (u16, Seq<crate::specs::Part2Quantization>),
    ), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok((styles, quantization, quantizations)) => Ok((
                component_style_owner_view(&styles),
                quantization_view(&quantization),
                parsed_quantization_owner_view(&quantizations),
            )),
        }
    }

    pub closed spec fn component_coding_style_result(styles: &ComponentCodingStyles, component: u16) -> Result<CodingStyle, DecodeError> {
        if component >= styles.components {
            Err(DecodeError::MalformedInput { offset: 0, kind: MalformedKind::InvalidCodingStyle })
        } else if component as nat >= styles.styles@.len() {
            Err(DecodeError::MalformedInput { offset: 0, kind: MalformedKind::InvalidCodingStyle })
        } else { Ok(styles.styles@[component as int]) }
    }

    pub closed spec fn component_coding_style_count(styles: &ComponentCodingStyles) -> u16 {
        styles.components
    }

    pub closed spec fn coding_style_tier1_result(style: CodingStyle) -> Result<Tier1CodingStyle, DecodeError> {
        crate::specs::part1_tier1_coding_style_byte(style.code_block_style)
    }

    pub closed spec fn coding_style_packet_markers(style: &CodingStyle) -> (bool, bool) {
        (style.sop_markers, style.eph_markers)
    }

    pub proof fn coding_style_known_packet_markers(style: &CodingStyle)
        ensures coding_style_packet_markers(style) == (style.sop_markers, style.eph_markers),
    {
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn component_quantization_result(values: &ComponentQuantizations, component: u16)
        -> Result<Quantization, DecodeError>
    {
        if component >= values.components || component as nat >= values.quantizations@.len() {
            Err(DecodeError::MalformedInput { offset: 0, kind: MalformedKind::InvalidQuantization })
        } else { Ok(values.quantizations@[component as int]) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn roi_shifts_view(value: &RoiShifts) -> Seq<u8> { value.shifts@ }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn quantization_view(value: &Quantization) -> crate::specs::Part2Quantization {
        (value.style, value.guard_bits, value.step_count, value.steps@)
    }

    closed spec fn parsed_quantization_outcome(result: Result<Quantization, DecodeError>)
        -> Result<crate::specs::Part2Quantization, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(quantization_view(&value)) }
    }

    closed spec fn parsed_component_quantization_outcome(result: Result<(u16, Quantization), DecodeError>)
        -> Result<(u16, crate::specs::Part2Quantization), DecodeError>
    {
        match result { Err(error) => Err(error), Ok((component, value)) => Ok((component, quantization_view(&value))) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn raw_kernel_coefficient_view(value: KernelCoefficient) -> crate::specs::Part2RawKernelCoefficient {
        (value.bytes@, value.width)
    }

    pub open spec fn kernel_coefficient_outcome(value: Result<KernelCoefficient, DecodeError>)
        -> Result<crate::specs::Part2RawKernelCoefficient, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(value) => Ok(raw_kernel_coefficient_view(value)) }
    }

    pub open spec fn raw_kernel_coefficient_option(value: Option<KernelCoefficient>)
        -> Option<crate::specs::Part2RawKernelCoefficient>
    {
        match value {
            Some(coefficient) => Some(raw_kernel_coefficient_view(coefficient)),
            None => None,
        }
    }

    pub open spec fn raw_kernel_coefficients_view(values: Seq<KernelCoefficient>)
        -> Seq<crate::specs::Part2RawKernelCoefficient>
    {
        Seq::new(values.len(), |i: int| raw_kernel_coefficient_view(values[i]))
    }

    pub closed spec fn raw_kernel_step_view(value: KernelLiftingStep) -> crate::specs::Part2RawKernelStep {
        (value.offset, value.exponent, raw_kernel_coefficient_option(value.residue),
            raw_kernel_coefficients_view(value.coefficients@))
    }

    pub open spec fn kernel_step_outcome(value: Result<(KernelLiftingStep, usize), DecodeError>)
        -> Result<(crate::specs::Part2RawKernelStep, usize), DecodeError>
    {
        match value { Err(error) => Err(error), Ok((step, next)) => Ok((raw_kernel_step_view(step), next)) }
    }

    pub open spec fn raw_kernel_steps_view(values: Seq<KernelLiftingStep>) -> Seq<crate::specs::Part2RawKernelStep> {
        Seq::new(values.len(), |i: int| raw_kernel_step_view(values[i]))
    }

    pub closed spec fn raw_kernel_view(value: ArbitraryKernel) -> crate::specs::Part2RawKernel {
        (value.reversible, value.coefficient_type, value.whole_sample_filter, value.initial_odd,
            value.whole_sample_extension, raw_kernel_coefficient_option(value.scaling), raw_kernel_steps_view(value.steps@))
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn part2_execution_registry(extensions: &Part2Extensions) -> (Seq<u8>, Seq<u8>) {
        (Seq::new(extensions.decomposition_structures@.len(), |index: int| extensions.decomposition_structures@[index].index),
            Seq::new(extensions.arbitrary_decompositions@.len(), |index: int| extensions.arbitrary_decompositions@[index].index))
    }

    pub open spec fn component_depth_views(values: Seq<ComponentBitDepth>) -> Seq<(u8, bool)> {
        Seq::new(values.len(), |index: int| (values[index].precision, values[index].signed))
    }

    pub closed spec fn part2_component_depths(extensions: &Part2Extensions) -> Seq<(u8, bool)> {
        component_depth_views(extensions.component_bit_depths@)
    }

    pub closed spec fn part2_kernel_registry(extensions: &Part2Extensions) -> Seq<(u8, crate::specs::Part2RawKernel)> {
        Seq::new(extensions.arbitrary_kernels@.len(), |index: int|
            (extensions.arbitrary_kernels@[index].index, raw_kernel_view(extensions.arbitrary_kernels@[index])))
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn extended_capabilities_view(value: &ExtendedCapabilities) -> (u32, Seq<u16>) {
        (value.p_cap, value.c_capabilities@)
    }

    pub closed spec fn profile_number_view(value: &ProfileNumber) -> Seq<u16> {
        value.words@
    }

    pub open spec fn cap_payload_outcome(value: Result<ExtendedCapabilities, DecodeError>)
        -> Result<(u32, Seq<u16>), DecodeError>
    {
        match value { Err(error) => Err(error), Ok(capabilities) => Ok(extended_capabilities_view(&capabilities)) }
    }

    pub open spec fn profile_number_outcome(value: Result<ProfileNumber, DecodeError>)
        -> Result<Seq<u16>, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(profile) => Ok(profile_number_view(&profile)) }
    }

    pub open spec fn marker_words_outcome(value: Result<Vec<u16>, DecodeError>)
        -> Result<Seq<u16>, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(words) => Ok(words@) }
    }

    pub closed spec fn codestream_profile_capabilities(value: &CodestreamProfile) -> Option<(u32, Seq<u16>)> {
        match value.extended_capabilities { None => None, Some(capabilities) => Some(extended_capabilities_view(&capabilities)) }
    }

    pub(crate) closed spec fn optional_capabilities_view(value: &Option<ExtendedCapabilities>)
        -> Option<(u32, Seq<u16>)>
    {
        match value { None => None, Some(caps) => Some(extended_capabilities_view(caps)) }
    }

    pub(crate) closed spec fn optional_profile_number_view(value: &Option<ProfileNumber>) -> Option<Seq<u16>> {
        match value { None => None, Some(number) => Some(profile_number_view(number)) }
    }

    pub(crate) closed spec fn profile_tile_inputs_view(values: Seq<TilePartPayload<'_>>)
        -> Seq<crate::specs::Part1ProfileTile>
    {
        values.map_values(|value: TilePartPayload<'_>| crate::specs::Part1ProfileTile {
            styles: component_style_owner_view(&value.component_coding_styles),
            roi: roi_shifts_view(&value.roi_shifts), has_roi: value.has_roi_marker,
            has_functional: value.has_functional_header_marker,
        })
    }

    pub(crate) closed spec fn complete_codestream_profile_view(value: &CodestreamProfile)
        -> crate::specs::Part1ProfileMetadata
    {
        (value.r_siz, value.block_coding, optional_capabilities_view(&value.extended_capabilities),
         optional_profile_number_view(&value.profile), optional_profile_number_view(&value.corresponding_profile))
    }

    pub(crate) closed spec fn complete_codestream_profile_outcome(value: Result<CodestreamProfile, DecodeError>)
        -> Result<crate::specs::Part1ProfileMetadata, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(profile) => Ok(complete_codestream_profile_view(&profile)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) proof fn mct_fixed_precision_is_q32()
        ensures MCT_FIXED_BITS == 32,
    {
    }

    pub closed spec fn mct_array_view(array: &MctArray) -> crate::specs::Part2MctArray {
        (array.index, array.kind, array.numeric_format, array.fraction_bits, array.values@)
    }

    closed spec fn mct_array_outcome(value: Result<MctArray, DecodeError>) -> Result<crate::specs::Part2MctArray, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(mct_array_view(&value)) }
    }

    closed spec fn mct_arrays_view(values: Seq<MctArray>) -> Seq<crate::specs::Part2MctArray> {
        values.map_values(|value: MctArray| mct_array_view(&value))
    }

    pub closed spec fn mct_record_view(value: &MctRecord) -> crate::specs::Part1MctRecord {
        (value.index, mcc_collection_references_view(value.collections@))
    }

    closed spec fn mct_records_view(values: Seq<MctRecord>) -> Seq<crate::specs::Part1MctRecord> {
        values.map_values(|value: MctRecord| mct_record_view(&value))
    }

    closed spec fn mct_array_reference_outcome(value: Result<&MctArray, DecodeError>)
        -> Result<crate::specs::Part2MctArray, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(array) => Ok(mct_array_view(array)) }
    }

    closed spec fn mct_parameters_view(value: &MctParameters) -> crate::specs::Part1MctParameters {
        crate::specs::Part1MctParameters {
            arrays: mct_arrays_view(value.arrays@), records: mct_records_view(value.records@), order: value.order@,
        }
    }

    pub closed spec fn mct_parameter_copy_view(value: &MctParameters)
        -> (Seq<crate::specs::Part2MctArray>, Seq<crate::specs::Part1MctRecord>, Seq<u8>)
    {
        let complete = mct_parameters_view(value);
        (complete.arrays, complete.records, complete.order)
    }

    closed spec fn mct_collections_view(values: Seq<MctCollection>) -> Seq<crate::specs::Part2MctCollection> {
        values.map_values(|value: MctCollection| mct_collection_view(&value))
    }

    closed spec fn mct_stages_view(values: Seq<MctStage>) -> Seq<crate::specs::Part2MctStage> {
        values.map_values(|value: MctStage| mct_stage_view(&value))
    }

    closed spec fn mct_collection_outcome(value: Result<MctCollection, DecodeError>)
        -> Result<crate::specs::Part2MctCollection, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(collection) => Ok(mct_collection_view(&collection)) }
    }

    closed spec fn mct_stage_outcome(value: Result<MctStage, DecodeError>)
        -> Result<crate::specs::Part2MctStage, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(stage) => Ok(mct_stage_view(&stage)) }
    }

    closed spec fn mct_graph_outcome(value: Result<Option<MultipleComponentTransform>, DecodeError>)
        -> Result<Option<Seq<crate::specs::Part2MctStage>>, DecodeError>
    {
        match value {
            Err(error) => Err(error), Ok(None) => Ok(None),
            Ok(Some(graph)) => Ok(Some(multiple_component_transform_view(&graph))),
        }
    }

    pub open spec fn mct_array_option(value: Option<&MctArray>) -> Option<crate::specs::Part2MctArray> {
        match value { None => None, Some(array) => Some(mct_array_view(array)) }
    }

    pub closed spec fn mct_wavelet_view(wavelet: MctWavelet) -> crate::specs::Part2MctWavelet {
        (wavelet.transform, wavelet.levels, wavelet.component_offset)
    }

    pub open spec fn mct_wavelet_option(value: Option<MctWavelet>) -> Option<crate::specs::Part2MctWavelet> {
        match value { None => None, Some(wavelet) => Some(mct_wavelet_view(wavelet)) }
    }

    pub closed spec fn mct_collection_view(collection: &MctCollection) -> crate::specs::Part2MctCollection {
        (collection.reversible, collection.input_components@, collection.output_components@, collection.kind,
            match collection.matrix { None => None, Some(array) => Some(mct_array_view(&array)) },
            match collection.offsets { None => None, Some(array) => Some(mct_array_view(&array)) },
            mct_wavelet_option(collection.wavelet))
    }

    pub closed spec fn mct_stage_view(stage: &MctStage) -> crate::specs::Part2MctStage {
        (stage.index, Seq::new(stage.collections@.len(), |index: int| mct_collection_view(&stage.collections@[index])))
    }

    pub closed spec fn multiple_component_transform_view(transform: &MultipleComponentTransform) -> Seq<crate::specs::Part2MctStage> {
        Seq::new(transform.stages@.len(), |index: int| mct_stage_view(&transform.stages@[index]))
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn packed_packet_headers_view(headers: &PackedPacketHeaders) -> crate::specs::Part1PackedHeaders {
        crate::specs::Part1PackedHeaders {
            source: match headers.source {
                PackedPacketHeaderSource::None => crate::specs::Part1PackedHeaderSource::None,
                PackedPacketHeaderSource::MarkerSegments { header, marker, logical_start } =>
                    crate::specs::Part1PackedHeaderSource::MarkerSegments { header: header@, marker, logical_start },
            },
            length: headers.length, fragments: headers.fragments,
        }
    }

    closed spec fn tile_part_main_metadata_outcome(
        result: Result<(PacketLengths<'_>, PackedPacketHeaders<'_>), DecodeError>,
    ) -> Result<(crate::specs::Part1PacketLengths, crate::specs::Part1PackedHeaders), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok((lengths, headers)) => Ok((packet_lengths_view(&lengths), packed_packet_headers_view(&headers))),
        }
    }

    pub open spec fn packed_header_reassembly_outcome(result: Result<Vec<u8>, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match result { Ok(bytes) => Ok(bytes@), Err(error) => Err(error) }
    }

    pub closed spec fn packed_packet_headers_present(headers: &PackedPacketHeaders) -> bool {
        !matches!(headers.source, PackedPacketHeaderSource::None)
    }

    closed spec fn packed_packet_headers_outcome(result: Result<PackedPacketHeaders, DecodeError>)
        -> Result<crate::specs::Part1PackedHeaders, DecodeError>
    {
        match result { Ok(headers) => Ok(packed_packet_headers_view(&headers)), Err(error) => Err(error) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn packet_length_source_view(source: PacketLengthSource<'_>) -> crate::specs::Part1PacketLengthSource {
        match source {
            PacketLengthSource::None => crate::specs::Part1PacketLengthSource::None,
            PacketLengthSource::Plm(bytes) => crate::specs::Part1PacketLengthSource::Plm(bytes@),
            PacketLengthSource::Plt(header) => crate::specs::Part1PacketLengthSource::Plt(header@),
        }
    }

    pub closed spec fn packet_lengths_view(lengths: &PacketLengths) -> crate::specs::Part1PacketLengths {
        crate::specs::Part1PacketLengths {
            source: packet_length_source_view(lengths.source), packet_count: lengths.packet_count, encoded_bytes: lengths.encoded_bytes,
        }
    }

    closed spec fn packet_length_groups_view(groups: Seq<PacketLengths>) -> Seq<crate::specs::Part1PacketLengths> {
        groups.map(|_i: int, group: PacketLengths| packet_lengths_view(&group))
    }

    closed spec fn packet_lengths_outcome(result: Result<PacketLengths, DecodeError>)
        -> Result<crate::specs::Part1PacketLengths, DecodeError>
    {
        match result { Ok(lengths) => Ok(packet_lengths_view(&lengths)), Err(error) => Err(error) }
    }

    pub closed spec fn packet_length_iter_view(iter: &PacketLengthIter) -> crate::specs::Part1PacketLengthIter {
        crate::specs::Part1PacketLengthIter {
            source: packet_length_source_view(iter.source), position: iter.position, segment_end: iter.segment_end,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn mcc_reference_transform_view(value: MctCollectionReferenceTransform) -> crate::specs::Part1MccTransformReference {
        match value {
            MctCollectionReferenceTransform::Array { kind, reversible, transform_index, offset_index } =>
                crate::specs::Part1MccTransformReference::Array { kind, reversible, transform_index, offset_index },
            MctCollectionReferenceTransform::Wavelet(wavelet) =>
                crate::specs::Part1MccTransformReference::Wavelet(mct_wavelet_view(wavelet)),
        }
    }

    pub closed spec fn mcc_collection_reference_view(value: &MctCollectionReference) -> crate::specs::Part1MccCollectionReference {
        crate::specs::Part1MccCollectionReference {
            inputs: value.input_components@, outputs: value.output_components@, transform: mcc_reference_transform_view(value.transform),
        }
    }

    closed spec fn mcc_collection_references_view(values: Seq<MctCollectionReference>) -> Seq<crate::specs::Part1MccCollectionReference> {
        values.map_values(|value: MctCollectionReference| mcc_collection_reference_view(&value))
    }

    closed spec fn mcc_collection_outcome(value: Result<(MctCollectionReference, usize), DecodeError>)
        -> Result<(crate::specs::Part1MccCollectionReference, usize), DecodeError>
    {
        match value { Err(error) => Err(error), Ok((collection, next)) => Ok((mcc_collection_reference_view(&collection), next)) }
    }

    closed spec fn mcc_record_outcome(value: Result<MctRecord, DecodeError>)
        -> Result<(u8, Seq<crate::specs::Part1MccCollectionReference>), DecodeError>
    {
        match value { Err(error) => Err(error), Ok(record) => Ok((record.index, mcc_collection_references_view(record.collections@))) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn mct_fragment_view(value: &MctFragment) -> crate::specs::Part1MctFragment {
        crate::specs::Part1MctFragment { descriptor: value.descriptor, next_index: value.next_index,
            final_index: value.final_index, offset: value.offset, data: value.data@ }
    }

    closed spec fn mct_pending_view(values: Seq<MctFragment>) -> Seq<crate::specs::Part1MctFragment> {
        values.map_values(|value: MctFragment| mct_fragment_view(&value))
    }

    closed spec fn mct_fragment_outcome(value: Result<Option<MctArray>, DecodeError>)
        -> Result<Option<crate::specs::Part2MctArray>, DecodeError>
    {
        match value {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(array)) => Ok(Some(mct_array_view(&array))),
        }
    }

    closed spec fn mcc_fragment_view(value: &MccFragment) -> crate::specs::Part1MccFragment {
        crate::specs::Part1MccFragment { record_index: value.record_index, next_index: value.next_index,
            final_index: value.final_index, collection_count: value.collection_count, offset: value.offset, data: value.data@ }
    }

    closed spec fn mcc_pending_view(values: Seq<MccFragment>) -> Seq<crate::specs::Part1MccFragment> {
        values.map_values(|value: MccFragment| mcc_fragment_view(&value))
    }

    closed spec fn mcc_fragment_outcome(value: Result<Option<MctRecord>, DecodeError>)
        -> Result<Option<(u8, Seq<crate::specs::Part1MccCollectionReference>)>, DecodeError>
    {
        match value {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(record)) => Ok(Some((record.index, mcc_collection_references_view(record.collections@)))),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn packed_header_frames_view(values: Seq<PackedHeaderFrame>) -> Seq<(usize, usize)> {
        values.map_values(|value: PackedHeaderFrame| (value.start, value.length))
    }

    closed spec fn packed_header_frames_outcome(value: Result<Vec<PackedHeaderFrame>, DecodeError>)
        -> Result<Seq<(usize, usize)>, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(frames) => Ok(packed_header_frames_view(frames@)) }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn quantization_owner_view(value: &ComponentQuantizations) -> (u16, Seq<Quantization>) {
        (value.components, value.quantizations@)
    }

    pub closed spec fn owned_decomposition_view(value: &DecompositionStructure) -> (u8, Seq<DecompositionDirection>) {
        (value.index, value.directions@)
    }

    closed spec fn dfs_payload_outcome(result: Result<DecompositionStructure, DecodeError>)
        -> Result<(u8, Seq<DecompositionDirection>), DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(owned_decomposition_view(&value)) }
    }

    pub closed spec fn owned_arbitrary_decomposition_view(value: &ArbitraryDecomposition) -> (u8, Seq<u8>, Seq<DecompositionDirection>) {
        (value.index, value.sublevel_depths@, value.subband_splits@)
    }

    pub closed spec fn dfs_option_view(value: Option<&DecompositionStructure>)
        -> Option<(u8, Seq<DecompositionDirection>)>
    {
        match value { None => None, Some(value) => Some(owned_decomposition_view(value)) }
    }

    pub closed spec fn ads_option_view(value: Option<&ArbitraryDecomposition>)
        -> Option<(u8, Seq<u8>, Seq<DecompositionDirection>)>
    {
        match value { None => None, Some(value) => Some(owned_arbitrary_decomposition_view(value)) }
    }

    closed spec fn ads_payload_outcome(result: Result<ArbitraryDecomposition, DecodeError>)
        -> Result<(u8, Seq<u8>, Seq<DecompositionDirection>), DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(owned_arbitrary_decomposition_view(&value)) }
    }

    closed spec fn two_bit_values_outcome(result: Result<Vec<u8>, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match result { Err(error) => Err(error), Ok(values) => Ok(values@) }
    }

    pub closed spec fn owned_nonlinear_view(value: &NonlinearPointTransform) -> crate::specs::Part2OwnedNonlinear {
        crate::specs::Part2OwnedNonlinear {
            component: value.component, precision: value.precision, signed: value.signed, transform_type: value.transform_type,
            parameters: value.parameters@, d_min: value.d_min, d_max: value.d_max, point_bits: value.point_bits,
            points: value.points@, gamma: value.gamma_parameters,
        }
    }

    pub open spec fn nonlinear_transform_option_view(value: Option<&NonlinearPointTransform>)
        -> Option<crate::specs::Part2OwnedNonlinear>
    {
        match value { None => None, Some(value) => Some(owned_nonlinear_view(value)) }
    }

    pub open spec fn nlt_payload_outcome(value: Result<NonlinearPointTransform, DecodeError>)
        -> Result<crate::specs::Part2OwnedNonlinear, DecodeError>
    {
        match value { Err(error) => Err(error), Ok(value) => Ok(owned_nonlinear_view(&value)) }
    }

    pub open spec fn segment_tail_outcome(value: Result<Vec<u8>, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(value@) }
    }

    pub closed spec fn owned_kernel_view(value: &ArbitraryKernel) -> (u8, u16, crate::specs::Part2RawKernel) {
        (value.index, value.descriptor, raw_kernel_view(*value))
    }

    pub open spec fn atk_payload_outcome(value: Result<ArbitraryKernel, DecodeError>)
        -> Result<(u8, u16, crate::specs::Part2RawKernel), DecodeError>
    {
        match value { Err(error) => Err(error), Ok(value) => Ok(owned_kernel_view(&value)) }
    }

    pub closed spec fn owned_extensions_view(value: &Part2Extensions) -> crate::specs::Part2OwnedExtensions {
        crate::specs::Part2OwnedExtensions {
            decompositions: value.decomposition_structures@.map_values(|entry: DecompositionStructure| owned_decomposition_view(&entry)),
            arbitrary: value.arbitrary_decompositions@.map_values(|entry: ArbitraryDecomposition| owned_arbitrary_decomposition_view(&entry)),
            nonlinear: value.nonlinear_transforms@.map_values(|entry: NonlinearPointTransform| owned_nonlinear_view(&entry)),
            depths: value.component_bit_depths@,
            kernels: value.arbitrary_kernels@.map_values(|entry: ArbitraryKernel| owned_kernel_view(&entry)),
            registrations: value.component_registrations@, lengths: value.tile_part_lengths@, metadata_bytes: value.metadata_bytes,
        }
    }

    pub open spec fn tile_part_owned_view(value: &TilePartPayload<'_>) -> crate::specs::Part2OwnedTilePart {
        crate::specs::Part2OwnedTilePart {
            tile_index: value.tile_index, tile_part_index: value.tile_part_index, tile_part_count: value.tile_part_count,
            coding_style: value.coding_style, quantization: value.quantization, component_coding_styles: value.component_coding_styles,
            component_quantizations: quantization_owner_view(&value.component_quantizations), roi_shifts: value.roi_shifts,
            progression_changes: progression_changes_view(&value.progression_changes),
            multiple_component_transform: match value.multiple_component_transform { None => None, Some(transform) => Some(multiple_component_transform_view(&transform)) },
            part2_extensions: owned_extensions_view(&value.part2_extensions), packet_lengths: packet_lengths_view(&value.packet_lengths),
            packed_packet_headers: packed_packet_headers_view(&value.packed_packet_headers),
            has_functional_header_marker: value.has_functional_header_marker, has_roi_marker: value.has_roi_marker, data: value.data@,
        }
    }

    pub open spec fn tile_parts_owned_view(values: Seq<TilePartPayload<'_>>) -> Seq<crate::specs::Part2OwnedTilePart> {
        values.map_values(|value: TilePartPayload| tile_part_owned_view(&value))
    }

    pub proof fn tile_part_owned_tile_known(value: &TilePartPayload<'_>)
        ensures tile_part_owned_view(value).tile_index == value.tile_index,
    {
        reveal(tile_part_owned_view);
    }

    pub proof fn packed_header_presence_matches_view(value: &PackedPacketHeaders<'_>)
        ensures packed_packet_headers_present(value)
            == !matches!(packed_packet_headers_view(value).source, crate::specs::Part1PackedHeaderSource::None),
    {
        reveal(packed_packet_headers_present);
        reveal(packed_packet_headers_view);
    }

    pub proof fn owned_extensions_registry_known(value: &Part2Extensions)
        ensures crate::specs::part2_owned_kernel_registry(owned_extensions_view(value)) == part2_kernel_registry(value),
    {
        reveal(owned_extensions_view);
        reveal(owned_kernel_view);
        reveal(part2_kernel_registry);
        assert(crate::specs::part2_owned_kernel_registry(owned_extensions_view(value)) =~= part2_kernel_registry(value));
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn parser_view<'a>(parser: &Parser<'a>) -> crate::specs::Part1CodestreamReader<'a> {
        crate::specs::Part1CodestreamReader {
            input: parser.input@, limits: parser.limits, position: parser.position,
            work_units: parser.work_units, packet_length_bytes: parser.packet_length_bytes, packet_lengths: parser.packet_lengths,
        }
    }

    closed spec fn parser_initial_outcome<'a>(result: Result<Parser<'a>, DecodeError>)
        -> Result<crate::specs::Part1CodestreamReader<'a>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(parser) => Ok(parser_view(&parser)) }
    }

    closed spec fn tile_data_window_outcome(result: Result<(usize, &[u8]), DecodeError>)
        -> Result<(usize, Seq<u8>), DecodeError>
    {
        match result { Err(error) => Err(error), Ok((end, data)) => Ok((end, data@)) }
    }

    closed spec fn segment_view(segment: Segment<'_>) -> crate::specs::Part1CodestreamSegment {
        crate::specs::Part1CodestreamSegment { marker: segment.marker, offset: segment.offset, payload: segment.payload@ }
    }

    closed spec fn segment_outcome(result: Result<Segment<'_>, DecodeError>)
        -> Result<crate::specs::Part1CodestreamSegment, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(segment) => Ok(segment_view(segment)) }
    }

    closed spec fn main_header_segment_outcome(result: Result<Option<Segment<'_>>, DecodeError>)
        -> Result<Option<crate::specs::Part1CodestreamSegment>, DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(segment)) => Ok(Some(segment_view(segment))),
        }
    }

    closed spec fn tile_part_header_view(value: TilePart) -> (usize, u32, u16, u8, u8) {
        (value.start, value.length, value.tile_index, value.tile_part_index, value.tile_part_count)
    }

    closed spec fn tile_part_header_outcome(result: Result<TilePart, DecodeError>)
        -> Result<(usize, u32, u16, u8, u8), DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(tile_part_header_view(value)) }
    }

    closed spec fn parsed_siz_outcome(result: Result<(ImageSize, u16), DecodeError>)
        -> Result<(crate::specs::Part1ParsedImageSize, u16), DecodeError>
    {
        match result { Err(error) => Err(error), Ok((size, r_siz)) => Ok((parsed_image_size_view(&size), r_siz)) }
    }

    closed spec fn layout_prologue_outcome(result: Result<(ImageSize, u16, usize), DecodeError>)
        -> Result<(crate::specs::Part1ParsedImageSize, u16, usize), DecodeError>
    {
        match result {
            Err(error) => Err(error),
            Ok((size, r_siz, start)) => Ok((parsed_image_size_view(&size), r_siz, start)),
        }
    }

    closed spec fn siz_components_view(
        infos: Seq<ComponentInfo>, offset: usize, component: u16, first_precision: u8, first_signed: bool, uniform: bool,
    ) -> crate::specs::Part1SizComponents {
        crate::specs::Part1SizComponents { infos, offset, component, first_precision, first_signed, uniform }
    }
}
