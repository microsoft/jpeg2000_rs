#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) proof fn decoder_layout_errors_known()
        ensures forall|error: DecodeError|
            #[trigger] complete_layout_outcome(Err(error)) == Err(error),
    {
        reveal(complete_layout_outcome);
    }

    pub(crate) closed spec fn decoder_native_size(raw: crate::specs::Part1ParsedImageSize) -> ImageSize {
        choose|value: ImageSize| parsed_image_size_view(&value) == raw
    }

    pub(crate) proof fn decoder_native_size_inverse(value: &ImageSize)
        ensures decoder_native_size(parsed_image_size_view(value)) == *value,
    {
        reveal(decoder_native_size);
        reveal(parsed_image_size_view);
        reveal(selection_geometry_view);
        let recovered = decoder_native_size(parsed_image_size_view(value));
        assert(exists|owner: ImageSize| parsed_image_size_view(&owner) == parsed_image_size_view(value));
        assert(parsed_image_size_view(&recovered) == parsed_image_size_view(value));
        assert(recovered.component_info@ == value.component_info@);
        assert(recovered.component_info == value.component_info);
    }

    pub(crate) closed spec fn decoder_native_style(raw: crate::specs::Part1ParsedCodingStyle) -> CodingStyle {
        choose|value: CodingStyle| parsed_coding_style_view(value) == raw
    }

    pub(crate) proof fn decoder_native_style_inverse(value: CodingStyle)
        ensures decoder_native_style(parsed_coding_style_view(value)) == value,
    {
        reveal(decoder_native_style);
        reveal(parsed_coding_style_view);
        let recovered = decoder_native_style(parsed_coding_style_view(value));
        assert(exists|owner: CodingStyle| parsed_coding_style_view(owner) == parsed_coding_style_view(value));
        assert(parsed_coding_style_view(recovered) == parsed_coding_style_view(value));
        assert(recovered.decomposition_directions@ == value.decomposition_directions@);
        assert(recovered.precinct_exponents@ == value.precinct_exponents@);
        assert(recovered.decomposition_directions == value.decomposition_directions);
        assert(recovered.precinct_exponents == value.precinct_exponents);
    }

    pub(crate) closed spec fn decoder_native_quantization(raw: crate::specs::Part2Quantization) -> Quantization {
        choose|value: Quantization| quantization_view(&value) == raw
    }

    pub(crate) proof fn decoder_native_quantization_inverse(value: Quantization)
        ensures decoder_native_quantization(quantization_view(&value)) == value,
    {
        reveal(decoder_native_quantization);
        reveal(quantization_view);
        let recovered = decoder_native_quantization(quantization_view(&value));
        assert(exists|owner: Quantization| quantization_view(&owner) == quantization_view(&value));
        assert(quantization_view(&recovered) == quantization_view(&value));
        assert(recovered.steps@ == value.steps@);
        assert(recovered.steps == value.steps);
    }

    pub(crate) closed spec fn decoder_native_roi(raw: Seq<u8>) -> RoiShifts {
        choose|value: RoiShifts| roi_shifts_view(&value) == raw
    }

    pub(crate) proof fn decoder_native_roi_inverse(value: RoiShifts)
        ensures decoder_native_roi(roi_shifts_view(&value)) == value,
    {
        reveal(decoder_native_roi);
        reveal(roi_shifts_view);
        let recovered = decoder_native_roi(roi_shifts_view(&value));
        assert(exists|owner: RoiShifts| roi_shifts_view(&owner) == roi_shifts_view(&value));
        assert(roi_shifts_view(&recovered) == roi_shifts_view(&value));
        assert(recovered.shifts@ == value.shifts@);
        assert(recovered.shifts == value.shifts);
    }

    pub(crate) proof fn decoder_native_component_styles_inverse(value: &ComponentCodingStyles)
        ensures tile_part_native_styles(component_style_owner_view(value)) == *value,
    {
        tile_part_native_styles_inverse(value);
    }

    pub(crate) closed spec fn decoder_layout_input_view(layout: &CodestreamLayout<'_>)
        -> crate::specs::Part2DecoderLayoutInput
    {
        crate::specs::Part2DecoderLayoutInput {
            size: layout.info.image_size,
            main_execution: (
                layout.info.component_coding_styles,
                part2_execution_registry(&layout.info.part2_extensions),
                part2_kernel_registry(&layout.info.part2_extensions),
                part2_component_depths(&layout.info.part2_extensions),
            ),
            main_extensions: owned_extensions_view(&layout.info.part2_extensions),
            parts: tile_parts_owned_view(layout.tile_parts@),
            capabilities: codestream_profile_capabilities(&layout.info.profile),
        }
    }

    pub(crate) proof fn decoder_layout_input_fields(layout: &CodestreamLayout<'_>)
        ensures decoder_layout_input_view(layout).size == layout.info.image_size,
            decoder_layout_input_view(layout).main_execution == (
                layout.info.component_coding_styles,
                part2_execution_registry(&layout.info.part2_extensions),
                part2_kernel_registry(&layout.info.part2_extensions),
                part2_component_depths(&layout.info.part2_extensions)),
            decoder_layout_input_view(layout).main_extensions == owned_extensions_view(&layout.info.part2_extensions),
            decoder_layout_input_view(layout).parts == tile_parts_owned_view(layout.tile_parts@),
            decoder_layout_input_view(layout).capabilities == codestream_profile_capabilities(&layout.info.profile),
    {
        reveal(decoder_layout_input_view);
    }

    pub(crate) proof fn decoder_execution_header_fields(styles: ComponentCodingStyles, extensions: &Part2Extensions)
        ensures crate::specs::part2_decoder_execution_header(styles, owned_extensions_view(extensions))
            == (styles, part2_execution_registry(extensions), part2_kernel_registry(extensions), part2_component_depths(extensions)),
    {
        reveal(owned_extensions_view);
        reveal(part2_execution_registry);
        reveal(part2_component_depths);
        reveal(owned_decomposition_view);
        reveal(owned_arbitrary_decomposition_view);
        owned_extensions_registry_known(extensions);
        let projected = crate::specs::part2_decoder_execution_header(styles, owned_extensions_view(extensions));
        assert(projected.1.0 =~= part2_execution_registry(extensions).0);
        assert(projected.1.1 =~= part2_execution_registry(extensions).1);
        assert(projected.3 =~= part2_component_depths(extensions));
    }

    pub(crate) proof fn decoder_tile_input_matches_raw(part: &TilePartPayload<'_>)
        ensures crate::specs::part2_decoder_tile_from_raw(tile_part_payload_view(part)) == tile_part_owned_view(part),
    {
        reveal(tile_part_payload_view);
        reveal(parsed_quantization_owner_view);
        reveal(quantization_owner_view);
        decoder_native_style_inverse(part.coding_style);
        decoder_native_quantization_inverse(part.quantization);
        decoder_native_component_styles_inverse(&part.component_coding_styles);
        decoder_native_roi_inverse(part.roi_shifts);
        let raw = tile_part_payload_view(part);
        let projected = crate::specs::part2_decoder_tile_from_raw(raw);
        assert forall|index: int| 0 <= index < part.component_quantizations.quantizations@.len()
            implies projected.component_quantizations.1[index]
                == #[trigger] part.component_quantizations.quantizations@[index] by {
            decoder_native_quantization_inverse(part.component_quantizations.quantizations@[index]);
        }
        assert(projected.component_quantizations.1 =~= part.component_quantizations.quantizations@);
    }

    pub(crate) proof fn decoder_layout_input_matches_raw(layout: &CodestreamLayout<'_>)
        ensures match complete_layout_outcome(Ok(*layout)) {
            Err(_) => false,
            Ok(raw) => crate::specs::part2_decoder_input_from_raw(raw) == decoder_layout_input_view(layout),
        },
    {
        reveal(complete_layout_outcome);
        reveal(complete_codestream_info_view);
        reveal(main_header_fields_view);
        reveal(decoder_layout_input_view);
        reveal(complete_codestream_profile_view);
        reveal(codestream_profile_capabilities);
        decoder_native_size_inverse(&layout.info.image_size);
        decoder_native_component_styles_inverse(&layout.info.component_coding_styles);
        decoder_execution_header_fields(layout.info.component_coding_styles, &layout.info.part2_extensions);
        let raw_parts = layout.tile_parts@.map_values(|part: TilePartPayload<'_>| tile_part_payload_view(&part));
        let recovered = raw_parts.map_values(|part: crate::specs::Part1TilePartPayload| crate::specs::part2_decoder_tile_from_raw(part));
        assert forall|index: int| 0 <= index < layout.tile_parts.len()
            implies #[trigger] recovered[index] == tile_part_owned_view(&layout.tile_parts@[index]) by {
            decoder_tile_input_matches_raw(&layout.tile_parts@[index]);
        }
        assert(recovered =~= tile_parts_owned_view(layout.tile_parts@));
    }
}
