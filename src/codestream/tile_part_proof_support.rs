#[cfg(verus_keep_ghost)]
verus! {
    // The existing POC model takes a native owner. This inverse preserves its
    // complete projection, including the logical count and every physical tail.
    pub(crate) closed spec fn tile_part_native_styles(raw: (u16, Seq<crate::specs::Part1ParsedCodingStyle>))
        -> ComponentCodingStyles
    {
        choose|owner: ComponentCodingStyles| component_style_owner_view(&owner) == raw
    }

    proof fn tile_part_native_styles_inverse(owner: &ComponentCodingStyles)
        ensures tile_part_native_styles(component_style_owner_view(owner)) == *owner,
    {
        reveal(tile_part_native_styles);
        reveal(component_style_owner_view);
        reveal(parsed_coding_style_view);
        let recovered = tile_part_native_styles(component_style_owner_view(owner));
        assert(exists|value: ComponentCodingStyles| component_style_owner_view(&value) == component_style_owner_view(owner));
        assert(component_style_owner_view(&recovered) == component_style_owner_view(owner));
        assert(recovered.components == owner.components);
        assert(recovered.styles@.map_values(|style: CodingStyle| parsed_coding_style_view(style))
            == owner.styles@.map_values(|style: CodingStyle| parsed_coding_style_view(style)));
        let left = recovered.styles@.map_values(|style: CodingStyle| parsed_coding_style_view(style));
        let right = owner.styles@.map_values(|style: CodingStyle| parsed_coding_style_view(style));
        assert forall|index: int| 0 <= index < owner.styles@.len()
            implies recovered.styles@[index] == owner.styles@[index] by {
            assert(left[index] == right[index]);
            assert(left[index] == parsed_coding_style_view(recovered.styles@[index]));
            assert(right[index] == parsed_coding_style_view(owner.styles@[index]));
            assert(parsed_coding_style_view(recovered.styles@[index]) == parsed_coding_style_view(owner.styles@[index]));
            assert(recovered.styles@[index].decomposition_directions@ == owner.styles@[index].decomposition_directions@);
            assert(recovered.styles@[index].precinct_exponents@ == owner.styles@[index].precinct_exponents@);
            assert(recovered.styles@[index].decomposition_directions == owner.styles@[index].decomposition_directions);
            assert(recovered.styles@[index].precinct_exponents == owner.styles@[index].precinct_exponents);
        }
        assert(recovered.styles@ =~= owner.styles@);
        assert(recovered.styles == owner.styles);
    }

    pub(crate) closed spec fn tile_part_payload_view(value: &TilePartPayload<'_>)
        -> crate::specs::Part1TilePartPayload
    {
        crate::specs::Part1TilePartPayload {
            tile_index: value.tile_index, tile_part_index: value.tile_part_index, tile_part_count: value.tile_part_count,
            coding_style: parsed_coding_style_view(value.coding_style), quantization: quantization_view(&value.quantization),
            component_coding_styles: component_style_owner_view(&value.component_coding_styles),
            component_quantizations: parsed_quantization_owner_view(&value.component_quantizations),
            roi_shifts: roi_shifts_view(&value.roi_shifts),
            progression_changes: progression_changes_view(&value.progression_changes),
            multiple_component_transform: match value.multiple_component_transform {
                None => None, Some(transform) => Some(multiple_component_transform_view(&transform)),
            },
            part2_extensions: owned_extensions_view(&value.part2_extensions),
            packet_lengths: packet_lengths_view(&value.packet_lengths),
            packed_packet_headers: packed_packet_headers_view(&value.packed_packet_headers),
            has_functional_header_marker: value.has_functional_header_marker,
            has_roi_marker: value.has_roi_marker, data: value.data@,
        }
    }

    closed spec fn tile_part_read_outcome(
        result: Result<(TilePartPayload<'_>, MctParameters, Part2Extensions), DecodeError>,
    ) -> crate::specs::Part1TilePartResult {
        match result {
            Err(error) => Err(error),
            Ok((payload, parameters, extensions)) => Ok((
                tile_part_payload_view(&payload), mct_parameters_view(&parameters), owned_extensions_view(&extensions),
            )),
        }
    }
}
