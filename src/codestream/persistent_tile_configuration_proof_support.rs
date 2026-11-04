#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) closed spec fn persistent_tile_selection_view(
        roi: &[Option<RoiShifts>], styles: &[Option<CodingStyle>],
        quantizations: &[Option<Quantization>], style_parts: &[Option<usize>],
        payloads: &[TilePartPayload<'_>],
    ) -> crate::specs::Part1PersistentTileSelection {
        (
            roi@.map_values(|value: Option<RoiShifts>| optional_roi_shifts_view(value)),
            styles@.map_values(|value: Option<CodingStyle>| match value {
                None => None, Some(style) => Some(parsed_coding_style_view(style)),
            }),
            quantizations@.map_values(|value: Option<Quantization>| match value {
                None => None, Some(quantization) => Some(quantization_view(&quantization)),
            }),
            style_parts@,
            payloads@.map_values(|value: TilePartPayload<'_>| tile_part_payload_view(&value)),
        )
    }

    pub(crate) closed spec fn inherited_tile_configuration_outcome(
        result: Result<persistent_tile_configuration::InheritedTileConfiguration, DecodeError>,
    ) -> Result<crate::specs::Part1InheritedTileConfiguration, DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok((previous, roi, style, quantization, components)) => Ok((
                optional_roi_shifts_view(previous), roi_shifts_view(&roi),
                parsed_coding_style_view(style), quantization_view(&quantization),
                component_style_owner_view(&components),
            )),
        }
    }

    pub(crate) closed spec fn persistent_tile_configuration_view(
        roi: &[Option<RoiShifts>], styles: &[Option<CodingStyle>],
        quantizations: &[Option<Quantization>], style_parts: &[Option<usize>],
        component_quantizations: &[Option<ComponentQuantizations>],
        progression: &[Option<ProgressionChanges>],
    ) -> crate::specs::Part1PersistentTileConfiguration {
        (
            roi@.map_values(|value: Option<RoiShifts>| match value {
                None => None, Some(shifts) => Some(roi_shifts_view(&shifts)),
            }),
            styles@.map_values(|value: Option<CodingStyle>| match value {
                None => None, Some(style) => Some(parsed_coding_style_view(style)),
            }),
            quantizations@.map_values(|value: Option<Quantization>| match value {
                None => None, Some(quantization) => Some(quantization_view(&quantization)),
            }),
            style_parts@,
            component_quantizations@.map_values(|value: Option<ComponentQuantizations>| match value {
                None => None, Some(owner) => Some(parsed_quantization_owner_view(&owner)),
            }),
            progression@.map_values(|value: Option<ProgressionChanges>| match value {
                None => None, Some(changes) => Some(progression_changes_view(&changes)),
            }),
        )
    }

    pub(crate) closed spec fn optional_roi_shifts_view(value: Option<RoiShifts>) -> Option<Seq<u8>> {
        match value { None => None, Some(shifts) => Some(roi_shifts_view(&shifts)) }
    }
}
