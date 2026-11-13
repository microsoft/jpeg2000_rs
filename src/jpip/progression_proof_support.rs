#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn jpip_parsed_packet_value(value: Option<Vec<u8>>) -> Option<Seq<u8>> {
        match value { None => None, Some(bytes) => Some(bytes@) }
    }

    pub open spec fn jpip_parsed_packet_row(value: Vec<Option<Vec<u8>>>) -> Seq<Option<Seq<u8>>> {
        value@.map_values(|cell: Option<Vec<u8>>| jpip_parsed_packet_value(cell))
    }

    pub open spec fn jpip_parsed_packet_matrix(value: Seq<Vec<Option<Vec<u8>>>>)
        -> Seq<Seq<Option<Seq<u8>>>> {
        value.map_values(|row: Vec<Option<Vec<u8>>>| jpip_parsed_packet_row(row))
    }

    pub proof fn jpip_parsed_packet_matrix_update(
        value: Seq<Vec<Option<Vec<u8>>>>, index: int, row: Vec<Option<Vec<u8>>>,
    )
        requires 0 <= index < value.len(),
        ensures jpip_parsed_packet_matrix(value.update(index, row))
            == jpip_parsed_packet_matrix(value).update(index, jpip_parsed_packet_row(row)),
    {
        assert(jpip_parsed_packet_matrix(value.update(index, row))
            =~= jpip_parsed_packet_matrix(value).update(index, jpip_parsed_packet_row(row)));
    }

    pub proof fn jpip_parsed_packet_row_update(
        before: Vec<Option<Vec<u8>>>, after: Vec<Option<Vec<u8>>>, index: int, value: Option<Vec<u8>>,
    )
        requires 0 <= index < before@.len(), after@ == before@.update(index, value),
        ensures jpip_parsed_packet_row(after)
            == jpip_parsed_packet_row(before).update(index, jpip_parsed_packet_value(value)),
    {
        assert(jpip_parsed_packet_row(after)
            =~= jpip_parsed_packet_row(before).update(index, jpip_parsed_packet_value(value)));
    }

    pub closed spec fn jpip_progressive_decoder_view(value: &JpipProgressiveDecoder)
        -> crate::specs::Part2JpipProgressiveDecoder {
        (jpip_plan_view(&value.plan), value.decoded_layers)
    }

    pub closed spec fn jpip_progressive_plan_owner(value: &JpipProgressiveDecoder) -> &JpipPrecinctCodestreamPlan {
        &value.plan
    }

    pub closed spec fn jpip_progressive_update_view(value: &JpipProgressiveUpdate)
        -> crate::specs::Part2JpipProgressiveUpdate {
        (value.status, value.previous_layers, value.available_layers, jpip_missing_views(&value.missing),
            match &value.image { None => None, Some(image) => Some(crate::image::typed_image_value_view(*image)) })
    }

    pub closed spec fn jpip_progressive_image_borrow(value: &JpipProgressiveUpdate) -> Option<&crate::image::TypedImage> {
        match &value.image { None => None, Some(image) => Some(image) }
    }

    pub closed spec fn jpip_progressive_image_owner(value: &JpipProgressiveUpdate) -> &Option<crate::image::TypedImage> {
        &value.image
    }

    pub open spec fn jpip_optional_image_view(value: Option<crate::image::TypedImage>)
        -> Option<crate::specs::Part1DecodedTypedImage> {
        match value { None => None, Some(image) => Some(crate::image::typed_image_value_view(image)) }
    }

    pub open spec fn jpip_optional_image_borrow_view(value: Option<&crate::image::TypedImage>)
        -> Option<crate::specs::Part1DecodedTypedImage> {
        match value { None => None, Some(image) => Some(crate::image::typed_image_value_view(*image)) }
    }

    pub open spec fn jpip_progressive_outcome(value: Result<JpipProgressiveUpdate, DecodeError>)
        -> Result<crate::specs::Part2JpipProgressiveUpdate, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_progressive_update_view(&value)) }
    }

    pub open spec fn jpip_progressive_availability_outcome(value: Result<(u16, Vec<JpipMissingRange>), DecodeError>)
        -> Result<(u16, Seq<crate::specs::Part2JpipMissing>), DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok((value.0, jpip_missing_views(&value.1))) }
    }
}
