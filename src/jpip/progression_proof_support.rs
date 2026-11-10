#[cfg(verus_keep_ghost)]
verus! {
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
