#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn jpip_fragment_view(value: &JpipFragment) -> crate::specs::Part2JpipFragment {
        (databin_id_view(value.databin), value.offset, value.bytes@, value.final_length, value.auxiliary)
    }

    pub open spec fn jpip_fragment_outcome(value: Result<JpipFragment, DecodeError>)
        -> Result<crate::specs::Part2JpipFragment, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_fragment_view(&value)) }
    }

    pub open spec fn jpip_fragment_new_input(
        databin: DatabinId, offset: u64, bytes: &Vec<u8>, last: bool, auxiliary: Option<u64>, limits: &ResourceLimits,
    ) -> Result<crate::specs::Part2JpipFragment, DecodeError> {
        crate::specs::part2_jpip_fragment_new(databin_id_view(databin), offset, bytes@, last, auxiliary, limits)
    }

    pub open spec fn jpip_fragment_message_input(
        header: JpipMessageHeader, body: &[u8], limits: &ResourceLimits,
    ) -> Result<crate::specs::Part2JpipFragment, DecodeError> {
        crate::specs::part2_jpip_fragment_from_message(jpip_header_view(header), body@, limits)
    }

    pub closed spec fn jpip_stored_fragment_view(value: &StoredFragment) -> crate::specs::Part2JpipStoredFragment {
        (value.offset, value.bytes@)
    }

    pub closed spec fn jpip_databin_view(value: &Databin) -> crate::specs::Part2JpipDatabinState {
        (databin_id_view(value.id),
            value.fragments@.map_values(|fragment: StoredFragment| jpip_stored_fragment_view(&fragment)),
            value.final_length)
    }

    pub closed spec fn jpip_cache_view(value: &DatabinCache) -> crate::specs::Part2JpipCache {
        (value.limits, value.databins@.map_values(|databin: Databin| jpip_databin_view(&databin)),
            value.stored_bytes, value.accepted_fragments)
    }

    pub closed spec fn jpip_status_view(value: &DatabinStatus) -> crate::specs::Part2JpipStatus {
        (value.final_length, value.contiguous_prefix, value.stored_bytes, value.intervals)
    }

    pub closed spec fn jpip_byte_view(value: &JpipByteView) -> Seq<u8> { value.bytes@ }

    pub closed spec fn jpip_byte_storage(value: &JpipByteView) -> &Vec<u8> { &value.bytes }

    pub open spec fn jpip_byte_outcome(value: Result<JpipByteView, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_byte_view(&value)) }
    }

    pub open spec fn jpip_status_outcome(value: Option<DatabinStatus>) -> Option<crate::specs::Part2JpipStatus> {
        match value { None => None, Some(value) => Some(jpip_status_view(&value)) }
    }

    pub open spec fn jpip_layout_view(value: &[DatabinId]) -> Seq<crate::specs::Part2JpipDatabin> {
        value@.map_values(|id: DatabinId| databin_id_view(id))
    }

    pub open spec fn jpip_view_parts(value: &Vec<JpipByteView>) -> Seq<Seq<u8>> {
        value@.map_values(|part: JpipByteView| jpip_byte_view(&part))
    }

    proof fn jpip_fragment_fields(value: &JpipFragment)
        ensures jpip_fragment_view(value) == (databin_id_view(value.databin), value.offset, value.bytes@,
            value.final_length, value.auxiliary),
    {
        reveal(jpip_fragment_view);
    }

    proof fn jpip_cache_fields(value: &DatabinCache)
        ensures jpip_cache_view(value).0 == value.limits,
            jpip_cache_view(value).1.len() == value.databins.len(),
            forall|index: int| 0 <= index < value.databins.len() ==>
                #[trigger] jpip_cache_view(value).1[index].0 == databin_id_view(value.databins@[index].id),
            forall|index: int| 0 <= index < value.databins.len() ==>
                #[trigger] jpip_cache_view(value).1[index] == jpip_databin_view(&value.databins@[index]),
            jpip_cache_view(value).2 == value.stored_bytes,
            jpip_cache_view(value).3 == value.accepted_fragments,
    {
        reveal(jpip_cache_view);
        reveal(jpip_databin_view);
    }

    proof fn jpip_databin_fields(value: &Databin)
        ensures jpip_databin_view(value).2 == value.final_length,
            jpip_databin_view(value).1.len() == value.fragments.len(),
            forall|index: int| 0 <= index < value.fragments.len() ==>
                #[trigger] jpip_databin_view(value).1[index] == jpip_stored_fragment_view(&value.fragments@[index]),
            forall|index: int| 0 <= index < value.fragments.len() ==>
                #[trigger] jpip_databin_view(value).1[index] == (value.fragments@[index].offset, value.fragments@[index].bytes@),
    {
        reveal(jpip_databin_view);
        reveal(jpip_stored_fragment_view);
    }

    proof fn jpip_status_fields(value: &DatabinStatus)
        ensures jpip_status_view(value) == (value.final_length, value.contiguous_prefix, value.stored_bytes, value.intervals),
    {
        reveal(jpip_status_view);
    }
}
