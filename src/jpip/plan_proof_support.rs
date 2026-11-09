#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn jpip_packet_outcome(value: Result<JpipPrecinctPacket, DecodeError>)
        -> Result<crate::specs::Part2JpipPacket, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_packet_view(value)) }
    }

    pub open spec fn jpip_owned_packets_view(value: &Vec<JpipPrecinctPacket>) -> Seq<crate::specs::Part2JpipPacket> {
        value@.map_values(|packet: JpipPrecinctPacket| jpip_packet_view(packet))
    }

    pub closed spec fn jpip_plan_view(value: &JpipPrecinctCodestreamPlan) -> crate::specs::Part2JpipPlan {
        (databin_id_view(value.main_header), databin_id_view(value.tile_header),
            jpip_owned_packets_view(&value.packets), value.layer_ends@)
    }

    pub closed spec fn jpip_plan_packet_owner(value: &JpipPrecinctCodestreamPlan) -> &Vec<JpipPrecinctPacket> {
        &value.packets
    }

    pub open spec fn jpip_plan_layer_count(value: &JpipPrecinctCodestreamPlan) -> u16 {
        jpip_plan_view(value).3.len() as u16
    }

    pub open spec fn jpip_plan_outcome(value: Result<JpipPrecinctCodestreamPlan, DecodeError>)
        -> Result<crate::specs::Part2JpipPlan, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_plan_view(&value)) }
    }

    pub closed spec fn jpip_planned_packets_view(value: &JpipPrecinctPackets) -> crate::specs::Part2JpipPlannedPackets {
        (value.layers, jpip_availability_view(&value.availability),
            match &value.packets { None => None, Some(bytes) => Some(jpip_byte_view(bytes)) })
    }

    pub closed spec fn jpip_planned_availability_owner(value: &JpipPrecinctPackets) -> &JpipAvailabilityReport {
        &value.availability
    }

    pub closed spec fn jpip_planned_packet_owner(value: &JpipPrecinctPackets) -> &Option<JpipByteView> {
        &value.packets
    }

    pub open spec fn jpip_planned_packets_outcome(value: Result<JpipPrecinctPackets, DecodeError>)
        -> Result<crate::specs::Part2JpipPlannedPackets, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_planned_packets_view(&value)) }
    }

    pub open spec fn jpip_optional_byte_view(value: Option<&JpipByteView>) -> Option<Seq<u8>> {
        match value { None => None, Some(bytes) => Some(jpip_byte_view(bytes)) }
    }

    pub open spec fn jpip_optional_owned_byte_view(value: Option<JpipByteView>) -> Option<Seq<u8>> {
        match value { None => None, Some(bytes) => Some(jpip_byte_view(&bytes)) }
    }

    proof fn jpip_plan_fields(value: &JpipPrecinctCodestreamPlan)
        ensures jpip_plan_view(value) == (databin_id_view(value.main_header), databin_id_view(value.tile_header),
            jpip_owned_packets_view(&value.packets), value.layer_ends@),
    {
        reveal(jpip_plan_view);
    }
}
