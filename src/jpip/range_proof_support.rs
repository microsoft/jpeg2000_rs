#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn jpip_range_view(value: JpipDatabinRange) -> crate::specs::Part2JpipRange {
        (databin_id_view(value.databin), value.offset, value.length)
    }

    pub open spec fn jpip_range_outcome(value: Result<JpipDatabinRange, DecodeError>)
        -> Result<crate::specs::Part2JpipRange, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_range_view(value)) }
    }

    pub open spec fn jpip_ranges_view(value: &[JpipDatabinRange]) -> Seq<crate::specs::Part2JpipRange> {
        value@.map_values(|range: JpipDatabinRange| jpip_range_view(range))
    }

    pub closed spec fn jpip_missing_view(value: JpipMissingRange) -> crate::specs::Part2JpipMissing {
        (databin_id_view(value.databin), value.offset, value.length)
    }

    pub open spec fn jpip_missing_views(value: &Vec<JpipMissingRange>) -> Seq<crate::specs::Part2JpipMissing> {
        value@.map_values(|range: JpipMissingRange| jpip_missing_view(range))
    }

    pub closed spec fn jpip_availability_view(value: &JpipAvailabilityReport) -> crate::specs::Part2JpipAvailabilityReport {
        (value.status, value.required_bytes, value.available_bytes, jpip_missing_views(&value.missing))
    }

    pub open spec fn jpip_availability_outcome(value: Result<JpipAvailabilityReport, DecodeError>)
        -> Result<crate::specs::Part2JpipAvailabilityReport, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_availability_view(&value)) }
    }

    pub closed spec fn jpip_packet_view(value: JpipPrecinctPacket) -> crate::specs::Part2JpipPacket {
        (jpip_range_view(value.range), value.layer)
    }

    pub open spec fn jpip_packets_view(value: &[JpipPrecinctPacket]) -> Seq<crate::specs::Part2JpipPacket> {
        value@.map_values(|packet: JpipPrecinctPacket| jpip_packet_view(packet))
    }

    pub open spec fn jpip_packet_bytes_outcome(value: Result<Vec<u8>, DecodeError>) -> Result<Seq<u8>, DecodeError> {
        match value { Err(error) => Err(error), Ok(bytes) => Ok(bytes@) }
    }
}
