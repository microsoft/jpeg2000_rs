//! Actual owned packet plans, physical layer selection and packet reconstruction.

use super::*;

verus! {

pub type Part2JpipPlan = (Part2JpipDatabin, Part2JpipDatabin, Seq<Part2JpipPacket>, Seq<usize>);
pub type Part2JpipPlannedPackets = (u16, Part2JpipAvailabilityReport, Option<Seq<u8>>);

pub open spec fn part2_jpip_plan_invalid(offset: u64) -> crate::DecodeError {
    part2_jpip_cache_error(offset, crate::MalformedKind::InvalidJpipLayout)
}

pub open spec fn part2_jpip_packet_new(id: Part2JpipDatabin, layer: u16, offset: u64, length: u64)
    -> Result<Part2JpipPacket, crate::DecodeError> {
    if id.1 != crate::jpip::DatabinClass::Precinct { Err(part2_jpip_plan_invalid(offset)) }
    else { match part2_jpip_range_new(id, offset, length) { Err(error) => Err(error), Ok(range) => Ok((range, layer)) } }
}

#[verifier::opaque]
pub open spec fn part2_jpip_plan_layer_packets(
    main: Part2JpipDatabin, packets: Seq<Part2JpipPacket>, layer: u16, position: nat, total: u64, input_limit: u64,
) -> Result<(usize, u64), crate::DecodeError>
    decreases if position < packets.len() { packets.len() - position } else { 0 },
{
    if position >= packets.len() || packets[position as int].1 != layer { Ok((position as usize, total)) }
    else {
        let packet = packets[position as int];
        if packet.0.0.2 != main.2 { Err(part2_jpip_plan_invalid(packet.0.1)) }
        else {
            let next = total as nat + packet.0.2 as nat;
            if next > u64::MAX as nat { Err(part2_jpip_range_overflow(packet.0.1)) }
            else if next > input_limit as nat {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes, limit: input_limit, actual: next as u64 })
            } else { part2_jpip_plan_layer_packets(main, packets, layer, position + 1, next as u64, input_limit) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_plan_layers(
    main: Part2JpipDatabin, tile: Part2JpipDatabin, packets: Seq<Part2JpipPacket>,
    layers: u16, layer: u16, position: usize, total: u64, ends: Seq<usize>, input_limit: u64,
) -> Result<Part2JpipPlan, crate::DecodeError>
    decreases if layer < layers { layers as nat - layer as nat } else { 0 },
{
    if layer >= layers {
        if position as nat != packets.len() { Err(part2_jpip_plan_invalid(position as u64)) }
        else { Ok((main, tile, packets, ends)) }
    } else {
        match part2_jpip_plan_layer_packets(main, packets, layer, position as nat, total, input_limit) {
            Err(error) => Err(error),
            Ok(next) => if next.0 == position { Err(part2_jpip_plan_invalid(layer as u64)) }
            else { part2_jpip_plan_layers(main, tile, packets, layers, (layer + 1) as u16,
                next.0, next.1, ends.push(next.0), input_limit) },
        }
    }
}

pub open spec fn part2_jpip_plan_new(
    main: Part2JpipDatabin, tile: Part2JpipDatabin, packets: Seq<Part2JpipPacket>, layers: u16, limits: &crate::ResourceLimits,
) -> Result<Part2JpipPlan, crate::DecodeError> {
    if layers == 0 || layers > crate::limits::resource_layer_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Layers,
            limit: crate::limits::resource_layer_limit(limits) as u64, actual: layers as u64 })
    } else if main.1 != crate::jpip::DatabinClass::MainHeader || main.3 != 0
        || tile.1 != crate::jpip::DatabinClass::TileHeader || main.2 != tile.2 {
        Err(part2_jpip_plan_invalid(0))
    } else if packets.len() == 0 || packets.len() as u64 > crate::limits::resource_packet_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Packets,
            limit: crate::limits::resource_packet_limit(limits), actual: packets.len() as u64 })
    } else {
        part2_jpip_plan_layers(main, tile, packets, layers, 0, 0, 0, Seq::empty(),
            crate::limits::resource_input_byte_limit(limits))
    }
}

pub open spec fn part2_jpip_plan_packet_end(plan: Part2JpipPlan, layers: u16)
    -> Result<usize, crate::DecodeError> {
    if layers == 0 || layers > plan.3.len() as u16 { Err(part2_jpip_plan_invalid(layers as u64)) }
    else {
        let index = layers as nat - 1;
        if index >= plan.3.len() { Err(part2_jpip_range_overflow(0)) }
        else { Ok(plan.3[index as int]) }
    }
}

pub open spec fn part2_jpip_planned_packets(cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16)
    -> Result<Part2JpipPlannedPackets, crate::DecodeError> {
    match part2_jpip_plan_packet_end(plan, layers) {
        Err(error) => Err(error),
        Ok(end) => if end as nat > plan.2.len() { Err(part2_jpip_range_overflow(0)) }
        else {
            let selected = plan.2.subrange(0, end as int);
            let ranges = selected.map_values(|packet: Part2JpipPacket| packet.0);
            match part2_jpip_cache_availability(cache, ranges) {
                Err(error) => Err(error),
                Ok(availability) => {
                    if availability.0 != crate::jpip::JpipAvailability::Available { Ok((layers, availability, None)) }
                    else {
                        match part2_jpip_read_packets(cache, selected) {
                            Err(error) => Err(error),
                            Ok(bytes) => Ok((layers, availability, Some(bytes))),
                        }
                    }
                },
            }
        },
    }
}

}
