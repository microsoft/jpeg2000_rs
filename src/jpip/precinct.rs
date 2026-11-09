//! Explicit precinct packet plans, packet reconstruction, and header transcoding.

use super::{
    DatabinCache, DatabinClass, DatabinId, DecodeError, EOC, JpipAvailabilityReport, JpipByteView,
    JpipDatabinRange, JpipPrecinctCodestreamPlan, JpipPrecinctPacket, JpipPrecinctPackets,
    JpipPrecinctTranscode, MalformedKind, Resource, ResourceLimits, SOC,
};
#[cfg(verus_keep_ghost)]
use super::{
    databin_id_view, jpip_availability_view, jpip_byte_view, jpip_cache_view,
    jpip_optional_byte_view, jpip_optional_owned_byte_view, jpip_owned_packets_view,
    jpip_packet_outcome, jpip_packet_view, jpip_packets_view, jpip_plan_fields,
    jpip_plan_layer_count, jpip_plan_outcome, jpip_plan_packet_owner, jpip_plan_view,
    jpip_planned_availability_owner, jpip_planned_packet_owner, jpip_planned_packets_outcome,
    jpip_planned_packets_view, jpip_range_view, jpip_ranges_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(test)]
#[path = "planned_packet_result_tests.rs"]
mod result_tests;

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipPrecinctPacket {
    pub fn new(
        databin: DatabinId,
        layer: u16,
        offset: u64,
        length: u64,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                jpip_packet_outcome(result),
                crate::specs::part2_jpip_packet_new(
                    databin_id_view(databin),
                    layer,
                    offset,
                    length,
                ),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_packet_view); }
        if !matches!(databin.class(), DatabinClass::Precinct) {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidJpipLayout,
            ));
        }
        Ok(Self {
            range: JpipDatabinRange::new(databin, offset, length)?,
            layer,
        })
    }

    pub const fn range(&self) -> JpipDatabinRange {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: JpipDatabinRange| {
            vstd::prelude::equal(jpip_range_view(result), jpip_packet_view(*self).0)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_packet_view); }
        self.range
    }

    pub const fn layer(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u16| {
            vstd::prelude::equal(result, jpip_packet_view(*self).1)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_packet_view); }
        self.layer
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipPrecinctCodestreamPlan {
    pub fn new(
        main_header: DatabinId,
        tile_header: DatabinId,
        packets: Vec<JpipPrecinctPacket>,
        layers: u16,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                jpip_plan_outcome(result),
                crate::specs::part2_jpip_plan_new(
                    databin_id_view(main_header),
                    databin_id_view(tile_header),
                    jpip_owned_packets_view(&packets),
                    layers,
                    limits,
                ),
            ) && match result {
                Err(_) => true,
                Ok(value) => vstd::prelude::equal(*jpip_plan_packet_owner(&value), packets),
            }
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_plan_view); reveal(jpip_plan_packet_owner); reveal(jpip_packet_view); reveal(jpip_range_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost entries = jpip_owned_packets_view(&packets);
            let ghost main = databin_id_view(main_header);
            let ghost tile = databin_id_view(tile_header);
            let ghost original_owner = packets;
            let ghost expected = crate::specs::part2_jpip_plan_new(main, tile, entries, layers, limits);
        }
        if layers == 0 || layers > limits.maximum_layers() {
            return Err(DecodeError::limit(
                Resource::Layers,
                u64::from(limits.maximum_layers()),
                u64::from(layers),
            ));
        }
        if !matches!(main_header.class(), DatabinClass::MainHeader)
            || main_header.in_class() != 0
            || !matches!(tile_header.class(), DatabinClass::TileHeader)
            || main_header.codestream() != tile_header.codestream()
        {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
        }
        if packets.is_empty() || packets.len() as u64 > limits.maximum_packets() {
            return Err(DecodeError::limit(
                Resource::Packets,
                limits.maximum_packets(),
                packets.len() as u64,
            ));
        }
        let mut layer_ends = Vec::with_capacity(usize::from(layers));
        let mut packet_index = 0_usize;
        let mut layer = 0_u16;
        let mut total_bytes = 0_u64;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant packet_index <= packets.len() && layer <= layers,
                    packets == original_owner,
                    entries == jpip_owned_packets_view(&packets), entries.len() == packets.len(),
                    forall|index: int| 0 <= index < packets.len() ==>
                        #[trigger] entries[index] == ((databin_id_view(packets@[index].range.databin),
                            packets@[index].range.offset, packets@[index].range.length), packets@[index].layer),
                    main == databin_id_view(main_header), tile == databin_id_view(tile_header),
                    layer_ends.len() == layer as nat,
                    expected == crate::specs::part2_jpip_plan_new(main, tile, entries, layers, limits),
                    expected == crate::specs::part2_jpip_plan_layers(main, tile, entries, layers,
                        layer, packet_index, total_bytes, layer_ends@, crate::limits::resource_input_byte_limit(limits)),
                decreases layers - layer,
            )
        )]
        while layer < layers {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_plan_layers); }
            let layer_start = packet_index;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost scan_expected = crate::specs::part2_jpip_plan_layer_packets(
                    main, entries, layer, packet_index as nat, total_bytes, crate::limits::resource_input_byte_limit(limits));
            }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant packet_index <= packets.len(),
                        packets == original_owner,
                        entries == jpip_owned_packets_view(&packets), entries.len() == packets.len(),
                        forall|index: int| 0 <= index < packets.len() ==>
                            #[trigger] entries[index] == ((databin_id_view(packets@[index].range.databin),
                                packets@[index].range.offset, packets@[index].range.length), packets@[index].layer),
                        main == databin_id_view(main_header), tile == databin_id_view(tile_header),
                        layer < layers, layer_start <= packet_index,
                        expected == crate::specs::part2_jpip_plan_new(main, tile, entries, layers, limits),
                        scan_expected == crate::specs::part2_jpip_plan_layer_packets(
                            main, entries, layer, packet_index as nat, total_bytes, crate::limits::resource_input_byte_limit(limits)),
                        expected == match scan_expected {
                            Err(error) => Err(error),
                            Ok(next) => if next.0 == layer_start { Err(crate::specs::part2_jpip_plan_invalid(layer as u64)) }
                            else { crate::specs::part2_jpip_plan_layers(main, tile, entries, layers, (layer + 1) as u16,
                                next.0, next.1, layer_ends@.push(next.0), crate::limits::resource_input_byte_limit(limits)) },
                        },
                    decreases packets.len() - packet_index,
                )
            )]
            while packet_index < packets.len() && packets[packet_index].layer == layer {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_plan_layer_packets); }
                let packet = packets[packet_index];
                if packet.range.databin.codestream() != main_header.codestream() {
                    return Err(DecodeError::malformed(
                        packet.range.offset,
                        MalformedKind::InvalidJpipLayout,
                    ));
                }
                total_bytes = total_bytes
                    .checked_add(packet.range.length)
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(packet.range.offset),
                        ))]
                        || {
                            DecodeError::malformed(packet.range.offset, MalformedKind::ArithmeticOverflow)
                        },
                    )?;
                if total_bytes > limits.maximum_input_bytes() {
                    return Err(DecodeError::limit(
                        Resource::InputBytes,
                        limits.maximum_input_bytes(),
                        total_bytes,
                    ));
                }
                packet_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_plan_layer_packets); }
            if packet_index == layer_start {
                return Err(DecodeError::malformed(
                    u64::from(layer),
                    MalformedKind::InvalidJpipLayout,
                ));
            }
            layer_ends.push(packet_index);
            layer += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_plan_layers); }
        if packet_index != packets.len() {
            return Err(DecodeError::malformed(
                packet_index as u64,
                MalformedKind::InvalidJpipLayout,
            ));
        }
        Ok(Self {
            main_header,
            tile_header,
            packets,
            layer_ends,
        })
    }

    pub const fn main_header(&self) -> DatabinId {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: DatabinId| {
            vstd::prelude::equal(databin_id_view(result), jpip_plan_view(self).0)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_plan_view); }
        self.main_header
    }

    pub const fn tile_header(&self) -> DatabinId {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: DatabinId| {
            vstd::prelude::equal(databin_id_view(result), jpip_plan_view(self).1)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_plan_view); }
        self.tile_header
    }

    pub fn packets(&self) -> &[JpipPrecinctPacket] {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: &[JpipPrecinctPacket]| {
            vstd::prelude::equal(jpip_packets_view(result), jpip_plan_view(self).2)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_plan_view); }
        &self.packets
    }

    pub fn layers(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u16| {
            vstd::prelude::equal(result, jpip_plan_layer_count(self))
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_plan_view); }
        self.layer_ends.len() as u16
    }

    fn packet_end_for_layers(&self, layers: u16) -> Result<usize, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<usize, DecodeError>| {
            vstd::prelude::equal(
                result,
                crate::specs::part2_jpip_plan_packet_end(jpip_plan_view(self), layers),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_plan_view); }
        if layers == 0 || layers > self.layers() {
            return Err(DecodeError::malformed(
                u64::from(layers),
                MalformedKind::InvalidJpipLayout,
            ));
        }
        match self.layer_ends.get(usize::from(layers - 1)) {
            Some(end) => Ok(*end),
            None => Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)),
        }
    }
}

impl JpipPrecinctPackets {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_planned_packets_view(self).0,))]
    pub const fn layers(&self) -> u16 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_planned_packets_view); }
        self.layers
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_availability_view(result) == jpip_planned_packets_view(self).1,
            result == jpip_planned_availability_owner(self),
    ))]
    pub const fn availability(&self) -> &JpipAvailabilityReport {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_planned_packets_view); reveal(jpip_planned_availability_owner); }
        &self.availability
    }

    /// Returns the caller-planned LRCP packet byte stream. Packet bytes are
    /// copied exactly; no packet-header syntax is invented or rewritten.
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures jpip_optional_byte_view(result) == jpip_planned_packets_view(self).2,))]
    pub const fn packets(&self) -> Option<&JpipByteView> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_planned_packets_view); }
        self.packets.as_ref()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_optional_owned_byte_view(result) == jpip_planned_packets_view(&self).2,
            result == *jpip_planned_packet_owner(&self),
    ))]
    pub fn into_packets(self) -> Option<JpipByteView> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_planned_packets_view); reveal(jpip_planned_packet_owner); }
        self.packets
    }
}

impl JpipPrecinctTranscode {
    pub const fn layers(&self) -> u16 {
        self.layers
    }

    pub const fn availability(&self) -> &JpipAvailabilityReport {
        &self.availability
    }

    pub const fn codestream(&self) -> Option<&JpipByteView> {
        self.codestream.as_ref()
    }

    pub fn into_codestream(self) -> Option<JpipByteView> {
        self.codestream
    }
}

impl DatabinCache {
    pub fn transcode_precinct_codestream(
        &self,
        plan: &JpipPrecinctCodestreamPlan,
        layers: u16,
    ) -> Result<JpipPrecinctTranscode, DecodeError> {
        let packet_end = plan.packet_end_for_layers(layers)?;
        let availability = self.precinct_availability(plan, packet_end)?;
        if !availability.is_available() {
            return Ok(JpipPrecinctTranscode {
                layers,
                availability,
                codestream: None,
            });
        }
        let mut main_header = self.databin_view(plan.main_header)?.into_bytes();
        let mut tile_header = self.databin_view(plan.tile_header)?.into_bytes();
        validate_and_patch_main_header(&mut main_header, layers)?;
        validate_and_patch_tile_header(&mut tile_header, layers)?;
        let selected_packets = plan
            .packets
            .get(..packet_end)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let packet_bytes = self.read_packet_ranges(selected_packets)?;
        let tile_part_length = tile_header
            .len()
            .checked_add(packet_bytes.len())
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let tile_part_length = u32::try_from(tile_part_length)
            .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let tile_part_bytes = [
            u8::try_from((tile_part_length >> 24) & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            u8::try_from((tile_part_length >> 16) & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            u8::try_from((tile_part_length >> 8) & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            u8::try_from(tile_part_length & 0xff)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        ];
        tile_header
            .get_mut(6..10)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::InvalidTilePart))?
            .copy_from_slice(&tile_part_bytes);
        let total = main_header
            .len()
            .checked_add(tile_header.len())
            .and_then(|value| value.checked_add(packet_bytes.len()))
            .and_then(|value| value.checked_add(EOC.len()))
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let contracted_total = crate::refinement::jpip_reconstruction_length(
            main_header.len() as u64,
            tile_header.len() as u64,
            packet_bytes.len() as u64,
            EOC.len() as u64,
        );
        if contracted_total != total as u128 {
            return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow));
        }
        if total as u64 > self.limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.limits.maximum_input_bytes(),
                total as u64,
            ));
        }
        let mut bytes = Vec::with_capacity(total);
        bytes.extend_from_slice(&main_header);
        bytes.extend_from_slice(&tile_header);
        bytes.extend_from_slice(&packet_bytes);
        bytes.extend_from_slice(&EOC);
        validate_precinct_codestream(&bytes, layers, &self.limits)?;
        Ok(JpipPrecinctTranscode {
            layers,
            availability,
            codestream: Some(JpipByteView { bytes }),
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_planned_packets_outcome(result)
            == crate::specs::part2_jpip_planned_packets(jpip_cache_view(self), jpip_plan_view(plan), layers),
    ))]
    pub fn reconstruct_precinct_packets(
        &self,
        plan: &JpipPrecinctCodestreamPlan,
        layers: u16,
    ) -> Result<JpipPrecinctPackets, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_plan_fields(plan); reveal(jpip_packet_view); reveal(jpip_planned_packets_view); reveal(jpip_byte_view); }
        let packet_end = plan.packet_end_for_layers(layers)?;
        let selected_packets = plan.packets.get(..packet_end).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
        let ranges: Vec<JpipDatabinRange> = selected_packets
            .iter()
            .map(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: JpipDatabinRange =>
                ensures result == packet.range,
            ))]
                |packet: &JpipPrecinctPacket| packet.range,
            )
            .collect();
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(jpip_packets_view(selected_packets) =~= jpip_plan_view(plan).2.subrange(0, packet_end as int));
            assert(ranges@.map_values(|range: JpipDatabinRange| jpip_range_view(range)) =~= jpip_packets_view(selected_packets).map_values(
                |packet: crate::specs::Part2JpipPacket| packet.0));
        }
        let availability = self.availability(&ranges)?;
        let packets = if availability.is_available() {
            Some(JpipByteView {
                bytes: self.read_packet_ranges(selected_packets)?,
            })
        } else {
            None
        };
        Ok(JpipPrecinctPackets {
            layers,
            availability,
            packets,
        })
    }
}

fn validate_and_patch_main_header(header: &mut [u8], layers: u16) -> Result<(), DecodeError> {
    if !header.starts_with(&SOC) {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    patch_cod_layers(header, 2, layers, false)?;
    Ok(())
}

fn validate_and_patch_tile_header(header: &mut [u8], layers: u16) -> Result<(), DecodeError> {
    if header.len() < 14
        || header.get(0..2) != Some(&[0xff, 0x90])
        || header.get(2..4) != Some(&[0, 10])
        || !matches!(header.get(10), Some(0))
        || !matches!(header.get(11), Some(0 | 1))
        || !header.ends_with(&[0xff, 0x93])
    {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
    }
    patch_cod_layers(header, 0, layers, true)?;
    Ok(())
}

fn patch_cod_layers(
    header: &mut [u8],
    start: usize,
    layers: u16,
    stop_at_sod: bool,
) -> Result<(), DecodeError> {
    if start > header.len() {
        return Err(DecodeError::malformed(
            start as u64,
            MalformedKind::Truncated,
        ));
    }
    let mut position = start;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= header.len(),
            decreases header.len() - position,
        )
    )]
    while position < header.len() {
        let marker_bytes = header
            .get(position..position.saturating_add(2))
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
        let marker_high = *marker_bytes
            .first()
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
        let marker_low = *marker_bytes
            .get(1)
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
        let marker = (u16::from(marker_high) << 8) | u16::from(marker_low);
        if marker == 0xff93 {
            if stop_at_sod && position + 2 == header.len() {
                return Ok(());
            }
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        if marker == 0xff4f || marker == 0xffd9 || marker == 0xff90 && position != 0 {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerOrder,
            ));
        }
        let length_bytes = header
            .get(position.saturating_add(2)..position.saturating_add(4))
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
        let length_high = *length_bytes
            .first()
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
        let length_low = *length_bytes
            .get(1)
            .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?;
        let segment_length = usize::from((u16::from(length_high) << 8) | u16::from(length_low));
        if segment_length < 2 {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidMarkerLength,
            ));
        }
        let segment_end = position
            .checked_add(2)
            .and_then(|value| value.checked_add(segment_length))
            .ok_or_else(|| {
                DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
            })?;
        if segment_end <= position || segment_end > header.len() {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::Truncated,
            ));
        }
        if marker == 0xff52 {
            if segment_length < 7 {
                return Err(DecodeError::malformed(
                    position as u64,
                    MalformedKind::InvalidCodingStyle,
                ));
            }
            let bytes = [
                u8::try_from((layers >> 8) & 0xff).map_err(|_| {
                    DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
                })?,
                u8::try_from(layers & 0xff).map_err(|_| {
                    DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
                })?,
            ];
            let layer_start = position.checked_add(6).ok_or_else(|| {
                DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
            })?;
            let layer_end = layer_start.checked_add(2).ok_or_else(|| {
                DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
            })?;
            header
                .get_mut(layer_start..layer_end)
                .ok_or_else(|| DecodeError::malformed(position as u64, MalformedKind::Truncated))?
                .copy_from_slice(&bytes);
        }
        position = segment_end;
    }
    if stop_at_sod {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::MissingRequiredStructure,
        ));
    }
    Ok(())
}

fn validate_precinct_codestream(
    bytes: &[u8],
    layers: u16,
    limits: &ResourceLimits,
) -> Result<(), DecodeError> {
    let layout = crate::codestream::parse_layout(bytes, limits)?;
    if layout.info.image_size.tile_count()? != 1
        || layout.tile_parts.len() != 1
        || layout.info.coding_style.layers != layers
        || !matches!(
            layout.info.coding_style.progression_order,
            crate::codestream::ProgressionOrder::Lrcp
        )
        || !matches!(
            layout.tile_parts[0].coding_style.progression_order,
            crate::codestream::ProgressionOrder::Lrcp
        )
        || layout.info.progression_changes.is_present()
        || layout.tile_parts[0].progression_changes.is_present()
        || layout.tile_parts[0].packet_lengths.is_present()
        || layout.tile_parts[0].packed_packet_headers.is_present()
    {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipLayout));
    }
    Ok(())
}
