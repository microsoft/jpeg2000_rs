//! Actual caller-planned progressive availability and full/selected update Results.

use super::*;

verus! {

pub type Part2JpipProgressiveDecoder = (Part2JpipPlan, u16);
pub type Part2JpipProgressiveUpdate = (
    crate::jpip::JpipProgressiveStatus, u16, u16, Seq<Part2JpipMissing>, Option<Part1DecodedTypedImage>,
);

pub open spec fn part2_jpip_ordinal_matrix_write(
    before: Seq<Seq<Option<u16>>>, after: Seq<Seq<Option<u16>>>,
    execution: usize, layer: u16, sequence: u16,
) -> bool {
    (execution as nat) < before.len()
        && (layer as nat) < before[execution as int].len()
        && before[execution as int][layer as int].is_none()
        && after == before.update(execution as int,
            before[execution as int].update(layer as int, Some(sequence)))
}

pub open spec fn part2_jpip_packet_matrix_write(
    before: Seq<Seq<Option<Seq<u8>>>>, after: Seq<Seq<Option<Seq<u8>>>>,
    execution: usize, layer: u16, bytes: Seq<u8>,
) -> bool {
    (execution as nat) < before.len()
        && (layer as nat) < before[execution as int].len()
        && after == before.update(execution as int,
            before[execution as int].update(layer as int, Some(bytes)))
}

#[verifier::opaque]
pub open spec fn part2_jpip_progressive_layers(
    cache: Part2JpipCache, packets: Seq<Part2JpipPacket>, ends: Seq<usize>, layer: nat, start: usize,
) -> Result<(u16, Seq<Part2JpipMissing>), crate::DecodeError>
    decreases if layer < ends.len() { ends.len() - layer } else { 0 },
{
    if layer >= ends.len() {
        if layer > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else { Ok((layer as u16, Seq::empty())) }
    } else {
        let end = ends[layer as int];
        if start > end || end as nat > packets.len() { Err(part2_jpip_range_overflow(0)) }
        else {
            let ranges = packets.subrange(start as int, end as int).map_values(|packet: Part2JpipPacket| packet.0);
            match part2_jpip_cache_availability(cache, ranges) {
                Err(error) => Err(error),
                Ok(report) => if report.0 != crate::jpip::JpipAvailability::Available {
                    if layer > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                    else { Ok((layer as u16, report.3)) }
                } else { part2_jpip_progressive_layers(cache, packets, ends, layer + 1, end) },
            }
        }
    }
}

pub open spec fn part2_jpip_progressive_availability(cache: Part2JpipCache, plan: Part2JpipPlan)
    -> Result<(u16, Seq<Part2JpipMissing>), crate::DecodeError> {
    let main = part2_jpip_append_complete_requirement(cache, plan.0,
        (crate::jpip::JpipAvailability::Available, 0, 0, Seq::empty()));
    match main.0 {
        Err(error) => Err(error),
        Ok(()) => {
            let tile = part2_jpip_append_complete_requirement(cache, plan.1, main.1);
            match tile.0 {
                Err(error) => Err(error),
                Ok(()) => if tile.1.3.len() != 0 { Ok((0, tile.1.3)) }
                else { part2_jpip_progressive_layers(cache, plan.2, plan.3, 0, 0) },
            }
        },
    }
}

pub open spec fn part2_jpip_progressive_update(
    cache: Part2JpipCache, decoder: Part2JpipProgressiveDecoder,
    options: &crate::DecodeOptions, selection: Option<&crate::DecodeSelection>,
) -> (Result<Part2JpipProgressiveUpdate, crate::DecodeError>, Part2JpipProgressiveDecoder) {
    let previous = decoder.1;
    let planned = decoder.0.3.len() as u16;
    match part2_jpip_progressive_availability(cache, decoder.0) {
        Err(error) => (Err(error), decoder),
        Ok((available, missing)) => {
            if !valid_jpip_progressive_update(previous as nat, available as nat, planned as nat) {
                (Err(part2_jpip_plan_invalid(0)), decoder)
            } else if available <= previous {
                (Ok((if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                    else { crate::jpip::JpipProgressiveStatus::WaitingForData }, previous, available, missing, None)), decoder)
            } else {
                match part2_jpip_transcode(cache, decoder.0, available) {
                    Err(error) => (Err(error), decoder),
                    Ok(transcoded) => match transcoded.2 {
                        None => (Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)), decoder),
                        Some(bytes) => match part2_decode_raw_codestream(
                            bytes, crate::options::decode_options_limits(options), selection) {
                            Err(error) => (Err(error), decoder),
                            Ok(image) => (Ok((
                                if available == planned { crate::jpip::JpipProgressiveStatus::Complete }
                                else { crate::jpip::JpipProgressiveStatus::QualityAdvanced },
                                previous, available, missing, Some(image),
                            )), (decoder.0, available)),
                        },
                    },
                }
            }
        },
    }
}

}
