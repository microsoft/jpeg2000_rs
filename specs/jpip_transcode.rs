//! Actual header availability, in-place COD rewriting and raw-validated transcoding.

use super::*;

verus! {

pub type Part2JpipTranscode = (u16, Part2JpipAvailabilityReport, Option<Seq<u8>>);
pub type Part2JpipHeaderResult = (Result<(), crate::DecodeError>, Seq<u8>);

pub open spec fn part2_jpip_append_complete_requirement(
    cache: Part2JpipCache, id: Part2JpipDatabin, report: Part2JpipAvailabilityReport,
) -> (Result<(), crate::DecodeError>, Part2JpipAvailabilityReport) {
    match part2_jpip_cache_status(cache, id) {
        None => (Ok(()), (report.0, report.1, report.2, report.3.push((id, 0, None)))),
        Some(status) => match status.0 {
            None => {
                let available = report.2 as nat + status.1 as nat;
                if available > u64::MAX as nat { (Err(part2_jpip_range_overflow(0)), report) }
                else { (Ok(()), (report.0, report.1, available as u64, report.3.push((id, status.1, None)))) }
            },
            Some(length) => {
                let header = if length == 0 {
                    Ok((crate::jpip::JpipAvailability::Available, 0u64, 0u64, Seq::empty()))
                } else {
                    match part2_jpip_range_new(id, 0, length) {
                        Err(error) => Err(error),
                        Ok(range) => part2_jpip_cache_availability(cache, seq![range]),
                    }
                };
                match header {
                    Err(error) => (Err(error), report),
                    Ok(header) => {
                        let required = report.1 as nat + header.1 as nat;
                        if required > u64::MAX as nat { (Err(part2_jpip_range_overflow(0)), report) }
                        else {
                            let committed = (report.0, required as u64, report.2, report.3);
                            let available = report.2 as nat + header.2 as nat;
                            if available > u64::MAX as nat { (Err(part2_jpip_range_overflow(0)), committed) }
                            else { (Ok(()), (report.0, required as u64, available as u64, report.3 + header.3)) }
                        }
                    },
                }
            },
        },
    }
}

pub open spec fn part2_jpip_precinct_availability(cache: Part2JpipCache, plan: Part2JpipPlan, end: usize)
    -> Result<Part2JpipAvailabilityReport, crate::DecodeError> {
    if end as nat > plan.2.len() { Err(part2_jpip_range_overflow(0)) }
    else {
        let ranges = plan.2.subrange(0, end as int).map_values(|packet: Part2JpipPacket| packet.0);
        match part2_jpip_cache_availability(cache, ranges) {
            Err(error) => Err(error),
            Ok(report) => {
                let main = part2_jpip_append_complete_requirement(cache, plan.0, report);
                match main.0 {
                    Err(error) => Err(error),
                    Ok(()) => {
                        let tile = part2_jpip_append_complete_requirement(cache, plan.1, main.1);
                        match tile.0 {
                            Err(error) => Err(error),
                            Ok(()) => Ok((
                                if tile.1.3.len() == 0 { crate::jpip::JpipAvailability::Available }
                                else if tile.1.2 == 0 { crate::jpip::JpipAvailability::Missing }
                                else { crate::jpip::JpipAvailability::Partial },
                                tile.1.1, tile.1.2, tile.1.3,
                            )),
                        }
                    },
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_patch_cod_loop(header: Seq<u8>, position: usize, layers: u16, stop: bool)
    -> Part2JpipHeaderResult
    decreases if position < header.len() { header.len() - position } else { 0 },
{
    if position as nat >= header.len() {
        (if stop { Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::MissingRequiredStructure)) }
            else { Ok(()) }, header)
    } else {
        let offset = position as u64;
        if position as nat + 2 > header.len() || position as nat + 2 > usize::MAX as nat {
            (Err(part2_jpip_cache_error(offset, crate::MalformedKind::Truncated)), header)
        } else {
            let marker = ((header[position as int] as u16) << 8) | header[position as int + 1] as u16;
            if marker == 0xff93 {
                (if stop && position as nat + 2 == header.len() { Ok(()) }
                    else { Err(part2_jpip_cache_error(offset, crate::MalformedKind::InvalidMarkerOrder)) }, header)
            } else if marker == 0xff4f || marker == 0xffd9 || marker == 0xff90 && position != 0 {
                (Err(part2_jpip_cache_error(offset, crate::MalformedKind::InvalidMarkerOrder)), header)
            } else if position as nat + 4 > header.len() || position as nat + 4 > usize::MAX as nat {
                (Err(part2_jpip_cache_error(offset, crate::MalformedKind::Truncated)), header)
            } else {
                let length = (((header[position as int + 2] as u16) << 8) | header[position as int + 3] as u16) as nat;
                if length < 2 { (Err(part2_jpip_cache_error(offset, crate::MalformedKind::InvalidMarkerLength)), header) }
                else {
                    let end = position as nat + 2 + length;
                    if end > usize::MAX as nat { (Err(part2_jpip_range_overflow(offset)), header) }
                    else if end <= position as nat || end > header.len() {
                        (Err(part2_jpip_cache_error(offset, crate::MalformedKind::Truncated)), header)
                    } else if marker == 0xff52 {
                        if length < 7 { (Err(part2_jpip_cache_error(offset, crate::MalformedKind::InvalidCodingStyle)), header) }
                        else {
                            let patched = header.update(position as int + 6, ((layers >> 8) & 0xff) as u8)
                                .update(position as int + 7, (layers & 0xff) as u8);
                            part2_jpip_patch_cod_loop(patched, end as usize, layers, stop)
                        }
                    } else { part2_jpip_patch_cod_loop(header, end as usize, layers, stop) }
                }
            }
        }
    }
}

pub open spec fn part2_jpip_patch_cod(header: Seq<u8>, start: usize, layers: u16, stop: bool)
    -> Part2JpipHeaderResult {
    if start as nat > header.len() {
        (Err(part2_jpip_cache_error(start as u64, crate::MalformedKind::Truncated)), header)
    } else { part2_jpip_patch_cod_loop(header, start, layers, stop) }
}

pub open spec fn part2_jpip_patch_main(header: Seq<u8>, layers: u16) -> Part2JpipHeaderResult {
    if header.len() < 2 || header[0] != 0xff || header[1] != 0x4f {
        (Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure)), header)
    } else { part2_jpip_patch_cod(header, 2, layers, false) }
}

pub open spec fn part2_jpip_patch_tile(header: Seq<u8>, layers: u16) -> Part2JpipHeaderResult {
    if header.len() < 14 || header[0] != 0xff || header[1] != 0x90 || header[2] != 0
        || header[3] != 10 || header[10] != 0 || !(header[11] == 0 || header[11] == 1)
        || header[header.len() as int - 2] != 0xff || header[header.len() as int - 1] != 0x93 {
        (Err(part2_jpip_plan_invalid(0)), header)
    } else { part2_jpip_patch_cod(header, 0, layers, true) }
}

pub(crate) open spec fn part2_jpip_validate_precinct_layout(layout: Part1CompleteLayout, layers: u16)
    -> Result<(), crate::DecodeError> {
    match part2_selection_tile_count(layout.0.image_size.geometry) {
            Err(error) => Err(error),
            Ok(count) => if count != 1 || layout.4.len() != 1 {
                Err(part2_jpip_plan_invalid(0))
            } else {
                let tile = layout.4[0];
                if layout.0.coding_style.layers != layers
                    || !matches!(layout.0.coding_style.progression_order, crate::codestream::ProgressionOrder::Lrcp)
                    || !matches!(tile.coding_style.progression_order, crate::codestream::ProgressionOrder::Lrcp)
                    || layout.0.progression.len() != 0 || tile.progression_changes.len() != 0
                    || !matches!(tile.packet_lengths.source, Part1PacketLengthSource::None)
                    || !matches!(tile.packed_packet_headers.source, Part1PackedHeaderSource::None) {
                    Err(part2_jpip_plan_invalid(0))
                } else { Ok(()) }
            },
    }
}

pub(crate) open spec fn part2_jpip_validate_precinct_raw(bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits)
    -> Result<(), crate::DecodeError> {
    match part1_parse_layout(bytes, limits) {
        Err(error) => Err(error),
        Ok(layout) => part2_jpip_validate_precinct_layout(layout, layers),
    }
}

pub(crate) open spec fn part2_jpip_validate_precinct_cold_run(
    bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<()> {
    part2_jpip_snapshot_bind(part2_cold_parse(bytes, limits, 7, 0, events),
        |layout: Part1CompleteLayout, rest| Some((part2_jpip_validate_precinct_layout(layout, layers), rest)))
}

pub(crate) open spec fn part2_jpip_validate_precinct_cold_result(
    bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits, result: Result<(), crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_jpip_validate_precinct_cold_run(bytes, layers, limits, events), result)
}

pub(crate) proof fn part2_jpip_validate_precinct_cold_actual(
    bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits, parsed: Part1CompleteLayoutResult,
)
    requires part1_parse_layout_cold_result(bytes, limits, parsed),
    ensures part2_jpip_validate_precinct_cold_result(bytes, layers, limits, match parsed {
        Err(error) => Err(error), Ok(layout) => part2_jpip_validate_precinct_layout(layout, layers),
    }),
{
    let result = match parsed {
        Err(error) => Err(error), Ok(layout) => part2_jpip_validate_precinct_layout(layout, layers),
    };
    part2_cold_parse_then_actual(bytes, limits, 7, 0, parsed,
        |layout: Part1CompleteLayout| part2_jpip_validate_precinct_layout(layout, layers));
    part2_cold_framed_extensional(
        |events| part2_jpip_snapshot_bind(part2_cold_parse(bytes, limits, 7, 0, events),
            |layout: Part1CompleteLayout, rest| Some((part2_jpip_validate_precinct_layout(layout, layers), rest))),
        |events| part2_jpip_validate_precinct_cold_run(bytes, layers, limits, events), result);
}

pub(crate) proof fn part2_jpip_validate_precinct_cold_normal(
    bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits,
)
    ensures part2_jpip_validate_precinct_cold_result(
        bytes, layers, limits, part2_jpip_validate_precinct(bytes, layers, limits)),
{
    part1_parse_layout_cold_normal(bytes, limits);
    part2_jpip_validate_precinct_cold_actual(bytes, layers, limits, part1_parse_layout(bytes, limits));
    part2_jpip_validate_precinct_unfold(bytes, layers, limits);
}

pub(crate) open spec fn part2_jpip_transcode_pre_bytes(
    cache: Part2JpipCache, main: Seq<u8>, tile: Seq<u8>, packets: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError> {
    let length = tile.len() + packets.len();
    if length > usize::MAX as nat || length > u32::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else if tile.len() < 10 { Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart)) }
    else {
        let tile = tile.update(6, ((length as u32 >> 24) & 0xff) as u8)
            .update(7, ((length as u32 >> 16) & 0xff) as u8)
            .update(8, ((length as u32 >> 8) & 0xff) as u8)
            .update(9, (length as u32 & 0xff) as u8);
        let total = main.len() + tile.len() + packets.len() + 2;
        if total > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else if total > crate::limits::resource_input_byte_limit(&cache.0) as nat {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(&cache.0), actual: total as u64 })
        } else { Ok(main + tile + packets + seq![0xffu8, 0xd9u8]) }
    }
}

pub(crate) open spec fn part2_jpip_transcode_pre_payload(
    cache: Part2JpipCache, plan: Part2JpipPlan, end: usize, layers: u16,
) -> Result<Seq<u8>, crate::DecodeError> {
    match part2_jpip_cache_view(cache, plan.0) {
        Err(error) => Err(error),
        Ok(main) => match part2_jpip_cache_view(cache, plan.1) {
            Err(error) => Err(error),
            Ok(tile) => {
                let patched_main = part2_jpip_patch_main(main, layers);
                match patched_main.0 {
                    Err(error) => Err(error),
                    Ok(()) => {
                        let patched_tile = part2_jpip_patch_tile(tile, layers);
                        match patched_tile.0 {
                            Err(error) => Err(error),
                            Ok(()) => if end as nat > plan.2.len() { Err(part2_jpip_range_overflow(0)) }
                            else {
                                match part2_jpip_read_packets(cache, plan.2.subrange(0, end as int)) {
                                    Err(error) => Err(error),
                                    Ok(packets) => part2_jpip_transcode_pre_bytes(
                                        cache, patched_main.1, patched_tile.1, packets),
                                }
                            },
                        }
                    },
                }
            },
        },
    }
}

pub(crate) open spec fn part2_jpip_transcode_pre(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16,
) -> Result<Part2JpipTranscode, crate::DecodeError> {
    match part2_jpip_plan_packet_end(plan, layers) {
        Err(error) => Err(error),
        Ok(end) => match part2_jpip_precinct_availability(cache, plan, end) {
            Err(error) => Err(error),
            Ok(availability) => if availability.0 != crate::jpip::JpipAvailability::Available {
                Ok((layers, availability, None))
            } else {
                match part2_jpip_transcode_pre_payload(cache, plan, end, layers) {
                    Err(error) => Err(error), Ok(bytes) => Ok((layers, availability, Some(bytes))),
                }
            },
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_jpip_transcode_cold_run(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2JpipTranscode> {
    match part2_jpip_transcode_pre(cache, plan, layers) {
        Err(error) => Some((Err(error), events)),
        Ok(value) => match value.2 {
            None => Some((Ok(value), events)),
            Some(bytes) => part2_jpip_snapshot_bind(
                part2_jpip_validate_precinct_cold_run(bytes, layers, &cache.0, events),
                |_: (), tail| Some((Ok(value), tail))),
        },
    }
}

pub closed spec fn part2_jpip_transcode_cold_result(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16,
    result: Result<Part2JpipTranscode, crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events| part2_jpip_transcode_cold_run(cache, plan, layers, events), result)
}

pub(crate) proof fn part2_jpip_transcode_cold_frames(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16,
    result: Result<Part2JpipTranscode, crate::DecodeError>,
)
    requires part2_jpip_transcode_cold_result(cache, plan, layers, result),
    ensures part2_cold_framed(|events| part2_jpip_transcode_cold_run(cache, plan, layers, events), result),
{
    reveal(part2_jpip_transcode_cold_result);
}

pub(crate) proof fn part2_jpip_transcode_pre_equivalent(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16,
)
    ensures part2_jpip_transcode(cache, plan, layers) == match part2_jpip_transcode_pre(cache, plan, layers) {
        Err(error) => Err(error),
        Ok(value) => match value.2 {
            None => Ok(value),
            Some(bytes) => match part2_jpip_validate_precinct(bytes, layers, &cache.0) {
                Err(error) => Err(error), Ok(()) => Ok(value),
            },
        },
    },
{
}

pub(crate) proof fn part2_jpip_transcode_cold_normal(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16,
)
    ensures part2_jpip_transcode_cold_result(cache, plan, layers, part2_jpip_transcode(cache, plan, layers)),
{
    reveal(part2_jpip_transcode_cold_result);
    reveal(part2_jpip_transcode_cold_run);
    part2_jpip_transcode_pre_equivalent(cache, plan, layers);
    match part2_jpip_transcode_pre(cache, plan, layers) {
        Err(error) => { part2_cold_pure::<Part2JpipTranscode>(Err(error)); },
        Ok(value) => match value.2 {
            None => { part2_cold_pure(Ok(value)); },
            Some(bytes) => {
                let validated = part2_jpip_validate_precinct(bytes, layers, &cache.0);
                part2_jpip_validate_precinct_cold_normal(bytes, layers, &cache.0);
                if validated.is_ok() { part2_cold_pure(Ok(value)); }
                part2_cold_bind(
                    |events| part2_jpip_validate_precinct_cold_run(bytes, layers, &cache.0, events),
                    |_: (), tail| Some((Ok(value), tail)), validated, part2_jpip_transcode(cache, plan, layers));
            },
        },
    }
}

pub(crate) proof fn part2_jpip_transcode_validation_actual(
    cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16,
    availability: Part2JpipAvailabilityReport, bytes: Seq<u8>, validated: Result<(), crate::DecodeError>,
)
    requires part2_jpip_transcode_pre(cache, plan, layers) == Ok((layers, availability, Some(bytes))),
        part2_jpip_validate_precinct_cold_result(bytes, layers, &cache.0, validated),
    ensures part2_jpip_transcode_cold_result(cache, plan, layers, match validated {
        Err(error) => Err(error), Ok(()) => Ok((layers, availability, Some(bytes))),
    }),
{
    reveal(part2_jpip_transcode_cold_result);
    reveal(part2_jpip_transcode_cold_run);
    if validated.is_ok() { part2_cold_pure(Ok((layers, availability, Some(bytes)))); }
    part2_cold_bind(
        |events| part2_jpip_validate_precinct_cold_run(bytes, layers, &cache.0, events),
        |_: (), tail| Some((Ok((layers, availability, Some(bytes))), tail)), validated,
        match validated { Err(error) => Err(error), Ok(()) => Ok((layers, availability, Some(bytes))) });
}

pub closed spec fn part2_jpip_validate_precinct(bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits)
    -> Result<(), crate::DecodeError> {
    part2_jpip_validate_precinct_raw(bytes, layers, limits)
}

pub(crate) proof fn part2_jpip_validate_precinct_unfold(bytes: Seq<u8>, layers: u16, limits: &crate::ResourceLimits)
    ensures part2_jpip_validate_precinct(bytes, layers, limits) == part2_jpip_validate_precinct_raw(bytes, layers, limits),
{
}

pub open spec fn part2_jpip_transcode_bytes(
    cache: Part2JpipCache, main: Seq<u8>, tile: Seq<u8>, packets: Seq<u8>, layers: u16,
) -> Result<Seq<u8>, crate::DecodeError> {
    let length = tile.len() + packets.len();
    if length > usize::MAX as nat || length > u32::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else if tile.len() < 10 { Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart)) }
    else {
        let tile = tile.update(6, ((length as u32 >> 24) & 0xff) as u8)
            .update(7, ((length as u32 >> 16) & 0xff) as u8)
            .update(8, ((length as u32 >> 8) & 0xff) as u8)
            .update(9, (length as u32 & 0xff) as u8);
        let total = main.len() + tile.len() + packets.len() + 2;
        if total > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
        else if total > crate::limits::resource_input_byte_limit(&cache.0) as nat {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::InputBytes,
                limit: crate::limits::resource_input_byte_limit(&cache.0), actual: total as u64 })
        } else {
            let bytes = main + tile + packets + seq![0xffu8, 0xd9u8];
            match part2_jpip_validate_precinct(bytes, layers, &cache.0) {
                Err(error) => Err(error), Ok(()) => Ok(bytes),
            }
        }
    }
}

pub open spec fn part2_jpip_transcode_payload(
    cache: Part2JpipCache, plan: Part2JpipPlan, end: usize, layers: u16,
) -> Result<Seq<u8>, crate::DecodeError> {
    match part2_jpip_cache_view(cache, plan.0) {
        Err(error) => Err(error),
        Ok(main) => match part2_jpip_cache_view(cache, plan.1) {
            Err(error) => Err(error),
            Ok(tile) => {
                let patched_main = part2_jpip_patch_main(main, layers);
                match patched_main.0 {
                    Err(error) => Err(error),
                    Ok(()) => {
                        let patched_tile = part2_jpip_patch_tile(tile, layers);
                        match patched_tile.0 {
                            Err(error) => Err(error),
                            Ok(()) => if end as nat > plan.2.len() { Err(part2_jpip_range_overflow(0)) }
                            else {
                                match part2_jpip_read_packets(cache, plan.2.subrange(0, end as int)) {
                                    Err(error) => Err(error),
                                    Ok(packets) => part2_jpip_transcode_bytes(cache, patched_main.1, patched_tile.1, packets, layers),
                                }
                            },
                        }
                    },
                }
            },
        },
    }
}

pub open spec fn part2_jpip_transcode(cache: Part2JpipCache, plan: Part2JpipPlan, layers: u16)
    -> Result<Part2JpipTranscode, crate::DecodeError> {
    match part2_jpip_plan_packet_end(plan, layers) {
        Err(error) => Err(error),
        Ok(end) => match part2_jpip_precinct_availability(cache, plan, end) {
            Err(error) => Err(error),
            Ok(availability) => if availability.0 != crate::jpip::JpipAvailability::Available {
                Ok((layers, availability, None))
            } else {
                match part2_jpip_transcode_payload(cache, plan, end, layers) {
                    Err(error) => Err(error), Ok(bytes) => Ok((layers, availability, Some(bytes))),
                }
            },
        },
    }
}

}
