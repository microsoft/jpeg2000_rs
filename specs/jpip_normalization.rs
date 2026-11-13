//! Complete raw/cardinality, cached-header preparation and normalization Results.

use super::*;

verus! {

pub open spec fn part2_jpip_ceil_div(value: u64, divisor: u64)
    -> Result<u64, crate::DecodeError> {
    if divisor == 0 || value as int + divisor as int - 1 > u64::MAX as int {
        Err(part2_jpip_range_overflow(0))
    } else { Ok(((value as int + divisor as int - 1) / divisor as int) as u64) }
}

pub open spec fn part2_jpip_siz_payload(
    payload: Seq<u8>, position: usize, limits: &crate::ResourceLimits,
) -> Result<(u64, u16), crate::DecodeError> {
    if payload.len() < 36 {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidImageGeometry))
    } else {
        let x = part2_jpip_read_u32(payload, 2).get_Ok_0();
        let y = part2_jpip_read_u32(payload, 6).get_Ok_0();
        let width = part2_jpip_read_u32(payload, 18).get_Ok_0();
        let height = part2_jpip_read_u32(payload, 22).get_Ok_0();
        let tx = part2_jpip_read_u32(payload, 26).get_Ok_0();
        let ty = part2_jpip_read_u32(payload, 30).get_Ok_0();
        let components = part2_jpip_read_u16(payload, 34).get_Ok_0();
        if components == 0 || components > crate::limits::resource_component_limit(limits)
            || width == 0 || height == 0 || x <= tx || y <= ty {
            Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidImageGeometry))
        } else {
            match part2_jpip_ceil_div((x - tx) as u64, width as u64) {
                Err(error) => Err(error),
                Ok(nx) => match part2_jpip_ceil_div((y - ty) as u64, height as u64) {
                    Err(error) => Err(error),
                    Ok(ny) => {
                        let count = nx as nat * ny as nat;
                        if count > u64::MAX as nat { Err(part2_jpip_range_overflow(0)) }
                        else if count == 0 || count > crate::limits::resource_tile_limit(limits) as nat {
                            Err(crate::DecodeError::LimitExceeded {
                                resource: crate::Resource::Tiles,
                                limit: crate::limits::resource_tile_limit(limits) as u64,
                                actual: count as u64,
                            })
                        } else { Ok((count as u64, components)) }
                    },
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_siz_scan(
    input: Seq<u8>, position: usize, remaining: usize, limits: &crate::ResourceLimits,
) -> Result<(u64, u16), crate::DecodeError>
    decreases remaining,
{
    if position as nat >= input.len() {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure))
    } else if remaining == 0 {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidMarkerLength))
    } else {
        match part2_jpip_marker_segment(input, position) {
            Err(error) => Err(error),
            Ok((marker, start, end)) => if marker == 0xff51 {
                if start > end || end as nat > input.len() {
                    Err(part2_jpip_cache_error(0, crate::MalformedKind::Truncated))
                } else {
                    part2_jpip_siz_payload(input.subrange(start as int, end as int), position, limits)
                }
            } else { part2_jpip_siz_scan(input, end, (remaining - 1) as usize, limits) },
        }
    }
}

pub open spec fn part2_jpip_siz_cardinality(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<(u64, u16), crate::DecodeError> {
    if input.len() < 2 || input[0] != 0xff || input[1] != 0x4f {
        Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure))
    } else { part2_jpip_siz_scan(input, 2, input.len() as usize, limits) }
}

pub type Part2JpipAutomaticHeaders = (Seq<u8>, Seq<Seq<u8>>, u64, u16);

pub enum Part2JpipAutomaticHeaderEvent {
    Capacity { site: u8, elements: usize, succeeded: bool },
    Main { calls: Seq<Part2JpipStorageEvent> },
}

pub open spec fn part2_jpip_automatic_headers_finish(
    result: Result<Part2JpipAutomaticHeaders, crate::DecodeError>,
    events: Seq<Part2JpipAutomaticHeaderEvent>,
) -> Option<Result<Part2JpipAutomaticHeaders, crate::DecodeError>> {
    if events.len() == 0 { Some(result) } else { None }
}

pub open spec fn part2_jpip_header_capacity(
    events: Seq<Part2JpipAutomaticHeaderEvent>, site: u8, elements: usize,
) -> Option<bool> {
    if events.len() == 0 { None } else {
        match events[0] {
            Part2JpipAutomaticHeaderEvent::Capacity { site: actual, elements: count, succeeded } =>
                if actual == site && count == elements { Some(succeeded) } else { None },
            _ => None,
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_automatic_raw_tiles(
    cache: Part2JpipCache, stream: u64, count: u64, tile: nat, output: Seq<Seq<u8>>,
) -> Result<Seq<Seq<u8>>, crate::DecodeError>
    decreases count - tile,
{
    if tile >= count { Ok(output) } else {
        match part2_jpip_cache_view(cache, (2u64, crate::jpip::DatabinClass::TileHeader, stream, tile as u64)) {
            Err(error) => Err(error),
            Ok(bytes) => part2_jpip_automatic_raw_tiles(cache, stream, count, tile + 1, output.push(bytes)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_automatic_first_tiles(
    tiles: Seq<Seq<u8>>, index: nat, output: Seq<Seq<u8>>,
) -> Result<Seq<Seq<u8>>, crate::DecodeError>
    decreases if index < tiles.len() { tiles.len() - index } else { 0 },
{
    if index >= tiles.len() { Ok(output) }
    else if index > u16::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else {
        match part2_jpip_normalize_automatic_tile_headers(tiles[index as int], index as u16) {
            Err(error) => Err(error),
            Ok(headers) => if headers.len() == 0 {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::MissingRequiredStructure))
            } else { part2_jpip_automatic_first_tiles(tiles, index + 1, output.push(headers[0])) },
        }
    }
}

pub open spec fn part2_jpip_automatic_headers_normalized(
    main: Seq<u8>, tiles: Seq<Seq<u8>>, count: u64, components: u16,
    events: Seq<Part2JpipAutomaticHeaderEvent>,
) -> Option<Result<Part2JpipAutomaticHeaders, crate::DecodeError>> {
    match part2_jpip_header_capacity(events, 1, tiles.len() as usize) {
        None => None,
        Some(false) => part2_jpip_automatic_headers_finish(
            Err(crate::DecodeError::AllocationFailed), events.drop_first()),
        Some(true) => match part2_jpip_automatic_first_tiles(tiles, 0, Seq::empty()) {
            Err(error) => part2_jpip_automatic_headers_finish(Err(error), events.drop_first()),
            Ok(normalized) => part2_jpip_automatic_headers_finish(
                Ok((main, normalized, count, components)), events.drop_first()),
        },
    }
}

pub open spec fn part2_jpip_automatic_headers_bins(
    main: Seq<u8>, bins: Result<Seq<Seq<u8>>, crate::DecodeError>, count: u64, components: u16,
    events: Seq<Part2JpipAutomaticHeaderEvent>,
) -> Option<Result<Part2JpipAutomaticHeaders, crate::DecodeError>> {
    match bins {
        Err(error) => part2_jpip_automatic_headers_finish(Err(error), events),
        Ok(tiles) => if events.len() == 0 { None } else {
            match events[0] {
                Part2JpipAutomaticHeaderEvent::Main { calls } =>
                    match part2_jpip_normalize_main_header(main, calls) {
                        None => None,
                        Some(Err(error)) => part2_jpip_automatic_headers_finish(Err(error), events.drop_first()),
                        Some(Ok(normalized)) => part2_jpip_automatic_headers_normalized(
                            normalized, tiles, count, components, events.drop_first()),
                    },
                _ => None,
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_automatic_headers(
    cache: Part2JpipCache, stream: u64, events: Seq<Part2JpipAutomaticHeaderEvent>,
) -> Option<Result<Part2JpipAutomaticHeaders, crate::DecodeError>> {
    match part2_jpip_cache_view(cache, (6u64, crate::jpip::DatabinClass::MainHeader, stream, 0u64)) {
        Err(error) => part2_jpip_automatic_headers_finish(Err(error), events),
        Ok(main) => match part2_jpip_siz_cardinality(main, &cache.0) {
            Err(error) => part2_jpip_automatic_headers_finish(Err(error), events),
            Ok((count, components)) => if count > usize::MAX as u64 {
                part2_jpip_automatic_headers_finish(Err(part2_jpip_range_overflow(0)), events)
            } else {
                match part2_jpip_header_capacity(events, 0, count as usize) {
                    None => None,
                    Some(false) => part2_jpip_automatic_headers_finish(
                        Err(crate::DecodeError::AllocationFailed), events.drop_first()),
                    Some(true) => part2_jpip_automatic_headers_bins(main,
                        part2_jpip_automatic_raw_tiles(cache, stream, count, 0, Seq::empty()),
                        count, components, events.drop_first()),
                }
            },
        },
    }
}

pub open spec fn part2_jpip_automatic_headers_result(
    cache: Part2JpipCache, stream: u64, result: Result<Part2JpipAutomaticHeaders, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part2JpipAutomaticHeaderEvent>|
        part2_jpip_automatic_headers(cache, stream, events) == Some(result)
}

/// Operation (0: byte-vector capacity, 1: byte extension), old length,
/// requested elements/additional bytes, and observed reservation success.
/// Physical capacity and allocator availability retain the existing vstd boundary.
pub type Part2JpipStorageEvent = (u8, usize, usize, bool);

pub open spec fn part2_jpip_storage_event(
    events: Seq<Part2JpipStorageEvent>, operation: u8, length: usize, requested: usize,
) -> Option<bool> {
    if events.len() == 0 || events[0].0 != operation
        || events[0].1 != length || events[0].2 != requested {
        None
    } else { Some(events[0].3) }
}

pub open spec fn part2_jpip_main_header_finish(
    result: Result<Seq<u8>, crate::DecodeError>, events: Seq<Part2JpipStorageEvent>,
) -> Option<Result<Seq<u8>, crate::DecodeError>> {
    if events.len() == 0 { Some(result) } else { None }
}

#[verifier::opaque]
pub open spec fn part2_jpip_main_header_scan(
    input: Seq<u8>, position: usize, remaining: usize, output: Seq<u8>,
    events: Seq<Part2JpipStorageEvent>,
) -> Option<Result<Seq<u8>, crate::DecodeError>>
    decreases remaining,
{
    if position as nat >= input.len() {
        part2_jpip_main_header_finish(Ok(output), events)
    } else if remaining == 0 {
        part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
            position as u64, crate::MalformedKind::InvalidMarkerLength)), events)
    } else {
        match part2_jpip_marker_segment(input, position) {
            Err(error) => part2_jpip_main_header_finish(Err(error), events),
            Ok((marker, _, end)) => if marker == 0xff90 || marker == 0xff93 || marker == 0xffd9 {
                part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
                    position as u64, crate::MalformedKind::InvalidMarkerOrder)), events)
            } else if part9_reframed_marker_removed(marker as nat, false) {
                part2_jpip_main_header_scan(input, end, (remaining - 1) as usize, output, events)
            } else if position > end || end as nat > input.len() {
                part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
                    position as u64, crate::MalformedKind::Truncated)), events)
            } else {
                let bytes = input.subrange(position as int, end as int);
                match part2_jpip_storage_event(events, 1, output.len() as usize, bytes.len() as usize) {
                    None => None,
                    Some(false) => part2_jpip_main_header_finish(
                        Err(crate::DecodeError::AllocationFailed), events.drop_first()),
                    Some(true) => part2_jpip_main_header_scan(input, end, (remaining - 1) as usize,
                        output + bytes, events.drop_first()),
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_normalize_main_header(
    input: Seq<u8>, events: Seq<Part2JpipStorageEvent>,
) -> Option<Result<Seq<u8>, crate::DecodeError>> {
    if input.len() < 2 || input[0] != 0xff || input[1] != 0x4f {
        part2_jpip_main_header_finish(Err(part2_jpip_cache_error(
            0, crate::MalformedKind::MissingRequiredStructure)), events)
    } else {
        match part2_jpip_storage_event(events, 0, 0, 2) {
            None => None,
            Some(false) => part2_jpip_main_header_finish(
                Err(crate::DecodeError::AllocationFailed), events.drop_first()),
            Some(true) => match part2_jpip_storage_event(events.drop_first(), 1, 0, 2) {
                None => None,
                Some(false) => part2_jpip_main_header_finish(
                    Err(crate::DecodeError::AllocationFailed), events.drop_first().drop_first()),
                Some(true) => part2_jpip_main_header_scan(input, 2, input.len() as usize,
                    seq![0xffu8, 0x4fu8], events.drop_first().drop_first()),
            },
        }
    }
}

pub open spec fn part2_jpip_main_header_result(
    input: Seq<u8>, result: Result<Seq<u8>, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part2JpipStorageEvent>|
        part2_jpip_normalize_main_header(input, events) == Some(result)
}

#[verifier::opaque]
pub open spec fn part2_jpip_normalized_header_scan(
    source: Seq<u8>, position: usize, remaining: usize, output: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases remaining,
{
    if position as nat >= source.len() {
        if position as nat != source.len() {
            Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::MissingRequiredStructure))
        } else { Ok(output + seq![0xffu8, 0x93u8]) }
    } else if remaining == 0 {
        Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::InvalidMarkerLength))
    } else if position as nat + 2 <= source.len()
        && source[position as int] == 0xff && source[position as int + 1] == 0x93 {
        let end = position as nat + 2;
        if end > usize::MAX as nat { Err(part2_jpip_range_overflow(position as u64)) }
        else if end != source.len() {
            Err(part2_jpip_cache_error(end as u64, crate::MalformedKind::MissingRequiredStructure))
        } else { Ok(output + seq![0xffu8, 0x93u8]) }
    } else {
        match part2_jpip_marker_segment(source, position) {
            Err(error) => Err(error),
            Ok((marker, _, end)) => if position > end || end as nat > source.len() {
                Err(part2_jpip_cache_error(position as u64, crate::MalformedKind::Truncated))
            } else {
                part2_jpip_normalized_header_scan(source, end, (remaining - 1) as usize,
                    if part9_reframed_marker_removed(marker as nat, true) { output }
                    else { output + source.subrange(position as int, end as int) })
            },
        }
    }
}

pub open spec fn part2_jpip_normalized_header_after_start(
    source: Seq<u8>, tile: u16, index: usize, count: u8, start: usize,
) -> Result<Seq<u8>, crate::DecodeError> {
    if index > u8::MAX as usize { Err(part2_jpip_range_overflow(0)) }
    else {
        part2_jpip_normalized_header_scan(source, start, source.len() as usize,
            seq![0xffu8, 0x90u8, 0u8, 10u8, ((tile >> 8) & 0xff) as u8,
                (tile & 0xff) as u8, 0u8, 0u8, 0u8, 0u8, index as u8, count])
    }
}

pub open spec fn part2_jpip_normalize_tile_header(
    source: Seq<u8>, tile: u16, index: usize, count: u8,
) -> Result<Seq<u8>, crate::DecodeError> {
    if source.len() >= 2 && source[0] == 0xff && source[1] == 0x90 {
        match part2_jpip_marker_segment(source, 0) {
            Err(error) => Err(error),
            Ok((marker, _, end)) => if marker != 0xff90 || end != 12 {
                Err(part2_jpip_cache_error(0, crate::MalformedKind::InvalidTilePart))
            } else { part2_jpip_normalized_header_after_start(source, tile, index, count, end) },
        }
    } else { part2_jpip_normalized_header_after_start(source, tile, index, count, 0) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_normalized_header_entries(
    entries: Seq<Part2JpipTransition>, tile: u16, position: nat, output: Seq<Seq<u8>>,
) -> Result<Seq<Seq<u8>>, crate::DecodeError>
    decreases if position < entries.len() { entries.len() - position } else { 0 },
{
    if position >= entries.len() { Ok(output) }
    else {
        match part2_jpip_normalize_tile_header(entries[position as int].5, tile,
            position as usize, entries.len() as u8) {
            Err(error) => Err(error),
            Ok(header) => part2_jpip_normalized_header_entries(entries, tile, position + 1, output.push(header)),
        }
    }
}

pub open spec fn part2_jpip_normalize_automatic_tile_headers(input: Seq<u8>, tile: u16)
    -> Result<Seq<Seq<u8>>, crate::DecodeError> {
    match part2_jpip_parse_transitions(input, tile) {
        Err(error) => Err(error),
        Ok(entries) => if entries.len() > u8::MAX as nat { Err(part2_jpip_range_overflow(0)) }
            else { part2_jpip_normalized_header_entries(entries, tile, 0, Seq::empty()) },
    }
}

}
