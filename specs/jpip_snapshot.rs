//! Automatic snapshot assembly from actual packet state and cache metadata.

use super::*;

verus! {

pub type Part2JpipAutomaticSnapshot = (Seq<u8>, u16, u16, Seq<Part2JpipMissing>);
pub type Part2JpipAutomaticSnapshotResult = (Option<Part2JpipAutomaticSnapshot>, Seq<Part2JpipMissing>);
pub type Part2JpipAutomaticTiles = Seq<Seq<Part2JpipAutomaticTilePart>>;

#[verifier::opaque]
pub open spec fn part2_jpip_snapshot_available(
    tiles: Part2JpipAutomaticTiles, tile: nat, part: nat, packet: nat, before: u16,
) -> u16
    decreases if tile < tiles.len() { tiles.len() - tile } else { 0 },
        if tile < tiles.len() && part < tiles[tile as int].len() {
            tiles[tile as int].len() - part } else { 0 },
        if tile < tiles.len() && part < tiles[tile as int].len()
            && packet < tiles[tile as int][part as int].1.len() {
            tiles[tile as int][part as int].1.len() - packet } else { 0 },
{
    if tile >= tiles.len() { before }
    else if part >= tiles[tile as int].len() {
        part2_jpip_snapshot_available(tiles, tile + 1, 0, 0, before)
    } else if packet >= tiles[tile as int][part as int].1.len() {
        part2_jpip_snapshot_available(tiles, tile, part + 1, 0, before)
    } else {
        let value = tiles[tile as int][part as int].1[packet as int];
        part2_jpip_snapshot_available(tiles, tile, part, packet + 1,
            if value.3 && value.1.is_none() && value.5 < before { value.5 } else { before })
    }
}

pub open spec fn part2_jpip_snapshot_missing_packet(
    cache: Part2JpipCache, packet: Part2JpipAutomaticPacket, available: u16,
    before: Seq<Part2JpipMissing>,
) -> Seq<Part2JpipMissing> {
    if packet.3 && packet.5 == available && packet.1.is_none()
        && !(exists|index: int| 0 <= index < before.len()
            && part2_jpip_identity(before[index].0, packet.0)) {
        let length = match part2_jpip_cache_status(cache, packet.0) {
            Some(status) => match status.0 {
                Some(length) => Some(if length > packet.2 { (length - packet.2) as u64 } else { 1u64 }),
                None => None,
            },
            None => None,
        };
        before.push((packet.0, packet.2, length))
    } else { before }
}

#[verifier::opaque]
pub open spec fn part2_jpip_snapshot_missing(
    cache: Part2JpipCache, tiles: Part2JpipAutomaticTiles, available: u16,
    tile: nat, part: nat, packet: nat, before: Seq<Part2JpipMissing>,
) -> Seq<Part2JpipMissing>
    decreases if tile < tiles.len() { tiles.len() - tile } else { 0 },
        if tile < tiles.len() && part < tiles[tile as int].len() {
            tiles[tile as int].len() - part } else { 0 },
        if tile < tiles.len() && part < tiles[tile as int].len()
            && packet < tiles[tile as int][part as int].1.len() {
            tiles[tile as int][part as int].1.len() - packet } else { 0 },
{
    if tile >= tiles.len() { before }
    else if part >= tiles[tile as int].len() {
        part2_jpip_snapshot_missing(cache, tiles, available, tile + 1, 0, 0, before)
    } else if packet >= tiles[tile as int][part as int].1.len() {
        part2_jpip_snapshot_missing(cache, tiles, available, tile, part + 1, 0, before)
    } else {
        part2_jpip_snapshot_missing(cache, tiles, available, tile, part, packet + 1,
            part2_jpip_snapshot_missing_packet(cache,
                tiles[tile as int][part as int].1[packet as int], available, before))
    }
}

pub open spec fn part2_jpip_snapshot_emit_packet(
    before: Seq<u8>, packet: Part2JpipAutomaticPacket, available: u16, sop: bool, eph: bool,
) -> Result<Seq<u8>, crate::DecodeError> {
    if packet.3 && packet.5 < available {
        match packet.1 {
            None => Err(part2_jpip_cache_error(packet.2, crate::MalformedKind::MissingRequiredStructure)),
            Some(bytes) => Ok(before + bytes),
        }
    } else { Ok(before + part2_jpip_empty_packet_bytes(sop, eph, packet.4)) }
}

#[verifier::opaque]
pub open spec fn part2_jpip_snapshot_emit_packets(
    part: Part2JpipAutomaticTilePart, available: u16, packet: nat, before: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if packet < part.1.len() { part.1.len() - packet } else { 0 },
{
    if packet >= part.1.len() { Ok(before) }
    else {
        match part2_jpip_snapshot_emit_packet(before, part.1[packet as int], available, part.2, part.3) {
            Err(error) => Err(error),
            Ok(next) => part2_jpip_snapshot_emit_packets(part, available, packet + 1, next),
        }
    }
}

pub open spec fn part2_jpip_snapshot_patch_part(before: Seq<u8>, start: usize)
    -> Result<Seq<u8>, crate::DecodeError> {
    if before.len() < start as nat || before.len() - start as nat > u32::MAX as nat {
        Err(part2_jpip_range_overflow(0))
    } else if start as nat + 6 > usize::MAX as nat { Err(part2_jpip_range_overflow(0)) }
    else {
        let written = part2_jpip_write_u32(before, (start as nat + 6) as usize,
            (before.len() - start as nat) as u32);
        match written.0 { Err(error) => Err(error), Ok(()) => Ok(written.1) }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_snapshot_emit_parts(
    parts: Seq<Part2JpipAutomaticTilePart>, available: u16, part: nat, before: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if part < parts.len() { parts.len() - part } else { 0 },
{
    if part >= parts.len() { Ok(before) }
    else {
        let emitted = part2_jpip_emit_part_phase(before, parts[part as int], available);
        match emitted.0 {
            Err(error) => Err(error),
            Ok(()) => part2_jpip_snapshot_emit_parts(parts, available, part + 1, emitted.1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_snapshot_emit_tiles(
    tiles: Part2JpipAutomaticTiles, available: u16, tile: nat, before: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if tile < tiles.len() { tiles.len() - tile } else { 0 },
{
    if tile >= tiles.len() { Ok(before) }
    else {
        match part2_jpip_snapshot_emit_parts(tiles[tile as int], available, 0, before) {
            Err(error) => Err(error),
            Ok(next) => part2_jpip_snapshot_emit_tiles(tiles, available, tile + 1, next),
        }
    }
}

pub open spec fn part2_jpip_snapshot_ready(
    cache: Part2JpipCache, tiles: Part2JpipAutomaticTiles, main: Seq<u8>, maximum: u16,
    limits: &crate::ResourceLimits,
) -> Result<Part2JpipAutomaticSnapshotResult, crate::DecodeError> {
    let available = part2_jpip_snapshot_available(tiles, 0, 0, 0, maximum);
    let missing = part2_jpip_snapshot_missing(cache, tiles, available, 0, 0, 0, Seq::empty());
    if available == 0 { Ok((Some((Seq::empty(), 0, maximum, missing)), Seq::empty())) }
    else {
        match part2_jpip_snapshot_emit_tiles(tiles, available, 0, main) {
            Err(error) => Err(error),
            Ok(emitted) => match part2_jpip_template_finish(emitted, limits) {
                Err(error) => Err(error),
                Ok(bytes) => match part1_parse_layout(bytes, limits) {
                    Err(error) => Err(error),
                    Ok(_) => Ok((Some((bytes, available, maximum, missing)), Seq::empty())),
                },
            },
        }
    }
}

}
