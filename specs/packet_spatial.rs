use super::*;
use vstd::prelude::*;

verus! {
pub struct Part1PacketSpatialGrid {
    pub rows: Seq<Part1PacketSpatialResolution>,
    pub x0: u32,
    pub y0: u32,
    pub step_x: u64,
    pub step_y: u64,
    pub across: u64,
    pub positions: u64,
}

pub struct Part1PacketSpatialResolution {
    pub first_x: u64,
    pub first_y: u64,
    pub origin_x: u64,
    pub origin_y: u64,
    pub step_x: u64,
    pub step_y: u64,
    pub across: u32,
    pub down: u32,
}

pub open spec fn part1_packet_is_spatial(order: crate::codestream::ProgressionOrder) -> bool {
    !matches!(order, crate::codestream::ProgressionOrder::Lrcp | crate::codestream::ProgressionOrder::Rlcp)
}

pub open spec fn part1_packet_position_count(grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder) -> u64 {
    if part1_packet_is_spatial(order) && grid.spatial.is_some() {
        grid.spatial.unwrap().positions
    } else { grid.maximum_precincts_per_resolution as u64 }
}

pub open spec fn part1_packet_candidate_count(grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder)
    -> Result<u64, crate::DecodeError>
{
    if !part1_packet_is_spatial(order) || grid.spatial.is_none() { Ok(grid.candidate_count) }
    else {
        let a = grid.layers as nat * grid.components as nat;
        let b = a * grid.resolutions as nat;
        let count = b * part1_packet_position_count(grid, order) as nat;
        if a > u64::MAX || b > u64::MAX || count > u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else if count > grid.maximum_work_units {
            Err(part1_packet_reader_limit(crate::Resource::WorkUnits, grid.maximum_work_units, count as u64))
        } else { Ok(count as u64) }
    }
}

pub open spec fn part1_packet_scan_axis(origin: u32, step: u64, index: u64) -> Result<u64, crate::DecodeError> {
    if index == 0 { Ok(origin as u64) }
    else if step == 0 { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else {
        let digit = origin as nat / step as nat + index as nat;
        if digit > u64::MAX || digit * step as nat > u64::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else { Ok((digit * step as nat) as u64) }
    }
}

pub open spec fn part1_packet_spatial_axis(position: u64, first: u64, origin: u64, step: u64, count: u32) -> Option<u64> {
    if count == 0 || step == 0 { None }
    else if position == first { Some(0) }
    else if position < origin || (position - origin) % (step as int) != 0 { None }
    else if (position - origin) / (step as int) < count { Some(((position - origin) / (step as int)) as u64) }
    else { None }
}

pub open spec fn part1_packet_candidate_precinct(
    grid: Part1PacketGrid, order: crate::codestream::ProgressionOrder,
    component: u64, resolution: u64, position: u64,
) -> Result<u32, crate::DecodeError> {
    if !part1_packet_is_spatial(order) || grid.spatial.is_none() {
        if position > u32::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
        else { Ok(position as u32) }
    } else {
        let spatial = grid.spatial.unwrap();
        let product = component as nat * grid.resolutions as nat;
        let index = product + resolution as nat;
        if product > u64::MAX || index > u64::MAX || index > usize::MAX {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else if index >= spatial.rows.len() {
            Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle))
        } else if spatial.across == 0 {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else {
            let row = spatial.rows[index as int];
            match part1_packet_scan_axis(spatial.x0, spatial.step_x, (position % spatial.across) as u64) {
                Err(error) => Err(error),
                Ok(x) => match part1_packet_scan_axis(spatial.y0, spatial.step_y, (position / spatial.across) as u64) {
                    Err(error) => Err(error),
                    Ok(y) => match part1_packet_spatial_axis(x, row.first_x, row.origin_x, row.step_x, row.across) {
                        None => Ok(u32::MAX),
                        Some(column) => match part1_packet_spatial_axis(y, row.first_y, row.origin_y, row.step_y, row.down) {
                            None => Ok(u32::MAX),
                            Some(line) => {
                                let product = line as nat * row.across as nat;
                                let precinct = product + column as nat;
                                if product > u64::MAX || precinct > u64::MAX || precinct > u32::MAX {
                                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                                } else { Ok(precinct as u32) }
                            },
                        },
                    },
                },
            }
        }
    }
}
}
