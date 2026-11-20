use super::errors::{packet_arithmetic_overflow, packet_reader_error, packet_reader_limit};
use super::{
    DecodeError, MalformedKind, PacketGrid, PacketSpatialGrid, ProgressionOrder, Resource,
};
#[cfg(verus_keep_ghost)]
use super::{packet_grid_view, packet_spatial_grid_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl PacketGrid {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == (packet_grid_view(self).components, packet_grid_view(self).resolutions),
    ))]
    pub(crate) fn spatial_row_shape(&self) -> (u16, u8) {
        (self.components, self.resolutions)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures packet_grid_view(&result) == (crate::specs::Part1PacketGrid {
            spatial: Some(packet_spatial_grid_view(&spatial)), ..packet_grid_view(&self)
        }),
    ))]
    pub(crate) fn with_spatial(self, spatial: PacketSpatialGrid) -> Self {
        let mut grid = self;
        grid.spatial = Some(spatial);
        grid
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_position_count(packet_grid_view(grid), order),
))]
pub(super) fn packet_position_count(grid: &PacketGrid, order: ProgressionOrder) -> u64 {
    match order {
        ProgressionOrder::Lrcp | ProgressionOrder::Rlcp => {
            u64::from(grid.maximum_precincts_per_resolution)
        }
        _ => match &grid.spatial {
            Some(spatial) => spatial.positions,
            None => u64::from(grid.maximum_precincts_per_resolution),
        },
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_candidate_count(packet_grid_view(grid), order),
))]
pub(super) fn packet_candidate_count(
    grid: &PacketGrid,
    order: ProgressionOrder,
) -> Result<u64, DecodeError> {
    if matches!(order, ProgressionOrder::Lrcp | ProgressionOrder::Rlcp) || grid.spatial.is_none() {
        return Ok(grid.candidate_count);
    }
    let positions = packet_position_count(grid, order);
    let first = match u64::from(grid.layers).checked_mul(u64::from(grid.components)) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    let second = match first.checked_mul(u64::from(grid.resolutions)) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    let count = match second.checked_mul(positions) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    if count > grid.maximum_work_units {
        return Err(packet_reader_limit(
            Resource::WorkUnits,
            grid.maximum_work_units,
            count,
        ));
    }
    Ok(count)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_spatial_axis(position, first, origin, step, count),
))]
fn spatial_axis(position: u64, first: u64, origin: u64, step: u64, count: u32) -> Option<u64> {
    if count == 0 || step == 0 {
        return None;
    }
    if position == first {
        return Some(0);
    }
    let offset = position.checked_sub(origin)?;
    if offset % step != 0 {
        return None;
    }
    let index = offset / step;
    if index < u64::from(count) {
        Some(index)
    } else {
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_scan_axis(origin, step, index),
))]
fn scan_axis(origin: u32, step: u64, index: u64) -> Result<u64, DecodeError> {
    if index == 0 {
        return Ok(u64::from(origin));
    }
    if step == 0 {
        return Err(packet_arithmetic_overflow());
    }
    let digit = match (u64::from(origin) / step).checked_add(index) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    match digit.checked_mul(step) {
        Some(value) => Ok(value),
        None => Err(packet_arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_candidate_precinct(
        packet_grid_view(grid), order, component, resolution, position),
))]
pub(super) fn packet_candidate_precinct(
    grid: &PacketGrid,
    order: ProgressionOrder,
    component: u64,
    resolution: u64,
    position: u64,
) -> Result<u32, DecodeError> {
    if matches!(order, ProgressionOrder::Lrcp | ProgressionOrder::Rlcp) || grid.spatial.is_none() {
        return match u32::try_from(position) {
            Ok(value) => Ok(value),
            Err(_) => Err(packet_arithmetic_overflow()),
        };
    }
    let spatial = match &grid.spatial {
        Some(spatial) => spatial,
        None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
    };
    let product = match component.checked_mul(u64::from(grid.resolutions)) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    let row_index = match product.checked_add(resolution) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    let row_index = match usize::try_from(row_index) {
        Ok(value) => value,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    let row = match spatial.rows.get(row_index) {
        Some(row) => row,
        None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
    };
    if spatial.across == 0 {
        return Err(packet_arithmetic_overflow());
    }
    let x = scan_axis(spatial.x0, spatial.step_x, position % spatial.across)?;
    let y = scan_axis(spatial.y0, spatial.step_y, position / spatial.across)?;
    let Some(column) = spatial_axis(x, row.first_x, row.origin_x, row.step_x, row.across) else {
        return Ok(u32::MAX);
    };
    let Some(line) = spatial_axis(y, row.first_y, row.origin_y, row.step_y, row.down) else {
        return Ok(u32::MAX);
    };
    let product = match line.checked_mul(u64::from(row.across)) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    let precinct = match product.checked_add(column) {
        Some(value) => value,
        None => return Err(packet_arithmetic_overflow()),
    };
    match u32::try_from(precinct) {
        Ok(value) => Ok(value),
        Err(_) => Err(packet_arithmetic_overflow()),
    }
}
