use super::{
    DecodeError, DecodeSelection, ImageSize, MalformedKind, SelectionError, TileSelection,
    ValidatedSelection, arithmetic_overflow,
};
#[cfg(verus_keep_ghost)]
use super::{
    codestream, selected_tiles_outcome, selection_region_outcome, validated_selection_outcome,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_tile_list_contains(tiles@, tile),
))]
pub(super) fn tile_list_contains(tiles: &[u16], tile: u16) -> Result<bool, DecodeError> {
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= tiles.len(),
            forall |i: int| 0 <= i < index ==> tiles@[i] != tile,
            decreases tiles.len() - index,
        )
    )]
    while index < tiles.len() {
        if *tiles.get(index).ok_or_else(arithmetic_overflow)? == tile {
            return Ok(true);
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(false)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_explicit_tile_prefix(explicit_tiles@, tile_count, explicit_tiles@.len()),
))]
pub(super) fn validate_explicit_tile_indices(
    explicit_tiles: &[u16],
    tile_count: u64,
) -> Result<(), DecodeError> {
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_explicit_tiles_empty(explicit_tiles@, tile_count); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= explicit_tiles.len(),
        crate::specs::part2_explicit_tile_prefix(explicit_tiles@, tile_count, index as nat) == Ok(()),
        decreases explicit_tiles.len() - index,
    ))]
    while index < explicit_tiles.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_explicit_tiles_step(explicit_tiles@, tile_count, index as nat);
            crate::proofs::production_impl::production_explicit_tiles_error_guard(explicit_tiles@, tile_count, index as nat + 1, explicit_tiles@.len());
        }
        let tile = *explicit_tiles.get(index).ok_or_else(arithmetic_overflow)?;
        if u64::from(tile) >= tile_count {
            return Err(DecodeError::InvalidSelection {
                reason: SelectionError::TileOutOfRange,
            });
        }
        let mut earlier = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant earlier <= index, index < explicit_tiles.len(),
            explicit_tiles@[index as int] == tile, (tile as u64) < tile_count,
            crate::specs::part2_explicit_tile_prefix(explicit_tiles@, tile_count, index as nat) == Ok(()),
            forall |i: int| 0 <= i < earlier ==> explicit_tiles@[i] != tile,
            decreases index - earlier,
        ))]
        while earlier < index {
            if explicit_tiles[earlier] == tile {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(explicit_tiles@.take(index as int)[earlier as int] == tile);
                    assert(explicit_tiles@.take(index as int).contains(tile));
                    crate::proofs::production_impl::production_explicit_tiles_step(explicit_tiles@, tile_count, index as nat);
                    crate::proofs::production_impl::production_explicit_tiles_error_guard(explicit_tiles@, tile_count, index as nat + 1, explicit_tiles@.len());
                }
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::DuplicateTile,
                });
            }
            earlier = earlier.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(!explicit_tiles@.take(index as int).contains(tile));
            crate::proofs::production_impl::production_explicit_tiles_step(explicit_tiles@, tile_count, index as nat);
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_rectangle_area(bounds),
))]
pub(super) fn selection_rectangle_area(bounds: (u32, u32, u32, u32)) -> Result<u32, DecodeError> {
    let error = DecodeError::InvalidSelection {
        reason: SelectionError::NonRectangularTileSet,
    };
    let rows = bounds
        .2
        .checked_sub(bounds.0)
        .ok_or(error)?
        .checked_add(1)
        .ok_or(error)?;
    let columns = bounds
        .3
        .checked_sub(bounds.1)
        .ok_or(error)?
        .checked_add(1)
        .ok_or(error)?;
    rows.checked_mul(columns).ok_or(error)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires bounds.0 <= bounds.2, bounds.1 <= bounds.3,
        bounds.2 < u32::MAX, bounds.3 < u32::MAX,
    ensures result == crate::specs::part2_rectangle_rows(explicit_tiles@, tiles_across, bounds,
        (bounds.2 as nat - bounds.0 as nat + 1) as nat),
))]
pub(super) fn validate_selection_rectangle_cells(
    explicit_tiles: &[u16],
    tiles_across: u32,
    bounds: (u32, u32, u32, u32),
) -> Result<(), DecodeError> {
    let mut row = bounds.0;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_rectangle_rows_empty(explicit_tiles@, tiles_across, bounds); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant bounds.0 <= bounds.2, bounds.1 <= bounds.3, bounds.2 < u32::MAX, bounds.3 < u32::MAX,
        bounds.0 <= row as int <= bounds.2 as int + 1,
        crate::specs::part2_rectangle_rows(explicit_tiles@, tiles_across, bounds, (row - bounds.0) as nat) == Ok(()),
        decreases bounds.2 as int + 1 - row as int,
    ))]
    while row <= bounds.2 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_rectangle_rows_step(explicit_tiles@, tiles_across, bounds, (row - bounds.0) as nat);
            crate::proofs::production_impl::production_rectangle_rows_error(explicit_tiles@, tiles_across, bounds,
                (row as nat - bounds.0 as nat + 1) as nat, (bounds.2 as nat - bounds.0 as nat + 1) as nat);
        }
        let mut column = bounds.1;
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_rectangle_columns_empty(explicit_tiles@, tiles_across, bounds, row); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant bounds.0 <= row <= bounds.2, bounds.1 <= bounds.3,
            bounds.2 < u32::MAX, bounds.3 < u32::MAX,
            bounds.1 <= column as int <= bounds.3 as int + 1,
            crate::specs::part2_rectangle_rows(explicit_tiles@, tiles_across, bounds, (row - bounds.0) as nat) == Ok(()),
            crate::specs::part2_rectangle_columns(explicit_tiles@, tiles_across, bounds, row, (column - bounds.1) as nat) == Ok(()),
            decreases bounds.3 as int + 1 - column as int,
        ))]
        while column <= bounds.3 {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_rectangle_columns_step(explicit_tiles@, tiles_across, bounds, row, (column - bounds.1) as nat);
                crate::proofs::production_impl::production_rectangle_columns_error(explicit_tiles@, tiles_across, bounds, row,
                    (column as nat - bounds.1 as nat + 1) as nat, (bounds.3 as nat - bounds.1 as nat + 1) as nat);
                crate::proofs::production_impl::production_rectangle_rows_step(explicit_tiles@, tiles_across, bounds, (row - bounds.0) as nat);
                crate::proofs::production_impl::production_rectangle_rows_error(explicit_tiles@, tiles_across, bounds,
                    (row as nat - bounds.0 as nat + 1) as nat, (bounds.2 as nat - bounds.0 as nat + 1) as nat);
            }
            let offset = row
                .checked_mul(tiles_across)
                .ok_or_else(arithmetic_overflow)?;
            let expected_index = offset.checked_add(column).ok_or_else(arithmetic_overflow)?;
            let expected_index = match u16::try_from(expected_index) {
                Ok(index) => index,
                Err(_) => return Err(arithmetic_overflow()),
            };
            if !tile_list_contains(explicit_tiles, expected_index)? {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::NonRectangularTileSet,
                });
            }
            column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_rectangle_rows_step(explicit_tiles@, tiles_across, bounds, (row - bounds.0) as nat); }
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires explicit_tiles.len() > 1, tiles_across > 0,
    ensures result == crate::specs::part2_validate_tile_rectangle(explicit_tiles@, tiles_across),
))]
pub(super) fn validate_selection_tile_rectangle(
    explicit_tiles: &[u16],
    tiles_across: u32,
) -> Result<(), DecodeError> {
    let first = u32::from(*explicit_tiles.first().ok_or_else(arithmetic_overflow)?);
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_unsigned_remainder_bound(first, tiles_across); }
    let mut first_row = first / tiles_across;
    let mut first_column = first % tiles_across;
    let mut last_row = first_row;
    let mut last_column = first_column;
    let mut bound_index = 1_usize;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_tile_box_first(explicit_tiles@, tiles_across); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= bound_index <= explicit_tiles.len(), explicit_tiles.len() > 1, tiles_across > 0,
        first_row <= last_row, first_column <= last_column, last_row <= u16::MAX, last_column <= u16::MAX,
        crate::specs::part2_tile_rectangle_prefix(explicit_tiles@, tiles_across, bound_index as nat)
            == (first_row, first_column, last_row, last_column),
        decreases explicit_tiles.len() - bound_index,
    ))]
    while bound_index < explicit_tiles.len() {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_tile_box_step(explicit_tiles@, tiles_across, bound_index as nat); }
        let current = u32::from(
            *explicit_tiles
                .get(bound_index)
                .ok_or_else(arithmetic_overflow)?,
        );
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_unsigned_remainder_bound(current, tiles_across); }
        let row = current / tiles_across;
        let column = current
            .checked_rem(tiles_across)
            .ok_or_else(arithmetic_overflow)?;
        first_row = first_row.min(row);
        first_column = first_column.min(column);
        last_row = last_row.max(row);
        last_column = last_column.max(column);
        bound_index = bound_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let bounds = (first_row, first_column, last_row, last_column);
    let expected = selection_rectangle_area(bounds)?;
    let expected = match usize::try_from(expected) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    if expected != explicit_tiles.len() {
        return Err(DecodeError::InvalidSelection {
            reason: SelectionError::NonRectangularTileSet,
        });
    }
    validate_selection_rectangle_cells(explicit_tiles, tiles_across, bounds)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures selection_region_outcome(result) == crate::specs::part2_selection_region(
        crate::codestream::selection_geometry_view(size), explicit_tiles@, requested, image_x1, image_y1,
    ),
))]
pub(super) fn selection_region(
    size: &ImageSize,
    explicit_tiles: &[u16],
    requested: Option<crate::ImageRegion>,
    image_x1: u32,
    image_y1: u32,
) -> Result<[u32; 4], DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::selection_geometry_known_fields(size); }
    match requested {
        Some(region) => {
            if region.width == 0 || region.height == 0 {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::EmptyRegion,
                });
            }
            let error = DecodeError::InvalidSelection {
                reason: SelectionError::RegionOutOfBounds,
            };
            let x1 = region.x.checked_add(region.width).ok_or(error)?;
            let y1 = region.y.checked_add(region.height).ok_or(error)?;
            if region.x < size.x_origin
                || region.y < size.y_origin
                || x1 > image_x1
                || y1 > image_y1
            {
                return Err(error);
            }
            Ok([region.x, region.y, x1, y1])
        }
        None if explicit_tiles.is_empty() => Ok([size.x_origin, size.y_origin, image_x1, image_y1]),
        None => {
            let mut x0 = image_x1;
            let mut y0 = image_y1;
            let mut x1 = size.x_origin;
            let mut y1 = size.y_origin;
            let mut tile_index = 0_usize;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_selected_region_empty(
                    crate::codestream::selection_geometry_view(size), explicit_tiles@, image_x1, image_y1);
            }
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant tile_index <= explicit_tiles.len(), explicit_tiles.len() > 0, requested.is_none(),
                crate::specs::part2_selected_region_prefix(crate::codestream::selection_geometry_view(size),
                    explicit_tiles@, image_x1, image_y1, tile_index as nat) == Ok((x0, y0, x1, y1)),
                decreases explicit_tiles.len() - tile_index,
            ))]
            while tile_index < explicit_tiles.len() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_selected_region_step(crate::codestream::selection_geometry_view(size),
                        explicit_tiles@, image_x1, image_y1, tile_index as nat);
                    crate::proofs::production_impl::production_selected_region_error(crate::codestream::selection_geometry_view(size),
                        explicit_tiles@, image_x1, image_y1, tile_index as nat + 1, explicit_tiles@.len());
                }
                let bounds = size.tile_bounds(
                    *explicit_tiles
                        .get(tile_index)
                        .ok_or_else(arithmetic_overflow)?,
                )?;
                x0 = x0.min(bounds.x0);
                y0 = y0.min(bounds.y0);
                x1 = x1.max(bounds.x1);
                y1 = y1.max(bounds.y1);
                tile_index = tile_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            Ok([x0, y0, x1, y1])
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_intersecting_tile_count(
        crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile_count,
    ),
        match result { Err(_) => true, Ok(count) =>
            crate::specs::part2_select_intersecting_tiles(crate::codestream::selection_geometry_view(size),
                explicit_tiles@, region@, tile_count).get_Ok_0().len() == count },
))]
fn intersecting_tile_count(
    size: &ImageSize,
    explicit_tiles: &[u16],
    region: [u32; 4],
    tile_count: u64,
) -> Result<usize, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::codestream::selection_geometry_known_fields(size); }
    let mut count = 0_usize;
    let mut tile = 0_u64;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_selected_tiles_empty(crate::codestream::selection_geometry_view(size), explicit_tiles@, region@); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tile <= tile_count, count as int <= tile, count <= u16::MAX as usize + 1,
            match crate::specs::part2_selected_tiles_prefix(crate::codestream::selection_geometry_view(size),
                explicit_tiles@, region@, tile as nat) {
                Ok(tiles) => tiles.len() == count, Err(_) => false,
            },
        decreases tile_count - tile,
    ))]
    while tile < tile_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_selected_tiles_step(crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile as nat);
            crate::proofs::production_impl::production_selected_tiles_error(crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile as nat + 1, tile_count as nat);
        }
        let tile_index = match u16::try_from(tile) {
            Ok(index) => index,
            Err(_) => return Err(arithmetic_overflow()),
        };
        let bounds = size.tile_bounds(tile_index)?;
        if bounds.x0 < region[2]
            && bounds.x1 > region[0]
            && bounds.y0 < region[3]
            && bounds.y1 > region[1]
        {
            if !explicit_tiles.is_empty() && !tile_list_contains(explicit_tiles, tile_index)? {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::RegionOutsideSelectedTiles,
                });
            }
            count = count.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        tile = tile.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    if count == 0 {
        return Err(DecodeError::InvalidSelection {
            reason: SelectionError::RegionOutsideSelectedTiles,
        });
    }
    Ok(count)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_select_tiles_result(crate::codestream::selection_geometry_view(size),
        explicit_tiles@, region@, tile_count, selected_tiles_outcome(result)),
        selected_tiles_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            selected_tiles_outcome(result) == crate::specs::part2_select_intersecting_tiles(
                crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile_count),
))]
pub(super) fn select_intersecting_tiles(
    size: &ImageSize,
    explicit_tiles: &[u16],
    region: [u32; 4],
    tile_count: u64,
) -> Result<Vec<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::codestream::selection_geometry_known_fields(size);
        crate::specs::part2_select_tiles_normal(crate::codestream::selection_geometry_view(size),
            explicit_tiles@, region@, tile_count);
    }
    let count = intersecting_tile_count(size, explicit_tiles, region, tile_count)?;
    let reserved = crate::allocation::empty_with_capacity(count);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_select_tiles_capacity_observed(crate::codestream::selection_geometry_view(size),
            explicit_tiles@, region@, tile_count, count,
            crate::allocation::inspection_capacity_outcome(reserved));
    }
    let mut tiles = reserved?;
    let mut tile = 0_u64;
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_selected_tiles_empty(crate::codestream::selection_geometry_view(size), explicit_tiles@, region@); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tile <= tile_count,
        crate::specs::part2_select_tiles_result(crate::codestream::selection_geometry_view(size),
            explicit_tiles@, region@, tile_count, crate::specs::part2_select_intersecting_tiles(
                crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile_count)),
        crate::specs::part2_selected_tiles_prefix(crate::codestream::selection_geometry_view(size),
            explicit_tiles@, region@, tile as nat) == Ok(tiles@),
        decreases tile_count - tile,
    ))]
    while tile < tile_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_selected_tiles_step(crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile as nat);
            crate::proofs::production_impl::production_selected_tiles_error(crate::codestream::selection_geometry_view(size), explicit_tiles@, region@, tile as nat + 1, tile_count as nat);
        }
        let tile_index = match u16::try_from(tile) {
            Ok(index) => index,
            Err(_) => return Err(arithmetic_overflow()),
        };
        let bounds = size.tile_bounds(tile_index)?;
        let intersects = bounds.x0 < region[2]
            && bounds.x1 > region[0]
            && bounds.y0 < region[3]
            && bounds.y1 > region[1];
        if intersects {
            if !explicit_tiles.is_empty() && !tile_list_contains(explicit_tiles, tile_index)? {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::RegionOutsideSelectedTiles,
                });
            }
            tiles.push(tile_index);
        }
        tile = tile.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    if tiles.is_empty() {
        return Err(DecodeError::InvalidSelection {
            reason: SelectionError::RegionOutsideSelectedTiles,
        });
    }
    Ok(tiles)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_explicit_selection_storage_result(
        crate::options::tile_selection_view(selection),selected_tiles_outcome(result)),
    selected_tiles_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
        selected_tiles_outcome(result) == crate::specs::part2_selection_explicit(crate::options::tile_selection_view(selection)),
))]
pub(super) fn explicit_tiles_from_selection(
    selection: &TileSelection,
) -> Result<Vec<u16>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_selection_explicit);
        reveal(crate::options::tile_selection_view);
        crate::specs::part2_explicit_selection_storage_normal(crate::options::tile_selection_view(selection));
    }
    match selection {
        TileSelection::All => {
            let tiles = Vec::new();
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(tiles@ =~= Seq::<u16>::empty());
                assert(crate::specs::part2_selection_explicit(crate::options::tile_selection_view(selection)) == Ok(tiles@));
            }
            Ok(tiles)
        }
        TileSelection::Index(index) => {
            let copied = crate::allocation::copy_values(&[*index]);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_explicit_selection_storage_observed(
                    crate::options::tile_selection_view(selection),crate::allocation::inspection_capacity_outcome(copied));
            }
            let tiles = copied?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(tiles@ =~= seq![*index]);
                assert(crate::specs::part2_selection_explicit(crate::options::tile_selection_view(selection)) == Ok(tiles@));
            }
            Ok(tiles)
        }
        TileSelection::Set(indices) => {
            if indices.is_empty() {
                return Err(DecodeError::InvalidSelection {
                    reason: SelectionError::EmptyTileSet,
                });
            }
            let copied = crate::allocation::copy_values(indices);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_explicit_selection_storage_observed(
                    crate::options::tile_selection_view(selection),crate::allocation::inspection_capacity_outcome(copied));
            }
            let copied = copied?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(copied@ == indices@);
                assert(crate::specs::part2_selection_explicit(crate::options::tile_selection_view(selection)) == Ok(copied@));
            }
            Ok(copied)
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_validate_selection_result(crate::codestream::selection_geometry_view(size),
        crate::options::decode_selection_view(selection), validated_selection_outcome(result)),
        validated_selection_outcome(result) != Err(DecodeError::AllocationFailed) ==>
            validated_selection_outcome(result) == crate::specs::part2_validate_selection(
                crate::codestream::selection_geometry_view(size), crate::options::decode_selection_view(selection)),
))]
pub(super) fn validate_selection(
    size: &ImageSize,
    selection: &DecodeSelection,
) -> Result<ValidatedSelection, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::codestream::selection_geometry_known_fields(size);
        reveal(crate::specs::part2_validate_selection);
        crate::specs::part2_validate_selection_normal(crate::codestream::selection_geometry_view(size),
            crate::options::decode_selection_view(selection));
    }
    let image_x1 = size
        .x_origin
        .checked_add(size.width)
        .ok_or_else(arithmetic_overflow)?;
    let image_y1 = size
        .y_origin
        .checked_add(size.height)
        .ok_or_else(arithmetic_overflow)?;
    let tile_count = size.tile_count()?;
    let tiles_across = size.tiles_across;
    if tiles_across == 0 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidImageGeometry,
        });
    }
    if tile_count > u64::from(u16::MAX) + 1 {
        return Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidImageGeometry,
        });
    }

    let copying = explicit_tiles_from_selection(selection.tile_selection());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=copying {crate::specs::part2_validate_selection_explicit_error(
            crate::codestream::selection_geometry_view(size),crate::options::decode_selection_view(selection),error);}
    }
    let explicit_tiles = copying?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part2_selection_explicit(crate::options::decode_selection_view(selection).0) == Ok(explicit_tiles@));
    }
    validate_explicit_tile_indices(&explicit_tiles, tile_count)?;
    if explicit_tiles.len() > 1 {
        validate_selection_tile_rectangle(&explicit_tiles, tiles_across)?;
    }

    let region = selection_region(
        size,
        &explicit_tiles,
        selection.region(),
        image_x1,
        image_y1,
    )?;
    let selected = select_intersecting_tiles(size, &explicit_tiles, region, tile_count);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_validate_selection_from_tiles(crate::codestream::selection_geometry_view(size),
            crate::options::decode_selection_view(selection), explicit_tiles@, region@, tile_count,
            selected_tiles_outcome(selected));
    }
    let tiles = selected?;
    Ok(ValidatedSelection {
        tiles,
        region,
        discard_levels: selection.discard_levels(),
    })
}
