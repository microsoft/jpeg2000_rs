use crate::ResourceLimits;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecodeOptions {
    limits: ResourceLimits,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn decode_options_limits<'a>(options: &'a DecodeOptions) -> &'a ResourceLimits {
        &options.limits
    }
}

impl DecodeOptions {
    pub const fn new(limits: ResourceLimits) -> Self {
        Self { limits }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == decode_options_limits(self),
    ))]
    pub const fn limits(&self) -> &ResourceLimits {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decode_options_limits); }
        &self.limits
    }
}

/// A half-open image-reference-grid rectangle.
///
/// `x` and `y` are absolute JPEG 2000 image-space coordinates (they include
/// the SIZ image origin), and the selected interval is
/// `[x, x + width) × [y, y + height)`.
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ImageRegion {
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
}

impl ImageRegion {
    pub const fn new(x: u32, y: u32, width: u32, height: u32) -> Self {
        Self {
            x,
            y,
            width,
            height,
        }
    }
}

#[derive(Clone, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub enum TileSelection {
    #[default]
    All,
    Index(u16),
    Set(Vec<u16>),
}

/// Spatial and resolution selection for the `*_selected` decode APIs.
///
/// `discard_levels` selects the native JPEG 2000 resolution obtained by
/// omitting that many highest DWT resolution levels. It is not a post-decode
/// resize operation.
///
/// Color-selected APIs retain any neighboring sampling context needed for
/// resampling before cropping to the requested output. Resource limits also
/// apply to that context, which can include adjacent tiles.
#[derive(Clone, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct DecodeSelection {
    tiles: TileSelection,
    region: Option<ImageRegion>,
    discard_levels: u8,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn tile_selection_view(tiles: &TileSelection) -> crate::specs::Part2TileSelection {
        match tiles {
            TileSelection::All => crate::specs::Part2TileSelection::All,
            TileSelection::Index(index) => crate::specs::Part2TileSelection::Index(*index),
            TileSelection::Set(indices) => crate::specs::Part2TileSelection::Set(indices@),
        }
    }

    pub closed spec fn decode_selection_view(selection: &DecodeSelection) -> crate::specs::Part2DecodeSelection {
        (tile_selection_view(&selection.tiles), selection.region, selection.discard_levels)
    }

    pub open spec fn decode_selection_value_view(selection: DecodeSelection) -> crate::specs::Part2DecodeSelection {
        decode_selection_view(&selection)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures decode_selection_value_view(result) == crate::specs::part2_selection_from_parts(tile_selection_view(&tiles), region, discard_levels),
))]
pub(crate) const fn selection_from_parts(
    tiles: TileSelection,
    region: Option<ImageRegion>,
    discard_levels: u8,
) -> DecodeSelection {
    DecodeSelection {
        tiles,
        region,
        discard_levels,
    }
}

impl DecodeSelection {
    pub const fn full_image() -> Self {
        selection_from_parts(TileSelection::All, None, 0)
    }

    pub const fn tile(tile_index: u16) -> Self {
        selection_from_parts(TileSelection::Index(tile_index), None, 0)
    }

    pub fn tiles(tile_indices: Vec<u16>) -> Self {
        selection_from_parts(TileSelection::Set(tile_indices), None, 0)
    }

    pub fn with_region(self, region: ImageRegion) -> Self {
        selection_from_parts(self.tiles, Some(region), self.discard_levels)
    }

    pub fn with_discard_levels(self, discard_levels: u8) -> Self {
        selection_from_parts(self.tiles, self.region, discard_levels)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tile_selection_view(result) == decode_selection_view(self).0,
    ))]
    pub const fn tile_selection(&self) -> &TileSelection {
        &self.tiles
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == decode_selection_view(self).1,
    ))]
    pub const fn region(&self) -> Option<ImageRegion> {
        self.region
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == decode_selection_view(self).2,
    ))]
    pub const fn discard_levels(&self) -> u8 {
        self.discard_levels
    }
}
