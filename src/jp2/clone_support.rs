//! Shared executing metadata-clone producers used by native Clone and Verus.

use super::{ColorSpecification, Jp2Header, Palette};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::full_color_specification_view(&result)
        == crate::specs::part2_color_specification_clone(super::full_color_specification_view(source)),
))]
pub(super) fn color_specification_clone(source: &ColorSpecification) -> ColorSpecification {
    ColorSpecification {
        method: Clone::clone(&source.method),
        precedence: Clone::clone(&source.precedence),
        approximation: Clone::clone(&source.approximation),
        icc_profile: Clone::clone(&source.icc_profile),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::palette_view(&result) == crate::specs::part2_owned_palette_clone(super::palette_view(source)),
))]
pub(super) fn palette_clone(source: &Palette) -> Palette {
    Palette {
        entries: Clone::clone(&source.entries),
        columns: Clone::clone(&source.columns),
        values: Clone::clone(&source.values),
    }
}

#[allow(
    clippy::manual_map,
    reason = "Explicit cases route the original optional-Palette clone through its checked native producer"
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::optional_palette_view(&result)
        == crate::specs::part2_optional_palette_clone(super::optional_palette_view(source)),
))]
pub(super) fn optional_palette_clone(source: &Option<Palette>) -> Option<Palette> {
    match source {
        None => None,
        Some(palette) => Some(palette_clone(palette)),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::raw_jp2_header_view(&result) == crate::specs::part2_jp2_header_clone(super::raw_jp2_header_view(source)),
))]
pub(super) fn jp2_header_clone(source: &Jp2Header) -> Jp2Header {
    Jp2Header {
        image: Clone::clone(&source.image),
        color: color_specification_clone(&source.color),
        nested_box_count: Clone::clone(&source.nested_box_count),
        palette_entries: Clone::clone(&source.palette_entries),
        palette_columns: Clone::clone(&source.palette_columns),
        component_mapping_entries: Clone::clone(&source.component_mapping_entries),
        channel_definitions: Clone::clone(&source.channel_definitions),
        palette: optional_palette_clone(&source.palette),
        component_mappings: Clone::clone(&source.component_mappings),
        channel_definition_records: Clone::clone(&source.channel_definition_records),
        capture_resolution: Clone::clone(&source.capture_resolution),
        display_resolution: Clone::clone(&source.display_resolution),
    }
}
