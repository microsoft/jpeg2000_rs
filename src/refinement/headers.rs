#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part1_marker_value(high, low),)
)]
pub(crate) const fn marker_value(high: u8, low: u8) -> u16 {
    ((high as u16) << 8) | (low as u16)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part1_parser_progress(previous, current, limit),
    )
)]
pub(crate) const fn parser_progress(previous: usize, current: usize, limit: usize) -> bool {
    previous < current && current <= limit
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part1_main_header_boundary(marker),)
)]
pub(crate) const fn main_header_boundary(marker: u16) -> bool {
    marker == 0xff4f || marker == 0xff93 || marker == 0xffd9
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part1_tile_header_boundary(marker),)
)]
pub(crate) const fn tile_header_boundary(marker: u16) -> bool {
    marker == 0xff4f || marker == 0xff51 || marker == 0xff90 || marker == 0xffd9
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part1_exact_consumption(consumed, expected),)
)]
pub(crate) const fn exact_consumption(consumed: usize, expected: usize) -> bool {
    consumed == expected
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part2_tlm_tile_index_bytes(style),)
)]
pub(crate) const fn tlm_tile_index_bytes(style: u8) -> usize {
    ((style >> 4) & 3) as usize
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part2_tlm_length_bytes(style),)
)]
pub(crate) const fn tlm_length_bytes(style: u8) -> usize {
    if style & 0x40 == 0 { 2 } else { 4 }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part2_crg_payload_bytes(components),)
)]
pub(crate) const fn crg_payload_bytes(components: u16) -> usize {
    components as usize * 4
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires elements <= usize::MAX - 3,
        ensures returns crate::specs::part2_packed_two_bit_bytes(elements),
    )
)]
#[allow(clippy::manual_div_ceil)]
pub(crate) const fn packed_two_bit_bytes(elements: usize) -> usize {
    (elements + 3) / 4
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires slot < 4,
        ensures returns crate::specs::part2_dfs_direction_code(byte, slot),
    )
)]
pub(crate) const fn dfs_direction_code(byte: u8, slot: u8) -> u8 {
    (byte >> (6 - 2 * slot)) & 3
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part2_cbd_precision(encoded),)
)]
pub(crate) const fn cbd_precision(encoded: u8) -> u8 {
    ((encoded & 0x7f) as u16 + 1) as u8
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part2_cbd_signed(encoded),)
)]
pub(crate) const fn cbd_signed(encoded: u8) -> bool {
    encoded & 0x80 != 0
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part2_palette_coordinates_valid(
            entry,
            entries,
            column,
            columns,
        ),
    )
)]
pub(crate) const fn palette_coordinates_valid(
    entry: u16,
    entries: u16,
    column: u8,
    columns: u8,
) -> bool {
    entry < entries && column < columns
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part2_component_mapping_valid(
            component,
            components,
            mapping_type,
            palette_column,
            palette_columns,
        ),
    )
)]
pub(crate) const fn component_mapping_valid(
    component: u16,
    components: u16,
    mapping_type: u8,
    palette_column: u8,
    palette_columns: u8,
) -> bool {
    component < components
        && ((mapping_type == 0 && palette_column == 0)
            || (mapping_type == 1 && palette_columns > 0 && palette_column < palette_columns))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part2_channel_definition_valid(
            channel,
            channel_type,
            _association,
            output_channels,
        ),
    )
)]
pub(crate) const fn channel_definition_valid(
    channel: u16,
    channel_type: u16,
    _association: u16,
    output_channels: u16,
) -> bool {
    // Associations identify colors, not physical channel slots.
    channel < output_channels && matches!(channel_type, 0 | 1 | 2 | 0xffff)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part2_first_override_allowed(already_overridden),)
)]
pub(crate) const fn first_override_allowed(already_overridden: bool) -> bool {
    !already_overridden
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires parent <= u32::MAX - child,
        ensures returns crate::specs::part2_metadata_count(parent, child),
    )
)]
pub(crate) const fn metadata_count(parent: u32, child: u32) -> u32 {
    parent + child
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::valid_jph_branding(
                primary_is_jph,
                minor_version as nat,
                compatible_brands as nat,
                sole_compatible_is_jph,
            )
        ),
    )
)]
pub(crate) const fn part15_jph_branding(
    primary_is_jph: bool,
    minor_version: u32,
    compatible_brands: usize,
    sole_compatible_is_jph: bool,
) -> bool {
    primary_is_jph && minor_version == 0 && compatible_brands == 1 && sole_compatible_is_jph
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part15_cap_payload_length(capabilities),
    )
)]
pub(crate) const fn part15_cap_payload_length(capabilities: u8) -> usize {
    4 + 2 * capabilities as usize
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part15_signaling_valid(
            rsiz_ht,
            pcap_ht,
            styles_ht,
            corresponding_profile,
        ),
    )
)]
pub(crate) const fn part15_signaling_valid(
    rsiz_ht: bool,
    pcap_ht: bool,
    styles_ht: bool,
    corresponding_profile: bool,
) -> bool {
    rsiz_ht == pcap_ht && (!styles_ht || pcap_ht) && (!corresponding_profile || pcap_ht)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part15_codestream_class(has_legacy, has_ht, has_mixed) as u8
        ),
    )
)]
pub(crate) const fn part15_codestream_class(has_legacy: bool, has_ht: bool, has_mixed: bool) -> u8 {
    if has_mixed || (has_legacy && has_ht) {
        2
    } else if has_ht {
        1
    } else {
        0
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part15_mode_allows(
            mode as nat,
            has_legacy,
            has_mixed,
        ),
    )
)]
pub(crate) const fn part15_mode_allows(mode: u8, has_legacy: bool, has_mixed: bool) -> bool {
    matches!(mode, 0 | 2 | 3) && (mode != 0 || !has_legacy) && (mode != 2 || !has_mixed)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part15_magnitude_bound(parameter as nat) as u8
        ),
    )
)]
pub(crate) const fn part15_magnitude_bound(parameter: u8) -> u8 {
    match parameter {
        0 => 8,
        1..=19 => parameter + 8,
        20..=30 => 4 * (parameter - 19) + 27,
        _ => 74,
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part15_cleanup_u_bound(
                missing_msbs as nat, placeholder_bitplanes as nat, capability_bound as nat,
            ) as u8
        ),
    )
)]
pub(crate) const fn part15_cleanup_u_bound(
    missing_msbs: u16,
    placeholder_bitplanes: u16,
    capability_bound: u8,
) -> u8 {
    let bound = missing_msbs as u32 + placeholder_bitplanes as u32 + 2;
    // MagSgn precision includes one sign-coding bit beyond the coefficient bound.
    let capability_limit = if capability_bound < u8::MAX {
        capability_bound + 1
    } else {
        u8::MAX
    };
    if bound <= capability_limit as u32 {
        bound as u8
    } else {
        capability_limit
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part15_component_allowed(
            roi_allowed,
            has_roi,
            roi_shift as nat,
            irreversible_allowed,
            uses_ht,
            irreversible,
        ),
    )
)]
pub(crate) const fn part15_component_allowed(
    roi_allowed: bool,
    has_roi: bool,
    roi_shift: u8,
    irreversible_allowed: bool,
    uses_ht: bool,
    irreversible: bool,
) -> bool {
    (!has_roi || (roi_allowed && roi_shift <= 37))
        && (irreversible_allowed || !uses_ht || !irreversible)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part15_capability_fields_valid(
            mode as nat,
            reserved as nat,
            magnitude_parameter as nat,
        ),
    )
)]
pub(crate) const fn part15_capability_fields_valid(
    mode: u8,
    reserved: u8,
    magnitude_parameter: u8,
) -> bool {
    matches!(mode, 0 | 2 | 3) && reserved == 0 && magnitude_parameter < 32
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part15_headers_allowed(
            heterogeneous_allowed,
            has_functional_tile_header,
        ),
    )
)]
pub(crate) const fn part15_headers_allowed(
    heterogeneous_allowed: bool,
    has_functional_tile_header: bool,
) -> bool {
    heterogeneous_allowed || !has_functional_tile_header
}
