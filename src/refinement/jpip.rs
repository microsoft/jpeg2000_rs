#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part9_header_form_valid(form as nat),)
)]
pub(crate) const fn jpip_header_form_valid(form: u8) -> bool {
    form >= 1 && form <= 3
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part9_header_has_explicit_class(form as nat),)
)]
pub(crate) const fn jpip_header_has_explicit_class(form: u8) -> bool {
    form >= 2
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part9_header_has_explicit_codestream(form as nat),)
)]
pub(crate) const fn jpip_header_has_explicit_codestream(form: u8) -> bool {
    form == 3
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires value <= (u64::MAX - group as u64) / 128,
        ensures returns (
            crate::specs::part9_vbas_step(value as nat, group as nat) as u64
        ),
    )
)]
pub(crate) const fn jpip_vbas_step(value: u64, group: u8) -> u64 {
    value * 128 + group as u64
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part9_auxiliary_present(class_identifier as nat),
    )
)]
pub(crate) const fn jpip_auxiliary_present(class_identifier: u64) -> bool {
    class_identifier % 2 == 1
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part9_eor_extent(header_length as nat, body_length as nat) as u128
        ),
    )
)]
pub(crate) const fn jpip_eor_extent(header_length: usize, body_length: usize) -> u128 {
    header_length as u128 + body_length as u128
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part9_class_identifier_valid(class_identifier as nat),
    )
)]
pub(crate) const fn jpip_class_identifier_valid(class_identifier: u64) -> bool {
    class_identifier <= 8
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part9_databin_identity(
            first_class as nat,
            first_codestream as nat,
            first_in_class as nat,
            second_class as nat,
            second_codestream as nat,
            second_in_class as nat,
        ),
    )
)]
pub(crate) const fn jpip_databin_identity(
    first_class: u64,
    first_codestream: u64,
    first_in_class: u64,
    second_class: u64,
    second_codestream: u64,
    second_in_class: u64,
) -> bool {
    first_class / 2 == second_class / 2
        && first_codestream == second_codestream
        && first_in_class == second_in_class
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::valid_jpip_fragment(
            offset as nat,
            length as nat,
            limit as nat,
        ),
    )
)]
pub(crate) const fn jpip_fragment_valid(offset: u64, length: u64, limit: u64) -> bool {
    offset <= limit && length <= limit - offset
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::consistent_jpip_final_length(
            existing as nat,
            announced as nat,
        ),
    )
)]
pub(crate) const fn jpip_final_length_consistent(existing: u64, announced: u64) -> bool {
    existing == announced
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part9_overlap_consistent(bytes_equal),)
)]
pub(crate) const fn jpip_overlap_consistent(bytes_equal: bool) -> bool {
    bytes_equal
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part9_transaction_commit(validation_complete),)
)]
pub(crate) const fn jpip_transaction_commit(validation_complete: bool) -> bool {
    validation_complete
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part9_merge_start(first as nat, second as nat) as u64
        ),
    )
)]
pub(crate) const fn jpip_merge_start(first: u64, second: u64) -> u64 {
    if first < second { first } else { second }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part9_merge_end(first as nat, second as nat) as u64
        ),
    )
)]
pub(crate) const fn jpip_merge_end(first: u64, second: u64) -> u64 {
    if first > second { first } else { second }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::complete_jpip_databin(
            contiguous_prefix as nat,
            final_length as nat,
        ),
    )
)]
pub(crate) const fn jpip_databin_complete(contiguous_prefix: u64, final_length: u64) -> bool {
    contiguous_prefix == final_length
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires available_end <= required_end,
        ensures returns (
            crate::specs::part9_missing_length(required_end as nat, available_end as nat) as u64
        ),
    )
)]
pub(crate) const fn jpip_missing_length(required_end: u64, available_end: u64) -> u64 {
    required_end - available_end
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires missing <= required,
        ensures returns (
            crate::specs::part9_available_bytes(required as nat, missing as nat) as u64
        ),
    )
)]
pub(crate) const fn jpip_available_bytes(required: u64, missing: u64) -> u64 {
    required - missing
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::complete_jpip_range(
            available as nat,
            required as nat,
        ),
    )
)]
pub(crate) const fn jpip_range_complete(available: u64, required: u64) -> bool {
    available == required
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires
            product as nat == (_component_precinct as nat) * (_tile_count as nat),
            tile <= u64::MAX - product,
        ensures returns (
            crate::specs::part9_precinct_flat_identity(
                tile as nat,
                _tile_count as nat,
                _component_precinct as nat,
            ) as u64
        ),
    )
)]
pub(crate) const fn jpip_precinct_in_class(
    tile: u64,
    _tile_count: u64,
    _component_precinct: u64,
    product: u64,
) -> u64 {
    tile + product
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::jpip_quality_prefix_available(
            available as nat,
            requested as nat,
        ),
    )
)]
pub(crate) const fn jpip_quality_prefix_available(available: u16, requested: u16) -> bool {
    requested <= available
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part9_metadata_descent_allowed(
            depth as nat,
            maximum_depth as nat,
            cycle,
        ),
    )
)]
pub(crate) const fn jpip_metadata_descent_allowed(
    depth: u32,
    maximum_depth: u32,
    cycle: bool,
) -> bool {
    depth <= maximum_depth && !cycle
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part9_reconstruction_length(
                main_header as nat,
                tile_headers as nat,
                packet_data as nat,
                eoc as nat,
            ) as u128
        ),
    )
)]
pub(crate) const fn jpip_reconstruction_length(
    main_header: u64,
    tile_headers: u64,
    packet_data: u64,
    eoc: u64,
) -> u128 {
    main_header as u128 + tile_headers as u128 + packet_data as u128 + eoc as u128
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::jpip_reconstructed_box_length(
            header as nat,
            payload as nat,
        ) as u128,
    )
)]
pub(crate) const fn jpip_box_length(header: u64, payload: u64) -> u128 {
    header as u128 + payload as u128
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part9_reframed_marker_removed(
            marker as nat,
            tile_header,
        ),
    )
)]
pub(crate) const fn jpip_reframed_marker_removed(marker: u16, tile_header: bool) -> bool {
    if tile_header {
        marker == 0xff58 || marker == 0xff61
    } else {
        marker == 0xff55 || marker == 0xff57 || marker == 0xff60
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(ensures returns crate::specs::part9_progression_supported(order as nat),)
)]
pub(crate) const fn jpip_progression_supported(order: u8) -> bool {
    order <= 4
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires payload <= usize::MAX - 8,
        ensures returns (
            crate::specs::part9_packet_reframed_length(payload as nat, sop, eph) as usize
        ),
    )
)]
pub(crate) const fn jpip_packet_reframed_length(payload: usize, sop: bool, eph: bool) -> usize {
    payload + if sop { 6 } else { 0 } + if eph { 2 } else { 0 }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::jpip_tile_transition_sufficient(
            later_functional,
            preceding_packet_count_known,
            preceding_exact_consumption_known,
        ),
    )
)]
pub(crate) const fn jpip_tile_transition_sufficient(
    later_functional: bool,
    preceding_packet_count_known: bool,
    preceding_exact_consumption_known: bool,
) -> bool {
    !later_functional || preceding_packet_count_known || preceding_exact_consumption_known
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::valid_jpip_progressive_update(
            previous_layers as nat,
            available_layers as nat,
            planned_layers as nat,
        ),
    )
)]
pub(crate) const fn jpip_progressive_update_valid(
    previous_layers: u16,
    available_layers: u16,
    planned_layers: u16,
) -> bool {
    previous_layers <= available_layers && available_layers <= planned_layers
}
