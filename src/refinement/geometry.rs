#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires divisor > 0,
        ensures returns (crate::specs::part1_ceil_div(value as nat, divisor as nat) as u32),
    )
)]
pub(crate) const fn ceil_div_u32(value: u32, divisor: u32) -> u32 {
    if value == 0 {
        0
    } else {
        1 + (value - 1) / divisor
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part1_clip_start(nominal as nat, image_start as nat) as u32
        ),
    )
)]
pub(crate) const fn tile_clip_start(nominal: u32, image_start: u32) -> u32 {
    if nominal < image_start {
        image_start
    } else {
        nominal
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns (
            crate::specs::part1_clip_end(nominal_end as nat, image_end as nat) as u32
        ),
    )
)]
pub(crate) const fn tile_clip_end(nominal_end: u32, image_end: u32) -> u32 {
    if nominal_end < image_end {
        nominal_end
    } else {
        image_end
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part1_decode_output_shape_valid(
            input_bytes,
            tile_parts,
            expected_components,
            output_components,
            width,
            height,
        ),
    )
)]
pub(crate) const fn decode_output_shape_valid(
    input_bytes: usize,
    tile_parts: usize,
    expected_components: u16,
    output_components: usize,
    width: u32,
    height: u32,
) -> bool {
    input_bytes > 0
        && tile_parts > 0
        && expected_components > 0
        && expected_components as usize == output_components
        && width > 0
        && height > 0
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        ensures returns crate::specs::part1_component_output_shape_valid(width, height, samples),
    )
)]
pub(crate) const fn component_output_shape_valid(width: u32, height: u32, samples: usize) -> bool {
    width > 0 && height > 0 && crate::refinement::wavelet_sample_count(width, height, samples)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires grid > 0,
        ensures returns crate::specs::part2_registered_extent(numerator, grid),
    )
)]
pub(crate) const fn registered_extent(numerator: u64, grid: u64) -> u64 {
    if numerator == 0 {
        0
    } else {
        1 + (numerator - 1) / grid
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(
        requires
            subsampling > 0,
            offset <= numerator,
        ensures returns crate::specs::part2_registered_source_coordinate(
            numerator,
            offset,
            subsampling,
        ),
    )
)]
pub(crate) const fn registered_source_coordinate(
    numerator: u32,
    offset: u32,
    subsampling: u32,
) -> u32 {
    (numerator - offset) / subsampling
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires divisor > 0,
    ensures result == crate::specs::part2_crg_component_predecessor(value, divisor, registration),
        result as nat * divisor as nat <= value as nat, result <= value as u64,
))]
pub(crate) fn crg_component_predecessor(value: u32, divisor: u32, registration: u16) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(divisor as int * registration as int <= u64::MAX) by(nonlinear_arith);
    }
    let position = u64::from(value) * 65_536;
    let phase = u64::from(divisor) * u64::from(registration);
    let denominator = u64::from(divisor) * 65_536;
    let adjusted = position.saturating_sub(phase);
    let predecessor = adjusted / denominator;
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(adjusted as int, denominator as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(adjusted as int, denominator as int);
        assert(denominator as int == divisor as int * 65536);
        assert(adjusted as int <= value as int * 65536);
        assert(predecessor as int * denominator as int <= adjusted as int);
        assert(predecessor as int * divisor as int <= value as int) by(nonlinear_arith)
            requires denominator as int == divisor as int * 65536,
                predecessor as int * denominator as int <= adjusted as int,
                adjusted as int <= value as int * 65536;
        assert(predecessor <= value as u64) by(nonlinear_arith)
            requires predecessor as int >= 0, divisor as int >= 1,
                predecessor as int * divisor as int <= value as int;
    }
    predecessor
}
