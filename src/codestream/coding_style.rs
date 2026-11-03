//! Coding-style selectors, component overrides and progression records.

use super::geometry::selection_geometry_arithmetic;
use super::{
    CodingStyle, ComponentCodingStyles, DecodeError, DecompositionDirection, MAX_COMPONENTS,
    MalformedKind, Parser, Part2Extensions, ProgressionChange, ProgressionChanges,
    ProgressionOrder, Segment, Tier1CodingStyle, WaveletTransform,
};
#[cfg(verus_keep_ghost)]
use super::{
    coding_style_tier1_result, component_coding_style_result, component_style_owner_view,
    decomposition_selector_view, owned_extensions_view, parsed_coding_style_view,
    parsed_style_owner_outcome, precinct_selector_view, progression_change_contains,
    progression_changes_view, segment_slots_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl ProgressionChange {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == progression_change_contains(self, layer, resolution, component),
    ))]
    pub const fn contains(self, layer: u16, resolution: u8, component: u16) -> bool {
        layer < self.layer_end
            && resolution >= self.resolution_start
            && resolution < self.resolution_end
            && component >= self.component_start
            && component < self.component_end
    }
}
impl ProgressionChanges {
    pub const fn none() -> Self {
        Self {
            records: Vec::new(),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result@ == progression_changes_view(self),))]
    pub fn records(&self) -> &[ProgressionChange] {
        &self.records
    }

    #[cfg(test)]
    pub(crate) fn from_records(records: Vec<ProgressionChange>) -> Self {
        Self { records }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (progression_changes_view(self).len() != 0),))]
    pub const fn is_present(&self) -> bool {
        !self.records.is_empty()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result as nat == progression_changes_view(self).len(),))]
    pub fn len(&self) -> usize {
        self.records.len()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (progression_changes_view(self).len() == 0),))]
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    pub fn equals(&self, other: &Self) -> bool {
        if self.records.len() != other.records.len() {
            return false;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.records.len(),
                decreases self.records.len() - index,
            )
        )]
        while index < self.records.len() {
            let Some(left) = self.records.get(index) else {
                return false;
            };
            let Some(right) = other.records.get(index) else {
                return false;
            };
            if left.resolution_start != right.resolution_start
                || left.component_start != right.component_start
                || left.layer_end != right.layer_end
                || left.resolution_end != right.resolution_end
                || left.component_end != right.component_end
                || !progression_orders_equal(left.progression_order, right.progression_order)
            {
                return false;
            }
            index += 1;
        }
        true
    }
}
impl Default for ProgressionChanges {
    fn default() -> Self {
        Self::none()
    }
}
impl CodingStyle {
    pub const fn resolution_levels(self) -> u16 {
        (self.decomposition_levels as u16) + 1
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_subband_count(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1,
        ),
    ))]
    pub fn subband_count(self) -> u16 {
        let mut count = 1_u16;
        let mut stage = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_subband_count_run); }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    stage <= self.decomposition_levels,
                    crate::specs::part2_subband_count(decomposition_selector_view(self).0, decomposition_selector_view(self).1)
                        == crate::specs::part2_subband_count_run(
                            decomposition_selector_view(self).0, decomposition_selector_view(self).1, stage, count,
                        ),
                decreases self.decomposition_levels - stage,
            )
        )]
        while stage < self.decomposition_levels && stage < 32 {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_subband_count_run); }
            let Some(direction) = self.decomposition_directions.get(stage as usize) else {
                return count;
            };
            let increment = match direction {
                DecompositionDirection::None => 0,
                DecompositionDirection::Horizontal | DecompositionDirection::Vertical => 1,
                DecompositionDirection::TwoDimensional => 3,
            };
            count = match count.checked_add(increment) {
                Some(value) => value,
                None => return count,
            };
            stage += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_subband_count_run); }
        count
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_decomposition_direction(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1, stage_from_finest,
        ),
    ))]
    pub fn decomposition_direction(
        self,
        stage_from_finest: u8,
    ) -> Result<DecompositionDirection, DecodeError> {
        if stage_from_finest >= self.decomposition_levels {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        match self
            .decomposition_directions
            .get(usize::from(stage_from_finest))
        {
            Some(direction) => Ok(*direction),
            None => Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            }),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_direction_for_resolution(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1, resolution,
        ),
    ))]
    pub fn direction_for_resolution(
        self,
        resolution: u8,
    ) -> Result<DecompositionDirection, DecodeError> {
        if resolution == 0 || resolution > self.decomposition_levels {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        let stage = self
            .decomposition_levels
            .checked_sub(resolution)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        self.decomposition_direction(stage)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_resolution_scale_step(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1, stage, scales,
        ),
    ))]
    pub(crate) fn resolution_downsampling_step(
        self,
        stage: u8,
        scales: (u32, u32),
    ) -> Result<(u32, u32), DecodeError> {
        let mut horizontal = scales.0;
        let mut vertical = scales.1;
        match self.decomposition_direction(stage)? {
            DecompositionDirection::None => {}
            DecompositionDirection::Horizontal => {
                horizontal = horizontal
                    .checked_mul(2)
                    .ok_or_else(selection_geometry_arithmetic)?;
            }
            DecompositionDirection::Vertical => {
                vertical = vertical
                    .checked_mul(2)
                    .ok_or_else(selection_geometry_arithmetic)?;
            }
            DecompositionDirection::TwoDimensional => {
                horizontal = horizontal
                    .checked_mul(2)
                    .ok_or_else(selection_geometry_arithmetic)?;
                vertical = vertical
                    .checked_mul(2)
                    .ok_or_else(selection_geometry_arithmetic)?;
            }
        }
        Ok((horizontal, vertical))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_resolution_downsampling(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1, resolution,
        ),
    ))]
    pub fn resolution_downsampling(self, resolution: u8) -> Result<(u32, u32), DecodeError> {
        if resolution > self.decomposition_levels {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        let discarded = self
            .decomposition_levels
            .checked_sub(resolution)
            .ok_or_else(selection_geometry_arithmetic)?;
        let mut horizontal = 1_u32;
        let mut vertical = 1_u32;
        let mut stage = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost selector = decomposition_selector_view(self); }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_resolution_scales_empty(selector.0, selector.1);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    stage <= discarded,
                    resolution <= self.decomposition_levels,
                    discarded == self.decomposition_levels as int - resolution as int,
                    selector == decomposition_selector_view(self),
                    crate::specs::part2_resolution_scale_prefix(selector.0, selector.1, stage as nat)
                        == Ok((horizontal, vertical)),
                decreases discarded - stage,
            )
        )]
        while stage < discarded {
            let next = self.resolution_downsampling_step(stage, (horizontal, vertical));
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_resolution_scales_step(
                    selector.0, selector.1, stage as nat,
                );
                if next.is_err() {
                    assert(crate::specs::part2_resolution_scale_prefix(
                        selector.0, selector.1, stage as nat + 1,
                    ) == next);
                    crate::proofs::production_impl::production_resolution_scales_error(
                        selector.0, selector.1, stage as nat + 1, discarded as nat,
                    );
                }
            }
            let next = next?;
            horizontal = next.0;
            vertical = next.1;
            stage = stage
                .checked_add(1)
                .ok_or_else(selection_geometry_arithmetic)?;
        }
        Ok((horizontal, vertical))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_subband_count_through_resolution(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1, resolution,
        ),
    ))]
    pub fn subband_count_through_resolution(self, resolution: u8) -> Result<usize, DecodeError> {
        if resolution > self.decomposition_levels {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        let mut count = 1_usize;
        let mut current = 1_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant current <= resolution + 1,
                current >= 1,
                resolution <= self.decomposition_levels,
                crate::specs::part1_subband_count_prefix(
                    decomposition_selector_view(self).0, decomposition_selector_view(self).1, (current - 1) as nat,
                ) == Ok(count),
                decreases resolution + 1 - current,
            )
        )]
        while current <= resolution {
            let direction = match self.direction_for_resolution(current) {
                Ok(direction) => direction,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_subband_count_error_persists(
                            decomposition_selector_view(self).0, decomposition_selector_view(self).1,
                            current as nat, resolution as nat, error,
                        );
                    }
                    return Err(error);
                }
            };
            let added = match direction {
                DecompositionDirection::None => 0,
                DecompositionDirection::Horizontal | DecompositionDirection::Vertical => 1,
                DecompositionDirection::TwoDimensional => 3,
            };
            count = match count.checked_add(added) {
                Some(next) => next,
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_subband_count_error_persists(
                            decomposition_selector_view(self).0, decomposition_selector_view(self).1,
                            current as nat, resolution as nat, crate::specs::part1_selector_error(true),
                        );
                    }
                    return Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::ArithmeticOverflow,
                    });
                }
            };
            current = match current.checked_add(1) {
                Some(next) => next,
                None => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_subband_count_error_persists(
                            decomposition_selector_view(self).0, decomposition_selector_view(self).1,
                            current as nat, resolution as nat, crate::specs::part1_selector_error(true),
                        );
                    }
                    return Err(DecodeError::MalformedInput {
                        offset: 0,
                        kind: MalformedKind::ArithmeticOverflow,
                    });
                }
            };
        }
        Ok(count)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_maximum_isotropic_reduction(
            decomposition_selector_view(self).0, decomposition_selector_view(self).1, 0,
        ),
    ))]
    pub fn maximum_isotropic_reduction(self) -> u8 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(decomposition_selector_view); }
        let mut count = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant count <= self.decomposition_levels,
                    crate::specs::part2_maximum_isotropic_reduction(self.decomposition_levels, self.decomposition_directions@, 0)
                        == crate::specs::part2_maximum_isotropic_reduction(self.decomposition_levels, self.decomposition_directions@, count),
                decreases self.decomposition_levels - count,
            )
        )]
        while count < self.decomposition_levels && count < 32 {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part2_maximum_isotropic_reduction, 1); }
            let Some(direction) = self.decomposition_directions.get(count as usize) else {
                return count;
            };
            if !matches!(direction, DecompositionDirection::TwoDimensional) {
                return count;
            }
            count += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_maximum_isotropic_reduction, 1); }
        count
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == coding_style_tier1_result(self),
    ))]
    pub fn tier1_coding_style(self) -> Result<Tier1CodingStyle, DecodeError> {
        crate::tier1::tier1_coding_style_from_code_block_style(self.code_block_style)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_precinct_exponents(
            precinct_selector_view(self).0, precinct_selector_view(self).1, resolution,
        ),
    ))]
    pub fn precinct_exponents(self, resolution: u8) -> Result<(u8, u8), DecodeError> {
        if resolution > self.decomposition_levels {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }
        match self.precinct_exponents.get(usize::from(resolution)) {
            Some(exponents) => Ok(*exponents),
            None => Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            }),
        }
    }

    pub fn equals(self, other: Self) -> bool {
        if !progression_orders_equal(self.progression_order, other.progression_order)
            || self.layers != other.layers
            || self.multiple_component_transform != other.multiple_component_transform
            || self.decomposition_levels != other.decomposition_levels
            || self.decomposition_structure != other.decomposition_structure
            || self.code_block_width != other.code_block_width
            || self.code_block_height != other.code_block_height
            || self.code_block_style != other.code_block_style
            || !wavelet_transforms_equal(self.transform, other.transform)
            || self.precincts_defined != other.precincts_defined
            || self.sop_markers != other.sop_markers
            || self.eph_markers != other.eph_markers
        {
            return false;
        }
        let mut stage = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant stage <= self.decomposition_directions.len(),
                decreases self.decomposition_directions.len() - stage,
            )
        )]
        while stage < self.decomposition_directions.len() {
            if !decomposition_directions_equal(
                self.decomposition_directions[stage],
                other.decomposition_directions[stage],
            ) {
                return false;
            }
            stage += 1;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.precinct_exponents.len(),
                decreases self.precinct_exponents.len() - index,
            )
        )]
        while index < self.precinct_exponents.len() {
            if self.precinct_exponents[index].0 != other.precinct_exponents[index].0
                || self.precinct_exponents[index].1 != other.precinct_exponents[index].1
            {
                return false;
            }
            index += 1;
        }
        true
    }
}
// The pinned verus_spec frontend cannot resolve associated static constructors.
// Both existing factory entry points use this one executable implementation.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures parsed_style_owner_outcome(result) == crate::specs::part1_component_styles_new(
        components, parsed_coding_style_view(default)),
))]
pub(super) fn new_component_coding_styles(
    components: u16,
    default: CodingStyle,
) -> Result<ComponentCodingStyles, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_component_styles_new); }
    if components == 0 || usize::from(components) > MAX_COMPONENTS {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::InvalidImageGeometry,
        ));
    }
    let owner = ComponentCodingStyles {
        components,
        styles: [default; MAX_COMPONENTS],
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(component_style_owner_view(&owner).1 =~= Seq::new(64, |i: int| parsed_coding_style_view(default)));
    }
    Ok(owner)
}

impl ComponentCodingStyles {
    pub(super) fn new(components: u16, default: CodingStyle) -> Result<Self, DecodeError> {
        new_component_coding_styles(components, default)
    }

    pub(crate) fn uniform(components: u16, default: CodingStyle) -> Result<Self, DecodeError> {
        Self::new(components, default)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == component_coding_style_result(self, component),
    ))]
    pub fn style(&self, component: u16) -> Result<CodingStyle, DecodeError> {
        if component >= self.components {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            });
        }

        match self.styles.get(usize::from(component)) {
            Some(style) => Ok(*style),
            None => Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodingStyle,
            }),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, component_style_owner_view(final(self))) == crate::specs::part1_set_component_style(
            component_style_owner_view(old(self)), component, parsed_coding_style_view(style)),
    ))]
    pub(super) fn set(&mut self, component: u16, style: CodingStyle) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_set_component_style); }
        if component >= self.components || usize::from(component) >= self.styles.len() {
            return Err(DecodeError::malformed(0, MalformedKind::InvalidCodingStyle));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = component_style_owner_view(self); }
        self.styles[usize::from(component)] = style;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(component_style_owner_view(self).1 =~= before.1.update(component as int, parsed_coding_style_view(style)));
        }
        Ok(())
    }

    pub fn equals(&self, other: &Self) -> bool {
        if self.components != other.components {
            return false;
        }
        let mut component = 0_u16;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component <= self.components,
                decreases self.components - component,
            )
        )]
        while component < self.components {
            let left = match self.style(component) {
                Ok(value) => value,
                Err(_) => return false,
            };
            let right = match other.style(component) {
                Ok(value) => value,
                Err(_) => return false,
            };
            if !left.equals(right) {
                return false;
            }
            component += 1;
        }
        true
    }
}
impl Parser<'_> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, component_style_owner_view(final(styles)))
            == crate::specs::part1_style_overrides_from(
                components, parsed_coding_style_view(default), segment_slots_view(segments@),
                &self.limits, component_style_owner_view(old(styles)), 0),
            match result {
                Ok(()) => crate::specs::part1_main_styles_from(
                    components, parsed_coding_style_view(default), segment_slots_view(segments@),
                    &self.limits, component_style_owner_view(old(styles)), 0)
                    == Ok(component_style_owner_view(final(styles))),
                Err(error) => crate::specs::part1_main_styles_from(
                    components, parsed_coding_style_view(default), segment_slots_view(segments@),
                    &self.limits, component_style_owner_view(old(styles)), 0) == Err(error),
            },
    ))]
    pub(super) fn apply_component_style_overrides(
        &self,
        components: u16,
        default: CodingStyle,
        segments: &[Option<Segment<'_>>],
        styles: &mut ComponentCodingStyles,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = component_style_owner_view(styles);
            let ghost frame_goal = crate::specs::part1_style_overrides_from(
                components, parsed_coding_style_view(default), segment_slots_view(segments@),
                &self.limits, initial, 0);
            let ghost result_goal = crate::specs::part1_main_styles_from(
                components, parsed_coding_style_view(default), segment_slots_view(segments@),
                &self.limits, initial, 0);
        }
        let mut component = 0_u16;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component <= components,
                initial == component_style_owner_view(old(styles)),
                frame_goal == crate::specs::part1_style_overrides_from(
                    components, parsed_coding_style_view(default), segment_slots_view(segments@),
                    &self.limits, initial, 0),
                result_goal == crate::specs::part1_main_styles_from(
                    components, parsed_coding_style_view(default), segment_slots_view(segments@),
                    &self.limits, initial, 0),
                frame_goal == crate::specs::part1_style_overrides_from(
                    components, parsed_coding_style_view(default), segment_slots_view(segments@),
                    &self.limits, component_style_owner_view(styles), component as nat),
                result_goal == crate::specs::part1_main_styles_from(
                    components, parsed_coding_style_view(default), segment_slots_view(segments@),
                    &self.limits, component_style_owner_view(styles), component as nat),
            decreases components - component,
        ))]
        while component < components {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_style_overrides_from, 1);
                reveal_with_fuel(crate::specs::part1_main_styles_from, 1);
                reveal(crate::specs::part1_set_component_style);
            }
            let coc_segment = match segments.get(usize::from(component)) {
                Some(segment) => *segment,
                None => None,
            };
            if let Some(segment) = coc_segment {
                let (_, style) = self.parse_coc(segment, components, default)?;
                styles.set(component, style)?;
            }
            component = component
                .checked_add(1)
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_style_overrides_from, 1);
            reveal_with_fuel(crate::specs::part1_main_styles_from, 1);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_style_owner_outcome(result) == crate::specs::part1_finish_main_styles(
            components, parsed_coding_style_view(default), segment_slots_view(segments@),
            &self.limits, owned_extensions_view(extensions)),
    ))]
    pub(super) fn finish_main_component_styles(
        &self,
        components: u16,
        default: CodingStyle,
        segments: &[Option<Segment<'_>>],
        extensions: &Part2Extensions,
    ) -> Result<ComponentCodingStyles, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_finish_main_styles);
            reveal(crate::specs::part1_component_styles_new);
            reveal(crate::specs::part1_set_component_style);
        }
        let mut styles = new_component_coding_styles(components, default)?;
        self.apply_component_style_overrides(components, default, segments, &mut styles)?;
        self.resolve_decomposition_structures(&mut styles, extensions)?;
        Ok(styles)
    }
}

impl Clone for ProgressionChanges {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures progression_changes_view(&result) == progression_changes_view(self),))]
    fn clone(&self) -> Self {
        Self {
            records: self.records.clone(),
        }
    }
}
const fn progression_orders_equal(left: ProgressionOrder, right: ProgressionOrder) -> bool {
    matches!(
        (left, right),
        (ProgressionOrder::Lrcp, ProgressionOrder::Lrcp)
            | (ProgressionOrder::Rlcp, ProgressionOrder::Rlcp)
            | (ProgressionOrder::Rpcl, ProgressionOrder::Rpcl)
            | (ProgressionOrder::Pcrl, ProgressionOrder::Pcrl)
            | (ProgressionOrder::Cprl, ProgressionOrder::Cprl)
    )
}
const fn decomposition_directions_equal(
    left: DecompositionDirection,
    right: DecompositionDirection,
) -> bool {
    matches!(
        (left, right),
        (DecompositionDirection::None, DecompositionDirection::None)
            | (
                DecompositionDirection::TwoDimensional,
                DecompositionDirection::TwoDimensional
            )
            | (
                DecompositionDirection::Horizontal,
                DecompositionDirection::Horizontal
            )
            | (
                DecompositionDirection::Vertical,
                DecompositionDirection::Vertical
            )
    )
}
const fn wavelet_transforms_equal(left: WaveletTransform, right: WaveletTransform) -> bool {
    match (left, right) {
        (WaveletTransform::Irreversible9x7, WaveletTransform::Irreversible9x7)
        | (WaveletTransform::Reversible5x3, WaveletTransform::Reversible5x3) => true,
        (WaveletTransform::Arbitrary(left), WaveletTransform::Arbitrary(right)) => left == right,
        _ => false,
    }
}
