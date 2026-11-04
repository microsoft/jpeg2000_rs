//! Quantization tables, component overrides and region-of-interest shifts.

use super::{
    CodingStyle, ComponentCodingStyles, ComponentQuantizations, DecodeError, MAX_COMPONENTS,
    MAX_QUANTIZATION_STEPS, MalformedKind, Parser, Quantization, QuantizationStep,
    QuantizationStyle, RoiShifts, Segment,
};
#[cfg(verus_keep_ghost)]
use super::{
    component_style_owner_view, decomposition_selector_view, parsed_quantization_owner_outcome,
    parsed_quantization_owner_view, segment_slots_view,
};
#[cfg(verus_keep_ghost)]
use super::{quantization_owner_view, quantization_view, roi_shifts_view};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Shared executable factory; see the associated-constructor frontend limitation
// documented alongside new_component_coding_styles.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures parsed_quantization_owner_outcome(result) == crate::specs::part1_component_quantizations_new(
        components, quantization_view(&default)),
))]
pub(super) fn new_component_quantizations(
    components: u16,
    default: Quantization,
) -> Result<ComponentQuantizations, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_component_quantizations_new); }
    if components == 0 || usize::from(components) > MAX_COMPONENTS {
        return Err(DecodeError::malformed(
            0,
            MalformedKind::InvalidImageGeometry,
        ));
    }
    let owner = ComponentQuantizations {
        components,
        quantizations: vec![default; usize::from(components)],
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(parsed_quantization_owner_view(&owner).1 =~= Seq::new(components as nat, |i: int| quantization_view(&default)));
    }
    Ok(owner)
}

impl ComponentQuantizations {
    pub(super) fn new(components: u16, default: Quantization) -> Result<Self, DecodeError> {
        new_component_quantizations(components, default)
    }

    pub(crate) fn uniform(components: u16, default: Quantization) -> Result<Self, DecodeError> {
        Self::new(components, default)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_component_quantization(self, component),
    ))]
    pub fn quantization(&self, component: u16) -> Result<Quantization, DecodeError> {
        if component >= self.components {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidQuantization,
            });
        }
        match self.quantizations.get(usize::from(component)) {
            Some(quantization) => Ok(*quantization),
            None => Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidQuantization,
            }),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parsed_quantization_owner_view(final(self))) == crate::specs::part1_set_component_quantization(
            parsed_quantization_owner_view(old(self)), component, quantization_view(&quantization)),
    ))]
    pub(super) fn set(
        &mut self,
        component: u16,
        quantization: Quantization,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_set_component_quantization); }
        if component >= self.components {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::InvalidQuantization,
            ));
        }
        if usize::from(component) >= self.quantizations.len() {
            return Err(DecodeError::malformed(
                0,
                MalformedKind::InvalidQuantization,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost before = parsed_quantization_owner_view(self); }
        self.quantizations[usize::from(component)] = quantization;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(parsed_quantization_owner_view(self).1 =~= before.1.update(component as int, quantization_view(&quantization)));
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
            let left = match self.quantization(component) {
                Ok(value) => value,
                Err(_) => return false,
            };
            let right = match other.quantization(component) {
                Ok(value) => value,
                Err(_) => return false,
            };
            if !left.equals(&right) {
                return false;
            }
            component += 1;
        }
        true
    }
}
impl RoiShifts {
    pub const fn none() -> Self {
        Self {
            shifts: [0; MAX_COMPONENTS],
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_roi_shift(roi_shifts_view(self), component),
    ))]
    pub fn shift(&self, component: u16) -> Result<u8, DecodeError> {
        match self.shifts.get(usize::from(component)) {
            Some(shift) => Ok(*shift),
            None => Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidRegionOfInterest,
            }),
        }
    }

    pub fn equals(&self, other: &Self) -> bool {
        let mut component = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component <= self.shifts.len(),
                decreases self.shifts.len() - component,
            )
        )]
        while component < self.shifts.len() {
            if self.shifts[component] != other.shifts[component] {
                return false;
            }
            component += 1;
        }
        true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, roi_shifts_view(final(self)))
            == crate::specs::part1_set_roi_shift(roi_shifts_view(old(self)), component, shift),
    ))]
    pub(super) fn set(&mut self, component: u16, shift: u8) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(roi_shifts_view);
            reveal(crate::specs::part1_set_roi_shift);
            reveal(crate::specs::part1_codestream_malformed);
            reveal(crate::specs::part1_codestream_offset);
        }
        let value = self.shifts.get_mut(usize::from(component)).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(
                        0, MalformedKind::InvalidRegionOfInterest),
                ))]
            || DecodeError::malformed(0, MalformedKind::InvalidRegionOfInterest),
        )?;
        *value = shift;
        Ok(())
    }
}
impl Default for RoiShifts {
    fn default() -> Self {
        Self::none()
    }
}
impl Quantization {
    pub(crate) fn reversible_default(coding_style: CodingStyle) -> Self {
        Self {
            style: QuantizationStyle::None,
            guard_bits: 0,
            step_count: coding_style.subband_count(),
            steps: [QuantizationStep {
                exponent: 0,
                mantissa: 0,
            }; MAX_QUANTIZATION_STEPS],
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == quantization_view(self).0,
    ))]
    pub const fn style(&self) -> QuantizationStyle {
        self.style
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == quantization_view(self).1,
    ))]
    pub const fn guard_bits(&self) -> u8 {
        self.guard_bits
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_quantization_lookup(quantization_view(self), index),
    ))]
    pub fn step(&self, index: u16) -> Result<QuantizationStep, DecodeError> {
        if index >= self.step_count {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidQuantization,
            });
        }
        let index = usize::from(index);
        if index >= self.steps.len() {
            return Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidQuantization,
            });
        }
        Ok(self.steps[index])
    }

    pub fn equals(&self, other: &Self) -> bool {
        if !quantization_styles_equal(self.style, other.style)
            || self.guard_bits != other.guard_bits
            || self.step_count != other.step_count
        {
            return false;
        }
        let mut index = 0_u16;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.step_count,
                decreases self.step_count - index,
            )
        )]
        while index < self.step_count {
            let left = match self.step(index) {
                Ok(value) => value,
                Err(_) => return false,
            };
            let right = match other.step(index) {
                Ok(value) => value,
                Err(_) => return false,
            };
            if left.exponent != right.exponent || left.mantissa != right.mantissa {
                return false;
            }
            index += 1;
        }
        true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_quantization_compatible(quantization_view(&self), decomposition_selector_view(coding_style)),
    ))]
    pub fn is_compatible_with(self, coding_style: CodingStyle) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_quantization_compatible); }
        match self.style {
            QuantizationStyle::None | QuantizationStyle::ScalarExpounded => {
                self.step_count == coding_style.subband_count()
            }
            QuantizationStyle::ScalarDerived => self.step_count == 1,
        }
    }
}

impl Parser<'_> {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, parsed_quantization_owner_view(final(quantizations)))
            == crate::specs::part1_quantization_overrides_from(
                components, component_style_owner_view(styles), segment_slots_view(segments@),
                parsed_quantization_owner_view(old(quantizations)), 0),
            match result {
                Ok(()) => crate::specs::part1_main_quantizations_from(
                    components, component_style_owner_view(styles), segment_slots_view(segments@),
                    parsed_quantization_owner_view(old(quantizations)), 0)
                    == Ok(parsed_quantization_owner_view(final(quantizations))),
                Err(error) => crate::specs::part1_main_quantizations_from(
                    components, component_style_owner_view(styles), segment_slots_view(segments@),
                    parsed_quantization_owner_view(old(quantizations)), 0) == Err(error),
            },
    ))]
    pub(super) fn apply_component_quantization_overrides(
        &self,
        components: u16,
        styles: &ComponentCodingStyles,
        segments: &[Option<Segment<'_>>],
        quantizations: &mut ComponentQuantizations,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = parsed_quantization_owner_view(quantizations);
            let ghost frame_goal = crate::specs::part1_quantization_overrides_from(
                components, component_style_owner_view(styles), segment_slots_view(segments@),
                initial, 0);
            let ghost result_goal = crate::specs::part1_main_quantizations_from(
                components, component_style_owner_view(styles), segment_slots_view(segments@),
                initial, 0);
        }
        let mut component = 0_u16;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component <= components,
                initial == parsed_quantization_owner_view(old(quantizations)),
                frame_goal == crate::specs::part1_quantization_overrides_from(
                    components, component_style_owner_view(styles), segment_slots_view(segments@),
                    initial, 0),
                result_goal == crate::specs::part1_main_quantizations_from(
                    components, component_style_owner_view(styles), segment_slots_view(segments@),
                    initial, 0),
                frame_goal == crate::specs::part1_quantization_overrides_from(
                    components, component_style_owner_view(styles), segment_slots_view(segments@),
                    parsed_quantization_owner_view(quantizations), component as nat),
                result_goal == crate::specs::part1_main_quantizations_from(
                    components, component_style_owner_view(styles), segment_slots_view(segments@),
                    parsed_quantization_owner_view(quantizations), component as nat),
            decreases components - component,
        ))]
        while component < components {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_quantization_overrides_from, 1);
                reveal_with_fuel(crate::specs::part1_main_quantizations_from, 1);
                reveal(crate::specs::part1_style_owner_lookup);
                reveal(crate::specs::part1_quantization_owner_lookup);
                reveal(crate::specs::part1_set_component_quantization);
            }
            let qcc_segment = match segments.get(usize::from(component)) {
                Some(segment) => *segment,
                None => None,
            };
            if let Some(segment) = qcc_segment {
                let style = styles.style(component)?;
                let (_, quantization) = self.parse_qcc(segment, components, style)?;
                quantizations.set(component, quantization)?;
            }
            if !quantizations
                .quantization(component)?
                .is_compatible_with(styles.style(component)?)
            {
                return Err(DecodeError::malformed(
                    0,
                    MalformedKind::InvalidQuantization,
                ));
            }
            component = component
                .checked_add(1)
                .ok_or_else(|| self.malformed_here(MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_quantization_overrides_from, 1);
            reveal_with_fuel(crate::specs::part1_main_quantizations_from, 1);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures parsed_quantization_owner_outcome(result) == crate::specs::part1_finish_main_quantizations(
            components, quantization_view(&default), component_style_owner_view(styles), segment_slots_view(segments@)),
    ))]
    pub(super) fn finish_main_component_quantizations(
        &self,
        components: u16,
        default: Quantization,
        styles: &ComponentCodingStyles,
        segments: &[Option<Segment<'_>>],
    ) -> Result<ComponentQuantizations, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_finish_main_quantizations);
            reveal(crate::specs::part1_component_quantizations_new);
            reveal(crate::specs::part1_style_owner_lookup);
            reveal(crate::specs::part1_quantization_owner_lookup);
            reveal(crate::specs::part1_set_component_quantization);
        }
        let mut quantizations = new_component_quantizations(components, default)?;
        self.apply_component_quantization_overrides(
            components,
            styles,
            segments,
            &mut quantizations,
        )?;
        Ok(quantizations)
    }
}
impl Clone for ComponentQuantizations {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures quantization_owner_view(&result) == quantization_owner_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(quantization_owner_view); }
        Self {
            components: self.components,
            quantizations: self.quantizations.clone(),
        }
    }
}
const fn quantization_styles_equal(left: QuantizationStyle, right: QuantizationStyle) -> bool {
    matches!(
        (left, right),
        (QuantizationStyle::None, QuantizationStyle::None)
            | (
                QuantizationStyle::ScalarDerived,
                QuantizationStyle::ScalarDerived
            )
            | (
                QuantizationStyle::ScalarExpounded,
                QuantizationStyle::ScalarExpounded
            )
    )
}
