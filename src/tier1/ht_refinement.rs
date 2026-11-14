use super::ht_refinement_readers::ht_refinement_readers_from_inputs;
use super::state::{
    arithmetic_overflow, ht_statistics_zero, invalid_code_block, significant_neighbor_count,
};
use super::{
    CodeBlockPlane, CoefficientState, HtRefinementPlaneState, HtRefinementSegment,
    HtSignificancePatchState, HtSigpropPlaneState, MAX_TIER1_BITPLANES, Tier1PassStatistics,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_view, coefficient_raw_views, ht_boolean_vector_view, ht_byte_vector_outcome,
    ht_plane_outcome, ht_refinement_core_view, ht_refinement_magnitude_outcome,
    ht_refinement_magnitude_view, ht_refinement_segment_view, ht_sigprop_patch_view,
    ht_sigprop_plane_outcome, ht_sigprop_plane_view,
};
use crate::magnitude::Magnitude;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures ht_refinement_magnitude_outcome(result) == crate::specs::ht_significance_magnitude(decoded_bitplanes),
))]
fn ht_significance_magnitude(decoded_bitplanes: u16) -> Result<Magnitude, DecodeError> {
    if !(2..=MAX_TIER1_BITPLANES).contains(&decoded_bitplanes) {
        return Err(invalid_code_block());
    }
    let centered = crate::magnitude::magnitude_from_u64(3).checked_shl(decoded_bitplanes - 2)?;
    #[cfg(verus_keep_ghost)]
    proof! { vstd::arithmetic::power2::lemma2_to64(); }
    Ok(centered.shift_right(1))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures ht_refinement_magnitude_outcome(result) == crate::specs::ht_refinement_delta(decoded_bitplanes),
))]
fn ht_refinement_delta(decoded_bitplanes: u16) -> Result<Magnitude, DecodeError> {
    if !(2..=MAX_TIER1_BITPLANES).contains(&decoded_bitplanes) {
        return Err(invalid_code_block());
    }
    if decoded_bitplanes == 2 {
        Ok(crate::magnitude::magnitude_from_u64(1))
    } else {
        crate::magnitude::magnitude_single_bit(decoded_bitplanes - 3)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures ht_boolean_vector_view(result) == crate::specs::ht_cleanup_significance(coefficient_raw_views(coefficients@)),
        result@ == crate::specs::ht_cleanup_significance(coefficient_raw_views(coefficients@)),
))]
pub(super) fn ht_collect_cleanup_significance(coefficients: &[CoefficientState]) -> Vec<bool> {
    let mut output = Vec::with_capacity(coefficients.len());
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= coefficients.len(), output.len() == index,
            forall |i: int| 0 <= i < index ==> output@[i] == coefficients@[i].significant,
        decreases coefficients.len() - index,
    ))]
    while index < coefficients.len() {
        output.push(coefficients[index].significant);
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= crate::specs::ht_cleanup_significance(coefficient_raw_views(coefficients@))); }
    output
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures ht_byte_vector_outcome(result) == crate::specs::ht_copy_refinement_bytes(input@),
))]
pub(super) fn copy_ht_refinement_bytes(input: &[u8]) -> Result<Vec<u8>, DecodeError> {
    let mut output = Vec::with_capacity(input.len());
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= input.len(), output.len() == index,
                forall |i: int| 0 <= i < index ==> output@[i] == input@[i],
            decreases input.len() - index,
        )
    )]
    while index < input.len() {
        output.push(*input.get(index).ok_or_else(invalid_code_block)?);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(output@ =~= input@); }
    Ok(output)
}

impl HtRefinementPlaneState<'_> {
    #[allow(
        clippy::too_many_arguments,
        reason = "The real magnitude-column loop consumes independent geometry and numeric inputs."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires rows <= 4,
        ensures (result, ht_refinement_core_view(final(self))) == crate::specs::ht_magref_rows(
            ht_refinement_core_view(old(self)), x, stripe_y, rows as nat, 0, crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            final(self).output.width == old(self).output.width, final(self).output.height == old(self).output.height,
            final(self).cleanup_significant@ == old(self).cleanup_significant@,
            result == Ok(()) || result.is_err(),
    ))]
    fn magnitude_column(
        &mut self,
        x: u16,
        stripe_y: u16,
        rows: u16,
        delta: Magnitude,
        decoded_bitplanes: u16,
    ) -> Result<(), DecodeError> {
        let mut row = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_magref_rows); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant row <= rows <= 4,
                self.output.width == old(self).output.width, self.output.height == old(self).output.height,
                self.cleanup_significant@ == old(self).cleanup_significant@,
                crate::specs::ht_magref_rows(ht_refinement_core_view(old(self)), x, stripe_y, rows as nat, 0,
                    crate::magnitude::magnitude_value(delta), decoded_bitplanes)
                    == crate::specs::ht_magref_rows(ht_refinement_core_view(self), x, stripe_y, rows as nat, row as nat,
                        crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            decreases rows - row,
        ))]
        while row < rows {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_magref_rows); }
            let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
            self.magnitude_sample(x, y, delta, decoded_bitplanes)?;
            row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_magref_rows); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires rows <= 4,
        ensures (result, ht_refinement_core_view(final(self))) == crate::specs::ht_magref_columns(
            ht_refinement_core_view(old(self)), width, stripe_y, rows as nat, 0, crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            final(self).output.width == old(self).output.width, final(self).output.height == old(self).output.height,
            final(self).cleanup_significant@ == old(self).cleanup_significant@,
            result == Ok(()) || result.is_err(),
    ))]
    fn magnitude_stripe(
        &mut self,
        width: u16,
        stripe_y: u16,
        rows: u16,
        delta: Magnitude,
        decoded_bitplanes: u16,
    ) -> Result<(), DecodeError> {
        let mut x = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_magref_columns); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant x <= width, rows <= 4,
                self.output.width == old(self).output.width, self.output.height == old(self).output.height,
                self.cleanup_significant@ == old(self).cleanup_significant@,
                crate::specs::ht_magref_columns(ht_refinement_core_view(old(self)), width, stripe_y, rows as nat, 0,
                    crate::magnitude::magnitude_value(delta), decoded_bitplanes)
                    == crate::specs::ht_magref_columns(ht_refinement_core_view(self), width, stripe_y, rows as nat, x as nat,
                        crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            decreases width - x,
        ))]
        while x < width {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_magref_columns); }
            self.magnitude_column(x, stripe_y, rows, delta, decoded_bitplanes)?;
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_magref_columns); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires width <= 4096, height <= 4096,
        ensures (result, ht_refinement_core_view(final(self))) == crate::specs::ht_magref_stripes(
            ht_refinement_core_view(old(self)), width, height, 0, crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            final(self).output.width == old(self).output.width, final(self).output.height == old(self).output.height,
            final(self).cleanup_significant@ == old(self).cleanup_significant@,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn magnitude_pass(
        &mut self,
        width: u16,
        height: u16,
        delta: Magnitude,
        decoded_bitplanes: u16,
    ) -> Result<(), DecodeError> {
        let mut stripe_y = 0_u16;
        let stripe_extent = height.checked_add(3).ok_or_else(arithmetic_overflow)?;
        let mut stripe_passes = stripe_extent
            .checked_div(4)
            .ok_or_else(arithmetic_overflow)?;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_magref_stripes); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant stripe_y <= height + 3, height <= 4096, width <= 4096,
                stripe_passes == if stripe_y >= height { 0int } else { (height - stripe_y + 3) / 4 },
                self.output.width == old(self).output.width, self.output.height == old(self).output.height,
                self.cleanup_significant@ == old(self).cleanup_significant@,
                crate::specs::ht_magref_stripes(ht_refinement_core_view(old(self)), width, height, 0,
                    crate::magnitude::magnitude_value(delta), decoded_bitplanes)
                    == crate::specs::ht_magref_stripes(ht_refinement_core_view(self), width, height, stripe_y as nat,
                        crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            decreases stripe_passes,
        ))]
        while stripe_y < height {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_magref_stripes); }
            let rows = crate::refinement::ht_stripe_rows(height, stripe_y);
            self.magnitude_stripe(width, stripe_y, rows, delta, decoded_bitplanes)?;
            stripe_y = stripe_y.checked_add(4).ok_or_else(arithmetic_overflow)?;
            stripe_passes = stripe_passes
                .checked_sub(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_magref_stripes); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, ht_refinement_core_view(final(self))) == crate::specs::ht_magref_sample(
            ht_refinement_core_view(old(self)), x, y, crate::magnitude::magnitude_value(delta), decoded_bitplanes),
            final(self).output.width == old(self).output.width,
            final(self).output.height == old(self).output.height,
            final(self).cleanup_significant@ == old(self).cleanup_significant@,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn magnitude_sample(
        &mut self,
        x: u16,
        y: u16,
        delta: Magnitude,
        decoded_bitplanes: u16,
    ) -> Result<(), DecodeError> {
        self.statistics.scanned(1)?;
        let index = self.output.index(x, y)?;
        if crate::refinement::ht_magref_eligible(
            *self
                .cleanup_significant
                .get(index)
                .ok_or_else(invalid_code_block)?,
        ) {
            let bit = self.readers.read_reverse()?;
            // The final upper half-bin truncates to the existing integer magnitude.
            let adjustment = if decoded_bitplanes == 2 && bit {
                crate::magnitude::magnitude_zero()
            } else {
                delta
            };
            self.output
                .apply_ht_refinement_decision(x, y, adjustment, bit)?;
            self.statistics.decoded_symbols(1)?;
            self.statistics.refined()?;
        }
        Ok(())
    }
}

impl HtSignificancePatchState<'_> {
    #[allow(
        clippy::too_many_arguments,
        reason = "The actual discovery column uses independent stripe, magnitude and causal inputs."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires rows <= 4,
        ensures (result, ht_sigprop_patch_view(final(self))) == crate::specs::ht_discovery_rows(
            ht_sigprop_patch_view(old(self)), x, stripe_y, rows as nat, 0, ht_refinement_magnitude_view(magnitude), causal),
            final(self).core.output.width == old(self).core.output.width,
            final(self).core.output.height == old(self).core.output.height,
            final(self).discovery.width == old(self).discovery.width,
            final(self).discovery.height == old(self).discovery.height,
            result == Ok(()) || result.is_err(),
    ))]
    fn discover_column(
        &mut self,
        x: u16,
        stripe_y: u16,
        rows: u16,
        magnitude: Magnitude,
        causal: bool,
    ) -> Result<(), DecodeError> {
        let mut row = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_discovery_rows); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant row <= rows <= 4,
                self.core.output.width == old(self).core.output.width, self.core.output.height == old(self).core.output.height,
                self.discovery.width == old(self).discovery.width, self.discovery.height == old(self).discovery.height,
                crate::specs::ht_discovery_rows(ht_sigprop_patch_view(old(self)), x, stripe_y, rows as nat, 0,
                    ht_refinement_magnitude_view(magnitude), causal) == crate::specs::ht_discovery_rows(
                        ht_sigprop_patch_view(self), x, stripe_y, rows as nat, row as nat, ht_refinement_magnitude_view(magnitude), causal),
            decreases rows - row,
        ))]
        while row < rows {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_discovery_rows); }
            let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
            self.discover_sample(x, y, magnitude, causal)?;
            row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_discovery_rows); }
        Ok(())
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "The actual four-column patch preserves its source traversal parameters."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires start <= end, rows <= 4,
        ensures (result, ht_sigprop_patch_view(final(self))) == crate::specs::ht_discovery_columns(
            ht_sigprop_patch_view(old(self)), end, stripe_y, rows as nat, start as nat, ht_refinement_magnitude_view(magnitude), causal),
            final(self).core.output.width == old(self).core.output.width,
            final(self).core.output.height == old(self).core.output.height,
            final(self).discovery.width == old(self).discovery.width,
            final(self).discovery.height == old(self).discovery.height,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn discover_patch(
        &mut self,
        start: u16,
        end: u16,
        stripe_y: u16,
        rows: u16,
        magnitude: Magnitude,
        causal: bool,
    ) -> Result<(), DecodeError> {
        let mut x = start;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_discovery_columns); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant start <= x <= end, rows <= 4,
                self.core.output.width == old(self).core.output.width, self.core.output.height == old(self).core.output.height,
                self.discovery.width == old(self).discovery.width, self.discovery.height == old(self).discovery.height,
                crate::specs::ht_discovery_columns(ht_sigprop_patch_view(old(self)), end, stripe_y, rows as nat, start as nat,
                    ht_refinement_magnitude_view(magnitude), causal) == crate::specs::ht_discovery_columns(
                        ht_sigprop_patch_view(self), end, stripe_y, rows as nat, x as nat, ht_refinement_magnitude_view(magnitude), causal),
            decreases end - x,
        ))]
        while x < end {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_discovery_columns); }
            self.discover_column(x, stripe_y, rows, magnitude, causal)?;
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_discovery_columns); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, ht_sigprop_patch_view(final(self))) == crate::specs::ht_pending_signs(
            ht_sigprop_patch_view(old(self)), 0, ht_refinement_magnitude_view(magnitude)),
            final(self).core.output.width == old(self).core.output.width,
            final(self).core.output.height == old(self).core.output.height,
            final(self).discovery.width == old(self).discovery.width,
            final(self).discovery.height == old(self).discovery.height,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn signs(&mut self, magnitude: Magnitude) -> Result<(), DecodeError> {
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_pending_signs); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.pending.len(), self.pending@ == old(self).pending@,
                self.core.output.width == old(self).core.output.width, self.core.output.height == old(self).core.output.height,
                self.discovery.width == old(self).discovery.width, self.discovery.height == old(self).discovery.height,
                crate::specs::ht_pending_signs(ht_sigprop_patch_view(old(self)), 0, ht_refinement_magnitude_view(magnitude))
                    == crate::specs::ht_pending_signs(ht_sigprop_patch_view(self), index as nat, ht_refinement_magnitude_view(magnitude)),
            decreases self.pending.len() - index,
        ))]
        while index < self.pending.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::ht_pending_signs); }
            self.sign_sample(index, magnitude)?;
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_pending_signs); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, ht_sigprop_patch_view(final(self))) == crate::specs::ht_discover_sample(
            ht_sigprop_patch_view(old(self)), x, y, ht_refinement_magnitude_view(magnitude), vertical_causal_context),
            final(self).core.output.width == old(self).core.output.width,
            final(self).core.output.height == old(self).core.output.height,
            final(self).discovery.width == old(self).discovery.width,
            final(self).discovery.height == old(self).discovery.height,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn discover_sample(
        &mut self,
        x: u16,
        y: u16,
        magnitude: Magnitude,
        vertical_causal_context: bool,
    ) -> Result<(), DecodeError> {
        self.core.statistics.scanned(1)?;
        if !self.discovery.coefficient(x, y)?.significant {
            let summary =
                self.discovery
                    .neighbor_summary_with_causality(x, y, vertical_causal_context)?;
            if crate::refinement::ht_sigprop_eligible(false, significant_neighbor_count(summary)) {
                let significant = self.core.readers.read_forward()?;
                self.core.statistics.decoded_symbols(1)?;
                if significant {
                    self.discovery
                        .mark_significant_magnitude(x, y, magnitude, false)?;
                    self.pending.push((x, y));
                }
            }
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, ht_sigprop_patch_view(final(self))) == crate::specs::ht_patch_sign_sample(
            ht_sigprop_patch_view(old(self)), index as nat, ht_refinement_magnitude_view(magnitude)),
            final(self).core.output.width == old(self).core.output.width,
            final(self).core.output.height == old(self).core.output.height,
            final(self).pending@ == old(self).pending@,
            result == Ok(()) || result.is_err(),
    ))]
    fn sign_sample(&mut self, index: usize, magnitude: Magnitude) -> Result<(), DecodeError> {
        let (x, y) = *self.pending.get(index).ok_or_else(invalid_code_block)?;
        let negative = self.core.readers.read_forward()?;
        self.core
            .output
            .mark_significant_magnitude(x, y, magnitude, negative)?;
        self.core.statistics.decoded_symbols(1)?;
        self.core.statistics.became_significant()?;
        Ok(())
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "The shared significance stripe keeps every original geometry and causal input."
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires width <= 4096, stripe_y <= 4096, rows <= 4,
    ensures ht_sigprop_plane_outcome(result) == crate::specs::ht_sigprop_patches(
        ht_sigprop_plane_view(&input), width, stripe_y, rows as nat, 0, ht_refinement_magnitude_view(magnitude), causal),
        result.1.core.output.width == input.core.output.width, result.1.core.output.height == input.core.output.height,
        result.1.discovery.width == input.discovery.width, result.1.discovery.height == input.discovery.height,
        result.0 == Ok(()) || result.0.is_err(),
))]
fn run_ht_significance_stripe(
    input: HtSigpropPlaneState<'_>,
    width: u16,
    stripe_y: u16,
    rows: u16,
    magnitude: Magnitude,
    causal: bool,
) -> (Result<(), DecodeError>, HtSigpropPlaneState<'_>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_sigprop_plane_view(&input); }
    let mut phase = input;
    let mut patch_x = 0_u16;
    let extent = match width.checked_add(3) {
        Some(value) => value,
        None => return (Err(arithmetic_overflow()), phase),
    };
    let mut patch_passes = match extent.checked_div(4) {
        Some(value) => value,
        None => return (Err(arithmetic_overflow()), phase),
    };
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::ht_sigprop_patches); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width <= 4096, stripe_y <= 4096, rows <= 4, patch_x <= width + 3,
            start == ht_sigprop_plane_view(&input),
            patch_passes == if patch_x >= width { 0int } else { (width - patch_x + 3) / 4 },
            phase.core.output.width == start.core.output.width, phase.core.output.height == start.core.output.height,
            phase.discovery.width == start.discovery.width, phase.discovery.height == start.discovery.height,
            crate::specs::ht_sigprop_patches(start, width, stripe_y, rows as nat, 0, ht_refinement_magnitude_view(magnitude), causal)
                == crate::specs::ht_sigprop_patches(ht_sigprop_plane_view(&phase), width, stripe_y, rows as nat,
                    patch_x as nat, ht_refinement_magnitude_view(magnitude), causal),
        decreases patch_passes,
    ))]
    while patch_x < width {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_sigprop_patches); }
        let patch_end = crate::refinement::ht_patch_end(patch_x, width);
        let mut patch = HtSignificancePatchState {
            core: phase.core,
            discovery: phase.discovery,
            pending: Vec::new(),
        };
        let discovered =
            patch.discover_patch(patch_x, patch_end, stripe_y, rows, magnitude, causal);
        let result = match discovered {
            Err(error) => Err(error),
            Ok(()) => patch.signs(magnitude),
        };
        phase = HtSigpropPlaneState {
            core: patch.core,
            discovery: patch.discovery,
        };
        if let Err(error) = result {
            return (Err(error), phase);
        }
        patch_x = match patch_x.checked_add(4) {
            Some(value) => value,
            None => return (Err(arithmetic_overflow()), phase),
        };
        patch_passes = match patch_passes.checked_sub(1) {
            Some(value) => value,
            None => return (Err(arithmetic_overflow()), phase),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::ht_sigprop_patches); }
    (Ok(()), phase)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires width <= 4096, height <= 4096,
    ensures ht_sigprop_plane_outcome(result) == crate::specs::ht_sigprop_stripes(
        ht_sigprop_plane_view(&input), width, height, 0, ht_refinement_magnitude_view(magnitude), causal),
        result.1.core.output.width == input.core.output.width, result.1.core.output.height == input.core.output.height,
        result.1.discovery.width == input.discovery.width, result.1.discovery.height == input.discovery.height,
        result.0 == Ok(()) || result.0.is_err(),
))]
pub(super) fn run_ht_significance_pass(
    input: HtSigpropPlaneState<'_>,
    width: u16,
    height: u16,
    magnitude: Magnitude,
    causal: bool,
) -> (Result<(), DecodeError>, HtSigpropPlaneState<'_>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_sigprop_plane_view(&input); }
    let mut phase = input;
    let mut stripe_y = 0_u16;
    let extent = match height.checked_add(3) {
        Some(value) => value,
        None => return (Err(arithmetic_overflow()), phase),
    };
    let mut stripe_passes = match extent.checked_div(4) {
        Some(value) => value,
        None => return (Err(arithmetic_overflow()), phase),
    };
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::ht_sigprop_stripes); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width <= 4096, height <= 4096, stripe_y <= height + 3,
            start == ht_sigprop_plane_view(&input),
            stripe_passes == if stripe_y >= height { 0int } else { (height - stripe_y + 3) / 4 },
            phase.core.output.width == start.core.output.width, phase.core.output.height == start.core.output.height,
            phase.discovery.width == start.discovery.width, phase.discovery.height == start.discovery.height,
            crate::specs::ht_sigprop_stripes(start, width, height, 0, ht_refinement_magnitude_view(magnitude), causal)
                == crate::specs::ht_sigprop_stripes(ht_sigprop_plane_view(&phase), width, height,
                    stripe_y as nat, ht_refinement_magnitude_view(magnitude), causal),
        decreases stripe_passes,
    ))]
    while stripe_y < height {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_sigprop_stripes); }
        let rows = crate::refinement::ht_stripe_rows(height, stripe_y);
        let (result, next) =
            run_ht_significance_stripe(phase, width, stripe_y, rows, magnitude, causal);
        phase = next;
        if let Err(error) = result {
            return (Err(error), phase);
        }
        stripe_y = match stripe_y.checked_add(4) {
            Some(value) => value,
            None => return (Err(arithmetic_overflow()), phase),
        };
        stripe_passes = match stripe_passes.checked_sub(1) {
            Some(value) => value,
            None => return (Err(arithmetic_overflow()), phase),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::ht_sigprop_stripes); }
    (Ok(()), phase)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_refinement_result(code_block_plane_view(cleanup_plane),ht_refinement_segment_view(&segment),refinement_passes,decoded_bitplanes,vertical_causal_context,
        crate::limits::resource_work_limit(limits),ht_plane_outcome(result)),
        ht_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==> ht_plane_outcome(result) == crate::specs::ht_refinement_plane(
        code_block_plane_view(cleanup_plane), ht_refinement_segment_view(&segment),
        refinement_passes, decoded_bitplanes, vertical_causal_context, crate::limits::resource_work_limit(limits)),
))]
pub(super) fn decode_ht_refinement_plane(
    cleanup_plane: &CodeBlockPlane,
    segment: HtRefinementSegment<'_>,
    refinement_passes: u8,
    decoded_bitplanes: u16,
    vertical_causal_context: bool,
    limits: &ResourceLimits,
) -> Result<(CodeBlockPlane, Tier1PassStatistics), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_refinement_normal(code_block_plane_view(cleanup_plane),ht_refinement_segment_view(&segment),refinement_passes,decoded_bitplanes,vertical_causal_context,crate::limits::resource_work_limit(limits));}
    if refinement_passes == 0 || refinement_passes > 2 || decoded_bitplanes < 2 {
        return Err(invalid_code_block());
    }
    let copied = cleanup_plane.duplicate(super::CoefficientStorageRole::RefinementOutput);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=copied {crate::specs::part2_plane_refinement_output_error(code_block_plane_view(cleanup_plane),ht_refinement_segment_view(&segment),refinement_passes,decoded_bitplanes,vertical_causal_context,crate::limits::resource_work_limit(limits),error);}}
    let output = copied?;
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost initial_output=code_block_plane_view(&output);}
    let readers = ht_refinement_readers_from_inputs(
        segment.significance_propagation().bytes(),
        segment.magnitude_refinement().bytes(),
        segment.encoded().len(),
        refinement_passes == 2,
        limits.maximum_work_units(),
    )?;
    let cleanup_significant = ht_collect_cleanup_significance(cleanup_plane.coefficients());
    let mut state = HtRefinementPlaneState {
        output,
        readers,
        cleanup_significant,
        statistics: ht_statistics_zero(),
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.output.width > 0 && state.output.height > 0);
        assert(state.output.width as nat * state.output.height as nat <= 4096);
        let width = state.output.width as nat;
        let height = state.output.height as nat;
        assert(width <= 4096 && height <= 4096) by(nonlinear_arith)
            requires width > 0, height > 0, width * height <= 4096;
    }

    if refinement_passes == 2 {
        let delta = ht_refinement_delta(decoded_bitplanes)?;
        let output_height = state.output.height();
        let output_width = state.output.width();
        state.magnitude_pass(output_width, output_height, delta, decoded_bitplanes)?;
    }

    let significance_magnitude = ht_significance_magnitude(decoded_bitplanes)?;
    let discovered = state
        .output
        .duplicate(super::CoefficientStorageRole::RefinementDiscovery);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=discovered {crate::specs::part2_plane_refinement_discovery_error(code_block_plane_view(cleanup_plane),ht_refinement_segment_view(&segment),
    refinement_passes,decoded_bitplanes,vertical_causal_context,crate::limits::resource_work_limit(limits),initial_output,ht_refinement_core_view(&state),error);}}
    let significance_plane = discovered?;
    let output_height = state.output.height();
    let output_width = state.output.width();
    let (result, phase) = run_ht_significance_pass(
        HtSigpropPlaneState {
            core: state,
            discovery: significance_plane,
        },
        output_width,
        output_height,
        significance_magnitude,
        vertical_causal_context,
    );
    result?;
    phase.core.readers.finish(segment.encoded())?;
    Ok((phase.core.output, phase.core.statistics))
}
