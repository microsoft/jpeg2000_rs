//! Borrowed selection and commits for the existing persistent configuration owners.

use super::{
    CodingStyle, ComponentCodingStyles, ComponentQuantizations, DecodeError, MalformedKind, Parser,
    ProgressionChanges, Quantization, RoiShifts, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    component_style_owner_view, inherited_tile_configuration_outcome, optional_roi_shifts_view,
    parsed_coding_style_view, parsed_quantization_owner_view, persistent_tile_configuration_view,
    persistent_tile_selection_view, quantization_owner_view, quantization_view, roi_shifts_view,
    tile_part_payload_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(super) type InheritedTileConfiguration = (
    Option<RoiShifts>,
    RoiShifts,
    CodingStyle,
    Quantization,
    ComponentCodingStyles,
);

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures *result == crate::specs::part1_inherited_tile_owner(index, *main, states@),
))]
pub(super) fn inherited_tile_owner<'owner, T>(
    index: usize,
    main: &'owner T,
    states: &'owner [Option<T>],
) -> &'owner T {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_inherited_tile_owner); }
    match states.get(index) {
        Some(Some(owner)) => owner,
        _ => main,
    }
}

impl Parser<'_> {
    #[inline]
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, persistent_tile_configuration_view(
            final(roi), final(styles), final(quantizations), final(style_parts),
            final(component_quantizations), final(progression)))
            == crate::specs::part1_commit_persistent_tile_configuration(
                self.position, start, index, payload_index, optional_roi_shifts_view(previous_roi),
                tile_part_payload_view(payload), persistent_tile_configuration_view(
                    old(roi), old(styles), old(quantizations), old(style_parts),
                    old(component_quantizations), old(progression))),
            result.is_ok() ==> index < final(style_parts).len()
                && final(style_parts)@ == old(style_parts)@.update(index as int, Some(payload_index)),
    ))]
    pub(super) fn commit_persistent_tile_configuration(
        &self,
        start: usize,
        index: usize,
        payload_index: usize,
        previous_roi: Option<RoiShifts>,
        payload: &TilePartPayload<'_>,
        roi: &mut [Option<RoiShifts>],
        styles: &mut [Option<CodingStyle>],
        quantizations: &mut [Option<Quantization>],
        style_parts: &mut [Option<usize>],
        component_quantizations: &mut [Option<ComponentQuantizations>],
        progression: &mut [Option<ProgressionChanges>],
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(persistent_tile_configuration_view);
            reveal(super::persistent_tile_configuration_sequences_view);
            reveal(optional_roi_shifts_view);
            reveal(tile_part_payload_view);
            reveal(roi_shifts_view);
            reveal(quantization_owner_view);
            reveal(parsed_quantization_owner_view);
            reveal(crate::specs::part1_commit_persistent_tile_configuration);
            reveal_with_fuel(crate::specs::part1_persistent_tile_configuration_prefix, 7);
        }
        let roi_consistent = match previous_roi {
            Some(previous) => previous.equals(&payload.roi_shifts),
            None => true,
        };
        if !roi_consistent {
            return Err(DecodeError::malformed(
                self.offset(start),
                MalformedKind::InvalidRegionOfInterest,
            ));
        }
        *roi.get_mut(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )? =
            Some(payload.roi_shifts);
        *styles
            .get_mut(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )? =
            Some(payload.coding_style);
        *quantizations
            .get_mut(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )? =
            Some(payload.quantization);
        *style_parts
            .get_mut(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )? =
            Some(payload_index);
        *component_quantizations
            .get_mut(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )? =
            Some(payload.component_quantizations.clone());
        *progression
            .get_mut(index)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                    ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                ))]
                || self.malformed_here(MalformedKind::InvalidTilePart),
            )? =
            Some(payload.progression_changes.clone());
        Ok(())
    }

    #[inline]
    #[allow(clippy::too_many_arguments)]
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures inherited_tile_configuration_outcome(result)
            == crate::specs::part1_select_inherited_tile_configuration(
                self.position, index, roi_shifts_view(main_roi),
                parsed_coding_style_view(*main_style), quantization_view(main_quantization),
                component_style_owner_view(main_components),
                persistent_tile_selection_view(roi, styles, quantizations, style_parts, payloads)),
    ))]
    pub(super) fn select_inherited_tile_configuration(
        &self,
        index: usize,
        main_roi: &RoiShifts,
        main_style: &CodingStyle,
        main_quantization: &Quantization,
        main_components: &ComponentCodingStyles,
        roi: &[Option<RoiShifts>],
        styles: &[Option<CodingStyle>],
        quantizations: &[Option<Quantization>],
        style_parts: &[Option<usize>],
        payloads: &[TilePartPayload<'_>],
    ) -> Result<InheritedTileConfiguration, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(inherited_tile_configuration_outcome);
            reveal(persistent_tile_selection_view);
            reveal(optional_roi_shifts_view);
            reveal(tile_part_payload_view);
            reveal(crate::specs::part1_select_inherited_tile_configuration);
        }
        let previous_roi_shifts = match roi.get(index) {
            Some(state) => *state,
            None => return Err(self.malformed_here(MalformedKind::InvalidTilePart)),
        };
        let inherited_roi_shifts = match previous_roi_shifts {
            Some(shifts) => shifts,
            None => *main_roi,
        };
        let inherited_default_style = match styles.get(index) {
            Some(Some(style)) => *style,
            _ => *main_style,
        };
        let inherited_default_quantization = match quantizations.get(index) {
            Some(Some(value)) => *value,
            _ => *main_quantization,
        };
        let inherited_component_styles = match style_parts.get(index) {
            Some(Some(part)) => {
                payloads
                    .get(*part)
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(error: DecodeError =>
                            ensures error == crate::specs::part1_codestream_malformed(self.position, MalformedKind::InvalidTilePart),
                        ))]
                        || self.malformed_here(MalformedKind::InvalidTilePart),
                    )?
                    .component_coding_styles
            }
            _ => *main_components,
        };
        Ok((
            previous_roi_shifts,
            inherited_roi_shifts,
            inherited_default_style,
            inherited_default_quantization,
            inherited_component_styles,
        ))
    }
}
