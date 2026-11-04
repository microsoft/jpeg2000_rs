//! Borrow-only commits into the existing persistent tile configuration owners.

use super::{
    CodingStyle, ComponentQuantizations, DecodeError, MalformedKind, Parser, ProgressionChanges,
    Quantization, RoiShifts, TilePartPayload,
};
#[cfg(verus_keep_ghost)]
use super::{
    optional_roi_shifts_view, parsed_quantization_owner_view, persistent_tile_configuration_view,
    quantization_owner_view, roi_shifts_view, tile_part_payload_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

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
}
