//! POC declaration scope and complete per-tile coverage after all parts arrive.
use super::{DecodeError, MalformedKind, Parser, ProgressionChange, Resource, TilePartPayload};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Parser<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_poc_resolutions(super::tile_part_payload_view(part), component),
    ))]
    fn poc_resolutions(
        &self,
        part: &TilePartPayload<'_>,
        component: u16,
    ) -> Result<u8, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(super::tile_part_payload_view);
            super::tile_part_native_styles_inverse(&part.component_coding_styles);
        }
        let levels = part
            .component_coding_styles
            .style(component)?
            .decomposition_levels;
        match levels.checked_add(1) {
            Some(levels) => Ok(levels),
            None => Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(work)) == crate::specs::part1_poc_charge(*old(work), self.limits),
    ))]
    fn charge_poc_coverage(&self, work: &mut u64) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_poc_charge); }
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint()?;
        let next = match work.checked_add(1) {
            Some(next) => next,
            None => return Err(self.malformed_at(0, MalformedKind::ArithmeticOverflow)),
        };
        *work = next;
        if next > self.limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: self.limits.maximum_work_units(),
                actual: next,
            });
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires end <= records.len(),
        ensures (result, *final(work)) == crate::specs::part1_poc_frontier_records(
            records@, coordinate, end, 0, frontier, *old(work), self.limits),
    ))]
    fn poc_record_frontier(
        &self,
        records: &[ProgressionChange],
        coordinate: (u16, u8),
        end: usize,
        frontier: u16,
        work: &mut u64,
    ) -> Result<u16, DecodeError> {
        let mut value = frontier;
        let mut record = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant record <= end <= records.len(),
                initial_work == *old(work),
                crate::specs::part1_poc_frontier_records(records@, coordinate, end, 0, frontier, *old(work), self.limits)
                    == crate::specs::part1_poc_frontier_records(records@, coordinate, end, record, value, *work, self.limits),
            decreases end - record,
        ))]
        while record < end {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_frontier_records, 1);
            }
            self.charge_poc_coverage(work)?;
            if records[record].contains(0, coordinate.1, coordinate.0) {
                value = value.max(records[record].layer_end);
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_frontier_records, 1); }
            record += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_poc_frontier_records, 1);
            assert(crate::specs::part1_poc_frontier_records(records@, coordinate, end, record, value, *work, self.limits)
                == (Ok(value), *work));
        }
        Ok(value)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(work)) == crate::specs::part1_poc_frontier_run(
            super::tile_parts_payload_view(parts@), tile, coordinate, prefix, 0, 0, *old(work), self.limits),
    ))]
    fn poc_frontier(
        &self,
        parts: &[TilePartPayload<'_>],
        tile: u16,
        coordinate: (u16, u8),
        prefix: (usize, usize),
        work: &mut u64,
    ) -> Result<u16, DecodeError> {
        let mut frontier = 0_u16;
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= parts.len(),
                initial_work == *old(work),
                crate::specs::part1_poc_frontier_run(super::tile_parts_payload_view(parts@), tile, coordinate, prefix, 0, 0, *old(work), self.limits)
                    == crate::specs::part1_poc_frontier_run(super::tile_parts_payload_view(parts@), tile, coordinate, prefix, index, frontier, *work, self.limits),
            decreases parts.len() - index,
        ))]
        while index < parts.len() && index <= prefix.0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_frontier_run, 1);
                reveal(super::tile_part_payload_view);
            }
            self.charge_poc_coverage(work)?;
            let part = &parts[index];
            if part.tile_index == tile {
                let records = part.progression_changes.records();
                let end = if index == prefix.0 {
                    prefix.1.min(records.len())
                } else {
                    records.len()
                };
                frontier = self.poc_record_frontier(records, coordinate, end, frontier, work)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_frontier_run, 1);
            }
            index = index
                .checked_add(1)
                .ok_or_else(|| self.malformed_at(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_poc_frontier_run, 1);
            assert(crate::specs::part1_poc_frontier_run(super::tile_parts_payload_view(parts@), tile, coordinate, prefix, index, frontier, *work, self.limits)
                == (Ok(frontier), *work));
        }
        Ok(frontier)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(work)) == crate::specs::part1_poc_first_run(
            super::tile_parts_payload_view(parts@), tile, 0, *old(work), self.limits),
    ))]
    fn first_tile_poc(
        &self,
        parts: &[TilePartPayload<'_>],
        tile: u16,
        work: &mut u64,
    ) -> Result<bool, DecodeError> {
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= parts.len(),
                initial_work == *old(work),
                crate::specs::part1_poc_first_run(super::tile_parts_payload_view(parts@), tile, 0, *old(work), self.limits)
                    == crate::specs::part1_poc_first_run(super::tile_parts_payload_view(parts@), tile, index, *work, self.limits),
            decreases parts.len() - index,
        ))]
        while index < parts.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_first_run, 1);
                reveal(super::tile_part_payload_view);
            }
            self.charge_poc_coverage(work)?;
            if parts[index].tile_index == tile && parts[index].tile_part_index == 0 {
                return Ok(parts[index].has_progression_marker);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_first_run, 1);
            }
            index = index
                .checked_add(1)
                .ok_or_else(|| self.malformed_at(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_poc_first_run, 1);
            assert(crate::specs::part1_poc_first_run(super::tile_parts_payload_view(parts@), tile, index, *work, self.limits)
                == (Ok(false), *work));
        }
        Ok(false)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires index < parts.len(), record_index < parts@[index as int].progression_changes.records@.len(),
        ensures (result, *final(work)) == crate::specs::part1_poc_novel_resolutions(
            super::tile_parts_payload_view(parts@), index, record_index, component,
            parts@[index as int].progression_changes.records@[record_index as int].resolution_start,
            resolutions, *old(work), self.limits),
    ))]
    fn novel_poc_resolutions(
        &self,
        parts: &[TilePartPayload<'_>],
        index: usize,
        record_index: usize,
        component: u16,
        resolutions: u8,
        work: &mut u64,
    ) -> Result<bool, DecodeError> {
        let part = &parts[index];
        let record = part.progression_changes.records()[record_index];
        let mut resolution = record.resolution_start;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index < parts.len(), record_index < parts@[index as int].progression_changes.records@.len(),
                initial_work == *old(work),
                super::tile_part_payload_view(part) == super::tile_parts_payload_view(parts@)[index as int],
                record == super::tile_parts_payload_view(parts@)[index as int].progression_changes[record_index as int],
                crate::specs::part1_poc_novel_resolutions(
                super::tile_parts_payload_view(parts@), index, record_index, component, record.resolution_start, resolutions, *old(work), self.limits)
                == crate::specs::part1_poc_novel_resolutions(
                    super::tile_parts_payload_view(parts@), index, record_index, component, resolution, resolutions, *work, self.limits),
            decreases if resolution < resolutions { resolutions - resolution } else { 0 },
        ))]
        while resolution < record.resolution_end && resolution < resolutions {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_novel_resolutions, 1);
                reveal(super::tile_part_payload_view);
            }
            let before = self.poc_frontier(
                parts,
                part.tile_index,
                (component, resolution),
                (index, record_index),
                work,
            )?;
            if record.layer_end.min(part.coding_style.layers) > before {
                return Ok(true);
            }
            resolution += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_novel_resolutions, 1); }
        Ok(false)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(work)) == crate::specs::part1_poc_novel_record(
            super::tile_parts_payload_view(parts@), index, record_index, *old(work), self.limits),
    ))]
    fn novel_tile_poc(
        &self,
        parts: &[TilePartPayload<'_>],
        index: usize,
        record_index: usize,
        work: &mut u64,
    ) -> Result<bool, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_poc_novel_record);
            reveal(super::tile_part_payload_view);
        }
        let part = match parts.get(index) {
            Some(part) => part,
            None => return Err(self.malformed_at(0, MalformedKind::InvalidTilePart)),
        };
        let record = match part.progression_changes.records().get(record_index) {
            Some(record) => *record,
            None => return Err(self.malformed_at(0, MalformedKind::InvalidProgressionOrderChange)),
        };
        let mut component = record.component_start;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component >= record.component_start,
                index < parts.len(), record_index < parts@[index as int].progression_changes.records@.len(),
                initial_work == *old(work),
                super::tile_part_payload_view(part) == super::tile_parts_payload_view(parts@)[index as int],
                record == super::tile_parts_payload_view(parts@)[index as int].progression_changes[record_index as int],
                crate::specs::part1_poc_novel_components(super::tile_parts_payload_view(parts@), index, record_index,
                    record.component_start, *old(work), self.limits)
                    == crate::specs::part1_poc_novel_components(super::tile_parts_payload_view(parts@), index, record_index,
                        component, *work, self.limits),
            decreases if component < record.component_end { record.component_end - component } else { 0 },
        ))]
        while component < record.component_end
            && component < part.component_coding_styles.components
        {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_poc_novel_components, 1); }
            let resolutions = self.poc_resolutions(part, component)?;
            if self.novel_poc_resolutions(
                parts,
                index,
                record_index,
                component,
                resolutions,
                work,
            )? {
                return Ok(true);
            }
            component += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_novel_components, 1); }
        Ok(false)
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires index < parts.len(),
        ensures (result, *final(work)) == crate::specs::part1_poc_complete_resolutions(
            super::tile_parts_payload_view(parts@), index, component, 0, resolutions, *old(work), self.limits),
    ))]
    fn complete_poc_resolutions(
        &self,
        parts: &[TilePartPayload<'_>],
        index: usize,
        component: u16,
        resolutions: u8,
        work: &mut u64,
    ) -> Result<(), DecodeError> {
        let part = &parts[index];
        let mut resolution = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant resolution <= resolutions,
                index < parts.len(), initial_work == *old(work),
                super::tile_part_payload_view(part) == super::tile_parts_payload_view(parts@)[index as int],
                crate::specs::part1_poc_complete_resolutions(super::tile_parts_payload_view(parts@), index, component, 0, resolutions, *old(work), self.limits)
                    == crate::specs::part1_poc_complete_resolutions(super::tile_parts_payload_view(parts@), index, component, resolution, resolutions, *work, self.limits),
            decreases resolutions - resolution,
        ))]
        while resolution < resolutions {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_complete_resolutions, 1);
                reveal(super::tile_part_payload_view);
            }
            let frontier = self.poc_frontier(
                parts,
                part.tile_index,
                (component, resolution),
                (parts.len(), 0),
                work,
            )?;
            if frontier < part.coding_style.layers {
                return Err(self.malformed_at(0, MalformedKind::InvalidProgressionOrderChange));
            }
            resolution += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_complete_resolutions, 1); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires index < parts.len(),
        ensures (result, *final(work)) == crate::specs::part1_poc_complete_components(
            super::tile_parts_payload_view(parts@), index, 0, *old(work), self.limits),
    ))]
    fn complete_tile_poc(
        &self,
        parts: &[TilePartPayload<'_>],
        index: usize,
        work: &mut u64,
    ) -> Result<(), DecodeError> {
        let part = &parts[index];
        let mut component = 0_u16;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant component <= part.component_coding_styles.components,
                index < parts.len(), initial_work == *old(work),
                super::tile_part_payload_view(part) == super::tile_parts_payload_view(parts@)[index as int],
                crate::specs::part1_poc_complete_components(super::tile_parts_payload_view(parts@), index, 0, *old(work), self.limits)
                    == crate::specs::part1_poc_complete_components(super::tile_parts_payload_view(parts@), index, component, *work, self.limits),
            decreases part.component_coding_styles.components - component,
        ))]
        while component < part.component_coding_styles.components {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_complete_components, 1);
                reveal(super::tile_part_payload_view);
            }
            let resolutions = self.poc_resolutions(part, component)?;
            self.complete_poc_resolutions(parts, index, component, resolutions, work)?;
            component += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_complete_components, 1); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires index < parts.len(),
        ensures (result, *final(work)) == crate::specs::part1_poc_coverage_records(
            super::tile_parts_payload_view(parts@), index, 0, *old(work), self.limits),
    ))]
    fn validate_tile_poc_records(
        &self,
        parts: &[TilePartPayload<'_>],
        index: usize,
        work: &mut u64,
    ) -> Result<(), DecodeError> {
        let part = &parts[index];
        let mut record = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost initial_work = *work; }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant record <= super::progression_changes_view(&part.progression_changes).len(),
                index < parts.len(), initial_work == *old(work),
                super::tile_part_payload_view(part) == super::tile_parts_payload_view(parts@)[index as int],
                crate::specs::part1_poc_coverage_records(super::tile_parts_payload_view(parts@), index, 0, *old(work), self.limits)
                    == crate::specs::part1_poc_coverage_records(super::tile_parts_payload_view(parts@), index, record, *work, self.limits),
            decreases super::progression_changes_view(&part.progression_changes).len() - record,
        ))]
        while record < part.progression_changes.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_coverage_records, 1);
                reveal(super::tile_part_payload_view);
            }
            if !self.novel_tile_poc(parts, index, record, work)? {
                return Err(self.malformed_at(0, MalformedKind::InvalidProgressionOrderChange));
            }
            record = record
                .checked_add(1)
                .ok_or_else(|| self.malformed_at(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_poc_coverage_records, 1); }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_complete_poc_coverage(
            super::tile_parts_payload_view(parts@), self.limits),
    ))]
    pub(super) fn validate_tile_progression_coverage(
        &self,
        parts: &[TilePartPayload<'_>],
    ) -> Result<(), DecodeError> {
        let mut work = 0_u64;
        let mut index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_complete_poc_coverage); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= parts.len(),
                crate::specs::part1_complete_poc_coverage(super::tile_parts_payload_view(parts@), self.limits)
                    == crate::specs::part1_poc_coverage_run(super::tile_parts_payload_view(parts@), index, work, self.limits).0,
                crate::specs::part1_poc_coverage_run(super::tile_parts_payload_view(parts@), 0, 0, self.limits)
                    == crate::specs::part1_poc_coverage_run(super::tile_parts_payload_view(parts@), index, work, self.limits),
            decreases parts.len() - index,
        ))]
        while index < parts.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_coverage_run, 1);
                reveal(super::tile_part_payload_view);
            }
            self.charge_poc_coverage(&mut work)?;
            let part = &parts[index];
            if part.tile_part_index == 0 && !part.progression_changes.is_empty() {
                self.complete_tile_poc(parts, index, &mut work)?;
            }
            if part.has_progression_marker {
                if !self.first_tile_poc(parts, part.tile_index, &mut work)? {
                    return Err(self.malformed_at(0, MalformedKind::InvalidMarkerOrder));
                }
                self.validate_tile_poc_records(parts, index, &mut work)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::part1_poc_coverage_run, 1);
            }
            index = index
                .checked_add(1)
                .ok_or_else(|| self.malformed_at(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_poc_coverage_run, 1);
            assert(crate::specs::part1_poc_coverage_run(super::tile_parts_payload_view(parts@), index, work, self.limits)
                == (Ok(()), work));
        }
        Ok(())
    }
}
