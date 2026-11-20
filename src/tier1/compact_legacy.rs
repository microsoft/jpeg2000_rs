use super::state::{
    ht_statistics_zero, invalid_code_block, sign_context, significant_neighbor_count,
    zero_coding_context,
};
use super::{
    CoefficientState, NeighborSummary, RUN_LENGTH_CONTEXT, SubbandOrientation, Tier1BitplaneState,
    Tier1BlockCoding, Tier1CodeBlockDecoder, Tier1PassKind, Tier1PassStatistics, UNIFORM_CONTEXT,
};
use crate::mq::MqDecoder;
use crate::{DecodeError, ResourceLimits};

const MAG: u64 = u32::MAX as u64;
const BP_SHIFT: u32 = 32;
const BP_MASK: u64 = 63 << BP_SHIFT;
const EMPTY: u64 = BP_MASK;
const SIG: u64 = 1 << 38;
const NEG: u64 = 1 << 39;
const REFINED: u64 = 1 << 40;
const SIG_NEIGHBORS: u32 = 41;
const NEG_NEIGHBORS: u32 = 49;
const CACHE: bool = true;
const DIRECTIONS: [(i32, i32); 8] = [
    (-1, -1),
    (0, -1),
    (1, -1),
    (-1, 0),
    (1, 0),
    (-1, 1),
    (0, 1),
    (1, 1),
];

struct CompactPlane {
    width: usize,
    height: usize,
    entries: Vec<u64>,
}

impl CompactPlane {
    fn summary(&self, x: usize, y: usize, causal: bool) -> NeighborSummary {
        let (mut sig, mut neg) = if CACHE {
            let value = self.entries[y * self.width + x];
            (
                (value >> SIG_NEIGHBORS) as u8,
                (value >> NEG_NEIGHBORS) as u8,
            )
        } else {
            let mut sig = 0u8;
            let mut neg = 0u8;
            for (bit, (dx, dy)) in DIRECTIONS.iter().enumerate() {
                let nx = x as i32 + dx;
                let ny = y as i32 + dy;
                if nx >= 0 && ny >= 0 && nx < self.width as i32 && ny < self.height as i32 {
                    let value = self.entries[ny as usize * self.width + nx as usize];
                    if value & SIG != 0 {
                        sig |= 1 << bit;
                        if value & NEG != 0 {
                            neg |= 1 << bit;
                        }
                    }
                }
            }
            (sig, neg)
        };
        if causal && y % 4 == 3 {
            sig &= 0x1f;
            neg &= 0x1f;
        }
        neg &= sig;
        let h = (sig & 0x18).count_ones() as u8;
        let v = (sig & 0x42).count_ones() as u8;
        NeighborSummary {
            horizontal_significant: h,
            vertical_significant: v,
            diagonal_significant: (sig & 0xa5).count_ones() as u8,
            horizontal_sign_balance: h as i8 - 2 * (neg & 0x18).count_ones() as i8,
            vertical_sign_balance: v as i8 - 2 * (neg & 0x42).count_ones() as i8,
        }
    }

    fn sign_and_mark(
        &mut self,
        x: usize,
        y: usize,
        bp: u16,
        summary: NeighborSummary,
        decoder: &mut MqDecoder<'_>,
    ) -> Result<(), DecodeError> {
        let sign = sign_context(summary);
        let bit = decoder.decode(usize::from(sign.context))?;
        let negative = crate::refinement::tier1_decoded_sign(bit, sign.predicted_negative, false);
        self.mark(x, y, bp, negative);
        Ok(())
    }

    fn mark(&mut self, x: usize, y: usize, bp: u16, negative: bool) {
        let index = y * self.width + x;
        self.entries[index] = (self.entries[index] & !(MAG | BP_MASK | NEG | REFINED))
            | (1u64 << bp)
            | ((u64::from(bp)) << BP_SHIFT)
            | SIG
            | if negative { NEG } else { 0 };
        if CACHE {
            for (direction, (dx, dy)) in DIRECTIONS.iter().enumerate() {
                let nx = x as i32 + dx;
                let ny = y as i32 + dy;
                if nx >= 0 && ny >= 0 && nx < self.width as i32 && ny < self.height as i32 {
                    let bit = 7 - direction;
                    let target = &mut self.entries[ny as usize * self.width + nx as usize];
                    *target |= 1u64 << (SIG_NEIGHBORS + bit as u32);
                    if negative {
                        *target |= 1u64 << (NEG_NEIGHBORS + bit as u32);
                    }
                }
            }
        }
    }

    fn initial_state(&self, bp: u16) -> Result<Tier1BitplaneState, DecodeError> {
        let mut significant_before = crate::allocation::empty_with_capacity(self.entries.len())?;
        significant_before.extend(self.entries.iter().map(|value| value & SIG != 0));
        let significance_visited = crate::allocation::filled_values(false, self.entries.len())?;
        Ok(Tier1BitplaneState {
            width: self.width as u16,
            height: self.height as u16,
            bitplane: bp,
            significant_before,
            significance_visited,
            significance_propagation_complete: false,
            magnitude_refinement_complete: false,
            cleanup_complete: false,
        })
    }

    fn sig_cell(
        &mut self,
        x: usize,
        y: usize,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        orientation: SubbandOrientation,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        stats.coefficients_scanned += 1;
        let index = y * self.width + x;
        if self.entries[index] & SIG == 0 {
            let summary = self.summary(x, y, causal);
            if significant_neighbor_count(summary) != 0 {
                let bit = decoder.decode(usize::from(zero_coding_context(summary, orientation)))?;
                state.significance_visited[index] = true;
                stats.coding_symbols += 1;
                if bit {
                    self.sign_and_mark(x, y, state.bitplane, summary, decoder)?;
                    stats.coding_symbols += 1;
                    stats.newly_significant += 1;
                }
            }
        }
        Ok(())
    }

    fn refine_cell(
        &mut self,
        x: usize,
        y: usize,
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        stats.coefficients_scanned += 1;
        let index = y * self.width + x;
        if state.significant_before[index] {
            let before = self.entries[index];
            let neighbors = if before & REFINED != 0 {
                0
            } else {
                u16::from(significant_neighbor_count(self.summary(x, y, causal)))
            };
            let context =
                crate::refinement::tier1_refinement_context(before & REFINED != 0, neighbors);
            let bit = decoder.decode(usize::from(context))?;
            stats.coding_symbols += 1;
            if bit {
                self.entries[index] += 1u64 << state.bitplane;
            }
            self.entries[index] = (self.entries[index] & !BP_MASK)
                | ((u64::from(state.bitplane)) << BP_SHIFT)
                | REFINED;
            stats.refined_coefficients += 1;
        }
        Ok(())
    }

    fn cleanup_cell(
        &mut self,
        x: usize,
        y: usize,
        state: &Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        orientation: SubbandOrientation,
        causal: bool,
        stats: &mut Tier1PassStatistics,
    ) -> Result<(), DecodeError> {
        let index = y * self.width + x;
        if self.entries[index] & SIG == 0 && !state.significance_visited[index] {
            let summary = self.summary(x, y, causal);
            let bit = decoder.decode(usize::from(zero_coding_context(summary, orientation)))?;
            stats.coding_symbols += 1;
            if bit {
                self.sign_and_mark(x, y, state.bitplane, summary, decoder)?;
                stats.coding_symbols += 1;
                stats.newly_significant += 1;
            }
        }
        Ok(())
    }

    fn run_candidate(&self, x: usize, y: usize, state: &Tier1BitplaneState, causal: bool) -> bool {
        self.entries[y * self.width + x] & SIG == 0
            && !state.significance_visited[y * self.width + x]
            && significant_neighbor_count(self.summary(x, y, causal)) == 0
    }

    fn pass(
        &mut self,
        state: &mut Tier1BitplaneState,
        decoder: &mut MqDecoder<'_>,
        kind: Tier1PassKind,
        orientation: SubbandOrientation,
        causal: bool,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut stats = ht_statistics_zero();
        let mut stripe = 0;
        while stripe < self.height {
            #[cfg(feature = "cooperative-deadlines")]
            crate::deadline::checkpoint()?;
            let rows = (self.height - stripe).min(4);
            for x in 0..self.width {
                match kind {
                    Tier1PassKind::SignificancePropagation => {
                        for row in 0..rows {
                            self.sig_cell(
                                x,
                                stripe + row,
                                state,
                                decoder,
                                orientation,
                                causal,
                                &mut stats,
                            )?;
                        }
                    }
                    Tier1PassKind::MagnitudeRefinement => {
                        for row in 0..rows {
                            self.refine_cell(x, stripe + row, state, decoder, causal, &mut stats)?;
                        }
                    }
                    Tier1PassKind::Cleanup => {
                        let run = rows == 4
                            && (0..4).all(|row| self.run_candidate(x, stripe + row, state, causal));
                        if run {
                            stats.coefficients_scanned += 4;
                            stats.run_mode_columns += 1;
                            let interrupted = decoder.decode(RUN_LENGTH_CONTEXT)?;
                            stats.coding_symbols += 1;
                            if interrupted {
                                let high = decoder.decode(UNIFORM_CONTEXT)?;
                                let low = decoder.decode(UNIFORM_CONTEXT)?;
                                stats.coding_symbols += 2;
                                let row = usize::from(high) * 2 + usize::from(low);
                                let summary = self.summary(x, stripe + row, causal);
                                self.sign_and_mark(
                                    x,
                                    stripe + row,
                                    state.bitplane,
                                    summary,
                                    decoder,
                                )?;
                                stats.coding_symbols += 1;
                                stats.newly_significant += 1;
                                for tail in row + 1..4 {
                                    self.cleanup_cell(
                                        x,
                                        stripe + tail,
                                        state,
                                        decoder,
                                        orientation,
                                        causal,
                                        &mut stats,
                                    )?;
                                }
                            }
                        } else {
                            for row in 0..rows {
                                stats.coefficients_scanned += 1;
                                self.cleanup_cell(
                                    x,
                                    stripe + row,
                                    state,
                                    decoder,
                                    orientation,
                                    causal,
                                    &mut stats,
                                )?;
                            }
                        }
                    }
                }
            }
            stripe += rows;
        }
        match kind {
            Tier1PassKind::SignificancePropagation => {
                state.significance_propagation_complete = true
            }
            Tier1PassKind::MagnitudeRefinement => state.magnitude_refinement_complete = true,
            Tier1PassKind::Cleanup => state.cleanup_complete = true,
        }
        Ok(stats)
    }
}

impl Tier1CodeBlockDecoder {
    pub(super) fn try_compact_legacy(
        &mut self,
        decoder: &mut MqDecoder<'_>,
        passes: u32,
        limits: &ResourceLimits,
    ) -> Option<Result<Tier1PassStatistics, DecodeError>> {
        let count = usize::from(self.plane.width) * usize::from(self.plane.height);
        if self.next_pass != 0
            || self.decoded_segments != 0
            || self.bitplane >= 31
            || self.bitplane_state.is_some()
            || self.legacy_segment.is_some()
            || passes != self.maximum_passes
            || passes != 3 * (u32::from(self.bitplane) + 1) - 2
            || count == 0
            || count > 4096
            || self.plane.coefficients.len() != count
            || !matches!(self.style.block_coding, Tier1BlockCoding::Legacy)
            || self.style.force_high_throughput
            || self.style.selective_arithmetic_coding_bypass
            || self.style.reset_contexts
            || self.style.terminate_all_passes
            || self.style.segmentation_symbols
            || (count as u64) * (core::mem::size_of::<CoefficientState>() as u64 + 10)
                > limits.maximum_decoded_bytes()
            || self.plane.coefficients.iter().any(|c| {
                c.magnitude != 0
                    || c.magnitude_high != [0; 5]
                    || c.legacy_bitplane.is_some()
                    || c.significant
                    || c.negative
                    || c.refined
            })
        {
            return None;
        }
        let result = crate::allocation::empty_with_capacity(count);
        let mut entries = match result {
            Ok(v) => v,
            Err(error) => return Some(Err(error)),
        };
        entries.resize(count, EMPTY);
        let mut packed = CompactPlane {
            width: usize::from(self.plane.width),
            height: usize::from(self.plane.height),
            entries,
        };
        let result = self.compact_passes(&mut packed, decoder, passes);
        for (wide, packed) in self.plane.coefficients.iter_mut().zip(packed.entries) {
            let bp = (packed & BP_MASK) >> BP_SHIFT;
            *wide = CoefficientState {
                magnitude: packed & MAG,
                magnitude_high: [0; 5],
                legacy_bitplane: if bp == 63 { None } else { Some(bp as u16) },
                significant: packed & SIG != 0,
                negative: packed & NEG != 0,
                refined: packed & REFINED != 0,
            };
        }

        #[cfg(test)]
        mod tests {
            use super::super::Tier1CodingStyle;
            use super::*;

            #[test]
            fn incremental_flags_match_checked_neighbors_after_every_mark() {
                let mut wide = super::super::CodeBlockPlane::new(7, 9).unwrap();
                let mut compact = CompactPlane {
                    width: 7,
                    height: 9,
                    entries: vec![EMPTY; 63],
                };
                for index in (0..63).map(|i| (i * 17) % 63) {
                    let x = index % 7;
                    let y = index / 7;
                    let negative = index % 3 == 0;
                    compact.mark(x, y, 4, negative);
                    wide.mark_significant_at_bitplane(x as u16, y as u16, 4, negative)
                        .unwrap();
                    for causal in [false, true] {
                        for yy in 0..9 {
                            for xx in 0..7 {
                                assert_eq!(
                                    compact.summary(xx, yy, causal),
                                    wide.neighbor_summary_with_causality(
                                        xx as u16, yy as u16, causal
                                    )
                                    .unwrap()
                                );
                            }
                        }
                    }
                }
            }

            #[test]
            fn bounded_complete_mq_block_reaches_compact_kernel() {
                let limits = ResourceLimits::default();
                let mut block = Tier1CodeBlockDecoder::new(
                    4,
                    4,
                    8,
                    SubbandOrientation::Ll,
                    Tier1CodingStyle::default(),
                )
                .unwrap();
                let mut mq = crate::mq::mq_from_input(
                    &[0x84, 0x3f, 0x00, 0xff, 0x7f],
                    100,
                    limits.maximum_work_units(),
                )
                .unwrap();
                super::super::state::initialize_tier1_contexts(&mut mq).unwrap();
                let passes = block.maximum_passes;
                assert!(block.try_compact_legacy(&mut mq, passes, &limits).is_some());
            }

            #[test]
            fn compact_matches_checked_result_and_every_visible_error_prefix() {
                for (width, height) in [(1, 1), (3, 5), (16, 16)] {
                    for planes in [1, 8, 31] {
                        for causal in [false, true] {
                            for input in [
                                &[0x84][..],
                                &[0xff, 0x90][..],
                                &[0x84, 0x3f, 0x00, 0xff, 0x7f][..],
                            ] {
                                for work in [1, 2, 7, 128, 100_000] {
                                    let mut style = Tier1CodingStyle::default();
                                    style.vertical_causal_context = causal;
                                    let mut compact = Tier1CodeBlockDecoder::new(
                                        width,
                                        height,
                                        planes,
                                        SubbandOrientation::Hh,
                                        style,
                                    )
                                    .unwrap();
                                    let mut scalar = compact.clone();
                                    let limits = ResourceLimits::default()
                                        .with_maximum_work_units(work)
                                        .unwrap();
                                    let scalar_limits = limits
                                        .with_maximum_decoded_bytes(
                                            u64::from(width) * u64::from(height) * 56,
                                        )
                                        .unwrap();
                                    let passes = u8::try_from(compact.maximum_passes).unwrap();
                                    let actual = compact.decode_segment(input, passes, &limits);
                                    let expected =
                                        scalar.decode_segment(input, passes, &scalar_limits);
                                    assert_eq!(
                                        actual, expected,
                                        "shape{width}x{height} planes{planes} work{work} causal{causal}"
                                    );
                                    assert_eq!(
                                        format!("{compact:?}"),
                                        format!("{scalar:?}"),
                                        "shape{width}x{height} planes{planes} work{work} causal{causal}"
                                    );
                                }

                                #[test]
                                fn compact_preserves_actual_mq_register_context_and_work_error_state()
                                 {
                                    for planes in [1, 8, 31] {
                                        for causal in [false, true] {
                                            for work in [1, 2, 7, 128, 100_000] {
                                                let mut style = Tier1CodingStyle::default();
                                                style.vertical_causal_context = causal;
                                                let mut compact = Tier1CodeBlockDecoder::new(
                                                    5,
                                                    7,
                                                    planes,
                                                    SubbandOrientation::Hl,
                                                    style,
                                                )
                                                .unwrap();
                                                let mut scalar = compact.clone();
                                                let limits = ResourceLimits::default()
                                                    .with_maximum_work_units(work)
                                                    .unwrap();
                                                let input = [0x84, 0x3f, 0x00, 0xff, 0x7f];
                                                let mut mq =
                                                    crate::mq::mq_from_input(&input, 100, work)
                                                        .unwrap();
                                                super::super::state::initialize_tier1_contexts(
                                                    &mut mq,
                                                )
                                                .unwrap();
                                                let mut reference =
                                                    crate::mq::mq_from_input(&input, 100, work)
                                                        .unwrap();
                                                super::super::state::initialize_tier1_contexts(
                                                    &mut reference,
                                                )
                                                .unwrap();
                                                let passes = compact.maximum_passes;
                                                let actual = compact
                                                    .try_compact_legacy(&mut mq, passes, &limits)
                                                    .unwrap();
                                                let expected = scalar.decode_mq_segment_passes(
                                                    &mut reference,
                                                    passes,
                                                );
                                                assert_eq!(actual, expected);
                                                assert_eq!(
                                                    format!("{compact:?}"),
                                                    format!("{scalar:?}")
                                                );
                                                assert_eq!(
                                                    format!("{mq:?}"),
                                                    format!("{reference:?}")
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        Some(result)
    }

    fn compact_passes(
        &mut self,
        packed: &mut CompactPlane,
        decoder: &mut MqDecoder<'_>,
        passes: u32,
    ) -> Result<Tier1PassStatistics, DecodeError> {
        let mut total = ht_statistics_zero();
        for _ in 0..passes {
            #[cfg(feature = "cooperative-deadlines")]
            crate::deadline::checkpoint()?;
            let kind = self.style.pass_plan(self.next_pass).kind;
            if self.bitplane_state.is_none() {
                self.bitplane_state = Some(packed.initial_state(self.bitplane)?);
            }
            let stats = packed.pass(
                self.bitplane_state
                    .as_mut()
                    .ok_or_else(invalid_code_block)?,
                decoder,
                kind,
                self.orientation,
                self.style.vertical_causal_context,
            )?;
            total.coefficients_scanned += stats.coefficients_scanned;
            total.coding_symbols += stats.coding_symbols;
            total.newly_significant += stats.newly_significant;
            total.refined_coefficients += stats.refined_coefficients;
            total.run_mode_columns += stats.run_mode_columns;
            self.next_pass += 1;
            if matches!(kind, Tier1PassKind::Cleanup) {
                self.bitplane_state = None;
                if self.next_pass < self.maximum_passes {
                    self.bitplane -= 1;
                }
            }
        }
        Ok(total)
    }
}
