use super::ht_cleanup_readers::ht_magsgn_from_input;
use super::ht_metadata::decode_ht_cleanup_segment_metadata;
use super::state::{
    arithmetic_overflow, code_block_plane_from_dimensions, ht_statistics_zero, invalid_code_block,
};
use super::{
    CodeBlockPlane, HtCleanupMetadata, HtCleanupPlaneReconstruction, HtCleanupSegment,
    HtForwardMagSgnReader, HtQuadMetadata, MAX_HT_MAGSGN_BITS, MAX_TIER1_BITPLANES,
    Tier1PassStatistics,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_view, ht_cleanup_metadata_view, ht_cleanup_prepare_outcome,
    ht_cleanup_segment_view, ht_magsgn_view, ht_numeric_magnitude_outcome, ht_plane_outcome,
    ht_plane_view,
};
use crate::magnitude::Magnitude;
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::ht_complete_kappa(
        u_base, significance, north_west_exponent, north_east_exponent, maximum_u),
))]
pub fn complete_ht_kappa(
    u_base: u8,
    significance: u8,
    north_west_exponent: u8,
    north_east_exponent: u8,
    maximum_u: u8,
) -> Result<u8, DecodeError> {
    if u_base == 0 || significance & 0xf0 != 0 || maximum_u == 0 || maximum_u > MAX_HT_MAGSGN_BITS {
        return Err(invalid_code_block());
    }
    let gamma = significance & significance.wrapping_sub(1) != 0;
    let exponent = north_west_exponent.max(north_east_exponent);
    if u_base > u8::MAX - exponent {
        return Err(arithmetic_overflow());
    }
    let completed = crate::refinement::ht_kappa_completion(u_base, gamma, exponent);
    if completed > maximum_u {
        return Err(invalid_code_block());
    }
    Ok(completed)
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        requires magnitude_bits <= 75, 1 <= decoded_bitplanes <= 292,
        ensures ht_numeric_magnitude_outcome(result) == crate::specs::ht_numeric_center(
            crate::magnitude::magnitude_value(bin), negative, initial_exponent,
            magnitude_bits, embedded_value, decoded_bitplanes),
            match result {
                Ok((value, _, _)) => crate::magnitude::magnitude_limbs(value)
                    == crate::specs::tier1_value_limbs(crate::magnitude::magnitude_value(value))
                    && crate::magnitude::magnitude_value(value) > 0
                    && crate::magnitude::magnitude_value(value) < crate::specs::part1_magnitude_capacity(),
                Err(_) => true,
            },
    )
)]
pub(super) fn center_ht_numeric_magnitude(
    bin: Magnitude,
    negative: bool,
    initial_exponent: u8,
    magnitude_bits: u8,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Result<(Magnitude, bool, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { vstd::arithmetic::power2::lemma2_to64(); }
    let mut bin_center = bin;
    let mut exponent = initial_exponent;
    if embedded_value {
        bin_center = bin_center.checked_add(crate::magnitude::magnitude_single_bit(u16::from(
            magnitude_bits,
        ))?)?;
        exponent = magnitude_bits
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    let low = bin_center.low_u64();
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_ht_low_word_parity(crate::magnitude::magnitude_value(bin_center));
        assert((low as nat % 2) == crate::magnitude::magnitude_value(bin_center) % 2);
    }
    if crate::refinement::ht_bin_center_odd(low) != low {
        bin_center = bin_center.checked_add(crate::magnitude::magnitude_from_u64(1))?;
        exponent = exponent.max(1);
    }
    let centered = bin_center.checked_add(crate::magnitude::magnitude_from_u64(2))?;
    let shift = decoded_bitplanes - 1;
    let magnitude = centered.checked_shl(shift)?.shift_right(1);
    if magnitude.is_zero() {
        return Err(invalid_code_block());
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude);
        crate::proofs::production_impl::production_tier1_value_limbs(crate::magnitude::magnitude_limbs(magnitude));
    }
    Ok((magnitude, negative, exponent))
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result =>
        ensures (ht_numeric_magnitude_outcome(result), ht_magsgn_view(final(reader)))
            == crate::specs::ht_reconstruct_numeric_magnitude(ht_magsgn_view(old(reader)),
                completed_u, embedded_bit, embedded_value, decoded_bitplanes),
            match result {
                Ok((value, _, _)) => crate::magnitude::magnitude_limbs(value)
                    == crate::specs::tier1_value_limbs(crate::magnitude::magnitude_value(value))
                    && crate::magnitude::magnitude_value(value) > 0
                    && crate::magnitude::magnitude_value(value) < crate::specs::part1_magnitude_capacity(),
                Err(_) => true,
            },
    )
)]
pub(super) fn reconstruct_ht_magnitude(
    reader: &mut HtForwardMagSgnReader<'_>,
    completed_u: u8,
    embedded_bit: bool,
    embedded_value: bool,
    decoded_bitplanes: u16,
) -> Result<(Magnitude, bool, u8), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_magsgn_view(reader); }
    #[cfg(verus_keep_ghost)]
    proof! {
        vstd::arithmetic::power2::lemma_pow2_pos(384);
        vstd::arithmetic::power2::lemma2_to64();
    }
    if completed_u == 0
        || completed_u > MAX_HT_MAGSGN_BITS
        || decoded_bitplanes == 0
        || decoded_bitplanes > MAX_TIER1_BITPLANES
    {
        return Err(invalid_code_block());
    }
    let magnitude_bits = crate::refinement::ht_magnitude_payload_bits(completed_u, embedded_bit);
    let mut bin_center = crate::magnitude::magnitude_zero();
    let mut negative = false;
    let mut exponent = 0_u8;
    let mut bit = 0_u8;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant bit <= magnitude_bits, magnitude_bits <= 75,
                1 <= completed_u <= 75, 1 <= decoded_bitplanes <= 292,
                start == ht_magsgn_view(old(reader)),
                magnitude_bits as nat == crate::specs::ht_magnitude_payload_bits(completed_u as nat, embedded_bit),
                crate::magnitude::magnitude_value(bin_center) < crate::specs::part1_magnitude_capacity(),
                vstd::arithmetic::power2::pow2(1) == 2,
                crate::specs::ht_reconstruct_numeric_magnitude(start, completed_u, embedded_bit, embedded_value, decoded_bitplanes)
                    == crate::specs::ht_numeric_finish(
                        crate::specs::ht_numeric_payload(ht_magsgn_view(reader), (magnitude_bits - bit) as nat,
                            bit as nat, crate::magnitude::magnitude_value(bin_center), negative, exponent),
                        magnitude_bits, embedded_value, decoded_bitplanes),
            decreases magnitude_bits - bit,
        )
    )]
    while bit < magnitude_bits {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_ht_numeric_payload_unfold(
                ht_magsgn_view(reader), (magnitude_bits - bit) as nat, bit as nat,
                crate::magnitude::magnitude_value(bin_center), negative, exponent,
            );
        }
        if reader.read_bit()? {
            if crate::refinement::ht_magnitude_sign(bit, true) {
                negative = true;
            }
            bin_center =
                bin_center.checked_add(crate::magnitude::magnitude_single_bit(u16::from(bit))?)?;
            exponent = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        bit = bit.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit == magnitude_bits);
        crate::proofs::production_impl::production_ht_numeric_payload_unfold(
            ht_magsgn_view(reader), 0, bit as nat,
            crate::magnitude::magnitude_value(bin_center), negative, exponent,
        );
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost final_value = crate::magnitude::magnitude_value(bin_center);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::ht_reconstruct_numeric_magnitude(start, completed_u, embedded_bit, embedded_value, decoded_bitplanes)
            == (crate::specs::ht_numeric_center(final_value, negative, exponent, magnitude_bits, embedded_value, decoded_bitplanes),
                ht_magsgn_view(reader)));
    }
    center_ht_numeric_magnitude(
        bin_center,
        negative,
        exponent,
        magnitude_bits,
        embedded_value,
        decoded_bitplanes,
    )
}

impl HtCleanupPlaneReconstruction<'_> {
    #[allow(
        clippy::too_many_arguments,
        reason = "The actual sample transition consumes these independent metadata and geometry fields."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires sample < 4, column + 1 < old(self).current_exponents.len(),
        ensures (result, ht_plane_view(final(self))) == crate::specs::ht_plane_sample(
            ht_plane_view(old(self)), quad, width, height, column as nat, completed_u, decoded_bitplanes, sample),
            final(self).current_exponents.len() == old(self).current_exponents.len(),
            final(self).previous_exponents@ == old(self).previous_exponents@,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn sample(
        &mut self,
        quad: HtQuadMetadata,
        width: u16,
        height: u16,
        column: usize,
        completed_u: u8,
        decoded_bitplanes: u16,
        sample: u8,
    ) -> Result<(), DecodeError> {
        let next_column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
        if sample >= 8 {
            return Err(invalid_code_block());
        }
        let x = quad
            .x
            .checked_add(u16::from(sample >> 1))
            .ok_or_else(arithmetic_overflow)?;
        let y = quad
            .y
            .checked_add(u16::from(sample & 1))
            .ok_or_else(arithmetic_overflow)?;
        if x < width && y < height {
            self.statistics.scanned(1)?;
            if quad.significance & (1_u8 << sample) != 0 {
                let embedded_bit = quad.embedded_bit_mask & (1_u8 << sample) != 0;
                let embedded_value = quad.embedded_magnitude & (1_u8 << sample) != 0;
                let (magnitude, negative, exponent) = reconstruct_ht_magnitude(
                    &mut self.reader,
                    completed_u,
                    embedded_bit,
                    embedded_value,
                    decoded_bitplanes,
                )?;
                self.output
                    .mark_significant_magnitude(x, y, magnitude, negative)?;
                self.statistics.decoded_symbols(1)?;
                self.statistics.became_significant()?;
                if sample == 1 {
                    let entry = self
                        .current_exponents
                        .get_mut(column)
                        .ok_or_else(invalid_code_block)?;
                    *entry = (*entry).max(exponent);
                } else if sample == 3 {
                    *self
                        .current_exponents
                        .get_mut(next_column)
                        .ok_or_else(invalid_code_block)? = exponent;
                }
            }
        }
        Ok(())
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "The shared quad stage preserves the real caller's metadata and traversal inputs."
    )]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires 0 < quads_per_row <= 32768,
            old(self).current_exponents.len() == quads_per_row + 1,
            old(self).previous_exponents.len() == quads_per_row + 1,
        ensures (result, ht_plane_view(final(self))) == crate::specs::ht_plane_quad(
            ht_plane_view(old(self)), quad, width, height, maximum_u, decoded_bitplanes,
            quads_per_row as nat, quad_index as nat),
            final(self).current_exponents.len() == quads_per_row + 1,
            final(self).previous_exponents.len() == quads_per_row + 1,
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn quad(
        &mut self,
        quad: HtQuadMetadata,
        width: u16,
        height: u16,
        maximum_u: u8,
        decoded_bitplanes: u16,
        quads_per_row: usize,
        quad_index: usize,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost start = ht_plane_view(self); }
        let column = quad_index
            .checked_rem(quads_per_row)
            .ok_or_else(arithmetic_overflow)?;
        if column == 0 {
            let mut exponent_index = 0_usize;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant exponent_index <= self.current_exponents.len(),
                        self.current_exponents.len() == quads_per_row + 1,
                        start.current.len() == quads_per_row + 1,
                        start == ht_plane_view(old(self)),
                        self.previous_exponents@ == start.previous,
                        code_block_plane_view(&self.output) == start.output,
                        ht_magsgn_view(&self.reader) == start.reader, self.statistics == start.statistics,
                        forall |i: int| 0 <= i < self.current_exponents.len() ==>
                            self.current_exponents@[i] == if i < exponent_index { 0u8 } else { start.current[i] },
                    decreases self.current_exponents.len() - exponent_index,
                )
            )]
            while exponent_index < self.current_exponents.len() {
                *self
                    .current_exponents
                    .get_mut(exponent_index)
                    .ok_or_else(invalid_code_block)? = 0;
                exponent_index = exponent_index
                    .checked_add(1)
                    .ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! { assert(self.current_exponents@ =~= Seq::new(start.current.len(), |i: int| 0u8)); }
        }
        let next_column = column.checked_add(1).ok_or_else(arithmetic_overflow)?;
        let completed_u = if quad.initial_row {
            if quad.u_base > maximum_u {
                return Err(invalid_code_block());
            }
            quad.u_base
        } else {
            complete_ht_kappa(
                quad.u_base,
                quad.significance,
                *self
                    .previous_exponents
                    .get(column)
                    .ok_or_else(invalid_code_block)?,
                *self
                    .previous_exponents
                    .get(next_column)
                    .ok_or_else(invalid_code_block)?,
                maximum_u,
            )?
        };
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost samples_start = ht_plane_view(self); }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::ht_plane_samples); }
        let mut sample = 0_u8;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant sample <= 4, column < quads_per_row, next_column == column + 1,
                    samples_start.current.len() == quads_per_row + 1,
                    self.current_exponents.len() == quads_per_row + 1,
                    self.previous_exponents.len() == quads_per_row + 1,
                    crate::specs::ht_plane_quad(ht_plane_view(old(self)), quad, width, height,
                        maximum_u, decoded_bitplanes, quads_per_row as nat, quad_index as nat)
                        == crate::specs::ht_plane_quad_finish(crate::specs::ht_plane_samples(
                            samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, 4),
                            quads_per_row as nat, column as nat),
                    (Ok::<(), DecodeError>(()), ht_plane_view(self)) == crate::specs::ht_plane_samples(
                        samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, sample as nat),
                decreases 4 - sample,
            )
        )]
        while sample < 4 {
            let result = self.sample(
                quad,
                width,
                height,
                column,
                completed_u,
                decoded_bitplanes,
                sample,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::ht_plane_samples);
                assert((result, ht_plane_view(self)) == crate::specs::ht_plane_samples(
                    samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, sample as nat + 1));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                if result.is_err() {
                    crate::proofs::production_impl::production_ht_plane_samples_error(
                        samples_start, quad, width, height, column as nat, completed_u, decoded_bitplanes, sample as nat + 1, 4);
                }
            }
            result?;
            sample = sample.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        if next_column == quads_per_row {
            core::mem::swap(&mut self.previous_exponents, &mut self.current_exponents);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, ht_plane_view(final(self))) == crate::specs::ht_plane_finish(ht_plane_view(old(self))),
    ))]
    pub(super) fn finish(&mut self) -> Result<(), DecodeError> {
        self.reader.finish()
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_cleanup_result(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),
        maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits),ht_plane_outcome(result)),
        ht_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==> ht_plane_outcome(result) == crate::specs::ht_cleanup_plane(
        code_block_plane_view(plane), ht_cleanup_segment_view(&cleanup), ht_cleanup_metadata_view(metadata),
        maximum_u, decoded_bitplanes, crate::limits::resource_work_limit(limits)),
))]
pub(super) fn reconstruct_ht_cleanup_plane(
    plane: &CodeBlockPlane,
    cleanup: HtCleanupSegment<'_>,
    metadata: &HtCleanupMetadata,
    maximum_u: u8,
    decoded_bitplanes: u16,
    limits: &ResourceLimits,
) -> Result<(CodeBlockPlane, Tier1PassStatistics), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_cleanup_normal(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits));}
    if metadata.width == 0 {
        return Err(invalid_code_block());
    }
    let output_result = code_block_plane_from_dimensions(
        plane.width(),
        plane.height(),
        super::CoefficientStorageRole::CleanupOutput,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=output_result {crate::specs::part2_plane_cleanup_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),
    maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits),error);}}
    let output = output_result?;
    let reader = ht_magsgn_from_input(cleanup.mag_sgn().bytes(), limits.maximum_work_units())?;
    let doubled_quads = usize::from(metadata.width)
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let quads_per_row = doubled_quads
        .checked_div(2)
        .ok_or_else(arithmetic_overflow)?;
    if quads_per_row == 0 {
        return Err(invalid_code_block());
    }
    let exponent_count = quads_per_row
        .checked_add(1)
        .ok_or_else(arithmetic_overflow)?;
    let mut state = HtCleanupPlaneReconstruction {
        output,
        reader,
        previous_exponents: vec![0_u8; exponent_count],
        current_exponents: vec![0_u8; exponent_count],
        statistics: ht_statistics_zero(),
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost start = ht_plane_view(&state); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(state.previous_exponents@ =~= Seq::new(quads_per_row as nat + 1, |i: int| 0u8));
        assert(state.current_exponents@ =~= Seq::new(quads_per_row as nat + 1, |i: int| 0u8));
        reveal(crate::specs::ht_plane_quads);
    }
    let mut quad_index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant quad_index <= metadata.quads.len(), 0 < quads_per_row <= 32768,
            crate::specs::part2_plane_cleanup_result(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),
                maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits),
                crate::specs::ht_cleanup_plane(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),ht_cleanup_metadata_view(metadata),maximum_u,decoded_bitplanes,crate::limits::resource_work_limit(limits))),
            start.current.len() == quads_per_row + 1,
            start.previous.len() == quads_per_row + 1,
            state.current_exponents.len() == quads_per_row + 1,
            state.previous_exponents.len() == quads_per_row + 1,
            crate::specs::ht_cleanup_plane(code_block_plane_view(plane), ht_cleanup_segment_view(&cleanup),
                ht_cleanup_metadata_view(metadata), maximum_u, decoded_bitplanes, crate::limits::resource_work_limit(limits))
                == crate::specs::ht_plane_output(crate::specs::ht_plane_quads(
                    start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                    decoded_bitplanes, quads_per_row as nat, metadata.quads@.len())),
            (Ok::<(), DecodeError>(()), ht_plane_view(&state)) == crate::specs::ht_plane_quads(
                start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                decoded_bitplanes, quads_per_row as nat, quad_index as nat),
        decreases metadata.quads.len() - quad_index,
    ))]
    while quad_index < metadata.quads.len() {
        let quad = *metadata
            .quads
            .get(quad_index)
            .ok_or_else(invalid_code_block)?;
        let result = state.quad(
            quad,
            metadata.width,
            metadata.height,
            maximum_u,
            decoded_bitplanes,
            quads_per_row,
            quad_index,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::ht_plane_quads);
            assert((result, ht_plane_view(&state)) == crate::specs::ht_plane_quads(
                start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                decoded_bitplanes, quads_per_row as nat, quad_index as nat + 1));
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if result.is_err() {
                crate::proofs::production_impl::production_ht_plane_quads_error(
                    start, metadata.quads@, metadata.width, metadata.height, maximum_u,
                    decoded_bitplanes, quads_per_row as nat, quad_index as nat + 1, metadata.quads@.len());
            }
        }
        result?;
        quad_index = quad_index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    state.finish()?;
    Ok((state.output, state.statistics))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_plane_prepare_result(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,
        crate::limits::resource_work_limit(limits),ht_cleanup_prepare_outcome(result)),
        ht_cleanup_prepare_outcome(result)!=Err(DecodeError::AllocationFailed) ==> ht_cleanup_prepare_outcome(result) == crate::specs::ht_cleanup_prepare(
        code_block_plane_view(plane), ht_cleanup_segment_view(&cleanup), maximum_passes,
        maximum_u, skipped_bitplanes, crate::limits::resource_work_limit(limits)),
))]
pub(super) fn prepare_ht_cleanup_symbols(
    plane: &CodeBlockPlane,
    cleanup: HtCleanupSegment<'_>,
    maximum_passes: u32,
    maximum_u: u8,
    skipped_bitplanes: u16,
    limits: &ResourceLimits,
) -> Result<(CodeBlockPlane, CodeBlockPlane, Tier1PassStatistics, u16), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_plane_prepare_normal(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,crate::limits::resource_work_limit(limits));}
    let metadata = decode_ht_cleanup_segment_metadata(
        cleanup,
        plane.width(),
        plane.height(),
        maximum_u,
        limits,
    )?;
    let significant_bitplanes = ht_significant_bitplanes(maximum_passes)?;
    let decoded_bitplanes = significant_bitplanes
        .checked_sub(skipped_bitplanes)
        .ok_or_else(arithmetic_overflow)?;
    let reconstructed = reconstruct_ht_cleanup_plane(
        plane,
        cleanup,
        &metadata,
        maximum_u,
        decoded_bitplanes,
        limits,
    );
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=reconstructed {crate::specs::part2_plane_prepare_cleanup_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,
    crate::limits::resource_work_limit(limits),(ht_cleanup_metadata_view(&metadata),decoded_bitplanes),error);}}
    let (output, statistics) = reconstructed?;
    let duplicated = output.duplicate(super::CoefficientStorageRole::CleanupCopy);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=duplicated {crate::specs::part2_plane_prepare_duplicate_error(code_block_plane_view(plane),ht_cleanup_segment_view(&cleanup),maximum_passes,maximum_u,skipped_bitplanes,
    crate::limits::resource_work_limit(limits),(ht_cleanup_metadata_view(&metadata),decoded_bitplanes),(code_block_plane_view(&output),statistics),error);}}
    let duplicate = duplicated?;
    Ok((output, duplicate, statistics, decoded_bitplanes))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::ht_significant_bitplanes(maximum_passes),
))]
pub(super) fn ht_significant_bitplanes(maximum_passes: u32) -> Result<u16, DecodeError> {
    let rounded_passes = maximum_passes
        .checked_add(2)
        .ok_or_else(arithmetic_overflow)?;
    let significant = rounded_passes
        .checked_div(3)
        .ok_or_else(arithmetic_overflow)?;
    if significant > u32::from(u16::MAX) {
        return Err(arithmetic_overflow());
    }
    Ok(significant as u16)
}
