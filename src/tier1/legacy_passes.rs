use super::coding::legacy_default_style;
use super::state::{
    arithmetic_overflow, ht_statistics_zero, invalid_code_block, is_bitplane_mask,
    magnitude_refinement_context, sign_context, significant_neighbor_count, zero_coding_context,
};
use super::{
    CodeBlockPlane, MAX_TIER1_BITPLANES, NeighborSummary, RUN_LENGTH_CONTEXT, RawBitReader,
    SubbandOrientation, Tier1BitplaneState, Tier1CodingStyle, Tier1PassStatistics,
    Tier1SymbolDecoder, UNIFORM_CONTEXT,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_view, legacy_bitplane_outcome, legacy_bitplane_view, legacy_frame_view,
    legacy_symbols_view, raw_bit_reader_view,
};
use crate::DecodeError;
use crate::mq::MqDecoder;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Clone for Tier1BitplaneState {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures legacy_bitplane_view(&result) == legacy_bitplane_view(self),
    ))]
    fn clone(&self) -> Self {
        Self {
            width: self.width,
            height: self.height,
            bitplane: self.bitplane,
            significant_before: self.significant_before.clone(),
            significance_visited: self.significance_visited.clone(),
            significance_propagation_complete: self.significance_propagation_complete,
            magnitude_refinement_complete: self.magnitude_refinement_complete,
            cleanup_complete: self.cleanup_complete,
        }
    }
}

impl Tier1BitplaneState {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_nested_bitplane_result(legacy_bitplane_view(self),_role,_legacy,legacy_bitplane_outcome(result)),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>legacy_bitplane_view(&value)==legacy_bitplane_view(self)},
    ))]
    pub(super) fn try_duplicate(
        &self,
        _role: super::HtRefinementCopyRole,
        _legacy: bool,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=legacy_bitplane_view(self);}
        Ok(Self {
            width: self.width,
            height: self.height,
            bitplane: self.bitplane,
            significant_before: {
                let copied = crate::allocation::copy_values(&self.significant_before);
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_nested_owner_observed(crate::specs::part2_nested_flags(before,_role,_legacy,false),
                        match copied{Err(error)=>Err(error),Ok(_)=>Ok(())});
                    if let Err(error)=copied{crate::specs::part2_nested_bitplane_first_error(before,_role,_legacy,error);}
                }
                copied?
            },
            significance_visited: {
                let copied = crate::allocation::copy_values(&self.significance_visited);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let result=match copied{Err(error)=>Err(error),Ok(_)=>Ok(())};
                    crate::specs::part2_nested_owner_observed(crate::specs::part2_nested_flags(before,_role,_legacy,true),result);
                    crate::specs::part2_nested_bitplane_observed(before,_role,_legacy,result);
                }
                copied?
            },
            significance_propagation_complete: self.significance_propagation_complete,
            magnitude_refinement_complete: self.magnitude_refinement_complete,
            cleanup_complete: self.cleanup_complete,
        })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_nested_bitplane_option_result(super::legacy_bitplane_option_view(source),role,legacy,super::legacy_bitplane_option_outcome(result)),
        match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>super::legacy_bitplane_option_view(&value)==super::legacy_bitplane_option_view(source)},
))]
pub(super) fn try_duplicate_bitplane(
    source: &Option<Tier1BitplaneState>,
    role: super::HtRefinementCopyRole,
    legacy: bool,
) -> Result<Option<Tier1BitplaneState>, DecodeError> {
    match source.as_ref() {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {crate::specs::part2_nested_option_none(|value,rest|crate::specs::part2_nested_bitplane_run(value,role,legacy,rest));}
            Ok(None)
        }
        Some(value) => {
            let copied = value.try_duplicate(role, legacy);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_nested_bitplane_frames(legacy_bitplane_view(value),role,legacy,legacy_bitplane_outcome(copied));
                crate::specs::part2_nested_option_observed(legacy_bitplane_view(value),|source,rest|crate::specs::part2_nested_bitplane_run(source,role,legacy,rest),legacy_bitplane_outcome(copied));
            }
            Ok(Some(copied?))
        }
    }
}

impl Tier1PassStatistics {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(self)) == crate::specs::tier1_statistics_increment(*old(self), 0, count),
    ))]
    pub(super) fn scanned(&mut self, count: u32) -> Result<(), DecodeError> {
        self.coefficients_scanned = self
            .coefficients_scanned
            .checked_add(count)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(self)) == crate::specs::tier1_statistics_increment(*old(self), 1, count),
    ))]
    pub(super) fn decoded_symbols(&mut self, count: u32) -> Result<(), DecodeError> {
        self.coding_symbols = self
            .coding_symbols
            .checked_add(count)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(self)) == crate::specs::tier1_statistics_increment(*old(self), 2, 1),
    ))]
    pub(super) fn became_significant(&mut self) -> Result<(), DecodeError> {
        self.newly_significant = self
            .newly_significant
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(self)) == crate::specs::tier1_statistics_increment(*old(self), 3, 1),
    ))]
    pub(super) fn refined(&mut self) -> Result<(), DecodeError> {
        self.refined_coefficients = self
            .refined_coefficients
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(self)) == crate::specs::tier1_statistics_increment(*old(self), 4, 1),
    ))]
    fn used_run_mode(&mut self) -> Result<(), DecodeError> {
        self.run_mode_columns = self
            .run_mode_columns
            .checked_add(1)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(self)) == crate::specs::tier1_statistics_merge(*old(self), other),
    ))]
    pub(super) fn merge(&mut self, other: Self) -> Result<(), DecodeError> {
        self.scanned(other.coefficients_scanned)?;
        self.decoded_symbols(other.coding_symbols)?;
        self.newly_significant = self
            .newly_significant
            .checked_add(other.newly_significant)
            .ok_or_else(arithmetic_overflow)?;
        self.refined_coefficients = self
            .refined_coefficients
            .checked_add(other.refined_coefficients)
            .ok_or_else(arithmetic_overflow)?;
        self.run_mode_columns = self
            .run_mode_columns
            .checked_add(other.run_mode_columns)
            .ok_or_else(arithmetic_overflow)?;
        Ok(())
    }
}

impl Tier1BitplaneState {
    pub fn new(plane: &CodeBlockPlane, bitplane_mask: u64) -> Result<Self, DecodeError> {
        if !is_bitplane_mask(bitplane_mask) {
            return Err(invalid_code_block());
        }
        let bitplane =
            u16::try_from(bitplane_mask.trailing_zeros()).map_err(|_| arithmetic_overflow())?;
        Self::new_at_bitplane(plane, bitplane)
    }

    pub fn new_at_bitplane(plane: &CodeBlockPlane, bitplane: u16) -> Result<Self, DecodeError> {
        legacy_bitplane_from_plane(plane, bitplane)
    }

    pub const fn bitplane_mask(&self) -> u64 {
        if self.bitplane < 64 {
            1_u64 << self.bitplane
        } else {
            0
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == legacy_bitplane_view(self).bitplane,
    ))]
    pub const fn bitplane(&self) -> u16 {
        self.bitplane
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == legacy_bitplane_view(self).significance_propagation_complete,
    ))]
    pub const fn significance_propagation_complete(&self) -> bool {
        self.significance_propagation_complete
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == legacy_bitplane_view(self).magnitude_refinement_complete,
    ))]
    pub const fn magnitude_refinement_complete(&self) -> bool {
        self.magnitude_refinement_complete
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == legacy_bitplane_view(self).cleanup_complete,
    ))]
    pub const fn cleanup_complete(&self) -> bool {
        self.cleanup_complete
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures legacy_bitplane_outcome(result) == crate::specs::part1_legacy_bitplane_initial(
            code_block_plane_view(plane), bitplane),
    ))]
pub(super) fn legacy_bitplane_from_plane(
    plane: &CodeBlockPlane,
    bitplane: u16,
) -> Result<Tier1BitplaneState, DecodeError> {
    if bitplane >= MAX_TIER1_BITPLANES {
        return Err(invalid_code_block());
    }
    let mut significant_before = Vec::with_capacity(plane.coefficients.len());
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= plane.coefficients.len(), significant_before.len() == index,
                bitplane < MAX_TIER1_BITPLANES,
                forall |i: int| 0 <= i < index ==> significant_before@[i] == plane.coefficients@[i].significant,
            decreases plane.coefficients.len() - index,
        ))]
    while index < plane.coefficients.len() {
        significant_before.push(plane.coefficients[index].significant);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(significant_before@ =~= code_block_plane_view(plane).coefficients.map_values(
            |c: crate::specs::Tier1RawCoefficient| c.significant));
    }
    let significance_visited = vec![false; significant_before.len()];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(significance_visited@ =~= Seq::new(code_block_plane_view(plane).coefficients.len(), |i: int| false));
    }
    Ok(Tier1BitplaneState {
        width: plane.width,
        height: plane.height,
        bitplane,
        significance_visited,
        significant_before,
        significance_propagation_complete: false,
        magnitude_refinement_complete: false,
        cleanup_complete: false,
    })
}

impl Tier1BitplaneState {
    pub fn was_visited_by_significance_propagation(
        &self,
        plane: &CodeBlockPlane,
        x: u16,
        y: u16,
    ) -> Result<bool, DecodeError> {
        self.validate_plane(plane)?;
        let index = plane.index(x, y)?;
        if index >= self.significance_visited.len() {
            return Err(invalid_code_block());
        }
        Ok(self.significance_visited[index])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_legacy_validate(legacy_bitplane_view(self), code_block_plane_view(plane)),
    ))]
    fn validate_plane(&self, plane: &CodeBlockPlane) -> Result<(), DecodeError> {
        if self.width != plane.width
            || self.height != plane.height
            || self.significant_before.len() != plane.coefficients.len()
            || self.significance_visited.len() != plane.coefficients.len()
        {
            return Err(invalid_code_block());
        }
        Ok(())
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
        == crate::specs::part1_legacy_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), orientation, false, 0),
))]
pub fn decode_significance_propagation_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_significance_propagation_pass_with_style(
        plane,
        state,
        decoder,
        orientation,
        legacy_default_style(),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
        == crate::specs::part1_legacy_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), orientation, style.vertical_causal_context, 0),
))]
pub fn decode_significance_propagation_pass_with_style(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_significance_propagation(
        plane,
        state,
        decoder,
        orientation,
        style.vertical_causal_context,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(final(reader))))
        == crate::specs::part1_legacy_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))), orientation, style.vertical_causal_context, 0),
))]
pub fn decode_raw_significance_propagation_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    reader: &mut RawBitReader<'_>,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_significance_propagation(
        plane,
        state,
        reader,
        orientation,
        style.vertical_causal_context,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)), legacy_symbols_view(final(decoder)))
        == crate::specs::part1_legacy_pass(
            code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
            orientation, vertical_causal_context, 0),
))]
fn decode_significance_propagation(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
) -> Result<Tier1PassStatistics, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part1_legacy_pass(
            code_block_plane_view(plane), legacy_bitplane_view(state), legacy_symbols_view(decoder),
            orientation, vertical_causal_context, 0);
    }
    state.validate_plane(plane)?;
    if state.significance_propagation_complete
        || state.magnitude_refinement_complete
        || state.cleanup_complete
    {
        return Err(invalid_code_block());
    }

    let mut statistics = ht_statistics_zero();
    let height = plane.height;
    let width = plane.width;
    let mut stripe_y = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant stripe_y <= height,
                goal == crate::specs::part1_legacy_pass(
                    code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                    orientation, vertical_causal_context, 0),
                goal == crate::specs::part1_legacy_finish(crate::specs::part1_legacy_stripes(
                    legacy_frame_view(plane, state, decoder, statistics), stripe_y as nat, width, height,
                    orientation, vertical_causal_context, 0), 0),
            decreases height - stripe_y,
        )
    )]
    while stripe_y < height {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_stripes); }
        let stripe_rows = crate::refinement::tier1_stripe_rows(height, stripe_y);
        let mut x = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= width,
                    stripe_y < height, stripe_rows > 0, stripe_rows <= 4,
                    stripe_y as nat + stripe_rows as nat <= height,
                    goal == crate::specs::part1_legacy_pass(
                        code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                        orientation, vertical_causal_context, 0),
                    goal == crate::specs::part1_legacy_column_tail(
                        legacy_frame_view(plane, state, decoder, statistics), x as nat, stripe_y, stripe_rows as nat,
                        width, height, orientation, vertical_causal_context, 0),
                decreases width - x,
            )
        )]
        while x < width {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_legacy_columns); }
            let mut row = 0;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant row <= stripe_rows,
                        x < width, stripe_y < height, stripe_rows > 0, stripe_rows <= 4,
                        stripe_y as nat + stripe_rows as nat <= height,
                        goal == crate::specs::part1_legacy_pass(
                            code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                            orientation, vertical_causal_context, 0),
                        goal == crate::specs::part1_legacy_row_tail(
                            legacy_frame_view(plane, state, decoder, statistics), x, stripe_y, row as nat, stripe_rows as nat,
                            width, height, orientation, vertical_causal_context, 0),
                    decreases stripe_rows - row,
                )
            )]
            while row < stripe_rows {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part1_legacy_rows); }
                let y = match stripe_y.checked_add(row) {
                    Some(y) => y,
                    None => return Err(arithmetic_overflow()),
                };
                decode_significance_coefficient(
                    plane,
                    state,
                    decoder,
                    orientation,
                    vertical_causal_context,
                    (x, y),
                    &mut statistics,
                )?;
                row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_legacy_rows); }
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_columns); }
        let next_stripe = stripe_y
            .checked_add(stripe_rows)
            .ok_or_else(arithmetic_overflow)?;
        if next_stripe <= stripe_y || next_stripe > height {
            return Err(invalid_code_block());
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_stripes); }
        stripe_y = next_stripe;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_legacy_stripes);
        assert(goal == crate::specs::part1_legacy_finish(
            (Ok(()), legacy_frame_view(plane, state, decoder, statistics)), 0));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before_finish = legacy_frame_view(plane, state, decoder, statistics); }
    state.significance_propagation_complete = crate::refinement::tier1_pass_complete(0) & 1 != 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(1u8 & 1u8 != 0) by(bit_vector);
        assert(state.significance_propagation_complete);
        assert(legacy_bitplane_view(state) == (crate::specs::Part1LegacyBitplane {
            significance_propagation_complete: true, ..before_finish.state
        }));
        assert(code_block_plane_view(plane) == before_finish.plane);
        assert(legacy_symbols_view(decoder) == before_finish.symbols);
        assert((Ok(statistics), code_block_plane_view(plane), legacy_bitplane_view(state), legacy_symbols_view(decoder)) == goal);
    }
    Ok(statistics)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(final(plane), final(state), final(decoder), *final(statistics)))
        == crate::specs::part1_legacy_sig_cell(
            legacy_frame_view(old(plane), old(state), old(decoder), *old(statistics)),
            coordinate.0, coordinate.1, orientation, vertical_causal_context),
))]
fn decode_significance_coefficient(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
    coordinate: (u16, u16),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_sig_cell); }
    let (x, y) = coordinate;
    statistics.scanned(1)?;
    let index = plane.index(x, y)?;
    let coefficient = plane.coefficient(x, y)?;
    if !coefficient.significant {
        let summary = plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
        let neighbors = significant_neighbor_count(summary);
        if crate::refinement::tier1_sigprop_eligible(coefficient.significant, neighbors) {
            if index >= state.significance_visited.len() {
                return Err(invalid_code_block());
            }
            let zero_context = zero_coding_context(summary, orientation);
            let significant = decoder.decode(usize::from(zero_context))?;
            state.significance_visited[index] = true;
            statistics.decoded_symbols(1)?;
            if significant {
                decode_sign_and_mark(plane, decoder, x, y, state.bitplane, summary)?;
                statistics.decoded_symbols(1)?;
                statistics.became_significant()?;
            }
        }
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
        == crate::specs::part1_legacy_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), SubbandOrientation::Ll, false, 1),
))]
pub fn decode_magnitude_refinement_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_magnitude_refinement_pass_with_style(plane, state, decoder, legacy_default_style())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
        == crate::specs::part1_legacy_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), SubbandOrientation::Ll, style.vertical_causal_context, 1),
))]
pub fn decode_magnitude_refinement_pass_with_style(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_magnitude_refinement(plane, state, decoder, style.vertical_causal_context)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(final(reader))))
        == crate::specs::part1_legacy_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Raw(raw_bit_reader_view(old(reader))), SubbandOrientation::Ll, style.vertical_causal_context, 1),
))]
pub fn decode_raw_magnitude_refinement_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    reader: &mut RawBitReader<'_>,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_magnitude_refinement(plane, state, reader, style.vertical_causal_context)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)), legacy_symbols_view(final(decoder)))
        == crate::specs::part1_legacy_pass(
            code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
            SubbandOrientation::Ll, vertical_causal_context, 1),
))]
fn decode_magnitude_refinement(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    vertical_causal_context: bool,
) -> Result<Tier1PassStatistics, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part1_legacy_pass(
            code_block_plane_view(plane), legacy_bitplane_view(state), legacy_symbols_view(decoder),
            SubbandOrientation::Ll, vertical_causal_context, 1);
    }
    state.validate_plane(plane)?;
    if !state.significance_propagation_complete
        || state.magnitude_refinement_complete
        || state.cleanup_complete
    {
        return Err(invalid_code_block());
    }

    let mut statistics = ht_statistics_zero();
    let height = plane.height;
    let width = plane.width;
    let mut stripe_y = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant stripe_y <= height,
                goal == crate::specs::part1_legacy_pass(
                    code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                    SubbandOrientation::Ll, vertical_causal_context, 1),
                goal == crate::specs::part1_legacy_finish(crate::specs::part1_legacy_stripes(
                    legacy_frame_view(plane, state, decoder, statistics), stripe_y as nat, width, height,
                    SubbandOrientation::Ll, vertical_causal_context, 1), 1),
            decreases height - stripe_y,
        )
    )]
    while stripe_y < height {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_stripes); }
        let stripe_rows = crate::refinement::tier1_stripe_rows(height, stripe_y);
        let mut x = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= width,
                    stripe_y < height, stripe_rows > 0, stripe_rows <= 4,
                    stripe_y as nat + stripe_rows as nat <= height,
                    goal == crate::specs::part1_legacy_pass(
                        code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                        SubbandOrientation::Ll, vertical_causal_context, 1),
                    goal == crate::specs::part1_legacy_column_tail(
                        legacy_frame_view(plane, state, decoder, statistics), x as nat, stripe_y, stripe_rows as nat,
                        width, height, SubbandOrientation::Ll, vertical_causal_context, 1),
                decreases width - x,
            )
        )]
        while x < width {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_legacy_columns); }
            let mut row = 0;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant row <= stripe_rows,
                        x < width, stripe_y < height, stripe_rows > 0, stripe_rows <= 4,
                        stripe_y as nat + stripe_rows as nat <= height,
                        goal == crate::specs::part1_legacy_pass(
                            code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                            SubbandOrientation::Ll, vertical_causal_context, 1),
                        goal == crate::specs::part1_legacy_row_tail(
                            legacy_frame_view(plane, state, decoder, statistics), x, stripe_y, row as nat, stripe_rows as nat,
                            width, height, SubbandOrientation::Ll, vertical_causal_context, 1),
                    decreases stripe_rows - row,
                )
            )]
            while row < stripe_rows {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part1_legacy_rows); }
                let y = stripe_y.checked_add(row).ok_or_else(arithmetic_overflow)?;
                decode_refinement_coefficient(
                    plane,
                    state,
                    decoder,
                    vertical_causal_context,
                    (x, y),
                    &mut statistics,
                )?;
                row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_legacy_rows); }
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_columns); }
        let next_stripe = stripe_y
            .checked_add(stripe_rows)
            .ok_or_else(arithmetic_overflow)?;
        if next_stripe <= stripe_y || next_stripe > height {
            return Err(invalid_code_block());
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_stripes); }
        stripe_y = next_stripe;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_legacy_stripes);
        assert(goal == crate::specs::part1_legacy_finish(
            (Ok(()), legacy_frame_view(plane, state, decoder, statistics)), 1));
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before_finish = legacy_frame_view(plane, state, decoder, statistics); }
    state.magnitude_refinement_complete = crate::refinement::tier1_pass_complete(1) & 2 != 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(2u8 & 2u8 != 0) by(bit_vector);
        assert(state.magnitude_refinement_complete);
        assert(legacy_bitplane_view(state) == (crate::specs::Part1LegacyBitplane {
            magnitude_refinement_complete: true, ..before_finish.state
        }));
        assert(code_block_plane_view(plane) == before_finish.plane);
        assert(legacy_symbols_view(decoder) == before_finish.symbols);
        assert((Ok(statistics), code_block_plane_view(plane), legacy_bitplane_view(state), legacy_symbols_view(decoder)) == goal);
    }
    Ok(statistics)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(final(plane), state, final(decoder), *final(statistics)))
        == crate::specs::part1_legacy_mag_cell(
            legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
            coordinate.0, coordinate.1, vertical_causal_context),
))]
fn decode_refinement_coefficient(
    plane: &mut CodeBlockPlane,
    state: &Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    vertical_causal_context: bool,
    coordinate: (u16, u16),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_mag_cell); }
    let (x, y) = coordinate;
    statistics.scanned(1)?;
    let index = plane.index(x, y)?;
    if index >= state.significant_before.len() {
        return Err(invalid_code_block());
    }
    if crate::refinement::tier1_magref_eligible(state.significant_before[index]) {
        let coefficient = plane.coefficient(x, y)?;
        let summary = plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
        let context = magnitude_refinement_context(coefficient, summary);
        let refinement_bit = decoder.decode(usize::from(context))?;
        statistics.decoded_symbols(1)?;
        plane.apply_refinement_bit(x, y, state.bitplane, refinement_bit)?;
        statistics.refined()?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
        == crate::specs::part1_legacy_cleanup_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), orientation, false, false),
))]
pub fn decode_cleanup_pass(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_cleanup_pass_with_style(plane, state, decoder, orientation, legacy_default_style())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)),
        crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(final(decoder))))
        == crate::specs::part1_legacy_cleanup_pass(code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)),
            crate::specs::Part1LegacySymbols::Mq(crate::mq::mq_decoder_view(old(decoder))), orientation,
            style.vertical_causal_context, style.segmentation_symbols),
))]
pub fn decode_cleanup_pass_with_style(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut MqDecoder<'_>,
    orientation: SubbandOrientation,
    style: Tier1CodingStyle,
) -> Result<Tier1PassStatistics, DecodeError> {
    decode_cleanup(
        plane,
        state,
        decoder,
        orientation,
        style.vertical_causal_context,
        style.segmentation_symbols,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_bitplane_view(final(state)), legacy_symbols_view(final(decoder)))
        == crate::specs::part1_legacy_cleanup_pass(
            code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
            orientation, vertical_causal_context, segmentation_symbols),
))]
pub(super) fn decode_cleanup(
    plane: &mut CodeBlockPlane,
    state: &mut Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
    segmentation_symbols: bool,
) -> Result<Tier1PassStatistics, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost goal = crate::specs::part1_legacy_cleanup_pass(
            code_block_plane_view(plane), legacy_bitplane_view(state), legacy_symbols_view(decoder),
            orientation, vertical_causal_context, segmentation_symbols);
    }
    state.validate_plane(plane)?;
    if state.cleanup_complete
        || state.significance_propagation_complete != state.magnitude_refinement_complete
    {
        return Err(invalid_code_block());
    }

    let mut statistics = ht_statistics_zero();
    let height = plane.height;
    let width = plane.width;
    let mut stripe_y = 0_u16;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant stripe_y <= height,
                goal == crate::specs::part1_legacy_cleanup_pass(
                    code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                    orientation, vertical_causal_context, segmentation_symbols),
                goal == crate::specs::part1_legacy_cleanup_finish(crate::specs::part1_legacy_stripes(
                    legacy_frame_view(plane, state, decoder, statistics), stripe_y as nat, width, height,
                    orientation, vertical_causal_context, 2), segmentation_symbols),
            decreases height - stripe_y,
        )
    )]
    while stripe_y < height {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_stripes); }
        let stripe_rows = crate::refinement::tier1_stripe_rows(height, stripe_y);
        let mut x = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant x <= width,
                    stripe_y < height, stripe_rows > 0, stripe_rows <= 4,
                    stripe_y as nat + stripe_rows as nat <= height,
                    goal == crate::specs::part1_legacy_cleanup_pass(
                        code_block_plane_view(old(plane)), legacy_bitplane_view(old(state)), legacy_symbols_view(old(decoder)),
                        orientation, vertical_causal_context, segmentation_symbols),
                    goal == crate::specs::part1_legacy_cleanup_column_tail(
                        legacy_frame_view(plane, state, decoder, statistics), x as nat, stripe_y, stripe_rows as nat,
                        width, height, orientation, vertical_causal_context, segmentation_symbols),
                decreases width - x,
            )
        )]
        while x < width {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_legacy_columns); }
            decode_cleanup_column(
                plane,
                state,
                decoder,
                (orientation, vertical_causal_context),
                (x, stripe_y, stripe_rows),
                &mut statistics,
            )?;
            x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_legacy_columns); }
        let next_stripe = stripe_y
            .checked_add(stripe_rows)
            .ok_or_else(arithmetic_overflow)?;
        if next_stripe <= stripe_y || next_stripe > height {
            return Err(invalid_code_block());
        }
        stripe_y = next_stripe;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_legacy_stripes);
    }
    if segmentation_symbols {
        decode_cleanup_segsym(plane, state, decoder, &mut statistics)?;
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost before_finish = legacy_frame_view(plane, state, decoder, statistics); }
    state.cleanup_complete = crate::refinement::tier1_pass_complete(2) & 4 != 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(4u8 & 4u8 != 0) by(bit_vector);
        assert((Ok(statistics), code_block_plane_view(plane), legacy_bitplane_view(state), legacy_symbols_view(decoder)) == goal);
    }
    Ok(statistics)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(_plane, _state, final(decoder), *final(statistics)))
        == crate::specs::part1_legacy_segsym(
            legacy_frame_view(_plane, _state, old(decoder), *old(statistics))),
))]
fn decode_cleanup_segsym(
    _plane: &CodeBlockPlane,
    _state: &Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_segsym); }
    let first = decoder.decode(UNIFORM_CONTEXT)?;
    let second = decoder.decode(UNIFORM_CONTEXT)?;
    let third = decoder.decode(UNIFORM_CONTEXT)?;
    let fourth = decoder.decode(UNIFORM_CONTEXT)?;
    statistics.decoded_symbols(4)?;
    if !first || second || !third || fourth {
        return Err(invalid_code_block());
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(final(plane), state, final(decoder), *final(statistics)))
        == crate::specs::part1_legacy_cleanup_column(
            legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
            coordinate.0, coordinate.1, coordinate.2, context.0, context.1),
))]
fn decode_cleanup_column(
    plane: &mut CodeBlockPlane,
    state: &Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    context: (SubbandOrientation, bool),
    coordinate: (u16, u16, u16),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_legacy_cleanup_column);
        reveal(crate::specs::part1_legacy_cleanup_run);
    }
    let (_orientation, vertical_causal_context) = context;
    let (x, stripe_y, stripe_rows) = coordinate;
    let stripe_y_1 = stripe_y.checked_add(1).ok_or_else(arithmetic_overflow)?;
    let stripe_y_2 = stripe_y.checked_add(2).ok_or_else(arithmetic_overflow)?;
    let stripe_y_3 = stripe_y.checked_add(3).ok_or_else(arithmetic_overflow)?;
    if stripe_rows == 4
        && cleanup_run_candidate(plane, state, x, stripe_y, vertical_causal_context)?
        && cleanup_run_candidate(plane, state, x, stripe_y_1, vertical_causal_context)?
        && cleanup_run_candidate(plane, state, x, stripe_y_2, vertical_causal_context)?
        && cleanup_run_candidate(plane, state, x, stripe_y_3, vertical_causal_context)?
    {
        statistics.scanned(4)?;
        statistics.used_run_mode()?;
        let interrupted = decoder.decode(RUN_LENGTH_CONTEXT)?;
        statistics.decoded_symbols(1)?;
        if interrupted {
            decode_cleanup_interrupt(plane, state, decoder, context, (x, stripe_y), statistics)?;
        }
    } else {
        decode_cleanup_rows(
            plane,
            state,
            decoder,
            context,
            (x, stripe_y, 0, stripe_rows, true),
            statistics,
        )?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(final(plane), state, final(decoder), *final(statistics)))
        == crate::specs::part1_legacy_cleanup_interrupt(
            legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
            coordinate.0, coordinate.1, context.0, context.1),
))]
fn decode_cleanup_interrupt(
    plane: &mut CodeBlockPlane,
    state: &Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    context: (SubbandOrientation, bool),
    coordinate: (u16, u16),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_cleanup_interrupt); }
    let (orientation, vertical_causal_context) = context;
    let (x, stripe_y) = coordinate;
    let run_high = decoder.decode(UNIFORM_CONTEXT)?;
    let run_low = decoder.decode(UNIFORM_CONTEXT)?;
    statistics.decoded_symbols(2)?;
    let run_length = if run_high {
        if run_low { 3 } else { 2 }
    } else if run_low {
        1
    } else {
        0
    };
    let y = stripe_y
        .checked_add(run_length)
        .ok_or_else(arithmetic_overflow)?;
    let summary = plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
    decode_sign_and_mark(plane, decoder, x, y, state.bitplane, summary)?;
    statistics.decoded_symbols(1)?;
    statistics.became_significant()?;
    let row = run_length.checked_add(1).ok_or_else(arithmetic_overflow)?;
    decode_cleanup_rows(
        plane,
        state,
        decoder,
        (orientation, vertical_causal_context),
        (x, stripe_y, row, 4, false),
        statistics,
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(final(plane), state, final(decoder), *final(statistics)))
        == if coordinate.4 {
            crate::specs::part1_legacy_rows(
                legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
                coordinate.0, coordinate.1, coordinate.2 as nat, coordinate.3 as nat, context.0, context.1, 2)
        } else {
            crate::specs::part1_legacy_cleanup_rows(
                legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
                coordinate.0, coordinate.1, coordinate.2 as nat, coordinate.3 as nat, context.0, context.1)
        },
))]
fn decode_cleanup_rows(
    plane: &mut CodeBlockPlane,
    state: &Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    context: (SubbandOrientation, bool),
    coordinate: (u16, u16, u16, u16, bool),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    let (orientation, vertical_causal_context) = context;
    let (x, stripe_y, mut row, rows, scan) = coordinate;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = legacy_frame_view(plane, state, decoder, *statistics);
        let ghost goal = if scan {
            crate::specs::part1_legacy_rows(initial, x, stripe_y, row as nat, rows as nat, orientation, vertical_causal_context, 2)
        } else {
            crate::specs::part1_legacy_cleanup_rows(initial, x, stripe_y, row as nat, rows as nat, orientation, vertical_causal_context)
        };
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant initial == legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
            goal == if coordinate.4 {
                crate::specs::part1_legacy_rows(initial, coordinate.0, coordinate.1, coordinate.2 as nat, coordinate.3 as nat, context.0, context.1, 2)
            } else {
                crate::specs::part1_legacy_cleanup_rows(initial, coordinate.0, coordinate.1, coordinate.2 as nat, coordinate.3 as nat, context.0, context.1)
            },
            goal == if scan {
                crate::specs::part1_legacy_rows(legacy_frame_view(plane, state, decoder, *statistics),
                    x, stripe_y, row as nat, rows as nat, orientation, vertical_causal_context, 2)
            } else {
                crate::specs::part1_legacy_cleanup_rows(legacy_frame_view(plane, state, decoder, *statistics),
                    x, stripe_y, row as nat, rows as nat, orientation, vertical_causal_context)
            },
        decreases rows as int - row as int,
    ))]
    while row < rows {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part1_legacy_rows);
            reveal(crate::specs::part1_legacy_cleanup_rows);
        }
        let y = match stripe_y.checked_add(row) {
            Some(y) => y,
            None => return Err(arithmetic_overflow()),
        };
        if scan {
            statistics.scanned(1)?;
        }
        decode_cleanup_coefficient(
            plane,
            state,
            decoder,
            orientation,
            vertical_causal_context,
            (x, y),
            statistics,
        )?;
        row = row.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part1_legacy_rows);
        reveal(crate::specs::part1_legacy_cleanup_rows);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, legacy_frame_view(final(plane), state, final(decoder), *final(statistics)))
        == crate::specs::part1_legacy_cleanup_cell(
            legacy_frame_view(old(plane), state, old(decoder), *old(statistics)),
            coordinate.0, coordinate.1, orientation, vertical_causal_context),
))]
fn decode_cleanup_coefficient(
    plane: &mut CodeBlockPlane,
    state: &Tier1BitplaneState,
    decoder: &mut impl Tier1SymbolDecoder,
    orientation: SubbandOrientation,
    vertical_causal_context: bool,
    coordinate: (u16, u16),
    statistics: &mut Tier1PassStatistics,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_cleanup_cell); }
    let (x, y) = coordinate;
    let index = plane.index(x, y)?;
    if index >= state.significance_visited.len() {
        return Err(invalid_code_block());
    }
    let coefficient = plane.coefficient(x, y)?;
    if !crate::refinement::tier1_cleanup_eligible(
        coefficient.significant,
        state.significance_visited[index],
    ) {
        return Ok(());
    }
    let summary = plane.neighbor_summary_with_causality(x, y, vertical_causal_context)?;
    let zero_context = zero_coding_context(summary, orientation);
    let significant = decoder.decode(usize::from(zero_context))?;
    statistics.decoded_symbols(1)?;
    if significant {
        decode_sign_and_mark(plane, decoder, x, y, state.bitplane, summary)?;
        statistics.decoded_symbols(1)?;
        statistics.became_significant()?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, code_block_plane_view(final(plane)), legacy_symbols_view(final(decoder)))
        == crate::specs::part1_legacy_sign_mark(
            code_block_plane_view(old(plane)), legacy_symbols_view(old(decoder)), x, y, bitplane, summary),
))]
fn decode_sign_and_mark(
    plane: &mut CodeBlockPlane,
    decoder: &mut impl Tier1SymbolDecoder,
    x: u16,
    y: u16,
    bitplane: u16,
    summary: NeighborSummary,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_sign_mark); }
    let sign = sign_context(summary);
    let raw = decoder.is_raw();
    let decoded_sign = decoder.decode(usize::from(sign.context))?;
    plane.mark_significant_at_bitplane(
        x,
        y,
        bitplane,
        crate::refinement::tier1_decoded_sign(decoded_sign, sign.predicted_negative, raw),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_cleanup_candidate(
        code_block_plane_view(plane), legacy_bitplane_view(state), x, y, vertical_causal_context),
))]
fn cleanup_run_candidate(
    plane: &CodeBlockPlane,
    state: &Tier1BitplaneState,
    x: u16,
    y: u16,
    vertical_causal_context: bool,
) -> Result<bool, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_legacy_cleanup_candidate); }
    let index = plane.index(x, y)?;
    if index >= state.significance_visited.len() {
        return Err(invalid_code_block());
    }
    Ok(!plane.coefficient(x, y)?.significant
        && !state.significance_visited[index]
        && significant_neighbor_count(plane.neighbor_summary_with_causality(
            x,
            y,
            vertical_causal_context,
        )?) == 0)
}
