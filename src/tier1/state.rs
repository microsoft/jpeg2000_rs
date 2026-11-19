use super::{
    CodeBlockPlane, CoefficientState, MAX_TIER1_BITPLANES, NeighborKind, NeighborSummary,
    RUN_LENGTH_CONTEXT, SignContext, SignificanceStep, SubbandOrientation, Tier1CodingStyle,
    Tier1PassStatistics, UNIFORM_CONTEXT,
};
#[cfg(verus_keep_ghost)]
use super::{
    code_block_plane_outcome, code_block_plane_view, coefficient_raw_outcome, coefficient_raw_view,
    coefficient_raw_views, coefficient_signed_outcome, coefficient_slice_view,
    coefficient_state_view, neighbor_kind_tag,
};
use crate::magnitude::Magnitude;
use crate::mq::MqDecoder;
use crate::transform::SignedMagnitude;
use crate::{DecodeError, MalformedKind};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures coefficient_raw_outcome(result) == crate::specs::tier1_coefficient_new_outcome(
        crate::magnitude::magnitude_limbs(magnitude), negative, significant, refined),
))]
fn coefficient_from_magnitude(
    magnitude: Magnitude,
    negative: bool,
    significant: bool,
    refined: bool,
) -> Result<CoefficientState, DecodeError> {
    let mut output = CoefficientState {
        magnitude: magnitude.low_u64(),
        magnitude_high: [0; 5],
        legacy_bitplane: None,
        negative,
        significant,
        refined,
    };
    output.set_magnitude(magnitude)?;
    Ok(output)
}

impl CoefficientState {
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures coefficient_signed_outcome(result)
                == crate::specs::tier1_raw_signed_coefficient(coefficient_raw_view(*self)),
        )
    )]
    pub(crate) fn signed_magnitude(&self) -> Result<SignedMagnitude, DecodeError> {
        let mut magnitude = if self.significant {
            self.wide_magnitude()
        } else {
            crate::magnitude::magnitude_zero()
        };
        if let (true, Some(bitplane)) = (self.significant, self.legacy_bitplane) {
            let midpoint = if bitplane <= 64 {
                crate::magnitude::magnitude_from_u64(crate::refinement::tier1_midpoint_delta(
                    bitplane,
                ))
            } else {
                crate::magnitude::magnitude_single_bit(bitplane - 1)?
            };
            magnitude = magnitude.checked_add(midpoint)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude);
            crate::proofs::production_impl::production_tier1_value_limbs(crate::magnitude::magnitude_limbs(magnitude));
        }
        Ok(SignedMagnitude {
            magnitude,
            negative: self.significant && self.negative,
        })
    }
    pub fn magnitude_limb(&self, index: usize) -> Option<u64> {
        if index == 0 {
            Some(self.magnitude)
        } else {
            let high_index = index.checked_sub(1)?;
            if high_index < self.magnitude_high.len() {
                Some(self.magnitude_high[high_index])
            } else {
                None
            }
        }
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(result =>
            ensures crate::magnitude::magnitude_limbs(result) == crate::specs::tier1_coefficient_limbs(coefficient_raw_view(*self)),
                crate::magnitude::magnitude_limbs(result) == coefficient_raw_view(*self).limbs,
                crate::magnitude::magnitude_value(result) == crate::specs::part1_magnitude_value(coefficient_raw_view(*self).limbs),
                crate::magnitude::magnitude_value(result) < crate::specs::part1_magnitude_capacity(),
        )
    )]
    pub fn wide_magnitude(&self) -> Magnitude {
        let mut limbs = [0_u64; 6];
        limbs[0] = self.magnitude;
        let mut index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.magnitude_high.len(),
                    limbs[0] == self.magnitude,
                    forall |i: int| 0 <= i < index ==> limbs@[i + 1] == self.magnitude_high@[i],
                decreases self.magnitude_high.len() - index,
            )
        )]
        while index < self.magnitude_high.len() {
            limbs[index + 1] = self.magnitude_high[index];
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(limbs@ =~= coefficient_raw_view(*self).limbs); }
        crate::magnitude::magnitude_from_limbs(limbs)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, coefficient_state_view(final(self))) == crate::specs::tier1_set_magnitude(
                coefficient_state_view(old(self)), crate::magnitude::magnitude_limbs(magnitude)),
            result == Ok(()),
            coefficient_raw_view(*final(self)) == (crate::specs::Tier1RawCoefficient {
                limbs: crate::magnitude::magnitude_limbs(magnitude), ..coefficient_raw_view(*old(self))
            }),
    ))]
    fn set_magnitude(&mut self, magnitude: Magnitude) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude); }
        self.magnitude = magnitude.low_u64();
        let mut index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.magnitude_high.len(),
                    crate::magnitude::magnitude_limbs(magnitude).len() == 6,
                    self.magnitude == crate::magnitude::magnitude_limbs(magnitude)[0],
                    self.legacy_bitplane == old(self).legacy_bitplane,
                    self.negative == old(self).negative, self.significant == old(self).significant,
                    self.refined == old(self).refined,
                    forall |i: int| 0 <= i < index ==> self.magnitude_high@[i]
                        == crate::magnitude::magnitude_limbs(magnitude)[i + 1],
                decreases self.magnitude_high.len() - index,
            )
        )]
        while index < self.magnitude_high.len() {
            self.magnitude_high[index] =
                magnitude.limb(index + 1).ok_or_else(arithmetic_overflow)?;
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(coefficient_raw_view(*self).limbs =~= crate::magnitude::magnitude_limbs(magnitude)); }
        Ok(())
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_zero_context(summary, orientation),
))]
pub fn zero_coding_context(summary: NeighborSummary, orientation: SubbandOrientation) -> u8 {
    let (horizontal, vertical) = if matches!(orientation, SubbandOrientation::Hl) {
        (summary.vertical_significant, summary.horizontal_significant)
    } else {
        (summary.horizontal_significant, summary.vertical_significant)
    };
    let diagonal = summary.diagonal_significant;
    crate::refinement::tier1_zero_context(
        u16::from(horizontal),
        u16::from(vertical),
        u16::from(diagonal),
        matches!(orientation, SubbandOrientation::Hh),
    )
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == if value < 0 { -1i8 } else if value > 0 { 1i8 } else { 0i8 },
))]
const fn signum_i8(value: i8) -> i8 {
    if value < 0 {
        -1
    } else if value > 0 {
        1
    } else {
        0
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_sign_context(summary),
))]
pub fn sign_context(summary: NeighborSummary) -> SignContext {
    let mut horizontal = signum_i8(summary.horizontal_sign_balance);
    let mut vertical = signum_i8(summary.vertical_sign_balance);
    if horizontal < 0 {
        horizontal = 1;
        vertical = if vertical < 0 {
            1
        } else if vertical > 0 {
            -1
        } else {
            0
        };
    }

    let offset = crate::refinement::tier1_sign_offset(horizontal, vertical);
    let predicted_negative = crate::refinement::tier1_predicted_negative(
        summary.horizontal_sign_balance,
        summary.vertical_sign_balance,
    );
    SignContext {
        context: 9 + offset,
        predicted_negative,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_legacy_refinement_context(coefficient_raw_view(coefficient), summary),
))]
pub fn magnitude_refinement_context(coefficient: CoefficientState, summary: NeighborSummary) -> u8 {
    let neighbors = u16::from(summary.horizontal_significant)
        + u16::from(summary.vertical_significant)
        + u16::from(summary.diagonal_significant);
    crate::refinement::tier1_refinement_context(coefficient.refined, neighbors)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, crate::mq::mq_decoder_view(final(decoder))) == (Ok(()),
        crate::specs::part1_legacy_initialized(crate::mq::mq_decoder_view(old(decoder)))),
))]
pub fn initialize_tier1_contexts(decoder: &mut MqDecoder<'_>) -> Result<(), DecodeError> {
    decoder.reset_contexts();
    decoder.set_context(0, 4, false)?;
    decoder.set_context(RUN_LENGTH_CONTEXT, 3, false)?;
    decoder.set_context(UNIFORM_CONTEXT, 46, false)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::mq::mq_decoder_view(decoder).contexts =~=
            crate::specs::part1_legacy_initialized(crate::mq::mq_decoder_view(old(decoder))).contexts);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, crate::mq::mq_decoder_view(final(decoder))) == (Ok(()),
        if style.reset_contexts {
            crate::specs::part1_legacy_initialized(crate::mq::mq_decoder_view(old(decoder)))
        } else { crate::mq::mq_decoder_view(old(decoder)) }),
))]
pub fn reset_tier1_contexts_after_pass(
    decoder: &mut MqDecoder<'_>,
    style: Tier1CodingStyle,
) -> Result<(), DecodeError> {
    if style.reset_contexts {
        initialize_tier1_contexts(decoder)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result as nat == crate::specs::ht_significant_neighbor_count(summary),
        result as nat == summary.horizontal_significant as nat
            + summary.vertical_significant as nat + summary.diagonal_significant as nat,
))]
pub(super) fn significant_neighbor_count(summary: NeighborSummary) -> u16 {
    u16::from(summary.horizontal_significant)
        + u16::from(summary.vertical_significant)
        + u16::from(summary.diagonal_significant)
}

pub(super) const fn is_bitplane_mask(bitplane_mask: u64) -> bool {
    bitplane_mask != 0 && bitplane_mask & (bitplane_mask - 1) == 0
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::ht_reader_error(MalformedKind::InvalidCodeBlock),)
)]
pub(super) fn invalid_code_block() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    }
}

#[cfg_attr(
    verus_keep_ghost,
    verus_spec(result => ensures result == crate::specs::ht_reader_error(MalformedKind::ArithmeticOverflow),)
)]
pub(super) fn arithmetic_overflow() -> DecodeError {
    DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    }
}

pub fn apply_significance_decision(
    plane: &mut CodeBlockPlane,
    x: u16,
    y: u16,
    bitplane_mask: u64,
    orientation: SubbandOrientation,
    significant: bool,
    decoded_sign: bool,
) -> Result<SignificanceStep, DecodeError> {
    if bitplane_mask == 0 {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidCodeBlock));
    }
    let summary = plane.neighbor_summary(x, y)?;
    let zero_context = zero_coding_context(summary, orientation);
    if !significant {
        return Ok(SignificanceStep {
            zero_coding_context: zero_context,
            sign_context: None,
            became_significant: false,
        });
    }
    let sign = sign_context(summary);
    plane.mark_significant(x, y, bitplane_mask, decoded_sign ^ sign.predicted_negative)?;
    Ok(SignificanceStep {
        zero_coding_context: zero_context,
        sign_context: Some(sign.context),
        became_significant: true,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == crate::specs::ht_neighbor_zero(),))]
fn ht_neighbor_summary_zero() -> NeighborSummary {
    NeighborSummary {
        horizontal_significant: 0,
        vertical_significant: 0,
        diagonal_significant: 0,
        horizontal_sign_balance: 0,
        vertical_sign_balance: 0,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == if !coefficient_raw_view(*coefficient).significant { 0i8 }
        else if coefficient_raw_view(*coefficient).negative { -1i8 } else { 1i8 },
        -1 <= result <= 1,
))]
fn neighbor_sign(coefficient: &CoefficientState) -> i8 {
    if !coefficient.significant {
        0
    } else if coefficient.negative {
        -1
    } else {
        1
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    spec fn interior_neighbor_value(plane: crate::specs::Tier1RawPlane, center: usize) -> NeighborSummary {
        let c = center as int;
        let w = plane.width as int;
        let left = plane.coefficients[c - 1];
        let right = plane.coefficients[c + 1];
        let above = plane.coefficients[c - w];
        let below = plane.coefficients[c + w];
        NeighborSummary {
            horizontal_significant: ((if left.significant { 1int } else { 0 })
                + (if right.significant { 1int } else { 0 })) as u8,
            vertical_significant: ((if above.significant { 1int } else { 0 })
                + (if below.significant { 1int } else { 0 })) as u8,
            diagonal_significant: ((if plane.coefficients[c-w-1].significant { 1int } else { 0 })
                + (if plane.coefficients[c-w+1].significant { 1int } else { 0 })
                + (if plane.coefficients[c+w-1].significant { 1int } else { 0 })
                + (if plane.coefficients[c+w+1].significant { 1int } else { 0 })) as u8,
            horizontal_sign_balance: ((if !left.significant { 0int } else if left.negative { -1 } else { 1 })
                + (if !right.significant { 0int } else if right.negative { -1 } else { 1 })) as i8,
            vertical_sign_balance: ((if !above.significant { 0int } else if above.negative { -1 } else { 1 })
                + (if !below.significant { 0int } else if below.negative { -1 } else { 1 })) as i8,
        }
    }

    proof fn interior_neighbor_lookup(plane: crate::specs::Tier1RawPlane,
        x: u16, y: u16, center: usize, dx: int, dy: int, index: int)
        requires crate::specs::tier1_raw_plane_index(plane,x,y) == Ok(center),
            0 < x, 0 < y, x as int + 1 < plane.width, y as int + 1 < plane.height,
            -1 <= dx <= 1, -1 <= dy <= 1,
            index == center as int + dy as int * plane.width as int + dx as int,
            0 <= index < plane.coefficients.len(), index <= usize::MAX,
        ensures crate::specs::tier1_raw_plane_coefficient(plane,
            (x as int + dx as int) as u16, (y as int + dy as int) as u16)
                == Ok(plane.coefficients[index]),
    {
        assert((y as int + dy as int) * plane.width as int + x as int + dx as int == index)
            by(nonlinear_arith)
            requires center as int == y as int * plane.width as int + x as int,
                index == center as int + dy as int * plane.width as int + dx as int;
    }

    spec fn neighbor_summary_add(state: NeighborSummary, kind: u8,
        coefficient: crate::specs::Tier1RawCoefficient) -> NeighborSummary {
        let count = if coefficient.significant { 1int } else { 0 };
        let sign = if !coefficient.significant { 0int } else if coefficient.negative { -1 } else { 1 };
        NeighborSummary {
            horizontal_significant: (state.horizontal_significant as int + if kind == 0 { count } else { 0 }) as u8,
            vertical_significant: (state.vertical_significant as int + if kind == 1 { count } else { 0 }) as u8,
            diagonal_significant: (state.diagonal_significant as int + if kind == 2 { count } else { 0 }) as u8,
            horizontal_sign_balance: (state.horizontal_sign_balance as int + if kind == 0 { sign } else { 0 }) as i8,
            vertical_sign_balance: (state.vertical_sign_balance as int + if kind == 1 { sign } else { 0 }) as i8,
        }
    }

    proof fn neighbor_step_known(plane: crate::specs::Tier1RawPlane, x:u16,y:u16,
        dx:int,dy:int,kind:u8,state:NeighborSummary,coefficient:crate::specs::Tier1RawCoefficient)
        requires -1 <= dx <= 1, -1 <= dy <= 1, kind <= 2,
            0 <= x as int + dx < plane.width, 0 <= y as int + dy < plane.height,
            crate::specs::tier1_raw_plane_coefficient(plane,(x as int+dx) as u16,(y as int+dy) as u16) == Ok(coefficient),
            state.horizontal_significant <= 4, state.vertical_significant <= 4, state.diagonal_significant <= 4,
            -4 <= state.horizontal_sign_balance <= 4, -4 <= state.vertical_sign_balance <= 4,
        ensures crate::specs::ht_accumulate_neighbor(plane,x,y,dx as i8,dy as i8,kind,state)
                == (Ok(()),neighbor_summary_add(state,kind,coefficient)),
            crate::specs::ht_neighbor_then((Ok(()),state),plane,x,y,dx as i8,dy as i8,kind)
                == (Ok(()),neighbor_summary_add(state,kind,coefficient)),
    {}

    proof fn interior_neighbor_value_matches(plane: crate::specs::Tier1RawPlane,
        x: u16, y: u16, center: usize, vertical_causal: bool)
        requires crate::specs::tier1_raw_plane_index(plane,x,y) == Ok(center),
            0 < x, 0 < y, x as int + 1 < plane.width, y as int + 1 < plane.height,
            !vertical_causal || y % 4 != 3,
            center as int - plane.width as int - 1 >= 0,
            center as int + plane.width as int + 1 < plane.coefficients.len(),
            center as int + plane.width as int + 1 <= usize::MAX,
        ensures crate::specs::ht_neighbors(plane,x,y,vertical_causal) == Ok(interior_neighbor_value(plane,center)),
    {
        hide(crate::specs::ht_neighbors);
        hide(crate::specs::ht_neighbor_then);
        hide(crate::specs::ht_accumulate_neighbor);
        hide(crate::specs::ht_neighbor_update);
        let c = center as int;
        let w = plane.width as int;
        interior_neighbor_lookup(plane,x,y,center,-1,0,c-1);
        interior_neighbor_lookup(plane,x,y,center,1,0,c+1);
        interior_neighbor_lookup(plane,x,y,center,0,-1,c-w);
        interior_neighbor_lookup(plane,x,y,center,-1,-1,c-w-1);
        interior_neighbor_lookup(plane,x,y,center,1,-1,c-w+1);
        interior_neighbor_lookup(plane,x,y,center,0,1,c+w);
        interior_neighbor_lookup(plane,x,y,center,-1,1,c+w-1);
        interior_neighbor_lookup(plane,x,y,center,1,1,c+w+1);
        let s0 = crate::specs::ht_neighbor_zero();
        let left = plane.coefficients[c-1];
        let right = plane.coefficients[c+1];
        let above = plane.coefficients[c-w];
        let ul = plane.coefficients[c-w-1];
        let ur = plane.coefficients[c-w+1];
        let below = plane.coefficients[c+w];
        let dl = plane.coefficients[c+w-1];
        let dr = plane.coefficients[c+w+1];
        neighbor_step_known(plane,x,y,-1,0,0,s0,left);
        let s1 = neighbor_summary_add(s0,0,left);
        neighbor_step_known(plane,x,y,1,0,0,s1,right);
        let s2 = neighbor_summary_add(s1,0,right);
        neighbor_step_known(plane,x,y,0,-1,1,s2,above);
        let s3 = neighbor_summary_add(s2,1,above);
        neighbor_step_known(plane,x,y,-1,-1,2,s3,ul);
        let s4 = neighbor_summary_add(s3,2,ul);
        neighbor_step_known(plane,x,y,1,-1,2,s4,ur);
        let s5 = neighbor_summary_add(s4,2,ur);
        neighbor_step_known(plane,x,y,0,1,1,s5,below);
        let s6 = neighbor_summary_add(s5,1,below);
        neighbor_step_known(plane,x,y,-1,1,2,s6,dl);
        let s7 = neighbor_summary_add(s6,2,dl);
        neighbor_step_known(plane,x,y,1,1,2,s7,dr);
        let s8 = neighbor_summary_add(s7,2,dr);
        assert(s8 == interior_neighbor_value(plane,center));
        reveal(crate::specs::ht_neighbors);
    }
}

impl Clone for CodeBlockPlane {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures code_block_plane_view(&result) == code_block_plane_view(self),
    ))]
    fn clone(&self) -> Self {
        Self {
            width: self.width,
            height: self.height,
            coefficients: self.coefficients.clone(),
        }
    }
}

impl CodeBlockPlane {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures if _legacy{crate::specs::part2_tier1_storage_framed(|calls|crate::specs::part2_nested_plane_run(code_block_plane_view(self),_role,calls),code_block_plane_outcome(result))}
            else{crate::specs::part2_decoder_plane_result(code_block_plane_view(self),_role,_cleanup,code_block_plane_outcome(result))},
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>code_block_plane_view(&value)==code_block_plane_view(self)},
    ))]
    pub(super) fn try_duplicate_raw(
        &self,
        _role: super::HtRefinementCopyRole,
        _cleanup: bool,
        _legacy: bool,
    ) -> Result<Self, DecodeError> {
        Ok(Self {
            width: self.width,
            height: self.height,
            coefficients: {
                let copied = crate::allocation::copy_values(&self.coefficients);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let result=match copied{Err(error)=>Err(error),Ok(_)=>Ok(())};
                    if _legacy{crate::specs::part2_nested_plane_observed(code_block_plane_view(self),_role,result);}
                    else{crate::specs::part2_decoder_plane_observed(code_block_plane_view(self),_role,_cleanup,result);}
                }
                copied?
            },
        })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_tier1_plane_storage_result(width,height,_role,code_block_plane_outcome(result)),
        code_block_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            code_block_plane_outcome(result) == crate::specs::tier1_empty_plane(width, height),
))]
pub(super) fn code_block_plane_from_dimensions(
    width: u16,
    height: u16,
    _role: super::CoefficientStorageRole,
) -> Result<CodeBlockPlane, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_tier1_plane_normal(width,height,_role);}
    if width == 0 || height == 0 {
        return Err(invalid_code_block());
    }
    let samples = usize::from(width)
        .checked_mul(usize::from(height))
        .ok_or_else(arithmetic_overflow)?;
    if samples > 4096 {
        return Err(invalid_code_block());
    }
    let empty = CoefficientState {
        magnitude: 0,
        magnitude_high: [0; 5],
        legacy_bitplane: None,
        negative: false,
        significant: false,
        refined: false,
    };
    let filled = crate::allocation::filled_values(empty, samples);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_tier1_plane_observed(width,height,_role,samples,match filled {Ok(_)=>Ok(()),Err(error)=>Err(error)});}
    let coefficients = filled?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(coefficient_raw_view(empty).limbs =~= Seq::new(6, |i: int| 0u64));
        assert(coefficient_raw_view(empty) == crate::specs::tier1_empty_coefficient());
        assert forall |i: int| 0 <= i < samples implies coefficient_raw_view(coefficients@[i])
            == crate::specs::tier1_empty_coefficient() by {
            assert(coefficients@[i] == empty);
        }
        assert(coefficient_raw_views(coefficients@) =~= Seq::new(samples as nat, |i: int| crate::specs::tier1_empty_coefficient()));
    }
    Ok(CodeBlockPlane {
        width,
        height,
        coefficients,
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == crate::specs::tier1_statistics_zero(),))]
pub(super) fn ht_statistics_zero() -> Tier1PassStatistics {
    Tier1PassStatistics {
        coefficients_scanned: 0,
        coding_symbols: 0,
        newly_significant: 0,
        refined_coefficients: 0,
        run_mode_columns: 0,
    }
}

impl CodeBlockPlane {
    pub fn new(width: u16, height: u16) -> Result<Self, DecodeError> {
        code_block_plane_from_dimensions(width, height, super::CoefficientStorageRole::Standalone)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_plane_duplicate_storage_result(code_block_plane_view(self),role,code_block_plane_outcome(result)),
            code_block_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                code_block_plane_outcome(result) == crate::specs::tier1_duplicate_plane(code_block_plane_view(self)),
    ))]
    pub(super) fn duplicate(
        &self,
        role: super::CoefficientStorageRole,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_plane_duplicate_normal(code_block_plane_view(self),role);}
        let output_result = code_block_plane_from_dimensions(self.width, self.height, role);
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=output_result {crate::specs::part2_plane_duplicate_error(code_block_plane_view(self),role,error);}}
        let mut output = output_result?;
        if output.coefficients.len() != self.coefficients.len() {
            return Err(invalid_code_block());
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.coefficients.len(),
                    crate::specs::part1_plane_duplicate_storage_result(code_block_plane_view(self),role,crate::specs::tier1_duplicate_plane(code_block_plane_view(self))),
                    output.width == self.width, output.height == self.height,
                    output.coefficients.len() == self.coefficients.len(),
                    forall |i: int| 0 <= i < index ==> coefficient_raw_view(output.coefficients@[i])
                        == coefficient_raw_view(self.coefficients@[i]),
                decreases self.coefficients.len() - index,
            )
        )]
        while index < self.coefficients.len() {
            *output
                .coefficients
                .get_mut(index)
                .ok_or_else(invalid_code_block)? = *self
                .coefficients
                .get(index)
                .ok_or_else(invalid_code_block)?;
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(code_block_plane_view(&output).coefficients =~= code_block_plane_view(self).coefficients); }
        Ok(output)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::tier1_raw_plane_width(code_block_plane_view(self)),
            result == code_block_plane_view(self).width,
    ))]
    pub const fn width(&self) -> u16 {
        self.width
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::tier1_raw_plane_height(code_block_plane_view(self)),
            result == code_block_plane_view(self).height,
    ))]
    pub const fn height(&self) -> u16 {
        self.height
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures coefficient_raw_outcome(result) == crate::specs::tier1_raw_plane_coefficient(code_block_plane_view(self), x, y),
    ))]
    pub fn coefficient(&self, x: u16, y: u16) -> Result<CoefficientState, DecodeError> {
        let index = self.index(x, y)?;
        if index >= self.coefficients.len() {
            return Err(invalid_code_block());
        }
        Ok(self.coefficients[index])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures coefficient_slice_view(result) == crate::specs::tier1_raw_plane_coefficients(code_block_plane_view(self)),
            coefficient_raw_views(result@) == code_block_plane_view(self).coefficients,
    ))]
    pub fn coefficients(&self) -> &[CoefficientState] {
        &self.coefficients
    }

    /// Returns the reconstructed integer coefficient, including any legacy
    /// truncation midpoint; `coefficient` retains the decoded magnitude bits.
    pub fn signed_coefficient(&self, x: u16, y: u16) -> Result<i64, DecodeError> {
        let coefficient = self.coefficient(x, y)?;
        if !coefficient.significant {
            return Ok(0);
        }
        let magnitude = coefficient
            .signed_magnitude()?
            .magnitude
            .to_u64()
            .and_then(|value| i64::try_from(value).ok())
            .ok_or_else(arithmetic_overflow)?;
        if coefficient.negative {
            if magnitude == i64::MIN {
                Err(arithmetic_overflow())
            } else {
                Ok(-magnitude)
            }
        } else {
            Ok(magnitude)
        }
    }

    pub fn mark_significant(
        &mut self,
        x: u16,
        y: u16,
        magnitude: u64,
        negative: bool,
    ) -> Result<(), DecodeError> {
        self.mark_significant_magnitude(x, y, Magnitude::from_u64(magnitude), negative)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, code_block_plane_view(final(self))) == crate::specs::part1_legacy_mark(
            code_block_plane_view(old(self)), x, y, bitplane, negative),
            final(self).width == old(self).width, final(self).height == old(self).height,
    ))]
    pub(super) fn mark_significant_at_bitplane(
        &mut self,
        x: u16,
        y: u16,
        bitplane: u16,
        negative: bool,
    ) -> Result<(), DecodeError> {
        self.mark_significant_magnitude(
            x,
            y,
            crate::magnitude::magnitude_single_bit(bitplane)?,
            negative,
        )?;
        let index = self.index(x, y)?;
        self.coefficients
            .get_mut(index)
            .ok_or_else(invalid_code_block)?
            .legacy_bitplane = Some(bitplane);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(code_block_plane_view(self).coefficients =~=
                crate::specs::part1_legacy_mark(code_block_plane_view(old(self)), x, y, bitplane, negative).1.coefficients);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, code_block_plane_view(final(self))) == crate::specs::tier1_mark_coefficient(
            code_block_plane_view(old(self)), x, y, crate::magnitude::magnitude_limbs(magnitude),
            crate::magnitude::magnitude_value(magnitude), negative),
    ))]
    pub(super) fn mark_significant_magnitude(
        &mut self,
        x: u16,
        y: u16,
        magnitude: Magnitude,
        negative: bool,
    ) -> Result<(), DecodeError> {
        if magnitude.is_zero() {
            return Err(invalid_code_block());
        }
        let index = self.index(x, y)?;
        if index >= self.coefficients.len() {
            return Err(invalid_code_block());
        }
        if self.coefficients[index].significant {
            return Err(invalid_code_block());
        }
        self.coefficients[index] = coefficient_from_magnitude(magnitude, negative, true, false)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(coefficient_raw_views(self.coefficients@) =~=
                code_block_plane_view(old(self)).coefficients.update(index as int,
                    crate::specs::tier1_new_coefficient(crate::magnitude::magnitude_limbs(magnitude), negative, true, false)));
        }
        Ok(())
    }

    pub fn refine(&mut self, x: u16, y: u16, bitplane_mask: u64) -> Result<(), DecodeError> {
        self.apply_refinement_decision(x, y, bitplane_mask, true)
    }

    pub fn apply_refinement_decision(
        &mut self,
        x: u16,
        y: u16,
        bitplane_mask: u64,
        refinement_bit: bool,
    ) -> Result<(), DecodeError> {
        if !is_bitplane_mask(bitplane_mask) {
            return Err(invalid_code_block());
        }
        let bitplane =
            u16::try_from(bitplane_mask.trailing_zeros()).map_err(|_| arithmetic_overflow())?;
        self.apply_refinement_bit(x, y, bitplane, refinement_bit)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, code_block_plane_view(final(self))) == crate::specs::part1_legacy_refine(
            code_block_plane_view(old(self)), x, y, bitplane, refinement_bit),
            final(self).width == old(self).width, final(self).height == old(self).height,
    ))]
    pub(super) fn apply_refinement_bit(
        &mut self,
        x: u16,
        y: u16,
        bitplane: u16,
        refinement_bit: bool,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost start = code_block_plane_view(self); }
        if bitplane >= MAX_TIER1_BITPLANES {
            return Err(invalid_code_block());
        }
        let index = self.index(x, y)?;
        if index >= self.coefficients.len() {
            return Err(invalid_code_block());
        }
        let coefficient = self.coefficients[index];
        if !coefficient.significant {
            return Err(invalid_code_block());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_magnitude_value_bound(coefficient_raw_view(coefficient).limbs);
        }
        if refinement_bit {
            let current = coefficient.wide_magnitude();
            let delta = crate::magnitude::magnitude_single_bit(bitplane)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::magnitude::representation_proofs::magnitude_limbs_shape(current);
                crate::magnitude::representation_proofs::magnitude_limbs_shape(delta);
                crate::proofs::production_impl::production_legacy_magnitude_u64(crate::magnitude::magnitude_limbs(current));
                crate::proofs::production_impl::production_legacy_magnitude_u64(crate::magnitude::magnitude_limbs(delta));
            }
            let magnitude = match (current.to_u64(), delta.to_u64()) {
                (Some(current), Some(delta)) if current <= u64::MAX - delta => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(current as nat == crate::specs::part1_magnitude_value(coefficient_raw_view(coefficient).limbs));
                        assert(delta as nat == vstd::arithmetic::power2::pow2(bitplane as nat));
                    }
                    crate::magnitude::magnitude_from_u64(
                        crate::refinement::tier1_refined_magnitude(current, delta, true),
                    )
                }
                _ => current.checked_add(delta)?,
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(crate::magnitude::magnitude_value(magnitude) ==
                    crate::specs::part1_magnitude_value(coefficient_raw_view(coefficient).limbs)
                        + vstd::arithmetic::power2::pow2(bitplane as nat));
                crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude);
                crate::proofs::production_impl::production_magnitude_value_bound(crate::magnitude::magnitude_limbs(magnitude));
                crate::proofs::production_impl::production_tier1_value_limbs(crate::magnitude::magnitude_limbs(magnitude));
            }
            self.coefficients[index].set_magnitude(magnitude)?;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(coefficient_raw_view(self.coefficients[index as int]).limbs
                    == crate::specs::tier1_value_limbs(
                        crate::specs::part1_magnitude_value(coefficient_raw_view(coefficient).limbs)
                            + vstd::arithmetic::power2::pow2(bitplane as nat)));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_legacy_refine(start, x, y, bitplane, refinement_bit).0 == Ok(()));
            assert(coefficient_raw_view(self.coefficients[index as int]) == (crate::specs::Tier1RawCoefficient {
                limbs: if refinement_bit {
                    crate::specs::tier1_value_limbs(crate::specs::part1_magnitude_value(coefficient_raw_view(coefficient).limbs)
                        + vstd::arithmetic::power2::pow2(bitplane as nat))
                } else { coefficient_raw_view(coefficient).limbs },
                ..coefficient_raw_view(coefficient)
            }));
        }
        self.coefficients[index].refined = true;
        if coefficient.legacy_bitplane.is_some() {
            self.coefficients[index].legacy_bitplane = Some(bitplane);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(coefficient_raw_view(self.coefficients[index as int])
                == crate::specs::part1_legacy_refine(start, x, y, bitplane, refinement_bit).1.coefficients[index as int]);
            assert(code_block_plane_view(self).coefficients =~=
                crate::specs::part1_legacy_refine(start, x, y, bitplane, refinement_bit).1.coefficients);
        }
        Ok(())
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, code_block_plane_view(final(self))) == crate::specs::ht_apply_refinement(
            code_block_plane_view(old(self)), x, y, crate::magnitude::magnitude_value(delta), refinement_bit),
            final(self).width == old(self).width, final(self).height == old(self).height,
    ))]
    pub(super) fn apply_ht_refinement_decision(
        &mut self,
        x: u16,
        y: u16,
        delta: Magnitude,
        refinement_bit: bool,
    ) -> Result<(), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost start = code_block_plane_view(self); }
        if delta.is_zero() && !refinement_bit {
            return Err(invalid_code_block());
        }
        let index = self.index(x, y)?;
        let coefficient = *self
            .coefficients
            .get(index)
            .ok_or_else(invalid_code_block)?;
        if !coefficient.significant {
            return Err(invalid_code_block());
        }
        let magnitude = if refinement_bit {
            coefficient.wide_magnitude().checked_add(delta)?
        } else {
            match coefficient.wide_magnitude().checked_sub(delta) {
                Ok(value) => value,
                Err(_) => return Err(invalid_code_block()),
            }
        };
        if magnitude.is_zero() {
            return Err(invalid_code_block());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::magnitude::representation_proofs::magnitude_limbs_shape(magnitude);
            crate::proofs::production_impl::production_tier1_value_limbs(crate::magnitude::magnitude_limbs(magnitude));
        }
        let output = self
            .coefficients
            .get_mut(index)
            .ok_or_else(invalid_code_block)?;
        output.set_magnitude(magnitude)?;
        output.refined = true;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(code_block_plane_view(self).coefficients =~= start.coefficients.update(index as int,
                crate::specs::Tier1RawCoefficient {
                    limbs: crate::specs::tier1_value_limbs(crate::magnitude::magnitude_value(magnitude)), refined: true,
                    ..start.coefficients[index as int]
                }));
        }
        Ok(())
    }

    pub fn neighbor_summary(&self, x: u16, y: u16) -> Result<NeighborSummary, DecodeError> {
        self.neighbor_summary_with_causality(x, y, false)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::ht_neighbors(code_block_plane_view(self), x, y, vertical_causal_context),
    ))]
    pub(super) fn neighbor_summary_with_causality(
        &self,
        x: u16,
        y: u16,
        vertical_causal_context: bool,
    ) -> Result<NeighborSummary, DecodeError> {
        let center = self.index(x, y)?;
        if let Some(summary) = self.interior_neighbor_summary(x, y, center, vertical_causal_context)
        {
            return Ok(summary);
        }
        let mut summary = ht_neighbor_summary_zero();
        self.accumulate_neighbor(x, y, (-1, 0), NeighborKind::Horizontal, &mut summary)?;
        self.accumulate_neighbor(x, y, (1, 0), NeighborKind::Horizontal, &mut summary)?;
        self.accumulate_neighbor(x, y, (0, -1), NeighborKind::Vertical, &mut summary)?;
        self.accumulate_neighbor(x, y, (-1, -1), NeighborKind::Diagonal, &mut summary)?;
        self.accumulate_neighbor(x, y, (1, -1), NeighborKind::Diagonal, &mut summary)?;
        if !vertical_causal_context || y % 4 != 3 {
            self.accumulate_neighbor(x, y, (0, 1), NeighborKind::Vertical, &mut summary)?;
            self.accumulate_neighbor(x, y, (-1, 1), NeighborKind::Diagonal, &mut summary)?;
            self.accumulate_neighbor(x, y, (1, 1), NeighborKind::Diagonal, &mut summary)?;
        }
        Ok(summary)
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires crate::specs::tier1_raw_plane_index(code_block_plane_view(self), x, y) == Ok(center),
        ensures match result { None => true, Some(summary) =>
            crate::specs::ht_neighbors(code_block_plane_view(self), x, y, vertical_causal_context)
                == Ok(summary) },
    ))]
    fn interior_neighbor_summary(
        &self,
        x: u16,
        y: u16,
        center: usize,
        vertical_causal_context: bool,
    ) -> Option<NeighborSummary> {
        if x == 0
            || y == 0
            || u32::from(x) + 1 >= u32::from(self.width)
            || u32::from(y) + 1 >= u32::from(self.height)
            || (vertical_causal_context && y % 4 == 3)
        {
            return None;
        }
        let stride = usize::from(self.width);
        let upper = center.checked_sub(stride)?.checked_sub(1)?;
        let middle = center.checked_sub(1)?;
        let lower = center.checked_add(stride)?.checked_sub(1)?;
        let upper = self.coefficients.get(upper..upper.checked_add(3)?)?;
        let middle = self.coefficients.get(middle..middle.checked_add(3)?)?;
        let lower = self.coefficients.get(lower..lower.checked_add(3)?)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(code_block_plane_view);
            reveal(coefficient_raw_view);
            interior_neighbor_value_matches(code_block_plane_view(self), x, y, center, vertical_causal_context);
        }
        Some(NeighborSummary {
            horizontal_significant: middle[0].significant as u8 + middle[2].significant as u8,
            vertical_significant: upper[1].significant as u8 + lower[1].significant as u8,
            diagonal_significant: upper[0].significant as u8
                + upper[2].significant as u8
                + lower[0].significant as u8
                + lower[2].significant as u8,
            horizontal_sign_balance: neighbor_sign(&middle[0]) + neighbor_sign(&middle[2]),
            vertical_sign_balance: neighbor_sign(&upper[1]) + neighbor_sign(&lower[1]),
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::tier1_raw_plane_index(code_block_plane_view(self), x, y),
    ))]
    pub(super) fn index(&self, x: u16, y: u16) -> Result<usize, DecodeError> {
        if x >= self.width || y >= self.height {
            return Err(invalid_code_block());
        }
        let index = usize::from(y)
            .checked_mul(usize::from(self.width))
            .ok_or_else(arithmetic_overflow)?
            .checked_add(usize::from(x))
            .ok_or_else(arithmetic_overflow)?;
        if index >= self.coefficients.len() {
            return Err(invalid_code_block());
        }
        Ok(index)
    }

    // Specialize the fixed offsets and neighbor kinds in the hot context traversal.
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, *final(summary)) == crate::specs::ht_accumulate_neighbor(
            code_block_plane_view(self), x, y, delta.0, delta.1, neighbor_kind_tag(kind), *old(summary)),
            result == Ok(()) || result.is_err(),
    ))]
    pub(super) fn accumulate_neighbor(
        &self,
        x: u16,
        y: u16,
        delta: (i8, i8),
        kind: NeighborKind,
        summary: &mut NeighborSummary,
    ) -> Result<(), DecodeError> {
        let neighbor_x = i32::from(x) + i32::from(delta.0);
        let neighbor_y = i32::from(y) + i32::from(delta.1);
        if neighbor_x < 0
            || neighbor_y < 0
            || neighbor_x >= i32::from(self.width)
            || neighbor_y >= i32::from(self.height)
        {
            return Ok(());
        }
        let coefficient = self.coefficient(
            u16::try_from(neighbor_x)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            u16::try_from(neighbor_y)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
        )?;
        if !coefficient.significant {
            return Ok(());
        }
        let sign = if coefficient.negative { -1 } else { 1 };
        if matches!(kind, NeighborKind::Horizontal) {
            summary.horizontal_significant = summary
                .horizontal_significant
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            summary.horizontal_sign_balance = summary
                .horizontal_sign_balance
                .checked_add(sign)
                .ok_or_else(arithmetic_overflow)?;
        } else if matches!(kind, NeighborKind::Vertical) {
            summary.vertical_significant = summary
                .vertical_significant
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
            summary.vertical_sign_balance = summary
                .vertical_sign_balance
                .checked_add(sign)
                .ok_or_else(arithmetic_overflow)?;
        } else {
            summary.diagonal_significant = summary
                .diagonal_significant
                .checked_add(1)
                .ok_or_else(arithmetic_overflow)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interior_neighbor_rows_preserve_exact_flags_and_guarded_fallbacks() {
        let mut plane = CodeBlockPlane {
            width: 3,
            height: 3,
            coefficients: vec![CoefficientState::default(); 9],
        };
        for index in [0, 1, 2, 3, 5, 8] {
            plane.coefficients[index].magnitude = 1;
            plane.coefficients[index].significant = true;
        }
        for index in [0, 1, 5] {
            plane.coefficients[index].negative = true;
        }
        let expected = NeighborSummary {
            horizontal_significant: 2,
            vertical_significant: 1,
            diagonal_significant: 3,
            horizontal_sign_balance: 0,
            vertical_sign_balance: -1,
        };
        assert_eq!(
            plane.interior_neighbor_summary(1, 1, 4, false),
            Some(expected)
        );
        assert_eq!(
            plane.neighbor_summary_with_causality(1, 1, false),
            Ok(expected)
        );
        assert_eq!(plane.interior_neighbor_summary(0, 1, 3, false), None);

        let mut short = plane.clone();
        short.coefficients.truncate(8);
        assert_eq!(short.interior_neighbor_summary(1, 1, 4, false), None);
        assert_eq!(
            short.neighbor_summary_with_causality(1, 1, false),
            Err(invalid_code_block())
        );

        let stripe = CodeBlockPlane {
            width: 3,
            height: 5,
            coefficients: vec![CoefficientState::default(); 15],
        };
        assert!(stripe.interior_neighbor_summary(1, 3, 10, true).is_none());
        assert!(stripe.interior_neighbor_summary(1, 3, 10, false).is_some());
        assert_eq!(
            stripe.neighbor_summary_with_causality(1, 3, true),
            Ok(NeighborSummary::default())
        );
    }
}
