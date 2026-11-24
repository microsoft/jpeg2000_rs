use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::{FIXED_ONE, InverseLiftingStep};
#[cfg(verus_keep_ghost)]
use super::{lifting_step_view, sequence_outcome};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_sequence_result(low@,high@,low_pass_first,false,None,sequence_outcome(result)),
        sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_inverse_five_three(low@, high@, low_pass_first),
))]
pub fn inverse_5_3(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_sequence_normal(low@,high@,low_pass_first,false,None);}
    let interleaved = interleave(low, high, low_pass_first);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=interleaved{crate::specs::part2_wavelet_sequence_interleave_error(low@,high@,low_pass_first,false,None,error);}}
    let mut output = interleaved?;
    if output.len() == 1 && !low_pass_first {
        output[0] >>= 1;
        return Ok(output);
    }
    inverse_lift(
        &mut output,
        low_pass_first,
        InverseLiftingStep::ReversibleUpdate,
    )?;
    inverse_lift(
        &mut output,
        !low_pass_first,
        InverseLiftingStep::ReversiblePredict,
    )?;
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_sequence_result(low@,high@,low_pass_first,true,None,sequence_outcome(result)),
        sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_inverse_nine_seven(low@, high@, low_pass_first),
))]
pub fn inverse_9_7(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    inverse_fixed_line::<false>(low, high, low_pass_first)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_sequence_result(low@,high@,low_pass_first,true,None,sequence_outcome(result)),
        sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_inverse_nine_seven(low@, high@, low_pass_first),
))]
pub(super) fn inverse_fixed_line<const HORIZONTAL: bool>(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_sequence_normal(low@,high@,low_pass_first,true,None);}
    let interleaved = interleave(low, high, low_pass_first);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=interleaved{crate::specs::part2_wavelet_sequence_interleave_error(low@,high@,low_pass_first,true,None,error);}}
    let mut output = interleaved?;
    if output.len() == 1 && !low_pass_first {
        output[0] >>= 1;
        return Ok(output);
    }
    if output.len() <= 1 {
        return Ok(output);
    }
    scale_parity(
        &mut output,
        low_pass_first,
        crate::refinement::nine_seven_scale(true),
    )?;
    scale_parity(
        &mut output,
        !low_pass_first,
        crate::refinement::nine_seven_scale(false),
    )?;
    // Scale with the original checks before inspecting the actual lifting
    // inputs. One scan admits all four lifts; no changes to the scale passes.
    if HORIZONTAL && super::rowwise::bounded(&output)? {
        inverse_nine_seven_lifts::<true>(&mut output, low_pass_first)?;
    } else {
        inverse_nine_seven_lifts::<false>(&mut output, low_pass_first)?;
    }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires BOUNDED ==> crate::specs::fixed_stage_bounded(old(samples)@,0),
    ensures (result, final(samples)@) == crate::specs::part1_nine_seven_lifting_prefix(old(samples)@, low_first, 4),
))]
pub(super) fn inverse_nine_seven_lifts<const BOUNDED: bool>(
    samples: &mut [i64],
    low_first: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let mut stage = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage <= 4,
        original == old(samples)@,
        BOUNDED ==> crate::specs::fixed_stage_bounded(samples@,stage as nat),
        crate::specs::part1_nine_seven_lifting_prefix(original, low_first, stage as nat) == (Ok(()), samples@),
        decreases 4 - stage,
    ))]
    while stage < 4 {
        let target_even = if stage == 0 || stage == 2 {
            low_first
        } else {
            !low_first
        };
        let factor = crate::refinement::nine_seven_lift(stage);
        match inverse_lift_impl::<BOUNDED>(
            samples,
            target_even,
            InverseLiftingStep::Fixed(factor),
            stage,
        ) {
            Ok(()) => {}
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::proofs::production_impl::production_nine_seven_error_persists(
                        original, low_first, stage as nat + 1, 4,
                    );
                }
                return Err(error);
            }
        }
        stage += 1;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_wavelet_interleave_result(low@,high@,low_pass_first,sequence_outcome(result)),
        sequence_outcome(result)!=Err(DecodeError::AllocationFailed) ==> sequence_outcome(result) == crate::specs::part1_interleaved(low@, high@, low_pass_first),
))]
pub(super) fn interleave(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_interleave_normal(low@,high@,low_pass_first);}
    let length = low
        .len()
        .checked_add(high.len())
        .ok_or_else(arithmetic_overflow)?;
    let expected_low = if low_pass_first {
        length / 2 + length % 2
    } else {
        length / 2
    };
    if low.len() != expected_low || high.len() != length - expected_low {
        return Err(invalid_transform());
    }
    let allocated = if length == 0 {
        Ok(Vec::new())
    } else {
        crate::allocation::empty_with_capacity(length)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let unit=match allocated{Err(error)=>Err(error),Ok(_)=>Ok(())};
        crate::specs::part2_wavelet_line_capacity_observed(crate::specs::Part2WaveletLineContext::Interleave {low:low@.len(),high:high@.len(),first:low_pass_first},unit);
        if let Err(error)=allocated{crate::specs::part2_wavelet_interleave_refused(low@,high@,low_pass_first,error);}
    }
    let mut output = allocated?;
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= length,
            crate::specs::part2_wavelet_interleave_result(low@,high@,low_pass_first,crate::specs::part1_interleaved(low@,high@,low_pass_first)),
            length == low.len() + high.len(),
            low.len() == if low_pass_first { length as int / 2 + length as int % 2 } else { length as int / 2 },
            high.len() == length - low.len(),
            output.len() == index,
            forall |i: int| 0 <= i < index ==>
                output[i] == if (i % 2 == 0) == low_pass_first { low[i / 2] } else { high[i / 2] },
            decreases length - index,
        )
    )]
    while index < length {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_index_parity(index); }
        let low_position = (index & 1 == 0) == low_pass_first;
        let source_index = index / 2;
        let value = if low_position {
            *low.get(source_index).ok_or_else(invalid_transform)?
        } else {
            *high.get(source_index).ok_or_else(invalid_transform)?
        };
        output.push(value);
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output@ =~= Seq::new(length as nat, |i: int|
            if (i % 2 == 0) == low_pass_first { low@[i / 2] } else { high@[i / 2] }));
    }
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(samples)@) == crate::specs::part1_lifting_prefix(
        old(samples)@, target_even, lifting_step_view(step).0, lifting_step_view(step).1, old(samples).len() as nat,
    ),
))]
pub(super) fn inverse_lift(
    samples: &mut [i64],
    target_even: bool,
    step: InverseLiftingStep,
) -> Result<(), DecodeError> {
    inverse_lift_impl::<false>(samples, target_even, step, 0)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires BOUNDED ==> stage<4 && lifting_step_view(step)==(2u8,crate::specs::part1_nine_seven_lift(stage))
        && crate::specs::fixed_stage_bounded(old(samples)@,stage as nat),
    ensures (result, final(samples)@) == crate::specs::part1_lifting_prefix(
        old(samples)@, target_even, lifting_step_view(step).0, lifting_step_view(step).1, old(samples).len() as nat,
    ),
        BOUNDED && result.is_ok() ==> crate::specs::fixed_stage_bounded(final(samples)@,stage as nat+1),
))]
fn inverse_lift_impl<const BOUNDED: bool>(
    samples: &mut [i64],
    target_even: bool,
    step: InverseLiftingStep,
    stage: u8,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    #[cfg(verus_keep_ghost)]
    proof! { if BOUNDED {crate::specs::fixed_stage_bound_grows(stage as nat);} }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= samples.len(),
            original == old(samples)@,
            samples.len() == original.len(),
            BOUNDED ==> stage<4 && lifting_step_view(step)==(2u8,crate::specs::part1_nine_seven_lift(stage))
                && crate::specs::fixed_stage_bounded(original,stage as nat)
                && crate::specs::fixed_stage_bounded(samples@,stage as nat+1),
            forall |i: int| 0 <= i < samples.len() && (i >= index || (i % 2 == 0) != target_even) ==>
                samples[i] == original[i],
            crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, index as nat,
            ) == (Ok(()), samples@),
            decreases samples.len() - index,
        )
    )]
    while index < samples.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(
                original, samples@, index as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
            );
            if BOUNDED {
                assert forall |i:int| 0<=i<samples.len() && (i>=index || (i%2==0)!=target_even) implies
                    -crate::specs::rowwise_fixed_bound(stage as nat)<=#[trigger] samples[i]<=crate::specs::rowwise_fixed_bound(stage as nat) by {
                    assert(samples[i]==original[i]);
                    assert(-crate::specs::rowwise_fixed_bound(stage as nat)<=original[i]<=crate::specs::rowwise_fixed_bound(stage as nat));
                }
            }
        }
        let value = match inverse_lifting_value::<BOUNDED>(samples, index, target_even, step, stage)
        {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part1_lifting_prefix(
                        original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, index as nat + 1,
                    ) == (Err(error), samples@));
                    crate::proofs::production_impl::production_lifting_error_persists(
                        original, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
                        index as nat + 1, original.len(),
                    );
                }
                return Err(error);
            }
        };
        samples[index] = value;
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < samples.len(),
        BOUNDED ==> stage<4 && lifting_step_view(step)==(2u8,crate::specs::part1_nine_seven_lift(stage))
            && forall |i:int| 0<=i<samples.len() && (i>=index || (i%2==0)!=target_even) ==>
                -crate::specs::rowwise_fixed_bound(stage as nat)<=#[trigger] samples[i]<=crate::specs::rowwise_fixed_bound(stage as nat),
    ensures result == crate::specs::part1_lifting_sample(
        samples@, index as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
    ),
        BOUNDED ==> result.is_ok() &&
            -crate::specs::rowwise_fixed_bound(stage as nat+1)<=(result->Ok_0)<=crate::specs::rowwise_fixed_bound(stage as nat+1),
))]
fn inverse_lifting_value<const BOUNDED: bool>(
    samples: &[i64],
    index: usize,
    target_even: bool,
    step: InverseLiftingStep,
    stage: u8,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_index_parity(index);
        if BOUNDED {crate::specs::fixed_stage_bound_grows(stage as nat);}
    }
    if (index & 1 == 0) != target_even || samples.len() <= 1 {
        return Ok(samples[index]);
    }
    let left = if index == 0 {
        samples[1]
    } else {
        samples[index - 1]
    };
    let right = if index + 1 < samples.len() {
        samples[index + 1]
    } else {
        samples[index - 1]
    };
    if BOUNDED {
        #[cfg(verus_keep_ghost)]
        proof! {
            let l=if index==0{1int}else{index-1};
            let r=if index+1<samples.len(){index as int+1}else{index-1};
            assert((l%2==0)!=target_even && (r%2==0)!=target_even);
            assert(left==samples[l] && right==samples[r]);
        }
        if let InverseLiftingStep::Fixed(factor) = step {
            return Ok(fixed_97_bounded(samples[index], left, right, factor, stage));
        }
    }
    inverse_lifting_neighbors(samples[index], left, right, step)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires _stage<4, factor==crate::specs::part1_nine_seven_lift(_stage),
        -crate::specs::rowwise_fixed_bound(_stage as nat)<=current<=crate::specs::rowwise_fixed_bound(_stage as nat),
        -crate::specs::rowwise_fixed_bound(_stage as nat)<=left<=crate::specs::rowwise_fixed_bound(_stage as nat),
        -crate::specs::rowwise_fixed_bound(_stage as nat)<=right<=crate::specs::rowwise_fixed_bound(_stage as nat),
    ensures crate::specs::rowwise_fixed_neighbors(current,left,right,_stage)==Ok(result),
        -crate::specs::rowwise_fixed_bound(_stage as nat+1)<=result<=crate::specs::rowwise_fixed_bound(_stage as nat+1),
))]
#[inline]
fn fixed_97_bounded(current: i64, left: i64, right: i64, factor: i64, _stage: u8) -> i64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::rowwise_fixed_neighbors_bound(current,left,right,_stage);
        assert(FIXED_ONE == 65536) by(compute);
        if _stage==0 {} else if _stage==1 {} else if _stage==2 {} else { assert(_stage==3); }
        assert(0<crate::specs::rowwise_fixed_bound(_stage as nat)<=2199023255552);
        assert(-131071<=factor<=131071);
    }
    let sum = left + right;
    #[cfg(verus_keep_ghost)]
    proof! {
        let bound=crate::specs::rowwise_fixed_bound(_stage as nat);
        crate::specs::rowwise_fixed_product_bound(sum,factor,(2*bound) as i64);
        assert(crate::specs::part1_fixed_product(sum,factor).is_ok());
    }
    let product = sum * factor;
    let biased = product + FIXED_ONE / 2;
    let adjustment = crate::refinement::fixed_round_q16(biased);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::specs::part1_fixed_product(sum,factor)==Ok(adjustment));
    }
    current - adjustment
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_lifting_sample(
        seq![left, current, right], 1, false, lifting_step_view(step).0, lifting_step_view(step).1,
    ),
))]
#[inline]
pub(super) fn inverse_lifting_neighbors(
    current: i64,
    left: i64,
    right: i64,
    step: InverseLiftingStep,
) -> Result<i64, DecodeError> {
    if matches!(step, InverseLiftingStep::ReversibleUpdate)
        || matches!(step, InverseLiftingStep::ReversiblePredict)
    {
        let predict = matches!(step, InverseLiftingStep::ReversiblePredict);
        let bound = if predict {
            2_147_483_648
        } else {
            1_073_741_824
        };
        if current >= -bound
            && current <= bound
            && left >= -bound
            && left <= bound
            && right >= -bound
            && right <= bound
        {
            return Ok(inverse_reversible_bounded(current, left, right, predict));
        }
    }
    let sum = left.checked_add(right).ok_or_else(arithmetic_overflow)?;
    let adjustment = match step {
        InverseLiftingStep::Fixed(coefficient) => fixed_mul(sum, coefficient)?,
        InverseLiftingStep::ReversibleUpdate => {
            let biased_sum = sum.checked_add(2).ok_or_else(arithmetic_overflow)?;
            crate::refinement::five_three_update(biased_sum)
        }
        InverseLiftingStep::ReversiblePredict => crate::refinement::five_three_predict(sum),
    };
    if matches!(step, InverseLiftingStep::ReversiblePredict) {
        current
            .checked_add(adjustment)
            .ok_or_else(arithmetic_overflow)
    } else {
        current
            .checked_sub(adjustment)
            .ok_or_else(arithmetic_overflow)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        -(if predict{2147483648int}else{1073741824int})<=current<=if predict{2147483648int}else{1073741824int},
        -(if predict{2147483648int}else{1073741824int})<=left<=if predict{2147483648int}else{1073741824int},
        -(if predict{2147483648int}else{1073741824int})<=right<=if predict{2147483648int}else{1073741824int},
    ensures crate::specs::rowwise_neighbors(current,left,right,predict)==Ok(result),
))]
#[inline]
pub(super) fn inverse_reversible_bounded(
    current: i64,
    left: i64,
    right: i64,
    predict: bool,
) -> i64 {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::rowwise_neighbors_bounded(current,left,right,predict);}
    let sum = left + right;
    if predict {
        current + crate::refinement::five_three_predict(sum)
    } else {
        current - crate::refinement::five_three_update(sum + 2)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(samples)@) == crate::specs::part1_scaling_prefix(
        old(samples)@, low_parity, factor, old(samples).len() as nat,
    ),
))]
pub(super) fn scale_parity(
    samples: &mut [i64],
    low_parity: bool,
    factor: i64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= samples.len(),
            original == old(samples)@,
            samples.len() == original.len(),
            forall |i: int| index <= i < samples.len() ==> samples[i] == original[i],
            crate::specs::part1_scaling_prefix(original, low_parity, factor, index as nat) == (Ok(()), samples@),
            decreases samples.len() - index,
        )
    )]
    while index < samples.len() {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_index_parity(index); }
        if (index & 1 == 0) == low_parity {
            let value = match fixed_mul(samples[index], factor) {
                Ok(value) => value,
                Err(error) => {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        crate::proofs::production_impl::production_scaling_error_persists(
                            original, low_parity, factor, index as nat + 1, original.len(),
                        );
                    }
                    return Err(error);
                }
            };
            samples[index] = value;
        }
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_fixed_product(value, factor),
))]
#[inline]
pub(super) fn fixed_mul(value: i64, factor: i64) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { assert(FIXED_ONE == 65536) by(compute); }
    // Two signed 32-bit operands leave room for the Q16 rounding bias.
    if value >= i32::MIN as i64
        && value <= i32::MAX as i64
        && factor >= i32::MIN as i64
        && factor <= i32::MAX as i64
    {
        #[cfg(verus_keep_ghost)]
        proof! {
            let a = value as int;
            let b = factor as int;
            let aa = if a < 0 { -a } else { a };
            let bb = if b < 0 { -b } else { b };
            vstd::arithmetic::mul::lemma_mul_inequality(aa, 2147483648, bb);
            vstd::arithmetic::mul::lemma_mul_inequality(bb, 2147483648, 2147483648);
            assert(aa * bb <= 4611686018427387904);
            assert(aa * bb == if a * b < 0 { -(a * b) } else { a * b }) by(nonlinear_arith)
                requires aa == if a < 0 { -a } else { a }, bb == if b < 0 { -b } else { b };
            assert(-4611686018427387904 <= a * b <= 4611686018427387904);
        }
        return Ok(crate::refinement::fixed_round_q16(
            value * factor + FIXED_ONE / 2,
        ));
    }
    let product = value.checked_mul(factor).ok_or_else(arithmetic_overflow)?;
    let adjusted = product
        .checked_add(FIXED_ONE / 2)
        .ok_or_else(arithmetic_overflow)?;
    Ok(crate::refinement::fixed_round_q16(adjusted))
}
