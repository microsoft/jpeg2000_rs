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
    synthesize_5_3(&mut output, low_pass_first)?;
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (match result { Ok(()) => Ok(final(output)@), Err(error) => Err(error) })
        == crate::specs::part1_synthesize_five_three(old(output)@, low_pass_first),
))]
fn synthesize_5_3(output: &mut [i64], low_pass_first: bool) -> Result<(), DecodeError> {
    if output.len() == 1 && !low_pass_first {
        output[0] >>= 1;
        return Ok(());
    }
    inverse_lift(output, low_pass_first, InverseLiftingStep::ReversibleUpdate)?;
    inverse_lift(
        output,
        !low_pass_first,
        InverseLiftingStep::ReversiblePredict,
    )
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
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_wavelet_sequence_normal(low@,high@,low_pass_first,true,None);}
    let interleaved = interleave(low, high, low_pass_first);
    #[cfg(verus_keep_ghost)]
    proof! {if let Err(error)=interleaved{crate::specs::part2_wavelet_sequence_interleave_error(low@,high@,low_pass_first,true,None,error);}}
    let mut output = interleaved?;
    synthesize_9_7(&mut output, low_pass_first)?;
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (match result { Ok(()) => Ok(final(output)@), Err(error) => Err(error) })
        == crate::specs::part1_synthesize_nine_seven(old(output)@, low_pass_first),
))]
fn synthesize_9_7(output: &mut [i64], low_pass_first: bool) -> Result<(), DecodeError> {
    if output.len() == 1 && !low_pass_first {
        output[0] >>= 1;
        return Ok(());
    }
    if output.len() <= 1 {
        return Ok(());
    }
    scale_parity(
        output,
        low_pass_first,
        crate::refinement::nine_seven_scale(true),
    )?;
    scale_parity(
        output,
        !low_pass_first,
        crate::refinement::nine_seven_scale(false),
    )?;
    inverse_nine_seven_lifts(output, low_pass_first)
}

// Later standard rows overwrite the first row's initialized storage.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(scratch)@.len() == low@.len() + high@.len(),
    ensures (match result { Ok(()) => Ok(final(scratch)@), Err(error) => Err(error) })
        == crate::specs::part1_inverse_sequence(low@, high@, low_pass_first, irreversible),
))]
pub(super) fn reuse_standard_row(
    scratch: &mut [i64],
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
    irreversible: bool,
) -> Result<(), DecodeError> {
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    let length = interleave_length(low, high, low_pass_first)?;
    if scratch.len() != length {
        return Err(invalid_transform());
    }
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= length,
        scratch@.len() == length,
        length == low@.len() + high@.len(),
        crate::specs::part2_wavelet_interleave_admit(low@.len(), high@.len(), low_pass_first) == Ok(()),
        forall |i:int| 0 <= i < index ==>
            scratch[i] == if (i % 2 == 0) == low_pass_first { low[i / 2] } else { high[i / 2] },
        decreases length - index,
    ))]
    while index < length {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        scratch[index] = interleaved_sample(low, high, low_pass_first, index)?;
        index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(scratch@ =~= Seq::new(length as nat, |i: int|
            if (i % 2 == 0) == low_pass_first { low@[i / 2] } else { high@[i / 2] }));
        assert(crate::specs::part1_interleaved(low@, high@, low_pass_first) == Ok(scratch@));
    }
    if irreversible {
        synthesize_9_7(scratch, low_pass_first)
    } else {
        synthesize_5_3(scratch, low_pass_first)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(samples)@) == crate::specs::part1_nine_seven_lifting_prefix(old(samples)@, low_first, 4),
))]
pub(super) fn inverse_nine_seven_lifts(
    samples: &mut [i64],
    low_first: bool,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let mut stage = 0_u8;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stage <= 4,
        original == old(samples)@,
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
        match inverse_lift(samples, target_even, InverseLiftingStep::Fixed(factor)) {
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
    let length = interleave_length(low, high, low_pass_first)?;
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
        output.push(interleaved_sample(low, high, low_pass_first, index)?);
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
    ensures (match result { Ok(_) => Ok(()), Err(error) => Err(error) })
            == crate::specs::part2_wavelet_interleave_admit(low@.len(), high@.len(), low_pass_first),
        result matches Ok(length) ==> length as int == low@.len() + high@.len(),
))]
fn interleave_length(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<usize, DecodeError> {
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
    Ok(length)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < low@.len() + high@.len(),
        crate::specs::part2_wavelet_interleave_admit(low@.len(), high@.len(), low_pass_first) == Ok(()),
    ensures result == Ok(if (index as int % 2 == 0) == low_pass_first { low@[index as int / 2] } else { high@[index as int / 2] }),
))]
fn interleaved_sample(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
    index: usize,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_index_parity(index); }
    let low_position = (index & 1 == 0) == low_pass_first;
    let source_index = index / 2;
    let value = if low_position {
        *low.get(source_index).ok_or_else(invalid_transform)?
    } else {
        *high.get(source_index).ok_or_else(invalid_transform)?
    };
    Ok(value)
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
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= samples.len(),
            original == old(samples)@,
            samples.len() == original.len(),
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
        }
        let value = match inverse_lifting_value(samples, index, target_even, step) {
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
    ensures result == crate::specs::part1_lifting_sample(
        samples@, index as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
    ),
))]
fn inverse_lifting_value(
    samples: &[i64],
    index: usize,
    target_even: bool,
    step: InverseLiftingStep,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { crate::proofs::production_impl::production_index_parity(index); }
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
    inverse_lifting_neighbors(samples[index], left, right, step)
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
