use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::{FIXED_ONE, InverseLiftingStep};
#[cfg(verus_keep_ghost)]
use super::{lifting_step_view, sequence_outcome};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures sequence_outcome(result) == crate::specs::part1_inverse_five_three(low@, high@, low_pass_first),
))]
pub fn inverse_5_3(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    let mut output = interleave(low, high, low_pass_first)?;
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
    ensures sequence_outcome(result) == crate::specs::part1_inverse_nine_seven(low@, high@, low_pass_first),
))]
pub fn inverse_9_7(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
    let mut output = interleave(low, high, low_pass_first)?;
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
    inverse_nine_seven_lifts(&mut output, low_pass_first)?;
    Ok(output)
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
    ensures sequence_outcome(result) == crate::specs::part1_interleaved(low@, high@, low_pass_first),
))]
pub(super) fn interleave(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
) -> Result<Vec<i64>, DecodeError> {
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
    let mut output = Vec::with_capacity(length);
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= length,
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
        samples[index]
            .checked_add(adjustment)
            .ok_or_else(arithmetic_overflow)
    } else {
        samples[index]
            .checked_sub(adjustment)
            .ok_or_else(arithmetic_overflow)
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
fn fixed_mul(value: i64, factor: i64) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { assert(FIXED_ONE == 65536) by(compute); }
    let product = value.checked_mul(factor).ok_or_else(arithmetic_overflow)?;
    let adjusted = product
        .checked_add(FIXED_ONE / 2)
        .ok_or_else(arithmetic_overflow)?;
    Ok(crate::refinement::fixed_round_q16(adjusted))
}
