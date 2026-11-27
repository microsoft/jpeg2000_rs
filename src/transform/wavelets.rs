use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::{FIXED_ONE, InverseLiftingStep};
#[cfg(verus_keep_ghost)]
use super::{lifting_step_view, sequence_outcome};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

const HORIZONTAL_BOUND: i64 = 1_073_741_824;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == forall |i: int| 0 <= i < samples.len() ==> -HORIZONTAL_BOUND <= #[trigger] samples@[i] <= HORIZONTAL_BOUND,
))]
#[inline]
fn row_within_bound(samples: &[i64]) -> bool {
    let mut i = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= samples.len(),
            forall |k: int| 0 <= k < i ==> -HORIZONTAL_BOUND <= #[trigger] samples@[k] <= HORIZONTAL_BOUND,
        decreases samples.len() - i,
    ))]
    while i < samples.len() {
        let v = samples[i];
        #[allow(
            clippy::manual_range_contains,
            reason = "Direct comparisons keep Verus loop invariants simple."
        )]
        if v < -HORIZONTAL_BOUND || v > HORIZONTAL_BOUND {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(samples).len() > 1,
        forall |i: int| 0 <= i < old(samples).len() ==>
            -(if predict { 2147483648int } else { 1073741824int }) <= #[trigger] old(samples)@[i]
                <= if predict { 2147483648int } else { 1073741824int },
    ensures
        crate::specs::part1_lifting_prefix(
            old(samples)@, target_even,
            if predict { 2u8 } else { 1u8 }, 0, old(samples).len() as nat,
        ) == (Ok::<(), DecodeError>(()), final(samples)@),
        forall |i: int| 0 <= i < final(samples).len() ==>
            -(if predict { 4294967296int } else { 2147483648int }) <= #[trigger] final(samples)@[i]
                <= if predict { 4294967296int } else { 2147483648int },
))]
#[inline]
fn inverse_lift_reversible_bounded(samples: &mut [i64], target_even: bool, predict: bool) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = samples@;
        let ghost kind: u8 = if predict { 2u8 } else { 1u8 };
    }
    let len = samples.len();
    let mut index = if target_even { 0_usize } else { 1_usize };
    #[cfg(verus_keep_ghost)]
    proof! {
        if !target_even {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            assert(samples@ =~= original.update(0, original[0]));
            assert(crate::specs::part1_lifting_prefix(original, target_even, kind, 0, 1) == (Ok(()), samples@));
        }
    }
    if index == 0 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, 0, target_even, kind, 0);
            crate::specs::rowwise_neighbors_bounded(samples[0], samples[1], samples[1], predict);
        }
        samples[0] = inverse_reversible_bounded(samples[0], samples[1], samples[1], predict);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            assert(crate::specs::part1_lifting_prefix(original, target_even, kind, 0, 1) == (Ok(()), samples@));
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, 1, target_even, kind, 0);
            assert(samples@ =~= samples@.update(1, original[1]));
            assert(crate::specs::part1_lifting_prefix(original, target_even, kind, 0, 2) == (Ok(()), samples@));
        }
        index = 2;
    }
    let last = len - 1;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= index <= len + 1,
            len == samples.len(), len > 1, last == len - 1,
            original == old(samples)@, samples.len() == original.len(),
            kind == if predict { 2u8 } else { 1u8 },
            (index % 2 == 0) == target_even,
            forall |i: int| 0 <= i < original.len() ==>
                -(if predict { 2147483648int } else { 1073741824int }) <= #[trigger] original[i]
                    <= if predict { 2147483648int } else { 1073741824int },
            forall |i: int| 0 <= i < samples.len() && (i >= index || (i % 2 == 0) != target_even) ==>
                samples[i] == original[i],
            forall |i: int| 0 <= i < samples.len() ==>
                -(if predict { 4294967296int } else { 2147483648int }) <= #[trigger] samples[i]
                    <= if predict { 4294967296int } else { 2147483648int },
            crate::specs::part1_lifting_prefix(
                original, target_even, kind, 0,
                if index <= len { index as nat } else { len as nat },
            ) == (Ok(()), samples@),
        decreases len + 1 - index,
    ))]
    while index < last {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, index as nat, target_even, kind, 0);
            crate::specs::rowwise_neighbors_bounded(samples[index as int], samples[index as int - 1], samples[index as int + 1], predict);
        }
        let left = samples[index - 1];
        let right = samples[index + 1];
        let cur = samples[index];
        samples[index] = inverse_reversible_bounded(cur, left, right, predict);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_lifting_prefix(original, target_even, kind, 0, index as nat + 1) == (Ok(()), samples@));
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, (index + 1) as nat, target_even, kind, 0);
            assert(crate::specs::part1_lifting_prefix(original, target_even, kind, 0, index as nat + 2) == (Ok(()), samples@));
        }
        index += 2;
    }
    if index == last {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, last as nat, target_even, kind, 0);
            crate::specs::rowwise_neighbors_bounded(samples[last as int], samples[last as int - 1], samples[last as int - 1], predict);
        }
        samples[last] = inverse_reversible_bounded(
            samples[last],
            samples[last - 1],
            samples[last - 1],
            predict,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_lifting_prefix(original, target_even, kind, 0, len as nat) == (Ok(()), samples@));
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 0 < bound <= 4_398_046_511_104i64,
        -bound <= value <= bound,
        -131_071 <= factor <= 131_071,
    ensures crate::specs::part1_fixed_product(value, factor) == Ok(result),
        -2 * bound <= result <= 2 * bound,
))]
#[inline(always)]
fn fixed_mul_row_bounded(
    value: i64,
    factor: i64,
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] bound: i64,
) -> i64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(FIXED_ONE == 65536) by(compute);
        crate::specs::rowwise_fixed_product_bound(value, factor, bound);
        assert(-(bound as int) * 131071 <= (value as int) * (factor as int) <= (bound as int) * 131071)
            by(nonlinear_arith)
            requires 0 < bound, -bound <= value <= bound, -131071 <= factor <= 131071;
        assert(i64::MIN <= (value as int) * (factor as int) <= i64::MAX
            && i64::MIN <= (value as int) * (factor as int) + 32768 <= i64::MAX)
            by(nonlinear_arith)
            requires 0 < bound <= 4_398_046_511_104i64,
                -(bound as int) * 131071 <= (value as int) * (factor as int) <= (bound as int) * 131071;
    }
    crate::refinement::fixed_round_q16(value * factor + FIXED_ONE / 2)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires -131_071 <= factor <= 131_071,
        0 < bound <= 4_398_046_511_104i64,
        forall |i: int| 0 <= i < old(samples).len() ==> -bound <= #[trigger] old(samples)@[i] <= bound,
    ensures
        crate::specs::part1_scaling_prefix(old(samples)@, low_parity, factor, old(samples).len() as nat)
            == (Ok::<(), DecodeError>(()), final(samples)@),
        forall |i: int| 0 <= i < final(samples).len() ==>
            -(if (i % 2 == 0) == low_parity { 2 * bound } else { bound }) <= #[trigger] final(samples)@[i]
                <= if (i % 2 == 0) == low_parity { 2 * bound } else { bound },
))]
#[inline]
fn scale_parity_bounded(samples: &mut [i64], low_parity: bool, factor: i64, bound: i64) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let len = samples.len();
    let mut index = if low_parity { 0_usize } else { 1_usize };
    #[cfg(verus_keep_ghost)]
    proof! {
        if !low_parity && len > 0 {
            reveal_with_fuel(crate::specs::part1_scaling_prefix, 2);
            assert(crate::specs::part1_scaling_prefix(original, low_parity, factor, 1) == (Ok(()), samples@));
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= len + 1,
            len == samples.len(), original == old(samples)@, samples.len() == original.len(),
            -131_071 <= factor <= 131_071, 0 < bound <= 4_398_046_511_104i64,
            (index % 2 == 0) == low_parity,
            forall |i: int| 0 <= i < original.len() ==> -bound <= #[trigger] original[i] <= bound,
            forall |i: int| index <= i < samples.len() ==> samples[i] == original[i],
            forall |i: int| 0 <= i < samples.len() ==>
                -(if i < index && (i % 2 == 0) == low_parity { 2 * bound } else { bound }) <= #[trigger] samples[i]
                    <= if i < index && (i % 2 == 0) == low_parity { 2 * bound } else { bound },
            crate::specs::part1_scaling_prefix(
                original, low_parity, factor,
                if index <= len { index as nat } else { len as nat },
            ) == (Ok(()), samples@),
        decreases len + 1 - index,
    ))]
    while index < len {
        samples[index] = fixed_mul_row_bounded(samples[index], factor, bound);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_scaling_prefix(original, low_parity, factor, index as nat + 1) == (Ok(()), samples@));
            if index + 1 < len {
                assert(((index + 1) % 2 == 0) != low_parity);
                assert(crate::specs::part1_scaling_prefix(original, low_parity, factor, index as nat + 2) == (Ok(()), samples@));
            }
        }
        index += 2;
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(samples).len() > 1, stage < 4,
        forall |i: int| 0 <= i < old(samples).len() ==>
            -crate::specs::rowwise_fixed_bound(stage as nat) <= #[trigger] old(samples)@[i]
                <= crate::specs::rowwise_fixed_bound(stage as nat),
    ensures
        crate::specs::part1_lifting_prefix(
            old(samples)@, target_even, 0u8, crate::specs::part1_nine_seven_lift(stage), old(samples).len() as nat,
        ) == (Ok::<(), DecodeError>(()), final(samples)@),
        forall |i: int| 0 <= i < final(samples).len() ==>
            -crate::specs::rowwise_fixed_bound(stage as nat + 1) <= #[trigger] final(samples)@[i]
                <= crate::specs::rowwise_fixed_bound(stage as nat + 1),
))]
#[inline]
fn inverse_lift_fixed_bounded(samples: &mut [i64], target_even: bool, stage: u8) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = samples@;
        let ghost bound = crate::specs::rowwise_fixed_bound(stage as nat);
    }
    let factor = crate::refinement::nine_seven_lift(stage);
    let len = samples.len();
    let mut index = if target_even { 0_usize } else { 1_usize };
    #[cfg(verus_keep_ghost)]
    proof! {
        if !target_even {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            assert(samples@ =~= original.update(0, original[0]));
            assert(crate::specs::part1_lifting_prefix(original, target_even, 0u8, factor, 1) == (Ok(()), samples@));
        }
    }
    if index == 0 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, 0, target_even, 0u8, factor);
            crate::specs::rowwise_fixed_neighbors_bound(samples[0], samples[1], samples[1], stage);
        }
        let sum = samples[1] + samples[1];
        samples[0] -= fixed_mul_row_bounded(sum, factor, 2_199_023_255_552);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            assert(crate::specs::part1_lifting_prefix(original, target_even, 0u8, factor, 1) == (Ok(()), samples@));
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, 1, target_even, 0u8, factor);
            assert(samples@ =~= samples@.update(1, original[1]));
            assert(crate::specs::part1_lifting_prefix(original, target_even, 0u8, factor, 2) == (Ok(()), samples@));
        }
        index = 2;
    }
    let last = len - 1;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= index <= len + 1,
            len == samples.len(), len > 1, last == len - 1, stage < 4,
            factor == crate::specs::part1_nine_seven_lift(stage),
            original == old(samples)@, samples.len() == original.len(),
            bound == crate::specs::rowwise_fixed_bound(stage as nat),
            (index % 2 == 0) == target_even,
            forall |i: int| 0 <= i < original.len() ==> -bound <= #[trigger] original[i] <= bound,
            forall |i: int| 0 <= i < samples.len() && (i >= index || (i % 2 == 0) != target_even) ==>
                samples[i] == original[i],
            forall |i: int| 0 <= i < samples.len() ==>
                -crate::specs::rowwise_fixed_bound(stage as nat + 1) <= #[trigger] samples[i]
                    <= crate::specs::rowwise_fixed_bound(stage as nat + 1),
            crate::specs::part1_lifting_prefix(
                original, target_even, 0u8, factor,
                if index <= len { index as nat } else { len as nat },
            ) == (Ok(()), samples@),
        decreases len + 1 - index,
    ))]
    while index < last {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, index as nat, target_even, 0u8, factor);
            crate::specs::rowwise_fixed_neighbors_bound(samples[index as int], samples[index as int - 1], samples[index as int + 1], stage);
        }
        let sum = samples[index - 1] + samples[index + 1];
        samples[index] -= fixed_mul_row_bounded(sum, factor, 2_199_023_255_552);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_lifting_prefix(original, target_even, 0u8, factor, index as nat + 1) == (Ok(()), samples@));
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, (index + 1) as nat, target_even, 0u8, factor);
            assert(crate::specs::part1_lifting_prefix(original, target_even, 0u8, factor, index as nat + 2) == (Ok(()), samples@));
        }
        index += 2;
    }
    if index == last {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(original, samples@, last as nat, target_even, 0u8, factor);
            crate::specs::rowwise_fixed_neighbors_bound(samples[last as int], samples[last as int - 1], samples[last as int - 1], stage);
        }
        let sum = samples[last - 1] + samples[last - 1];
        samples[last] -= fixed_mul_row_bounded(sum, factor, 2_199_023_255_552);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_lifting_prefix(original, target_even, 0u8, factor, len as nat) == (Ok(()), samples@));
        }
    }
}

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
    if output.len() > 1 && row_within_bound(&output) {
        inverse_lift_reversible_bounded(&mut output, low_pass_first, false);
        inverse_lift_reversible_bounded(&mut output, !low_pass_first, true);
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
    if row_within_bound(&output) {
        scale_parity_bounded(
            &mut output,
            low_pass_first,
            crate::refinement::nine_seven_scale(true),
            HORIZONTAL_BOUND,
        );
        scale_parity_bounded(
            &mut output,
            !low_pass_first,
            crate::refinement::nine_seven_scale(false),
            HORIZONTAL_BOUND * 2,
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: int| 0 <= i < output.len() implies
                -crate::specs::rowwise_fixed_bound(0) <= #[trigger] output[i] <= crate::specs::rowwise_fixed_bound(0) by {};
        }
        inverse_lift_fixed_bounded(&mut output, low_pass_first, 0);
        inverse_lift_fixed_bounded(&mut output, !low_pass_first, 1);
        inverse_lift_fixed_bounded(&mut output, low_pass_first, 2);
        inverse_lift_fixed_bounded(&mut output, !low_pass_first, 3);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_nine_seven_lifting_prefix, 5);
        }
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
    if low_pass_first {
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= length,
                index == length || index % 2 == 0,
                crate::specs::part2_wavelet_interleave_result(low@,high@,low_pass_first,crate::specs::part1_interleaved(low@,high@,low_pass_first)),
                length == low.len() + high.len(),
                low_pass_first,
                low.len() == length as int / 2 + length as int % 2,
                high.len() == length - low.len(),
                output.len() == index,
                forall |i: int| 0 <= i < index ==>
                    output[i] == if i % 2 == 0 { low[i / 2] } else { high[i / 2] },
                decreases length - index,
            )
        )]
        while index < length {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(index)?;
            let pair = index / 2;
            if length - index >= 64 {
                let mut chunk = [0_i64; 64];
                let mut k = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant k <= 32, pair == index / 2, index % 2 == 0, index + 64 <= length,
                        pair + 32 <= low.len(), pair + 32 <= high.len(),
                        forall |j: int| 0 <= j < 2 * k ==>
                            chunk@[j] == if j % 2 == 0 { low@[pair as int + j / 2] } else { high@[pair as int + j / 2] },
                    decreases 32 - k,
                ))]
                while k < 32 {
                    chunk[2 * k] = low[pair + k];
                    chunk[2 * k + 1] = high[pair + k];
                    k += 1;
                }
                output.extend_from_slice(&chunk);
                index += 64;
            } else {
                output.push(low[pair]);
                if index + 1 < length {
                    output.push(high[pair]);
                    index += 2;
                } else {
                    index += 1;
                }
            }
        }
    } else {
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= length,
                index == length || index % 2 == 0,
                crate::specs::part2_wavelet_interleave_result(low@,high@,low_pass_first,crate::specs::part1_interleaved(low@,high@,low_pass_first)),
                length == low.len() + high.len(),
                !low_pass_first,
                low.len() == length as int / 2,
                high.len() == length - low.len(),
                output.len() == index,
                forall |i: int| 0 <= i < index ==>
                    output[i] == if i % 2 != 0 { low[i / 2] } else { high[i / 2] },
                decreases length - index,
            )
        )]
        while index < length {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(index)?;
            let pair = index / 2;
            if length - index >= 64 {
                let mut chunk = [0_i64; 64];
                let mut k = 0_usize;
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant k <= 32, pair == index / 2, index % 2 == 0, index + 64 <= length,
                        pair + 32 <= low.len(), pair + 32 <= high.len(),
                        forall |j: int| 0 <= j < 2 * k ==>
                            chunk@[j] == if j % 2 != 0 { low@[pair as int + j / 2] } else { high@[pair as int + j / 2] },
                    decreases 32 - k,
                ))]
                while k < 32 {
                    chunk[2 * k] = high[pair + k];
                    chunk[2 * k + 1] = low[pair + k];
                    k += 1;
                }
                output.extend_from_slice(&chunk);
                index += 64;
            } else {
                output.push(high[pair]);
                if index + 1 < length {
                    output.push(low[pair]);
                    index += 2;
                } else {
                    index += 1;
                }
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(output.len() == length);
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
#[inline(always)]
pub(super) fn inverse_lift(
    samples: &mut [i64],
    target_even: bool,
    step: InverseLiftingStep,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let len = samples.len();
    if len <= 1 {
        #[cfg(verus_keep_ghost)]
        proof! {
            if len == 0 {
                assert(crate::specs::part1_lifting_prefix(
                    original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, 0,
                ) == (Ok(()), samples@));
            } else {
                assert(len == 1);
                reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
                assert(samples@ =~= original.update(0, original[0]));
                assert(crate::specs::part1_lifting_prefix(
                    original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, 1,
                ) == (Ok(()), samples@));
            }
        }
        return Ok(());
    }
    let mut index = if target_even { 0_usize } else { 1_usize };
    #[cfg(verus_keep_ghost)]
    proof! {
        if !target_even {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            assert(samples@ =~= original.update(0, original[0]));
            assert(crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, 1,
            ) == (Ok(()), samples@));
        }
    }
    if index == 0 {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(
                original, samples@, 0, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
            );
        }
        let value = match inverse_lifting_value(samples, 0, target_even, step) {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
                    assert(crate::specs::part1_lifting_prefix(
                        original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, 1,
                    ) == (Err(error), samples@));
                    crate::proofs::production_impl::production_lifting_error_persists(
                        original, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
                        1, original.len(),
                    );
                }
                return Err(error);
            }
        };
        samples[0] = value;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_lifting_prefix, 2);
            assert(crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, 1,
            ) == (Ok(()), samples@));
            crate::proofs::production_impl::production_lifting_sample_frame(
                original, samples@, 1, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
            );
            assert(samples@ =~= samples@.update(1, original[1]));
            assert(crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, 2,
            ) == (Ok(()), samples@));
        }
        index = 2;
    }
    let last = len - 1;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant 1 <= index <= len + 1,
            len == samples.len(),
            len > 1,
            last == len - 1,
            original == old(samples)@,
            samples.len() == original.len(),
            (index % 2 == 0) == target_even,
            forall |i: int| 0 <= i < samples.len() && (i >= index || (i % 2 == 0) != target_even) ==>
                samples[i] == original[i],
            crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
                if index <= len { index as nat } else { len as nat },
            ) == (Ok(()), samples@),
            decreases len + 1 - index,
        )
    )]
    while index < last {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(
                original, samples@, index as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
            );
        }
        let window = &samples[index - 1..index + 2];
        let value = match inverse_lifting_neighbors(window[1], window[0], window[2], step) {
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
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, index as nat + 1,
            ) == (Ok(()), samples@));
            assert(((index + 1) % 2 == 0) != target_even);
            crate::proofs::production_impl::production_lifting_sample_frame(
                original, samples@, (index + 1) as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
            );
            assert(crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, index as nat + 2,
            ) == (Ok(()), samples@));
        }
        index += 2;
    }
    if index == last {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_lifting_sample_frame(
                original, samples@, last as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
            );
        }
        let value = match inverse_lifting_value(samples, last, target_even, step) {
            Ok(value) => value,
            Err(error) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(crate::specs::part1_lifting_prefix(
                        original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, len as nat,
                    ) == (Err(error), samples@));
                }
                return Err(error);
            }
        };
        samples[last] = value;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_lifting_prefix(
                original, target_even, lifting_step_view(step).0, lifting_step_view(step).1, len as nat,
            ) == (Ok(()), samples@));
        }
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < samples.len(),
    ensures result == crate::specs::part1_lifting_sample(
        samples@, index as nat, target_even, lifting_step_view(step).0, lifting_step_view(step).1,
    ),
))]
#[inline(always)]
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
#[inline(always)]
pub(super) fn inverse_lifting_neighbors(
    current: i64,
    left: i64,
    right: i64,
    step: InverseLiftingStep,
) -> Result<i64, DecodeError> {
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
#[inline(always)]
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
#[inline(always)]
pub(super) fn scale_parity(
    samples: &mut [i64],
    low_parity: bool,
    factor: i64,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = samples@; }
    let len = samples.len();
    let mut index = if low_parity { 0_usize } else { 1_usize };
    #[cfg(verus_keep_ghost)]
    proof! {
        if !low_parity && len > 0 {
            reveal_with_fuel(crate::specs::part1_scaling_prefix, 2);
            assert(crate::specs::part1_scaling_prefix(original, low_parity, factor, 1) == (Ok(()), samples@));
        }
    }
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= len + 1,
            len == samples.len(),
            original == old(samples)@,
            samples.len() == original.len(),
            (index % 2 == 0) == low_parity,
            forall |i: int| index <= i < samples.len() ==> samples[i] == original[i],
            crate::specs::part1_scaling_prefix(
                original, low_parity, factor,
                if index <= len { index as nat } else { len as nat },
            ) == (Ok(()), samples@),
            decreases len + 1 - index,
        )
    )]
    while index < len {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
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
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::part1_scaling_prefix(original, low_parity, factor, index as nat + 1) == (Ok(()), samples@));
            if index + 1 < len {
                assert(((index + 1) % 2 == 0) != low_parity);
                assert(crate::specs::part1_scaling_prefix(original, low_parity, factor, index as nat + 2) == (Ok(()), samples@));
            }
        }
        if index + 1 < len {
            index += 2;
        } else {
            return Ok(());
        }
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_fixed_product(value, factor),
))]
#[inline(always)]
pub(super) fn fixed_mul(value: i64, factor: i64) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { assert(FIXED_ONE == 65536) by(compute); }
    let product = value.checked_mul(factor).ok_or_else(arithmetic_overflow)?;
    let adjusted = product
        .checked_add(FIXED_ONE / 2)
        .ok_or_else(arithmetic_overflow)?;
    Ok(crate::refinement::fixed_round_q16(adjusted))
}
