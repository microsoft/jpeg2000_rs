use super::arithmetic::{arithmetic_overflow, invalid_transform};
use super::coefficients::{
    coefficient_fixed, coefficient_integer, fixed_div_q32, fixed_mul_q32, round_shift_i128,
};
#[cfg(verus_keep_ghost)]
use super::sequence_outcome;
use super::wavelets::interleave;
use crate::DecodeError;
use crate::codestream::{ArbitraryKernel, KernelLiftingStep};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures sequence_outcome(result)
        == crate::specs::part2_inverse_arbitrary(low@, high@, low_pass_first, crate::codestream::raw_kernel_view(*kernel)),
))]
pub fn inverse_arbitrary(
    low: &[i64],
    high: &[i64],
    low_pass_first: bool,
    kernel: &ArbitraryKernel,
) -> Result<Vec<i64>, DecodeError> {
    let mut output = interleave(low, high, low_pass_first)?;
    if output.len() == 1 {
        if !low_pass_first {
            output[0] = output[0].checked_div(2).ok_or_else(arithmetic_overflow)?;
        }
        return Ok(output);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial = output@; }
    if !kernel.reversible() {
        let scaling = coefficient_fixed(
            kernel.scaling().ok_or_else(invalid_transform)?,
            kernel.coefficient_type(),
        )?;
        if scaling == 0 {
            return Err(invalid_transform());
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_atk_scale_empty(initial, scaling, low_pass_first);
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= output.len(),
                initial.len() == output.len(),
                initial.len() != 1,
                crate::specs::part1_interleaved(low@, high@, low_pass_first) == Ok(initial),
                !crate::codestream::raw_kernel_view(*kernel).0,
                crate::codestream::raw_kernel_view(*kernel).5.is_some(),
                crate::specs::part2_atk_fixed_coefficient(crate::codestream::raw_kernel_view(*kernel).5.unwrap(),
                    crate::codestream::raw_kernel_view(*kernel).1) == Ok(scaling),
                scaling != 0,
                crate::specs::part2_atk_scale_prefix(initial, scaling, low_pass_first, index as nat) == Ok(output@),
                decreases output.len() - index,
            )
        )]
        while index < output.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_atk_scale_step(initial, scaling, low_pass_first, index as nat);
                crate::proofs::production_impl::production_atk_scale_error_guard(initial, scaling, low_pass_first, index as nat + 1, initial.len());
            }
            let even = (index & 1 == 0) == low_pass_first;
            output[index] = if even {
                fixed_mul_q32(output[index], scaling)?
            } else {
                fixed_div_q32(output[index], scaling)?
            };
            index = index.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
    }
    apply_arbitrary_steps(&mut output, low_pass_first, kernel)?;
    Ok(output)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@)
        == crate::specs::part2_atk_steps(old(output)@, crate::codestream::raw_kernel_view(*kernel), low_pass_first, crate::codestream::raw_kernel_view(*kernel).6.len()),
))]
pub(super) fn apply_arbitrary_steps(
    output: &mut [i64],
    low_pass_first: bool,
    kernel: &ArbitraryKernel,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = output@; }
    let mut update_odd = kernel.initial_odd();
    let mut step_index = kernel.steps().len();
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost total_steps = step_index as nat; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_atk_steps_empty(original, crate::codestream::raw_kernel_view(*kernel), low_pass_first);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant step_index <= total_steps,
        total_steps == crate::codestream::raw_kernel_view(*kernel).6.len(),
        original == old(output)@,
        update_odd == if (total_steps - step_index) % 2 == 0 { crate::codestream::raw_kernel_view(*kernel).3 } else { !crate::codestream::raw_kernel_view(*kernel).3 },
        crate::specs::part2_atk_steps(original, crate::codestream::raw_kernel_view(*kernel), low_pass_first, (total_steps - step_index) as nat) == (Ok(()), output@),
        decreases step_index,
    ))]
    while step_index > 0 {
        step_index = crate::refinement::atk_reconstruction_step(step_index);
        let step = kernel
            .steps()
            .get(step_index)
            .ok_or_else(invalid_transform)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_atk_steps_step(original, crate::codestream::raw_kernel_view(*kernel), low_pass_first, (total_steps - step_index - 1) as nat);
            crate::proofs::production_impl::production_atk_steps_error_guard(original, crate::codestream::raw_kernel_view(*kernel), low_pass_first, (total_steps - step_index) as nat, total_steps);
        }
        let operation = apply_arbitrary_step(output, low_pass_first, update_odd, step, kernel);
        match operation {
            Ok(()) => {
                #[cfg(verus_keep_ghost)]
                proof! { assert(operation.is_ok()); assert(operation->Ok_0 == ()); assert(operation == Ok(())); }
            }
            Err(error) => return Err(error),
        }
        update_odd = crate::refinement::atk_next_parity(update_odd);
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, final(output)@) == crate::specs::part2_atk_step(
        old(output)@, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, update_odd,
    ),
))]
fn apply_arbitrary_step(
    output: &mut [i64],
    low_pass_first: bool,
    update_odd: bool,
    step: &KernelLiftingStep,
    kernel: &ArbitraryKernel,
) -> Result<(), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = output@; }
    let target_local_odd = if low_pass_first {
        update_odd
    } else {
        !update_odd
    };
    let mut target = if target_local_odd { 1usize } else { 0usize };
    let remaining = output
        .len()
        .checked_sub(target)
        .ok_or_else(arithmetic_overflow)?;
    let inclusive = remaining.checked_add(1).ok_or_else(arithmetic_overflow)?;
    let mut target_passes = inclusive.checked_div(2).ok_or_else(arithmetic_overflow)?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost total_passes = target_passes as nat; let ghost start = target; }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_atk_targets_empty(original, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, start);
    }
    #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant target_passes <= total_passes,
                original == old(output)@,
                output.len() == original.len(),
                start == if target_local_odd { 1usize } else { 0usize },
                target_local_odd == if low_pass_first { update_odd } else { !update_odd },
                total_passes == ((original.len() - start + 1) / 2) as nat,
                original.len() >= start, original.len() - start + 1 <= usize::MAX,
                target as nat == start as nat + 2 * (total_passes - target_passes),
                crate::specs::part2_atk_target_prefix(
                    original, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, start, (total_passes - target_passes) as nat,
                ) == (Ok(()), output@),
                decreases target_passes,
            )
        )]
    while target < output.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_atk_targets_step(original, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, start, (total_passes - target_passes) as nat);
            crate::proofs::production_impl::production_atk_targets_error_guard(original, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, start, (total_passes - target_passes + 1) as nat, total_passes);
        }
        if kernel.reversible() {
            output[target] =
                arbitrary_reversible_target(output, target, step, kernel, low_pass_first)?;
        } else {
            output[target] =
                arbitrary_irreversible_target(output, target, step, kernel, low_pass_first)?;
        }
        target = target.checked_add(2).ok_or_else(arithmetic_overflow)?;
        target_passes = target_passes
            .checked_sub(1)
            .ok_or_else(arithmetic_overflow)?;
    }
    Ok(())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires target < output.len(),
    ensures result == crate::specs::part2_atk_irreversible_target(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first),
))]
fn arbitrary_irreversible_target(
    output: &[i64],
    target: usize,
    step: &KernelLiftingStep,
    kernel: &ArbitraryKernel,
    low_pass_first: bool,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_atk_irreversible_sum_empty(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first);
    }
    let mut adjustment = 0_i128;
    let coefficient_count = step.coefficients().len();
    let mut coefficient = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant coefficient <= coefficient_count,
        target < output.len(),
        coefficient_count == crate::codestream::raw_kernel_step_view(*step).3.len(),
        crate::specs::part2_atk_irreversible_sum(output@, target, crate::codestream::raw_kernel_step_view(*step),
            crate::codestream::raw_kernel_view(*kernel), low_pass_first, coefficient as nat) == Ok(adjustment),
        decreases coefficient_count - coefficient,
    ))]
    while coefficient < coefficient_count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_atk_irreversible_sum_step(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, coefficient as nat);
            crate::proofs::production_impl::production_atk_irreversible_sum_error_guard(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, coefficient as nat + 1, coefficient_count as nat);
        }
        let alpha = coefficient_fixed(
            *step
                .coefficients()
                .get(coefficient)
                .ok_or_else(invalid_transform)?,
            kernel.coefficient_type(),
        )?;
        let contribution = lifting_source_sum(
            output,
            target,
            coefficient,
            step.offset(),
            kernel.whole_sample_filter(),
            kernel.whole_sample_extension(),
            low_pass_first,
        )?;
        adjustment = adjustment
            .checked_add(
                i128::from(alpha)
                    .checked_mul(i128::from(contribution))
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(arithmetic_overflow)?;
        coefficient = coefficient.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let rounded = round_shift_i128(adjustment, 32)?;
    let converted = match i64::try_from(rounded) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    output[target]
        .checked_sub(converted)
        .ok_or_else(arithmetic_overflow)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires target < output.len(),
    ensures result == crate::specs::part2_atk_reversible_target(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first),
))]
fn arbitrary_reversible_target(
    output: &[i64],
    target: usize,
    step: &KernelLiftingStep,
    kernel: &ArbitraryKernel,
    low_pass_first: bool,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::proofs::production_impl::production_atk_sum_empty(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first);
        crate::proofs::production_impl::production_atk_sum_error_guard(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, 0, crate::codestream::raw_kernel_step_view(*step).3.len());
    }
    let mut sum = coefficient_integer(
        step.residue().ok_or_else(invalid_transform)?,
        kernel.coefficient_type(),
    )?;
    let count = step.coefficients().len();
    let mut coefficient = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant coefficient <= count, target < output.len(),
        count == crate::codestream::raw_kernel_step_view(*step).3.len(),
        crate::specs::part2_atk_sum(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel).1,
            crate::codestream::raw_kernel_view(*kernel).2, crate::codestream::raw_kernel_view(*kernel).4, low_pass_first, coefficient as nat) == Ok(sum),
        decreases count - coefficient,
    ))]
    while coefficient < count {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::proofs::production_impl::production_atk_sum_step(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, coefficient as nat);
            crate::proofs::production_impl::production_atk_sum_error_guard(output@, target, crate::codestream::raw_kernel_step_view(*step), crate::codestream::raw_kernel_view(*kernel), low_pass_first, coefficient as nat + 1, count as nat);
        }
        let alpha = coefficient_integer(
            *step
                .coefficients()
                .get(coefficient)
                .ok_or_else(invalid_transform)?,
            kernel.coefficient_type(),
        )?;
        let contribution = lifting_source_sum(
            output,
            target,
            coefficient,
            step.offset(),
            kernel.whole_sample_filter(),
            kernel.whole_sample_extension(),
            low_pass_first,
        )?;
        sum = sum
            .checked_add(
                alpha
                    .checked_mul(i128::from(contribution))
                    .ok_or_else(arithmetic_overflow)?,
            )
            .ok_or_else(arithmetic_overflow)?;
        coefficient = coefficient.checked_add(1).ok_or_else(arithmetic_overflow)?;
    }
    let exponent = u32::from(step.exponent());
    if exponent >= 127 {
        return Err(invalid_transform());
    }
    let updated = i128::from(output[target])
        .checked_sub(sum >> exponent)
        .ok_or_else(arithmetic_overflow)?;
    match i64::try_from(updated) {
        Ok(value) => Ok(value),
        Err(_) => Err(arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_source_sum(samples@, target, coefficient, offset, whole_sample_filter, whole_sample_extension, low_pass_first),
))]
fn lifting_source_sum(
    samples: &[i64],
    target: usize,
    coefficient: usize,
    offset: i8,
    whole_sample_filter: bool,
    whole_sample_extension: bool,
    low_pass_first: bool,
) -> Result<i64, DecodeError> {
    let target = match isize::try_from(target) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    let coefficient = match isize::try_from(coefficient) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    if whole_sample_filter {
        let doubled = coefficient.checked_mul(2).ok_or_else(arithmetic_overflow)?;
        let distance = doubled.checked_add(1).ok_or_else(arithmetic_overflow)?;
        let left = extended_sample(
            samples,
            target
                .checked_sub(distance)
                .ok_or_else(arithmetic_overflow)?,
            whole_sample_extension,
        )?;
        let right = extended_sample(
            samples,
            target
                .checked_add(distance)
                .ok_or_else(arithmetic_overflow)?,
            whole_sample_extension,
        )?;
        left.checked_add(right).ok_or_else(arithmetic_overflow)
    } else {
        let local_parity = target & 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(0 <= local_parity <= 1) by(bit_vector)
                requires local_parity == (target & 1isize);
        }
        let target_parity = if low_pass_first {
            local_parity
        } else {
            1 - local_parity
        };
        let doubled_parity = 2_isize
            .checked_mul(target_parity)
            .ok_or_else(arithmetic_overflow)?;
        let base = 1_isize
            .checked_sub(doubled_parity)
            .ok_or_else(arithmetic_overflow)?;
        let position = coefficient
            .checked_add(offset as isize)
            .ok_or_else(arithmetic_overflow)?;
        let distance = position.checked_mul(2).ok_or_else(arithmetic_overflow)?;
        let delta = base.checked_add(distance).ok_or_else(arithmetic_overflow)?;
        extended_sample(
            samples,
            target.checked_add(delta).ok_or_else(arithmetic_overflow)?,
            whole_sample_extension,
        )
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_atk_extended(samples@, original_index, whole_sample_extension),
))]
fn extended_sample(
    samples: &[i64],
    original_index: isize,
    whole_sample_extension: bool,
) -> Result<i64, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_atk_extended); }
    let mut index = original_index;
    if samples.len() < 2 {
        return match samples.first() {
            Some(value) => Ok(*value),
            None => Err(invalid_transform()),
        };
    }
    let length = match isize::try_from(samples.len()) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    if whole_sample_extension {
        if index < 0 {
            index = 0_isize.checked_sub(index).ok_or_else(arithmetic_overflow)?;
        }
        if index >= length {
            let period = 2_isize
                .checked_mul(length.checked_sub(1).ok_or_else(arithmetic_overflow)?)
                .ok_or_else(arithmetic_overflow)?;
            let wrapped = index
                .checked_rem_euclid(period)
                .ok_or_else(arithmetic_overflow)?;
            index = if wrapped < length {
                wrapped
            } else {
                period
                    .checked_sub(wrapped)
                    .ok_or_else(arithmetic_overflow)?
            };
        }
    } else {
        let parity = index & 1;
        let first = parity;
        let end = length.checked_sub(1).ok_or_else(arithmetic_overflow)?;
        let last = if end & 1 == parity {
            end
        } else {
            length.checked_sub(2).ok_or_else(arithmetic_overflow)?
        };
        index = if index < first {
            first
        } else if index > last {
            last
        } else {
            index
        };
    }
    let final_index = match usize::try_from(index) {
        Ok(value) => value,
        Err(_) => return Err(arithmetic_overflow()),
    };
    match samples.get(final_index) {
        Some(value) => Ok(*value),
        None => Err(invalid_transform()),
    }
}
