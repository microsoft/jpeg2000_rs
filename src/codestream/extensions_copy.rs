//! Fallible copies of the actual cold inherited Part 2 owner.

#[cfg(verus_keep_ghost)]
use super::mct_copy::copy_outcome;
use super::mct_copy::{copy_flat, reserve_values};
use super::{
    ArbitraryDecomposition, ArbitraryKernel, DecodeError, DecompositionStructure,
    KernelLiftingStep, MctCopyPath, NonlinearPointTransform, Part2CopyPath, Part2Extensions,
};
#[cfg(verus_keep_ghost)]
use super::{
    owned_arbitrary_decomposition_view, owned_decomposition_view, owned_extensions_view,
    owned_kernel_view, owned_nonlinear_view, raw_kernel_step_view, raw_kernel_steps_view,
    raw_kernel_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) open spec fn dfs_values(values: Seq<DecompositionStructure>) -> Seq<(u8, Seq<super::DecompositionDirection>)> {
        values.map_values(|entry: DecompositionStructure| owned_decomposition_view(&entry))
    }
    pub(super) open spec fn ads_values(values: Seq<ArbitraryDecomposition>) -> Seq<(u8, Seq<u8>, Seq<super::DecompositionDirection>)> {
        values.map_values(|entry: ArbitraryDecomposition| owned_arbitrary_decomposition_view(&entry))
    }
    pub(super) open spec fn nlt_values(values: Seq<NonlinearPointTransform>) -> Seq<crate::specs::Part2OwnedNonlinear> {
        values.map_values(|entry: NonlinearPointTransform| owned_nonlinear_view(&entry))
    }
    pub(super) open spec fn kernel_values(values: Seq<ArbitraryKernel>) -> Seq<(u8, u16, crate::specs::Part2RawKernel)> {
        values.map_values(|entry: ArbitraryKernel| owned_kernel_view(&entry))
    }
}

impl DecompositionStructure {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_part2_dfs_requests(owned_decomposition_view(self), _position), copy_outcome(result)),
            match result { Ok(value) => owned_decomposition_view(&value) == owned_decomposition_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_decomposition_view); }
        let index = self.index;
        let directions = copy_flat(
            &self.directions,
            MctCopyPath::Extensions(Part2CopyPath::Directions(_position)),
        )?;
        Ok(Self { index, directions })
    }
}

impl ArbitraryDecomposition {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_part2_ads_requests(owned_arbitrary_decomposition_view(self), _position), copy_outcome(result)),
            match result { Ok(value) => owned_arbitrary_decomposition_view(&value) == owned_arbitrary_decomposition_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost first = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Sublevels(_position), self.sublevel_depths.len());
            let ghost last = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Splits(_position), self.subband_splits.len());
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_arbitrary_decomposition_view); crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(())); }
        let index = self.index;
        let copied = copy_flat(
            &self.sublevel_depths,
            MctCopyPath::Extensions(Part2CopyPath::Sublevels(_position)),
        );
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part1_mct_copy_continue(Seq::empty(), first, last, copy_outcome(copied)); }
        let sublevel_depths = copied?;
        let copied = copy_flat(
            &self.subband_splits,
            MctCopyPath::Extensions(Part2CopyPath::Splits(_position)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(first, last, Seq::empty(), copy_outcome(copied));
            assert((first + last) + Seq::<crate::specs::Part1MctCopyRequest>::empty() =~= first + last);
        }
        let subband_splits = copied?;
        Ok(Self {
            index,
            sublevel_depths,
            subband_splits,
        })
    }
}

impl NonlinearPointTransform {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_part2_nlt_requests(owned_nonlinear_view(self), _position), copy_outcome(result)),
            match result { Ok(value) => owned_nonlinear_view(&value) == owned_nonlinear_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost first = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Parameters(_position), self.parameters.len());
            let ghost last = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Points(_position), self.points.len());
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_nonlinear_view); crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(())); }
        let component = self.component;
        let precision = self.precision;
        let signed = self.signed;
        let transform_type = self.transform_type;
        let copied = copy_flat(
            &self.parameters,
            MctCopyPath::Extensions(Part2CopyPath::Parameters(_position)),
        );
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part1_mct_copy_continue(Seq::empty(), first, last, copy_outcome(copied)); }
        let parameters = copied?;
        let d_min = self.d_min;
        let d_max = self.d_max;
        let point_bits = self.point_bits;
        let copied = copy_flat(
            &self.points,
            MctCopyPath::Extensions(Part2CopyPath::Points(_position)),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part1_mct_copy_continue(first, last, Seq::empty(), copy_outcome(copied));
            assert((first + last) + Seq::<crate::specs::Part1MctCopyRequest>::empty() =~= first + last);
        }
        let points = copied?;
        Ok(Self {
            component,
            precision,
            signed,
            transform_type,
            parameters,
            d_min,
            d_max,
            point_bits,
            points,
            gamma_parameters: self.gamma_parameters,
        })
    }
}

impl KernelLiftingStep {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_part2_step_requests(raw_kernel_step_view(*self), _kernel, _position), copy_outcome(result)),
            match result { Ok(value) => raw_kernel_step_view(value) == raw_kernel_step_view(*self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _kernel: usize, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(raw_kernel_step_view); reveal(super::raw_kernel_coefficients_view); }
        let offset = self.offset;
        let exponent = self.exponent;
        let residue = self.residue;
        let coefficients = copy_flat(
            &self.coefficients,
            MctCopyPath::Extensions(Part2CopyPath::Coefficients(_kernel, _position)),
        )?;
        Ok(Self {
            offset,
            exponent,
            residue,
            coefficients,
        })
    }
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_mct_copy_result(
        crate::specs::part1_part2_copy_leaf(Part2CopyPath::Steps(_kernel), source.len())
            + crate::specs::part1_part2_steps_tail(raw_kernel_steps_view(source@), _kernel, 0), copy_outcome(result)),
        match result { Ok(values) => raw_kernel_steps_view(values@) == raw_kernel_steps_view(source@),
            Err(error) => error == DecodeError::AllocationFailed },
))]
fn copy_steps(
    source: &[KernelLiftingStep],
    _kernel: usize,
) -> Result<Vec<KernelLiftingStep>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost view = raw_kernel_steps_view(source@);
        let ghost mut done = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Steps(_kernel), source.len());
        let ghost all = done + crate::specs::part1_part2_steps_tail(view, _kernel, 0);
    }
    let copied = reserve_values(
        source.len(),
        MctCopyPath::Extensions(Part2CopyPath::Steps(_kernel)),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        crate::specs::part1_mct_copy_continue(Seq::empty(), done,
            crate::specs::part1_part2_steps_tail(view, _kernel, 0), copy_outcome(copied));
    }
    let mut values: Vec<KernelLiftingStep> = copied?;
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= source.len(), view == raw_kernel_steps_view(source@),
            raw_kernel_steps_view(values@) == view.take(position as int),
            all == crate::specs::part1_part2_copy_leaf(Part2CopyPath::Steps(_kernel), source.len())
                + crate::specs::part1_part2_steps_tail(view, _kernel, 0),
            all == done + crate::specs::part1_part2_steps_tail(view, _kernel, position as nat),
            crate::specs::part1_mct_copy_result(done, Ok(())),
        decreases source.len() - position,
    ))]
    while position < source.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_part2_steps_tail, 1); reveal(raw_kernel_steps_view); }
        let copied = source[position].try_duplicate_at(_kernel, position);
        #[cfg(verus_keep_ghost)]
        proof! {
            let step = crate::specs::part1_part2_step_requests(view[position as int], _kernel, position);
            let suffix = crate::specs::part1_part2_steps_tail(view, _kernel, position as nat + 1);
            crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
            assert(all =~= (done + step) + suffix);
        }
        let value = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = values@; let ghost copied_view = raw_kernel_step_view(value); }
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(raw_kernel_steps_view);
            assert(raw_kernel_steps_view(values@) =~= raw_kernel_steps_view(previous).push(copied_view));
            assert(view.take(position as int + 1) =~= view.take(position as int).push(view[position as int]));
            done = done + crate::specs::part1_part2_step_requests(view[position as int], _kernel, position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_part2_steps_tail, 1); assert(all =~= done); assert(view.take(position as int) =~= view); }
    Ok(values)
}

impl ArbitraryKernel {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(
            crate::specs::part1_part2_kernel_requests(owned_kernel_view(self), _position), copy_outcome(result)),
            match result { Ok(value) => owned_kernel_view(&value) == owned_kernel_view(self),
                Err(error) => error == DecodeError::AllocationFailed },
    ))]
    fn try_duplicate_at(&self, _position: usize) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_kernel_view); reveal(raw_kernel_view); }
        let index = self.index;
        let reversible = self.reversible;
        let descriptor = self.descriptor;
        let coefficient_type = self.coefficient_type;
        let whole_sample_filter = self.whole_sample_filter;
        let initial_odd = self.initial_odd;
        let whole_sample_extension = self.whole_sample_extension;
        let scaling = self.scaling;
        let steps = copy_steps(&self.steps, _position)?;
        Ok(Self {
            index,
            reversible,
            descriptor,
            coefficient_type,
            whole_sample_filter,
            initial_odd,
            whole_sample_extension,
            scaling,
            steps,
        })
    }
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(crate::specs::part1_part2_dfs_vector(dfs_values(source@)), copy_outcome(result)),
            match result { Ok(values) => dfs_values(values@) == dfs_values(source@), Err(error) => error == DecodeError::AllocationFailed },
    ))]
fn copy_decompositions(
    source: &[DecompositionStructure],
) -> Result<Vec<DecompositionStructure>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost view = dfs_values(source@);
        let ghost mut done = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Decompositions, source.len());
        let ghost all = crate::specs::part1_part2_dfs_vector(view);
    }
    let copied = reserve_values(
        source.len(),
        MctCopyPath::Extensions(Part2CopyPath::Decompositions),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        crate::specs::part1_mct_copy_continue(Seq::empty(), done, crate::specs::part1_part2_dfs_tail(view, 0), copy_outcome(copied));
    }
    let mut values: Vec<DecompositionStructure> = copied?;
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= source.len(), view == dfs_values(source@),
                dfs_values(values@) == view.take(position as int), all == crate::specs::part1_part2_dfs_vector(view),
                all == done + crate::specs::part1_part2_dfs_tail(view, position as nat),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases source.len() - position,
        ))]
    while position < source.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_part2_dfs_tail, 1); }
        let copied = source[position].try_duplicate_at(position);
        #[cfg(verus_keep_ghost)]
        proof! {
            let step = crate::specs::part1_part2_dfs_requests(view[position as int], position);
            let suffix = crate::specs::part1_part2_dfs_tail(view, position as nat + 1);
            crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
            assert(all =~= (done + step) + suffix);
        }
        let value = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = values@; let ghost copied_view = owned_decomposition_view(&value); }
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(dfs_values(values@) =~= dfs_values(previous).push(copied_view));
            assert(view.take(position as int + 1) =~= view.take(position as int).push(view[position as int]));
            done = done + crate::specs::part1_part2_dfs_requests(view[position as int], position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_part2_dfs_tail, 1); assert(all =~= done); assert(view.take(position as int) =~= view); }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(crate::specs::part1_part2_ads_vector(ads_values(source@)), copy_outcome(result)),
            match result { Ok(values) => ads_values(values@) == ads_values(source@), Err(error) => error == DecodeError::AllocationFailed },
    ))]
fn copy_arbitrary(
    source: &[ArbitraryDecomposition],
) -> Result<Vec<ArbitraryDecomposition>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost view = ads_values(source@);
        let ghost mut done = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Arbitrary, source.len());
        let ghost all = crate::specs::part1_part2_ads_vector(view);
    }
    let copied = reserve_values(
        source.len(),
        MctCopyPath::Extensions(Part2CopyPath::Arbitrary),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        crate::specs::part1_mct_copy_continue(Seq::empty(), done, crate::specs::part1_part2_ads_tail(view, 0), copy_outcome(copied));
    }
    let mut values: Vec<ArbitraryDecomposition> = copied?;
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= source.len(), view == ads_values(source@),
                ads_values(values@) == view.take(position as int), all == crate::specs::part1_part2_ads_vector(view),
                all == done + crate::specs::part1_part2_ads_tail(view, position as nat),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases source.len() - position,
        ))]
    while position < source.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_part2_ads_tail, 1); }
        let copied = source[position].try_duplicate_at(position);
        #[cfg(verus_keep_ghost)]
        proof! {
            let step = crate::specs::part1_part2_ads_requests(view[position as int], position);
            let suffix = crate::specs::part1_part2_ads_tail(view, position as nat + 1);
            crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
            assert(all =~= (done + step) + suffix);
        }
        let value = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = values@; let ghost copied_view = owned_arbitrary_decomposition_view(&value); }
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ads_values(values@) =~= ads_values(previous).push(copied_view));
            assert(view.take(position as int + 1) =~= view.take(position as int).push(view[position as int]));
            done = done + crate::specs::part1_part2_ads_requests(view[position as int], position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_part2_ads_tail, 1); assert(all =~= done); assert(view.take(position as int) =~= view); }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(crate::specs::part1_part2_nlt_vector(nlt_values(source@)), copy_outcome(result)),
            match result { Ok(values) => nlt_values(values@) == nlt_values(source@), Err(error) => error == DecodeError::AllocationFailed },
    ))]
fn copy_nonlinear(
    source: &[NonlinearPointTransform],
) -> Result<Vec<NonlinearPointTransform>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost view = nlt_values(source@);
        let ghost mut done = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Nonlinear, source.len());
        let ghost all = crate::specs::part1_part2_nlt_vector(view);
    }
    let copied = reserve_values(
        source.len(),
        MctCopyPath::Extensions(Part2CopyPath::Nonlinear),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        crate::specs::part1_mct_copy_continue(Seq::empty(), done, crate::specs::part1_part2_nlt_tail(view, 0), copy_outcome(copied));
    }
    let mut values: Vec<NonlinearPointTransform> = copied?;
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= source.len(), view == nlt_values(source@),
                nlt_values(values@) == view.take(position as int), all == crate::specs::part1_part2_nlt_vector(view),
                all == done + crate::specs::part1_part2_nlt_tail(view, position as nat),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases source.len() - position,
        ))]
    while position < source.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_part2_nlt_tail, 1); }
        let copied = source[position].try_duplicate_at(position);
        #[cfg(verus_keep_ghost)]
        proof! {
            let step = crate::specs::part1_part2_nlt_requests(view[position as int], position);
            let suffix = crate::specs::part1_part2_nlt_tail(view, position as nat + 1);
            crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
            assert(all =~= (done + step) + suffix);
        }
        let value = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = values@; let ghost copied_view = owned_nonlinear_view(&value); }
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(nlt_values(values@) =~= nlt_values(previous).push(copied_view));
            assert(view.take(position as int + 1) =~= view.take(position as int).push(view[position as int]));
            done = done + crate::specs::part1_part2_nlt_requests(view[position as int], position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_part2_nlt_tail, 1); assert(all =~= done); assert(view.take(position as int) =~= view); }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_mct_copy_result(crate::specs::part1_part2_kernel_vector(kernel_values(source@)), copy_outcome(result)),
            match result { Ok(values) => kernel_values(values@) == kernel_values(source@), Err(error) => error == DecodeError::AllocationFailed },
    ))]
fn copy_kernels(source: &[ArbitraryKernel]) -> Result<Vec<ArbitraryKernel>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost view = kernel_values(source@);
        let ghost mut done = crate::specs::part1_part2_copy_leaf(Part2CopyPath::Kernels, source.len());
        let ghost all = crate::specs::part1_part2_kernel_vector(view);
    }
    let copied = reserve_values(
        source.len(),
        MctCopyPath::Extensions(Part2CopyPath::Kernels),
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
        crate::specs::part1_mct_copy_continue(Seq::empty(), done, crate::specs::part1_part2_kernels_tail(view, 0), copy_outcome(copied));
    }
    let mut values: Vec<ArbitraryKernel> = copied?;
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= source.len(), view == kernel_values(source@),
                kernel_values(values@) == view.take(position as int), all == crate::specs::part1_part2_kernel_vector(view),
                all == done + crate::specs::part1_part2_kernels_tail(view, position as nat),
                crate::specs::part1_mct_copy_result(done, Ok(())),
            decreases source.len() - position,
        ))]
    while position < source.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part1_part2_kernels_tail, 1); }
        let copied = source[position].try_duplicate_at(position);
        #[cfg(verus_keep_ghost)]
        proof! {
            let step = crate::specs::part1_part2_kernel_requests(view[position as int], position);
            let suffix = crate::specs::part1_part2_kernels_tail(view, position as nat + 1);
            crate::specs::part1_mct_copy_continue(done, step, suffix, copy_outcome(copied));
            assert(all =~= (done + step) + suffix);
        }
        let value = copied?;
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = values@; let ghost copied_view = owned_kernel_view(&value); }
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(kernel_values(values@) =~= kernel_values(previous).push(copied_view));
            assert(view.take(position as int + 1) =~= view.take(position as int).push(view[position as int]));
            done = done + crate::specs::part1_part2_kernel_requests(view[position as int], position);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part1_part2_kernels_tail, 1); assert(all =~= done); assert(view.take(position as int) =~= view); }
    Ok(values)
}

impl Part2Extensions {
    #[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
            ensures crate::specs::part1_mct_copy_result(
                crate::specs::part1_part2_copy_requests(owned_extensions_view(self)), copy_outcome(result)),
                match result { Ok(value) => owned_extensions_view(&value) == owned_extensions_view(self),
                    Err(error) => error == DecodeError::AllocationFailed },
        ))]
    pub(super) fn try_duplicate(&self) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost source = owned_extensions_view(self);
            let ghost mut done = Seq::<crate::specs::Part1MctCopyRequest>::empty();
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(owned_extensions_view);
            crate::specs::part1_part2_copy_start(source);
            assert(crate::specs::part1_part2_copy_requests(source) =~= done + crate::specs::part1_part2_copy_tail(source, 0));
        }
        let copied = copy_decompositions(&self.decomposition_structures);
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part1_part2_copy_advance(source, 0, done, copy_outcome(copied)); }
        let decomposition_structures = copied?;
        let copied = copy_arbitrary(&self.arbitrary_decompositions);
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part1_part2_copy_advance(source, 1, done, copy_outcome(copied)); }
        let arbitrary_decompositions = copied?;
        let copied = copy_nonlinear(&self.nonlinear_transforms);
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part1_part2_copy_advance(source, 2, done, copy_outcome(copied)); }
        let nonlinear_transforms = copied?;
        let nonlinear_local_count = self.nonlinear_local_count;
        let copied = copy_flat(
            &self.component_bit_depths,
            MctCopyPath::Extensions(Part2CopyPath::Depths),
        );
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part1_part2_copy_advance(source, 3, done, copy_outcome(copied)); }
        let component_bit_depths = copied?;
        let copied = copy_kernels(&self.arbitrary_kernels);
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part1_part2_copy_advance(source, 4, done, copy_outcome(copied)); }
        let arbitrary_kernels = copied?;
        let copied = copy_flat(
            &self.component_registrations,
            MctCopyPath::Extensions(Part2CopyPath::Registrations),
        );
        #[cfg(verus_keep_ghost)]
        proof! { done = crate::specs::part1_part2_copy_advance(source, 5, done, copy_outcome(copied)); }
        let component_registrations = copied?;
        let copied = copy_flat(
            &self.tile_part_lengths,
            MctCopyPath::Extensions(Part2CopyPath::Lengths),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            done = crate::specs::part1_part2_copy_advance(source, 6, done, copy_outcome(copied));
            assert(crate::specs::part1_part2_copy_tail(source, 7) =~= Seq::<crate::specs::Part1MctCopyRequest>::empty());
            assert(crate::specs::part1_part2_copy_requests(source) =~= done);
        }
        let tile_part_lengths = copied?;
        let copied = Self {
            decomposition_structures,
            arbitrary_decompositions,
            nonlinear_transforms,
            nonlinear_local_count,
            component_bit_depths,
            arbitrary_kernels,
            component_registrations,
            tile_part_lengths,
            metadata_bytes: self.metadata_bytes,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let actual = owned_extensions_view(&copied);
            assert(actual.decompositions =~= source.decompositions);
            assert(actual.arbitrary =~= source.arbitrary);
            assert(actual.nonlinear =~= source.nonlinear);
            assert(actual.depths =~= source.depths);
            assert(actual.kernels =~= source.kernels);
            assert(actual.registrations =~= source.registrations);
            assert(actual.lengths =~= source.lengths);
        }
        Ok(copied)
    }
}
