//! Source-derived extension owner requests in executing field and nested order.

use super::*;
use crate::codestream::{DecompositionDirection, MctCopyPath, Part2CopyPath};

verus! {

pub(crate) open spec fn part1_part2_copy_site(path: Part2CopyPath) -> u8 {
    match path {
        Part2CopyPath::Decompositions => 23, Part2CopyPath::Directions(_) => 24,
        Part2CopyPath::Arbitrary => 25, Part2CopyPath::Sublevels(_) => 26, Part2CopyPath::Splits(_) => 27,
        Part2CopyPath::Nonlinear => 28, Part2CopyPath::Parameters(_) => 29, Part2CopyPath::Points(_) => 30,
        Part2CopyPath::Depths => 31, Part2CopyPath::Kernels => 32, Part2CopyPath::Steps(_) => 33,
        Part2CopyPath::Coefficients(_, _) => 34, Part2CopyPath::Registrations => 35, Part2CopyPath::Lengths => 36,
    }
}

pub(crate) open spec fn part1_part2_copy_leaf(path: Part2CopyPath, count: usize) -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::Extensions(path), count)
}

pub(crate) open spec fn part1_part2_dfs_requests(value: (u8, Seq<DecompositionDirection>), position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Directions(position), value.1.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_part2_dfs_tail(values: Seq<(u8, Seq<DecompositionDirection>)>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases values.len() - position,
{
    if position >= values.len() { Seq::empty() } else {
        part1_part2_dfs_requests(values[position as int], position as usize) + part1_part2_dfs_tail(values, position + 1)
    }
}

pub(crate) open spec fn part1_part2_ads_requests(value: (u8, Seq<u8>, Seq<DecompositionDirection>), position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Sublevels(position), value.1.len() as usize)
        + part1_part2_copy_leaf(Part2CopyPath::Splits(position), value.2.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_part2_ads_tail(values: Seq<(u8, Seq<u8>, Seq<DecompositionDirection>)>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases values.len() - position,
{
    if position >= values.len() { Seq::empty() } else {
        part1_part2_ads_requests(values[position as int], position as usize) + part1_part2_ads_tail(values, position + 1)
    }
}

pub(crate) open spec fn part1_part2_nlt_requests(value: Part2OwnedNonlinear, position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Parameters(position), value.parameters.len() as usize)
        + part1_part2_copy_leaf(Part2CopyPath::Points(position), value.points.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_part2_nlt_tail(values: Seq<Part2OwnedNonlinear>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases values.len() - position,
{
    if position >= values.len() { Seq::empty() } else {
        part1_part2_nlt_requests(values[position as int], position as usize) + part1_part2_nlt_tail(values, position + 1)
    }
}

pub(crate) open spec fn part1_part2_step_requests(value: Part2RawKernelStep, kernel: usize, position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Coefficients(kernel, position), value.3.len() as usize)
}

#[verifier::opaque]
pub(crate) open spec fn part1_part2_steps_tail(values: Seq<Part2RawKernelStep>, kernel: usize, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases values.len() - position,
{
    if position >= values.len() { Seq::empty() } else {
        part1_part2_step_requests(values[position as int], kernel, position as usize)
            + part1_part2_steps_tail(values, kernel, position + 1)
    }
}

pub(crate) open spec fn part1_part2_kernel_requests(value: (u8, u16, Part2RawKernel), position: usize)
    -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Steps(position), value.2.6.len() as usize)
        + part1_part2_steps_tail(value.2.6, position, 0)
}

#[verifier::opaque]
pub(crate) open spec fn part1_part2_kernels_tail(values: Seq<(u8, u16, Part2RawKernel)>, position: nat)
    -> Seq<Part1MctCopyRequest>
    decreases values.len() - position,
{
    if position >= values.len() { Seq::empty() } else {
        part1_part2_kernel_requests(values[position as int], position as usize) + part1_part2_kernels_tail(values, position + 1)
    }
}

pub(crate) open spec fn part1_part2_dfs_vector(values: Seq<(u8, Seq<DecompositionDirection>)>) -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Decompositions, values.len() as usize) + part1_part2_dfs_tail(values, 0)
}
pub(crate) open spec fn part1_part2_ads_vector(values: Seq<(u8, Seq<u8>, Seq<DecompositionDirection>)>) -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Arbitrary, values.len() as usize) + part1_part2_ads_tail(values, 0)
}
pub(crate) open spec fn part1_part2_nlt_vector(values: Seq<Part2OwnedNonlinear>) -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Nonlinear, values.len() as usize) + part1_part2_nlt_tail(values, 0)
}
pub(crate) open spec fn part1_part2_kernel_vector(values: Seq<(u8, u16, Part2RawKernel)>) -> Seq<Part1MctCopyRequest> {
    part1_part2_copy_leaf(Part2CopyPath::Kernels, values.len() as usize) + part1_part2_kernels_tail(values, 0)
}

pub(crate) open spec fn part1_part2_copy_requests(value: Part2OwnedExtensions) -> Seq<Part1MctCopyRequest> {
    part1_part2_dfs_vector(value.decompositions) + part1_part2_ads_vector(value.arbitrary)
        + part1_part2_nlt_vector(value.nonlinear)
        + part1_part2_copy_leaf(Part2CopyPath::Depths, value.depths.len() as usize)
        + part1_part2_kernel_vector(value.kernels)
        + part1_part2_copy_leaf(Part2CopyPath::Registrations, value.registrations.len() as usize)
        + part1_part2_copy_leaf(Part2CopyPath::Lengths, value.lengths.len() as usize)
}

pub(crate) open spec fn part1_part2_copy_stage(value: Part2OwnedExtensions, stage: nat) -> Seq<Part1MctCopyRequest> {
    if stage == 0 { part1_part2_dfs_vector(value.decompositions) }
    else if stage == 1 { part1_part2_ads_vector(value.arbitrary) }
    else if stage == 2 { part1_part2_nlt_vector(value.nonlinear) }
    else if stage == 3 { part1_part2_copy_leaf(Part2CopyPath::Depths, value.depths.len() as usize) }
    else if stage == 4 { part1_part2_kernel_vector(value.kernels) }
    else if stage == 5 { part1_part2_copy_leaf(Part2CopyPath::Registrations, value.registrations.len() as usize) }
    else if stage == 6 { part1_part2_copy_leaf(Part2CopyPath::Lengths, value.lengths.len() as usize) }
    else { Seq::empty() }
}

pub(crate) open spec fn part1_part2_copy_tail(value: Part2OwnedExtensions, stage: nat) -> Seq<Part1MctCopyRequest>
    decreases 7nat - stage,
{
    if stage >= 7 { Seq::empty() } else {
        part1_part2_copy_stage(value, stage) + part1_part2_copy_tail(value, stage + 1)
    }
}

pub(crate) proof fn part1_part2_copy_advance(
    source: Part2OwnedExtensions, stage: nat, done: Seq<Part1MctCopyRequest>, result: Result<(), crate::DecodeError>,
) -> (next: Seq<Part1MctCopyRequest>)
    requires stage < 7, part1_mct_copy_result(done, Ok(())),
        part1_mct_copy_result(part1_part2_copy_stage(source, stage), result),
        part1_part2_copy_requests(source) == done + part1_part2_copy_tail(source, stage),
    ensures next == done + part1_part2_copy_stage(source, stage),
        part1_part2_copy_requests(source) == next + part1_part2_copy_tail(source, stage + 1),
        if result.is_ok() { part1_mct_copy_result(next, Ok(())) }
            else { part1_mct_copy_result(part1_part2_copy_requests(source), result) },
{
    let step = part1_part2_copy_stage(source, stage);
    let tail = part1_part2_copy_tail(source, stage + 1);
    assert((done + step) + tail =~= done + (step + tail));
    part1_mct_copy_continue(done, step, tail, result);
    done + step
}

pub(crate) proof fn part1_part2_copy_start(source: Part2OwnedExtensions)
    ensures part1_part2_copy_requests(source) == part1_part2_copy_tail(source, 0),
        part1_mct_copy_result(Seq::empty(), Ok(())),
{
    reveal_with_fuel(part1_part2_copy_tail, 8);
    part1_mct_copy_observed(MctCopyPath::Order, 0, Ok(()));
}

}
