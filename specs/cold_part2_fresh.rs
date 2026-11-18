//! Input-derived Part 2 constructors and the reached NLT marker insertion.

use super::*;
use crate::codestream::{DecompositionDirection, FreshPart2Path, MctCopyPath};

verus! {

pub(crate) enum Part2FreshInput {
    Dfs(Part1CodestreamSegment),
    Ads(usize, Part1CodestreamSegment),
    Unpack(usize, Part1CodestreamSegment, usize, usize, bool),
    Atk(usize, Part1CodestreamSegment),
    Step(usize, Part1CodestreamSegment, usize, usize, u8, bool, bool),
    Nlt(Part1CodestreamSegment, u16),
    Tail(Part1CodestreamSegment, usize),
}

pub(crate) enum Part2FreshValue {
    Dfs(Result<(u8, Seq<DecompositionDirection>), crate::DecodeError>),
    Ads(Result<(u8, Seq<u8>, Seq<DecompositionDirection>), crate::DecodeError>),
    Unpack(Result<Seq<u8>, crate::DecodeError>),
    Atk(Result<(u8, u16, Part2RawKernel), crate::DecodeError>),
    Step(Result<(Part2RawKernelStep, usize), crate::DecodeError>),
    Nlt(Result<Part2OwnedNonlinear, crate::DecodeError>),
    Tail(Result<Seq<u8>, crate::DecodeError>),
}

pub(crate) open spec fn part1_p2_fresh_site(path: FreshPart2Path) -> u8 {
    match path {
        FreshPart2Path::Dfs(_) => 72, FreshPart2Path::AdsDepth(_, _) => 73,
        FreshPart2Path::AdsSplit(_, _) => 74, FreshPart2Path::AdsDirections(_) => 75,
        FreshPart2Path::AtkSteps(_, _) => 76, FreshPart2Path::AtkCoefficients(_, _, _) => 77,
        FreshPart2Path::NltPoints(_) => 78, FreshPart2Path::NltParameters(_, _) => 79,
    }
}
pub(crate) open spec fn part1_p2_fresh_leaf(path: FreshPart2Path, count: usize) -> Seq<Part1MctCopyRequest> {
    part1_mct_copy_leaf(MctCopyPath::FreshPart2(path), count)
}
pub(crate) open spec fn part1_p2_fresh_unpack(segment: Part1CodestreamSegment, start: usize, count: usize, terminal: bool) -> Seq<Part1MctCopyRequest> {
    part1_p2_fresh_leaf(if terminal { FreshPart2Path::AdsSplit(segment.offset, start) }
        else { FreshPart2Path::AdsDepth(segment.offset, start) }, count)
}
pub(crate) open spec fn part1_p2_fresh_ads_shape(segment: Part1CodestreamSegment) -> Option<(usize, usize, usize)> {
    if segment.payload.len() < 3 || segment.payload[0] == 0 || segment.payload[0] > 127 { None } else {
        let depths = segment.payload[1] as usize;
        let at = 2int + part2_packed_two_bit_bytes(depths) as int;
        if at >= segment.payload.len() { None } else {
            let splits = segment.payload[at] as usize;
            if segment.payload.len() != at + 1 + part2_packed_two_bit_bytes(splits) as int { None }
            else { Some((depths, (at + 1) as usize, splits)) }
        }
    }
}
pub(crate) open spec fn part1_p2_fresh_step_requests(
    cursor: usize, segment: Part1CodestreamSegment, start: usize, width: usize, kind: u8, reversible: bool, whole: bool,
) -> Seq<Part1MctCopyRequest> {
    match part1_atk_step_header(cursor, segment, start, width, kind, reversible, whole) {
        Err(_) => Seq::empty(),
        Ok(header) => part1_p2_fresh_leaf(FreshPart2Path::AtkCoefficients(segment.offset, start, header.4), header.3),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_fresh_steps_requests(
    cursor: usize, segment: Part1CodestreamSegment, position: usize, width: usize, kind: u8, reversible: bool, whole: bool, remaining: nat,
) -> Seq<Part1MctCopyRequest>
    decreases remaining,
{
    if remaining == 0 { Seq::empty() } else {
        part1_p2_fresh_step_requests(cursor, segment, position, width, kind, reversible, whole) +
            match part1_atk_step(cursor, segment, position, width, kind, reversible, whole) {
                Err(_) => Seq::empty(), Ok((_, next)) => part1_p2_fresh_steps_requests(cursor, segment, next, width, kind, reversible, whole, (remaining - 1) as nat),
            }
    }
}
pub(crate) open spec fn part1_p2_fresh_requests(input: Part2FreshInput) -> Seq<Part1MctCopyRequest> {
    match input {
        Part2FreshInput::Dfs(segment) => match part1_dfs_payload(segment) {
            Err(_) => Seq::empty(), Ok(value) => part1_p2_fresh_leaf(FreshPart2Path::Dfs(segment.offset), value.1.len() as usize),
        },
        Part2FreshInput::Unpack(_, segment, start, count, terminal) => part1_p2_fresh_unpack(segment, start, count, terminal),
        Part2FreshInput::Ads(cursor, segment) => match part1_p2_fresh_ads_shape(segment) {
            None => Seq::empty(), Some((depths, start, splits)) => {
                let first = part1_p2_fresh_unpack(segment, 2, depths, false);
                first + if part1_unpack_two_bit_values(cursor, segment, 2, depths, false).is_err() { Seq::empty() } else {
                    part1_p2_fresh_unpack(segment, start, splits, true) +
                    match part1_unpack_two_bit_values(cursor, segment, start, splits, true) {
                        Err(_) => Seq::empty(), Ok(values) => part1_p2_fresh_leaf(FreshPart2Path::AdsDirections(segment.offset), values.len() as usize),
                    }
                }
            },
        },
        Part2FreshInput::Step(cursor, segment, start, width, kind, reversible, whole) =>
            part1_p2_fresh_step_requests(cursor, segment, start, width, kind, reversible, whole),
        Part2FreshInput::Atk(cursor, segment) => match part1_atk_header(cursor, segment) {
            Err(_) => Seq::empty(), Ok(header) =>
                part1_p2_fresh_leaf(FreshPart2Path::AtkSteps(segment.offset, header.position), header.step_count) +
                part1_p2_fresh_steps_requests(cursor, segment, header.position, header.width, header.coefficient_type,
                    header.reversible, header.whole_sample_filter, header.step_count as nat),
        },
        Part2FreshInput::Tail(segment, start) => if start > segment.payload.len() { Seq::empty() }
            else { part1_p2_fresh_leaf(FreshPart2Path::NltParameters(segment.offset, start), (segment.payload.len() - start) as usize) },
        Part2FreshInput::Nlt(segment, components) => match part1_nlt_header(segment, components) {
            Err(_) => Seq::empty(), Ok(header) => {
                let first = if header.3 == 2 || header.3 == 4 { match part1_nlt_points_header(segment) {
                    Err(_) => Seq::empty(), Ok(points) => part1_p2_fresh_leaf(FreshPart2Path::NltPoints(segment.offset), points.0 as usize),
                }} else { Seq::empty() };
                first + if part1_nlt_payload(segment, components).is_ok() {
                    part1_p2_fresh_leaf(FreshPart2Path::NltParameters(segment.offset, 4), (segment.payload.len() - 4) as usize)
                } else { Seq::empty() }
            },
        },
    }
}

pub(crate) open spec fn part1_p2_fresh_ordinary(input: Part2FreshInput) -> Part2FreshValue {
    match input {
        Part2FreshInput::Dfs(segment) => Part2FreshValue::Dfs(part1_dfs_payload(segment)),
        Part2FreshInput::Ads(cursor, segment) => Part2FreshValue::Ads(part1_ads_payload(cursor, segment)),
        Part2FreshInput::Unpack(cursor, segment, start, count, terminal) => Part2FreshValue::Unpack(part1_unpack_two_bit_values(cursor, segment, start, count, terminal)),
        Part2FreshInput::Atk(cursor, segment) => Part2FreshValue::Atk(part1_atk_payload(cursor, segment)),
        Part2FreshInput::Step(cursor, segment, start, width, kind, reversible, whole) => Part2FreshValue::Step(part1_atk_step(cursor, segment, start, width, kind, reversible, whole)),
        Part2FreshInput::Nlt(segment, components) => Part2FreshValue::Nlt(part1_nlt_payload(segment, components)),
        Part2FreshInput::Tail(segment, start) => Part2FreshValue::Tail(part1_copy_segment_tail(segment, start)),
    }
}
pub(crate) open spec fn part1_p2_fresh_failure(input: Part2FreshInput) -> Part2FreshValue {
    match input {
        Part2FreshInput::Dfs(_) => Part2FreshValue::Dfs(Err(crate::DecodeError::AllocationFailed)),
        Part2FreshInput::Ads(_, _) => Part2FreshValue::Ads(Err(crate::DecodeError::AllocationFailed)),
        Part2FreshInput::Unpack(_, _, _, _, _) => Part2FreshValue::Unpack(Err(crate::DecodeError::AllocationFailed)),
        Part2FreshInput::Atk(_, _) => Part2FreshValue::Atk(Err(crate::DecodeError::AllocationFailed)),
        Part2FreshInput::Step(_, _, _, _, _, _, _) => Part2FreshValue::Step(Err(crate::DecodeError::AllocationFailed)),
        Part2FreshInput::Nlt(_, _) => Part2FreshValue::Nlt(Err(crate::DecodeError::AllocationFailed)),
        Part2FreshInput::Tail(_, _) => Part2FreshValue::Tail(Err(crate::DecodeError::AllocationFailed)),
    }
}
pub(crate) open spec fn part1_p2_fresh_run(input: Part2FreshInput, events: Seq<Part1ColdStorageEvent>) -> Option<(Part2FreshValue, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_p2_fresh_requests(input), events) {
        None => None, Some((Err(_), rest)) => Some((part1_p2_fresh_failure(input), rest)),
        Some((Ok(()), rest)) => Some((part1_p2_fresh_ordinary(input), rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_fresh_result(input: Part2FreshInput, result: Part2FreshValue) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_p2_fresh_run(input, events) == Some((result, Seq::empty()))
}
pub(crate) proof fn part1_p2_fresh_normal(input: Part2FreshInput)
    ensures part1_p2_fresh_result(input, part1_p2_fresh_ordinary(input)),
{
    reveal(part1_p2_fresh_result);
    let requests = part1_p2_fresh_requests(input);
    let calls = part1_mct_copy_normal_calls(requests);
    part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_p2_fresh_run(input, calls) == Some((part1_p2_fresh_ordinary(input), Seq::empty())));
}
pub(crate) proof fn part1_p2_fresh_refused(input: Part2FreshInput)
    requires part1_mct_copy_result(part1_p2_fresh_requests(input), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_p2_fresh_result(input, part1_p2_fresh_failure(input)),
{
    reveal(part1_p2_fresh_result); reveal(part1_mct_copy_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_p2_fresh_requests(input), calls) == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_p2_fresh_run(input, calls) == Some((part1_p2_fresh_failure(input), Seq::empty())));
}

pub(crate) proof fn part1_p2_unpack_no_alloc(cursor: usize, segment: Part1CodestreamSegment,
    start: usize, count: usize, terminal: bool, position: usize, values: Seq<u8>)
    ensures part1_unpack_two_bit_run(cursor, segment, start, count, terminal, position, values) != Err(crate::DecodeError::AllocationFailed),
    decreases count - position,
{
    reveal_with_fuel(part1_unpack_two_bit_run, 1); reveal(part1_segment_byte);
    if position < count && position < usize::MAX {
        if let Ok(byte) = part1_segment_byte(cursor, segment, start, position / 4) {
            let value = part2_dfs_direction_code(byte, (position % 4) as u8);
            if terminal || value != 0 { part1_p2_unpack_no_alloc(cursor, segment, start, count, terminal, (position + 1) as usize, values.push(value)); }
        }
    }
}
pub(crate) proof fn part1_p2_coefficients_no_alloc(cursor: usize, segment: Part1CodestreamSegment,
    position: usize, width: usize, kind: u8, remaining: nat, values: Seq<Part2RawKernelCoefficient>)
    ensures part1_atk_coefficients(cursor, segment, position, width, kind, remaining, values) != Err(crate::DecodeError::AllocationFailed),
    decreases remaining,
{
    reveal_with_fuel(part1_atk_coefficients, 1); reveal(part1_kernel_coefficient); reveal(part1_kernel_advance);
    if remaining > 0 {
        if let Ok(value) = part1_kernel_coefficient(cursor, segment, position, width, kind) {
            if let Ok(next) = part1_kernel_advance(cursor, position, width) {
                part1_p2_coefficients_no_alloc(cursor, segment, next, width, kind, (remaining - 1) as nat, values.push(value));
            }
        }
    }
}
pub(crate) proof fn part1_p2_step_no_alloc(cursor: usize, segment: Part1CodestreamSegment, start: usize,
    width: usize, kind: u8, reversible: bool, whole: bool)
    ensures part1_atk_step(cursor, segment, start, width, kind, reversible, whole) != Err(crate::DecodeError::AllocationFailed),
{
    reveal(part1_atk_step); reveal(part1_atk_step_header);
    reveal(part1_segment_byte); reveal(part1_kernel_coefficient); reveal(part1_kernel_advance);
    if let Ok(h) = part1_atk_step_header(cursor, segment, start, width, kind, reversible, whole) {
        part1_p2_coefficients_no_alloc(cursor, segment, h.4, width, kind, h.3 as nat, Seq::empty());
    }
}
pub(crate) proof fn part1_p2_steps_no_alloc(cursor: usize, segment: Part1CodestreamSegment,
    position: usize, width: usize, kind: u8, reversible: bool, whole: bool, remaining: nat, values: Seq<Part2RawKernelStep>)
    ensures part1_atk_steps(cursor, segment, position, width, kind, reversible, whole, remaining, values) != Err(crate::DecodeError::AllocationFailed),
    decreases remaining,
{
    reveal_with_fuel(part1_atk_steps, 1);
    if remaining > 0 {
        part1_p2_step_no_alloc(cursor, segment, position, width, kind, reversible, whole);
        if let Ok((value, next)) = part1_atk_step(cursor, segment, position, width, kind, reversible, whole) {
            part1_p2_steps_no_alloc(cursor, segment, next, width, kind, reversible, whole, (remaining - 1) as nat, values.push(value));
        }
    }
}
pub(crate) proof fn part1_p2_fresh_no_alloc(input: Part2FreshInput)
    ensures part1_p2_fresh_ordinary(input) != part1_p2_fresh_failure(input),
{
    match input {
        Part2FreshInput::Dfs(_) => { reveal(part1_dfs_payload); },
        Part2FreshInput::Tail(_, _) => { reveal(part1_copy_segment_tail); },
        Part2FreshInput::Unpack(cursor, segment, start, count, terminal) => {
            part1_p2_unpack_no_alloc(cursor, segment, start, count, terminal, 0, Seq::empty());
        },
        Part2FreshInput::Ads(cursor, segment) => {
            reveal(part1_ads_payload);
            if let Some((depths, start, splits)) = part1_p2_fresh_ads_shape(segment) {
                part1_p2_unpack_no_alloc(cursor, segment, 2, depths, false, 0, Seq::empty());
                part1_p2_unpack_no_alloc(cursor, segment, start, splits, true, 0, Seq::empty());
            }
        },
        Part2FreshInput::Step(cursor, segment, start, width, kind, reversible, whole) =>
            part1_p2_step_no_alloc(cursor, segment, start, width, kind, reversible, whole),
        Part2FreshInput::Atk(cursor, segment) => {
            reveal(part1_atk_payload); reveal(part1_atk_header);
            reveal(part1_segment_byte); reveal(part1_kernel_coefficient); reveal(part1_kernel_advance);
            if let Ok(h) = part1_atk_header(cursor, segment) {
                part1_p2_steps_no_alloc(cursor, segment, h.position, h.width, h.coefficient_type, h.reversible, h.whole_sample_filter, h.step_count as nat, Seq::empty());
            }
        },
        Part2FreshInput::Nlt(_, _) => {
            reveal(part1_nlt_payload); reveal(part1_nlt_header); reveal(part1_nlt_gamma);
            reveal(part1_nlt_points); reveal(part1_nlt_points_header);
        },
    }
}
pub(crate) proof fn part1_p2_fresh_observed(input: Part2FreshInput, result: Part2FreshValue)
    requires part1_p2_fresh_result(input, result),
    ensures part1_mct_copy_result(part1_p2_fresh_requests(input), if result == part1_p2_fresh_failure(input) {
        Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }),
        result != part1_p2_fresh_failure(input) ==> result == part1_p2_fresh_ordinary(input),
{
    reveal(part1_p2_fresh_result); reveal(part1_mct_copy_result);
    part1_p2_fresh_no_alloc(input);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_fresh_run(input, calls) == Some((result, Seq::empty()));
    let requests = part1_p2_fresh_requests(input);
    if let Some((unit, rest)) = part1_mct_copy_run(requests, calls) {
        part1_mct_copy_projection(requests, calls, unit, rest);
        assert(part1_mct_copy_run(requests, calls) == Some((if result == part1_p2_fresh_failure(input) {
            Err(crate::DecodeError::AllocationFailed) } else { Ok(()) }, Seq::empty())));
    }
}

pub(crate) enum Part2FreshKind { Dfs, Ads, Nlt, Atk }

pub(crate) open spec fn part1_p2_marker_input(kind: Part2FreshKind, cursor: usize, segment: Part1CodestreamSegment, components: u16) -> Part2FreshInput {
    match kind {
        Part2FreshKind::Dfs => Part2FreshInput::Dfs(segment),
        Part2FreshKind::Ads => Part2FreshInput::Ads(cursor, segment),
        Part2FreshKind::Nlt => Part2FreshInput::Nlt(segment, components),
        Part2FreshKind::Atk => Part2FreshInput::Atk(cursor, segment),
    }
}
pub(crate) open spec fn part1_p2_marker_ordinary<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions)
    -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    match kind {
        Part2FreshKind::Dfs => part1_parse_dfs(reader, segment, extensions),
        Part2FreshKind::Ads => part1_parse_ads(reader, segment, extensions),
        Part2FreshKind::Nlt => part1_parse_nlt(reader, segment, components, extensions),
        Part2FreshKind::Atk => part1_parse_atk(reader, segment, extensions),
    }
}
pub(crate) open spec fn part1_nlt_insert_requests(segment:Part1CodestreamSegment,components:u16,
    extensions:Part2OwnedExtensions)->Seq<Part1MctCopyRequest> {
    match part1_nlt_payload(segment,components) {
        Err(_)=>Seq::empty(),
        Ok(replacement)=>{
            let count=match extensions.nonlinear_local_count {Some(count)=>count,None=>extensions.nonlinear.len() as usize};
            if count>extensions.nonlinear.len() ||
                matches!(extensions.nonlinear_local_count,Some(value) if value==usize::MAX) {Seq::empty()}
            else if exists|i:int|0<=i<count && #[trigger] extensions.nonlinear[i].component==replacement.component {
                Seq::empty()
            }else{part1_mct_copy_leaf(MctCopyPath::NonlinearInsert(segment.offset,replacement.component,count),1)}
        },
    }
}
pub(crate) open spec fn part1_p2_marker_requests<'a>(kind:Part2FreshKind,reader:Part1CodestreamReader<'a>,
    segment:Part1CodestreamSegment,components:u16,extensions:Part2OwnedExtensions)->Seq<Part1MctCopyRequest> {
    let charged=part1_charge_extension_metadata(reader,segment,extensions);
    if charged.0.is_err() {Seq::empty()}else{
        part1_p2_fresh_requests(part1_p2_marker_input(kind,charged.1.position,segment,components))
            + if kind==Part2FreshKind::Nlt {part1_nlt_insert_requests(segment,components,charged.2)}else{Seq::empty()}
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_marker_run<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions, events: Seq<Part1ColdStorageEvent>)
    -> Option<((Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions), Seq<Part1ColdStorageEvent>)> {
    let charged = part1_charge_extension_metadata(reader, segment, extensions);
    if charged.0.is_err() { Some((charged, events)) } else {
        let input = part1_p2_marker_input(kind, charged.1.position, segment, components);
        match part1_mct_copy_run(part1_p2_marker_requests(kind,reader,segment,components,extensions), events) {
            None => None, Some((Err(error), rest)) => Some(((Err(error), charged.1, charged.2), rest)),
            Some((Ok(()), rest)) => Some((part1_p2_marker_ordinary(kind, reader, segment, components, extensions), rest)),
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_p2_marker_result<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions)) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_p2_marker_run(kind, reader, segment, components, extensions, events) == Some((result, Seq::empty()))
}
pub(crate) open spec fn part1_p2_marker_calls(kind: Part2FreshKind, reader: Part1CodestreamReader<'_>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions) -> Seq<Part1ColdStorageEvent> {
    let charged = part1_charge_extension_metadata(reader, segment, extensions);
    if charged.0.is_err() { Seq::empty() } else {
        part1_mct_copy_normal_calls(part1_p2_marker_requests(kind,reader,segment,components,extensions))
    }
}
pub(crate) proof fn part1_p2_marker_normal<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_p2_marker_run(kind, reader, segment, components, extensions,
        part1_p2_marker_calls(kind, reader, segment, components, extensions) + tail)
            == Some((part1_p2_marker_ordinary(kind, reader, segment, components, extensions), tail)),
        part1_p2_marker_result(kind, reader, segment, components, extensions, part1_p2_marker_ordinary(kind, reader, segment, components, extensions)),
{
    reveal(part1_p2_marker_run);
    reveal(part1_p2_marker_result);
    reveal(part1_parse_dfs); reveal(part1_parse_ads); reveal(part1_parse_nlt); reveal(part1_parse_atk);
    let charged = part1_charge_extension_metadata(reader, segment, extensions);
    if charged.0.is_ok() {
        let requests = part1_p2_marker_requests(kind,reader,segment,components,extensions);
        part1_mct_copy_normal(requests, tail); part1_mct_copy_normal(requests, Seq::empty());
    }
    let calls = part1_p2_marker_calls(kind, reader, segment, components, extensions);
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
    assert(part1_p2_marker_run(kind, reader, segment, components, extensions, calls)
        == Some((part1_p2_marker_ordinary(kind, reader, segment, components, extensions), Seq::empty())));
}
pub(crate) proof fn part1_p2_marker_refused<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions)
    requires part1_charge_extension_metadata(reader, segment, extensions).0.is_ok(),
        part1_p2_fresh_result(
            part1_p2_marker_input(kind, part1_charge_extension_metadata(reader, segment, extensions).1.position, segment, components),
            part1_p2_fresh_failure(part1_p2_marker_input(kind, part1_charge_extension_metadata(reader, segment, extensions).1.position, segment, components))),
    ensures part1_p2_marker_result(kind, reader, segment, components, extensions,
        (Err(crate::DecodeError::AllocationFailed), part1_charge_extension_metadata(reader, segment, extensions).1,
            part1_charge_extension_metadata(reader, segment, extensions).2)),
{
    reveal(part1_p2_marker_run);
    reveal(part1_p2_marker_result); reveal(part1_mct_copy_result);
    let charged = part1_charge_extension_metadata(reader, segment, extensions);
    let input = part1_p2_marker_input(kind, charged.1.position, segment, components);
    part1_p2_fresh_observed(input, part1_p2_fresh_failure(input));
    part1_mct_copy_observed(MctCopyPath::Order,0,Ok(()));
    let fresh=part1_p2_fresh_requests(input);
    let growth=if kind==Part2FreshKind::Nlt {part1_nlt_insert_requests(segment,components,charged.2)}else{Seq::empty()};
    part1_mct_copy_continue(Seq::empty(),fresh,growth,Err(crate::DecodeError::AllocationFailed));
    assert((Seq::empty()+fresh)+growth =~= part1_p2_marker_requests(kind,reader,segment,components,extensions));
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_p2_fresh_requests(input), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    part1_mct_copy_bind(fresh,growth,calls);
    assert(part1_p2_marker_run(kind, reader, segment, components, extensions, calls)
        == Some(((Err(crate::DecodeError::AllocationFailed), charged.1, charged.2), Seq::empty())));
}
pub(crate) proof fn part1_p2_marker_frame<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions),
    rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>)
    requires part1_p2_marker_run(kind, reader, segment, components, extensions, events) == Some((result, rest)),
    ensures part1_p2_marker_run(kind, reader, segment, components, extensions, events + tail) == Some((result, rest + tail)),
{
    reveal(part1_p2_marker_run);
    let charged = part1_charge_extension_metadata(reader, segment, extensions);
    let requests = part1_p2_marker_requests(kind,reader,segment,components,extensions);
    if charged.0.is_ok() { if let Some((copied, after)) = part1_mct_copy_run(requests, events) {
        part1_mct_copy_frame(requests, events, copied, after, tail);
    }}
}
pub(crate) proof fn part1_p2_marker_projection<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions,
    events: Seq<Part1ColdStorageEvent>, result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions),
    rest: Seq<Part1ColdStorageEvent>)
    requires part1_p2_marker_run(kind, reader, segment, components, extensions, events) == Some((result, rest)),
        result.0 != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_p2_marker_ordinary(kind, reader, segment, components, extensions),
{
    reveal(part1_p2_marker_run);
    reveal(part1_parse_dfs); reveal(part1_parse_ads); reveal(part1_parse_nlt); reveal(part1_parse_atk);
    let charged = part1_charge_extension_metadata(reader, segment, extensions);
    let requests = part1_p2_marker_requests(kind,reader,segment,components,extensions);
    if charged.0.is_ok() { if let Some((copied, after)) = part1_mct_copy_run(requests, events) {
        part1_mct_copy_projection(requests, events, copied, after);
    }}
}
pub(crate) open spec fn part1_p2_marker_storage_result<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions)) -> bool {
    if result.0 == Err(crate::DecodeError::AllocationFailed) {
        part1_p2_marker_result(kind, reader, segment, components, extensions, result)
    } else { result == part1_p2_marker_ordinary(kind, reader, segment, components, extensions) }
}
pub(crate) proof fn part1_p2_marker_storage_observed<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions))
    requires part1_p2_marker_storage_result(kind, reader, segment, components, extensions, result),
    ensures part1_p2_marker_result(kind, reader, segment, components, extensions, result),
        result.0 != Err(crate::DecodeError::AllocationFailed) ==> result == part1_p2_marker_ordinary(kind, reader, segment, components, extensions),
{
    if result.0 != Err(crate::DecodeError::AllocationFailed) { part1_p2_marker_normal(kind, reader, segment, components, extensions, Seq::empty()); }
}
pub(crate) proof fn part1_p2_marker_storage_equivalent<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions,
    result: (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions))
    requires part1_p2_marker_result(kind, reader, segment, components, extensions, result),
    ensures part1_p2_marker_storage_result(kind, reader, segment, components, extensions, result),
{
    reveal(part1_p2_marker_result);
    if result.0 != Err(crate::DecodeError::AllocationFailed) {
        let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_p2_marker_run(kind, reader, segment, components, extensions, calls) == Some((result, Seq::empty()));
        part1_p2_marker_projection(kind, reader, segment, components, extensions, calls, result, Seq::empty());
    }
}
pub(crate) proof fn part1_p2_marker_storage_normal<'a>(kind: Part2FreshKind, reader: Part1CodestreamReader<'a>,
    segment: Part1CodestreamSegment, components: u16, extensions: Part2OwnedExtensions)
    ensures part1_p2_marker_storage_result(kind, reader, segment, components, extensions,
        part1_p2_marker_ordinary(kind, reader, segment, components, extensions)),
{
    part1_p2_marker_normal(kind, reader, segment, components, extensions, Seq::empty());
    part1_p2_marker_storage_equivalent(kind, reader, segment, components, extensions, part1_p2_marker_ordinary(kind, reader, segment, components, extensions));
}
pub(crate) proof fn part1_nlt_insert_refused<'a>(reader:Part1CodestreamReader<'a>,segment:Part1CodestreamSegment,
    components:u16,extensions:Part2OwnedExtensions,replacement:Part2OwnedNonlinear)
    requires part1_charge_extension_metadata(reader,segment,extensions).0.is_ok(),
        part1_p2_fresh_result(Part2FreshInput::Nlt(segment,components),Part2FreshValue::Nlt(Ok(replacement))),
        part1_mct_copy_result(part1_nlt_insert_requests(segment,components,
            part1_charge_extension_metadata(reader,segment,extensions).2),Err(crate::DecodeError::AllocationFailed)),
    ensures part1_p2_marker_storage_result(Part2FreshKind::Nlt,reader,segment,components,extensions,
        (Err(crate::DecodeError::AllocationFailed),part1_charge_extension_metadata(reader,segment,extensions).1,
            part1_charge_extension_metadata(reader,segment,extensions).2)),
{
    let kind=Part2FreshKind::Nlt;let charged=part1_charge_extension_metadata(reader,segment,extensions);
    let fresh=part1_p2_fresh_requests(Part2FreshInput::Nlt(segment,components));
    let growth=part1_nlt_insert_requests(segment,components,charged.2);
    part1_p2_fresh_observed(Part2FreshInput::Nlt(segment,components),Part2FreshValue::Nlt(Ok(replacement)));
    part1_mct_copy_continue(fresh,growth,Seq::empty(),Err(crate::DecodeError::AllocationFailed));
    assert((fresh+growth)+Seq::empty() =~= fresh+growth);
    reveal(part1_mct_copy_result);reveal(part1_p2_marker_result);reveal(part1_p2_marker_run);
    let calls=choose|calls:Seq<Part1ColdStorageEvent>|part1_mct_copy_run(fresh+growth,calls)
        ==Some((Err(crate::DecodeError::AllocationFailed),Seq::empty()));
    assert(part1_p2_marker_run(kind,reader,segment,components,extensions,calls)
        ==Some(((Err(crate::DecodeError::AllocationFailed),charged.1,charged.2),Seq::empty())));
    part1_p2_marker_storage_equivalent(kind,reader,segment,components,extensions,
        (Err(crate::DecodeError::AllocationFailed),charged.1,charged.2));
}

}
