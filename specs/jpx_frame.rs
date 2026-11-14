//! Actual lazy effective-layer decoding into the complete frame renderer.

use super::*;

verus! {

pub type Part2FrameSourceConfig = (u32, u32, u8, Seq<Part2Frame>);
pub type Part2FrameSourceSupplies = (Seq<Part2SuppliedLayer>, bool);

pub open spec fn part2_owned_layer_image(owned: Part2OwnedLayer) -> Part2ConvertedImageResult {
    match part2_layer_area(owned.0, owned.1) {
        Err(error) => Err(error),
        Ok(pixels) => {
            let alpha = match owned.4 {
                Some(value) => value,
                None => (Seq::new(pixels as nat, |_i: int| u16::MAX), false),
            };
            part2_image_from_planes(owned.0, owned.1, owned.2, owned.3, alpha.0, alpha.1)
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_frame_source_supplies(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, count: nat,
) -> Part2FrameSourceSupplies
    decreases count,
{
    if count == 0 { (Seq::empty(), false) }
    else {
        let previous = part2_frame_source_supplies(file, layers, instructions, limits, (count - 1) as nat);
        if previous.1 { previous }
        else {
            let index = instructions[count - 1].0;
            let outcome = part2_decode_effective_layer(file, layers, index, limits);
            (previous.0.push((index, Some(outcome))), match outcome { Err(_) => true, Ok(_) => false })
        }
    }
}

pub(crate) proof fn part2_frame_source_supplies_step(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, count: nat,
)
    ensures part2_frame_source_supplies(file, layers, instructions, limits, count + 1)
        == {
            let previous = part2_frame_source_supplies(file, layers, instructions, limits, count);
            if previous.1 { previous }
            else {
                let index = instructions[count as int].0;
                let outcome = part2_decode_effective_layer(file, layers, index, limits);
                (previous.0.push((index, Some(outcome))), match outcome { Err(_) => true, Ok(_) => false })
            }
        },
{
    reveal(part2_frame_source_supplies);
}

pub(crate) proof fn part2_frame_source_supplies_stopped(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, count: nat, total: nat,
)
    requires count <= total, part2_frame_source_supplies(file, layers, instructions, limits, count).1,
    ensures part2_frame_source_supplies(file, layers, instructions, limits, total)
        == part2_frame_source_supplies(file, layers, instructions, limits, count),
    decreases total - count,
{
    reveal(part2_frame_source_supplies);
    if count < total {
        part2_frame_source_supplies_stopped(file, layers, instructions, limits, count, (total - 1) as nat);
    }
}

pub(crate) open spec fn part2_frame_cold_step(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, index: nat, previous: Part2FrameSourceSupplies,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2FrameSourceSupplies> {
    if previous.1 { Some((Ok(previous), events)) } else {
        let reference = instructions[index as int].0;
        match part2_effective_layer_cold_run(file, layers, reference, limits, events) {
            None => None,
            Some((outcome, tail)) => Some((Ok((previous.0.push((reference, Some(outcome))), outcome.is_err())), tail)),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_frame_cold_prefix(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, count: nat, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2FrameSourceSupplies>
    decreases count,
{
    if count == 0 { Some((Ok((Seq::empty(), false)), events)) } else {
        part2_jpip_snapshot_bind(
            part2_frame_cold_prefix(file, layers, instructions, limits, (count - 1) as nat, events),
            |previous, tail| part2_frame_cold_step(file, layers, instructions, limits, (count - 1) as nat, previous, tail))
    }
}

pub(crate) proof fn part2_frame_cold_step_actual(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, index: nat, previous: Part2FrameSourceSupplies, outcome: Part2OwnedLayerResult,
)
    requires !previous.1,
        part2_effective_layer_cold_result(file, layers, instructions[index as int].0, limits, outcome),
    ensures part2_cold_framed(
        |events| part2_frame_cold_step(file, layers, instructions, limits, index, previous, events),
        Ok((previous.0.push((instructions[index as int].0, Some(outcome))), outcome.is_err()))),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2FrameSourceSupplies>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_frame_cold_step(file, layers, instructions, limits, index, previous, events))
                ==> #[trigger] part2_cold_framed(run,
                    Ok(part2_frame_cold_step_value(instructions, index, previous, outcome))),
{
    let run = |events| part2_effective_layer_cold_run(file, layers, instructions[index as int].0, limits, events);
    let prefix = part2_cold_witness(run, outcome);
    let value = (previous.0.push((instructions[index as int].0, Some(outcome))), outcome.is_err());
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_frame_cold_step(file, layers, instructions, limits, index, previous, prefix + tail)
            == Some((Ok(value), tail)) by {
        part2_cold_prefix_at(run, prefix, outcome, tail);
    }
    assert(part2_cold_prefix(
        |events| part2_frame_cold_step(file, layers, instructions, limits, index, previous, events), prefix, Ok(value)));
    assert forall|other: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2FrameSourceSupplies>|
        (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] other(events)
            == part2_frame_cold_step(file, layers, instructions, limits, index, previous, events))
            implies #[trigger] part2_cold_framed(other,
                Ok(part2_frame_cold_step_value(instructions, index, previous, outcome))) by {
        assert(part2_cold_prefix(other, prefix, Ok(value)));
    }
}

pub(crate) open spec fn part2_frame_cold_step_value(
    instructions: Seq<Part2Instruction>, index: nat, previous: Part2FrameSourceSupplies, outcome: Part2OwnedLayerResult,
) -> Part2FrameSourceSupplies {
    (previous.0.push((instructions[index as int].0, Some(outcome))), outcome.is_err())
}

pub(crate) proof fn part2_frame_cold_next(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, index: nat, previous: Seq<Part2SuppliedLayer>, outcome: Part2OwnedLayerResult,
)
    requires part2_cold_framed(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, index, events), Ok((previous, false))),
        part2_effective_layer_cold_result(file, layers, instructions[index as int].0, limits, outcome),
    ensures part2_cold_framed(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, index + 1, events),
        Ok((previous.push((instructions[index as int].0, Some(outcome))), outcome.is_err()))),
{
    let before_run = |events| part2_frame_cold_prefix(file, layers, instructions, limits, index, events);
    let before = part2_cold_witness(before_run, Ok((previous, false)));
    let source_run = |events| part2_effective_layer_cold_run(file, layers, instructions[index as int].0, limits, events);
    let calls = part2_cold_witness(source_run, outcome);
    let after = (previous.push((instructions[index as int].0, Some(outcome))), outcome.is_err());
    assert forall|tail: Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_frame_cold_prefix(file, layers, instructions, limits, index + 1, (before + calls) + tail)
            == Some((Ok(after), tail)) by {
        assert((before + calls) + tail =~= before + (calls + tail));
        part2_cold_prefix_at(before_run, before, Ok((previous, false)), calls + tail);
        part2_cold_prefix_at(source_run, calls, outcome, tail);
        reveal_with_fuel(part2_frame_cold_prefix, 1);
    }
    assert(part2_cold_prefix(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, index + 1, events),
        before + calls, Ok(after)));
}

pub(crate) proof fn part2_frame_cold_stopped(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, count: nat, total: nat, supplied: Seq<Part2SuppliedLayer>,
)
    requires count <= total, part2_cold_framed(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, count, events), Ok((supplied, true))),
    ensures part2_cold_framed(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, total, events), Ok((supplied, true))),
    decreases total - count,
{
    if count < total {
        part2_frame_cold_stopped(file, layers, instructions, limits, count, (total - 1) as nat, supplied);
        reveal_with_fuel(part2_frame_cold_prefix, 1);
        part2_cold_pure(Ok((supplied, true)));
        part2_cold_bind(
            |events| part2_frame_cold_prefix(file, layers, instructions, limits, (total - 1) as nat, events),
            |previous, tail| part2_frame_cold_step(file, layers, instructions, limits, (total - 1) as nat, previous, tail),
            Ok((supplied, true)), Ok((supplied, true)));
    }
}

pub(crate) proof fn part2_frame_cold_normal(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, count: nat,
)
    ensures part2_cold_framed(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, count, events),
        Ok(part2_frame_source_supplies(file, layers, instructions, limits, count))),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2FrameSourceSupplies>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_frame_cold_prefix(file, layers, instructions, limits, count, events))
                ==> #[trigger] part2_cold_framed(run,
                    Ok(part2_frame_source_supplies(file, layers, instructions, limits, count))),
    decreases count,
{
    reveal_with_fuel(part2_frame_cold_prefix, 1);
    reveal_with_fuel(part2_frame_source_supplies, 1);
    if count == 0 { part2_cold_pure(Ok((Seq::<Part2SuppliedLayer>::empty(), false))); }
    else {
        let previous = part2_frame_source_supplies(file, layers, instructions, limits, (count - 1) as nat);
        part2_frame_cold_normal(file, layers, instructions, limits, (count - 1) as nat);
        if previous.1 {
            part2_frame_cold_stopped(file, layers, instructions, limits,
                (count - 1) as nat, count, previous.0);
        }
        else {
            part2_effective_layer_cold_normal(file, layers, instructions[count - 1].0, limits);
            part2_frame_cold_next(file, layers, instructions, limits, (count - 1) as nat,
                previous.0, part2_decode_effective_layer(file, layers, instructions[count - 1].0, limits));
        }
    }
    let result = Ok(part2_frame_source_supplies(file, layers, instructions, limits, count));
    assert forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2FrameSourceSupplies>|
        (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
            == part2_frame_cold_prefix(file, layers, instructions, limits, count, events))
            implies #[trigger] part2_cold_framed(run, result) by {
        part2_cold_framed_extensional(
            |events| part2_frame_cold_prefix(file, layers, instructions, limits, count, events), run, result);
    }
}

pub(crate) open spec fn part2_frame_cold_supplies_run(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Seq<Part2SuppliedLayer>> {
    part2_jpip_snapshot_bind(part2_frame_cold_prefix(file, layers, instructions, limits, instructions.len(), events),
        |state: Part2FrameSourceSupplies, tail| Some((Ok(state.0), tail)))
}

pub(crate) open spec fn part2_frame_cold_supplies_result(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, supplied: Seq<Part2SuppliedLayer>,
) -> bool {
    part2_cold_framed(|events| part2_frame_cold_supplies_run(file, layers, instructions, limits, events), Ok(supplied))
}

pub(crate) proof fn part2_frame_cold_supplies_finish(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, instructions: Seq<Part2Instruction>,
    limits: &crate::ResourceLimits, supplied: Seq<Part2SuppliedLayer>, stopped: bool,
)
    requires part2_cold_framed(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, instructions.len(), events), Ok((supplied, stopped))),
    ensures part2_frame_cold_supplies_result(file, layers, instructions, limits, supplied),
{
    part2_cold_pure(Ok(supplied));
    part2_cold_bind(
        |events| part2_frame_cold_prefix(file, layers, instructions, limits, instructions.len(), events),
        |state: Part2FrameSourceSupplies, tail| Some((Ok(state.0), tail)), Ok((supplied, stopped)), Ok(supplied));
}

pub(crate) open spec fn part2_render_inspected_cold_run(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>,
    composition: Option<Part2FrameSourceConfig>, requested: usize, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    match composition {
        None => Some((Err(crate::DecodeError::FrameIndexOutOfRange { index: requested, frames: 0 }), events)),
        Some(config) => match part2_select_frame(config.3, requested, config.2) {
            Err(error) => Some((Err(error), events)),
            Ok(instructions) => part2_jpip_snapshot_bind(
                part2_frame_cold_supplies_run(file, layers, instructions, limits, events),
                |supplied, tail| Some((part2_render_normalized_frame(config.0, config.1, config.3, config.2,
                    requested, supplied, crate::limits::resource_decoded_bytes_limit(limits),
                    crate::limits::resource_work_limit(limits)), tail))),
        },
    }
}

pub(crate) open spec fn part2_render_inspected_cold_result(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>,
    composition: Option<Part2FrameSourceConfig>, requested: usize, limits: &crate::ResourceLimits,
    result: Part2ConvertedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_render_inspected_cold_run(file, layers, composition, requested, limits, events), result)
}

pub(crate) proof fn part2_render_inspected_cold_normal(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>,
    composition: Option<Part2FrameSourceConfig>, requested: usize, limits: &crate::ResourceLimits,
)
    ensures part2_render_inspected_cold_result(file, layers, composition, requested, limits,
        part2_render_inspected_source_frame(file, layers, composition, requested, limits)),
{
    reveal(part2_render_inspected_source_frame);
    match composition {
        None => { part2_cold_pure::<Part2ConvertedImage>(Err(crate::DecodeError::FrameIndexOutOfRange { index: requested, frames: 0 })); },
        Some(config) => match part2_select_frame(config.3, requested, config.2) {
            Err(error) => { part2_cold_pure::<Part2ConvertedImage>(Err(error)); },
            Ok(instructions) => {
                let state = part2_frame_source_supplies(file, layers, instructions, limits, instructions.len());
                part2_frame_cold_normal(file, layers, instructions, limits, instructions.len());
                part2_frame_cold_supplies_finish(file, layers, instructions, limits, state.0, state.1);
                let result = part2_render_normalized_frame(config.0, config.1, config.3, config.2, requested,
                    state.0, crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits));
                part2_cold_pure(result);
                part2_cold_bind(
                    |events| part2_frame_cold_supplies_run(file, layers, instructions, limits, events),
                    |supplied, tail| Some((part2_render_normalized_frame(config.0, config.1, config.3, config.2,
                        requested, supplied, crate::limits::resource_decoded_bytes_limit(limits),
                        crate::limits::resource_work_limit(limits)), tail)), Ok(state.0), result);
            },
        },
    }
}

pub(crate) proof fn part2_render_inspected_cold_supplies_actual(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>, config: Part2FrameSourceConfig,
    requested: usize, limits: &crate::ResourceLimits, instructions: Seq<Part2Instruction>,
    supplied: Seq<Part2SuppliedLayer>,
)
    requires part2_select_frame(config.3, requested, config.2) == Ok(instructions),
        part2_frame_cold_supplies_result(file, layers, instructions, limits, supplied),
    ensures part2_render_inspected_cold_result(file, layers, Some(config), requested, limits,
        part2_render_normalized_frame(config.0, config.1, config.3, config.2, requested, supplied,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits))),
{
    let result = part2_render_normalized_frame(config.0, config.1, config.3, config.2, requested, supplied,
        crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits));
    part2_cold_pure(result);
    part2_cold_bind(
        |events| part2_frame_cold_supplies_run(file, layers, instructions, limits, events),
        |values, tail| Some((part2_render_normalized_frame(config.0, config.1, config.3, config.2, requested, values,
            crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits)), tail)),
        Ok(supplied), result);
}

#[verifier::opaque]
pub open spec fn part2_render_inspected_source_frame(
    file: Part2JpxDecodeInput, layers: Seq<Part2LayerRoutingConfig>,
    composition: Option<Part2FrameSourceConfig>, requested: usize, limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    match composition {
        None => Err(crate::DecodeError::FrameIndexOutOfRange { index: requested, frames: 0 }),
        Some(config) => match part2_select_frame(config.3, requested, config.2) {
            Err(error) => Err(error),
            Ok(instructions) => {
                let decoded = part2_frame_source_supplies(file, layers, instructions, limits, instructions.len());
                part2_render_normalized_frame(config.0, config.1, config.3, config.2, requested, decoded.0,
                    crate::limits::resource_decoded_bytes_limit(limits), crate::limits::resource_work_limit(limits))
            },
        },
    }
}

}
