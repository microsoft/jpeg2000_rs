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
