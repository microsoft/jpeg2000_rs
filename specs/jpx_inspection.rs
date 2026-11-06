//! Total actual inspection over parsed file metadata and native source-info geometry.

use super::*;

verus! {

pub struct Part2InspectionLayerConfig {
    pub grid: (u16, u16),
    pub registrations: Seq<crate::jp2::CodestreamRegistration>,
    pub has_color_group: bool,
    pub has_opacity_box: bool,
    pub nested_metadata_boxes: u32,
}

pub struct Part2InspectionCompositionConfig {
    pub width: u32,
    pub height: u32,
    pub loop_count: u8,
    pub sets: Seq<Part2TimelineSet>,
    pub has_unknown_boxes: bool,
}

pub struct Part2InspectionFileInput {
    pub layers: Seq<Part2InspectionLayerConfig>,
    pub codestreams: usize,
    pub composition: Option<Part2InspectionCompositionConfig>,
    pub metadata: (u32, u32),
}

pub struct Part2LayerInspection {
    pub index: usize,
    pub codestream_indices: Seq<u16>,
    pub grid: (u16, u16),
    pub offset: (u32, u32),
    pub geometry: (u32, u32),
    pub has_color_group: bool,
    pub has_opacity_box: bool,
    pub nested_metadata_boxes: u32,
}

pub struct Part2CompositionInspection {
    pub source: Part2FrameSourceConfig,
    pub instruction_sets: u32,
    pub total_duration_milliseconds: u64,
    pub has_unknown_boxes: bool,
}

pub struct Part2JpxInspection {
    pub layers: Seq<Part2LayerInspection>,
    pub composition: Option<Part2CompositionInspection>,
    pub metadata: (u32, u32),
}

pub type Part2InspectionRegistration = (Seq<u16>, u32, u32);

pub open spec fn part2_inspection_layer_count(input: Part2InspectionFileInput) -> nat {
    effective_jpx_layer_count(input.layers.len(), input.codestreams as nat)
}

#[verifier::opaque]
pub open spec fn part2_inspection_registration_step(
    layer: Part2InspectionLayerConfig, geometries: Seq<(u32, u32)>,
    index: nat, previous: Part2InspectionRegistration,
) -> Result<Part2InspectionRegistration, crate::DecodeError> {
    let registration = layer.registrations[index as int];
    let source = registration.codestream_index as int;
    if source >= geometries.len() { Err(part2_composition_error(false)) }
    else {
        match part2_native_registered_extent(geometries[source].0,
            registration.horizontal_subsampling as u32, layer.grid.0 as u32, registration.horizontal_offset) {
            Err(error) => Err(error),
            Ok(width) => match part2_native_registered_extent(geometries[source].1,
                registration.vertical_subsampling as u32, layer.grid.1 as u32, registration.vertical_offset) {
                Err(error) => Err(error),
                Ok(height) => Ok((previous.0.push(registration.codestream_index),
                    if previous.1 < width { previous.1 } else { width },
                    if previous.2 < height { previous.2 } else { height })),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_inspection_registration_prefix(
    layer: Part2InspectionLayerConfig, geometries: Seq<(u32, u32)>, count: nat,
) -> Result<Part2InspectionRegistration, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), u32::MAX, u32::MAX)) }
    else {
        match part2_inspection_registration_prefix(layer, geometries, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_inspection_registration_step(layer, geometries, (count - 1) as nat, previous),
        }
    }
}

pub open spec fn part2_inspection_layer_value(
    index: usize, config: Part2InspectionLayerConfig, source: Part2InspectionRegistration,
) -> Part2LayerInspection {
    Part2LayerInspection {
        index, codestream_indices: source.0, grid: config.grid, offset: (0, 0), geometry: (source.1, source.2),
        has_color_group: config.has_color_group, has_opacity_box: config.has_opacity_box,
        nested_metadata_boxes: config.nested_metadata_boxes,
    }
}

#[verifier::opaque]
pub open spec fn part2_inspection_layer(
    input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>, index: usize,
) -> Result<Part2LayerInspection, crate::DecodeError> {
    let config = if input.layers.len() == 0 {
        Part2InspectionLayerConfig { grid: (1, 1), registrations: Seq::empty(),
            has_color_group: false, has_opacity_box: false, nested_metadata_boxes: 0 }
    } else { input.layers[index as int] };
    if config.registrations.len() == 0 {
        if index as nat > u16::MAX as nat { Err(part2_composition_error(true)) }
        else if index >= geometries.len() { Err(part2_composition_error(false)) }
        else { Ok(part2_inspection_layer_value(index, config,
            (seq![index as u16], geometries[index as int].0, geometries[index as int].1))) }
    } else {
        match part2_inspection_registration_prefix(config, geometries, config.registrations.len()) {
            Err(error) => Err(error),
            Ok(source) => Ok(part2_inspection_layer_value(index, config, source)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_inspection_layers_prefix(
    input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>, count: nat,
) -> Result<Seq<Part2LayerInspection>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_inspection_layers_prefix(input, geometries, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_inspection_layer(input, geometries, (count - 1) as usize) {
                Err(error) => Err(error), Ok(layer) => Ok(previous.push(layer)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_inspection_duration_prefix(frames: Seq<Part2Frame>, count: nat)
    -> Result<u64, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(0) }
    else {
        match part2_inspection_duration_prefix(frames, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let next = previous as nat + frames[count - 1].2 as nat;
                if next > u64::MAX as nat { Err(part2_composition_error(true)) } else { Ok(next as u64) }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_inspection_composition(
    input: Part2InspectionFileInput, maximum_frames: u32,
) -> Result<Option<Part2CompositionInspection>, crate::DecodeError> {
    match input.composition {
        None => Ok(None),
        Some(composition) => match part2_build_timeline(composition.sets,
            part2_inspection_layer_count(input) as usize, maximum_frames) {
            Err(error) => Err(error),
            Ok(frames) => match part2_inspection_duration_prefix(frames, frames.len()) {
                Err(error) => Err(error),
                Ok(total) => {
                    if composition.sets.len() > u32::MAX as nat { Err(part2_composition_error(true)) }
                    else { Ok(Some(Part2CompositionInspection {
                        source: (composition.width, composition.height, composition.loop_count, frames),
                        instruction_sets: composition.sets.len() as u32,
                        total_duration_milliseconds: total, has_unknown_boxes: composition.has_unknown_boxes,
                    })) }
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_inspect_jpx_file(
    input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>, maximum_frames: u32,
) -> Result<Part2JpxInspection, crate::DecodeError> {
    match part2_inspection_layers_prefix(input, geometries, part2_inspection_layer_count(input)) {
        Err(error) => Err(error),
        Ok(layers) => match part2_inspection_composition(input, maximum_frames) {
            Err(error) => Err(error),
            Ok(composition) => Ok(Part2JpxInspection { layers, composition, metadata: input.metadata }),
        },
    }
}

pub(crate) proof fn part2_inspection_registrations_step(
    layer: Part2InspectionLayerConfig, geometries: Seq<(u32, u32)>, count: nat,
)
    ensures part2_inspection_registration_prefix(layer, geometries, count + 1)
        == match part2_inspection_registration_prefix(layer, geometries, count) {
            Err(error) => Err(error),
            Ok(previous) => part2_inspection_registration_step(layer, geometries, count, previous),
        },
{
    reveal(part2_inspection_registration_prefix);
}

pub(crate) proof fn part2_inspection_registrations_error(
    layer: Part2InspectionLayerConfig, geometries: Seq<(u32, u32)>, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_inspection_registration_prefix(layer, geometries, count) {
        Err(error) => part2_inspection_registration_prefix(layer, geometries, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_inspection_registration_prefix);
    if count < total {
        part2_inspection_registrations_error(layer, geometries, count, (total - 1) as nat);
    }
}

pub(crate) proof fn part2_inspection_layers_step(
    input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>, count: nat,
)
    ensures part2_inspection_layers_prefix(input, geometries, count + 1)
        == match part2_inspection_layers_prefix(input, geometries, count) {
            Err(error) => Err(error),
            Ok(previous) => match part2_inspection_layer(input, geometries, count as usize) {
                Err(error) => Err(error), Ok(layer) => Ok(previous.push(layer)),
            },
        },
{
    reveal(part2_inspection_layers_prefix);
}

pub(crate) proof fn part2_inspection_layers_error(
    input: Part2InspectionFileInput, geometries: Seq<(u32, u32)>, count: nat, total: nat,
)
    requires count <= total,
    ensures match part2_inspection_layers_prefix(input, geometries, count) {
        Err(error) => part2_inspection_layers_prefix(input, geometries, total) == Err(error),
        Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_inspection_layers_prefix);
    if count < total {
        part2_inspection_layers_error(input, geometries, count, (total - 1) as nat);
    }
}

pub(crate) proof fn part2_inspection_durations_step(frames: Seq<Part2Frame>, count: nat)
    ensures part2_inspection_duration_prefix(frames, count + 1)
        == match part2_inspection_duration_prefix(frames, count) {
            Err(error) => Err(error),
            Ok(previous) => {
                let next = previous as nat + frames[count as int].2 as nat;
                if next > u64::MAX as nat { Err(part2_composition_error(true)) } else { Ok(next as u64) }
            },
        },
{
    reveal(part2_inspection_duration_prefix);
}

pub(crate) proof fn part2_inspection_durations_error(frames: Seq<Part2Frame>, count: nat, total: nat)
    requires count <= total,
    ensures match part2_inspection_duration_prefix(frames, count) {
        Err(error) => part2_inspection_duration_prefix(frames, total) == Err(error), Ok(_) => true,
    },
    decreases total - count,
{
    reveal(part2_inspection_duration_prefix);
    if count < total {
        part2_inspection_durations_error(frames, count, (total - 1) as nat);
    }
}

}
