//! Raw source composition into the executing JPX inspector and timeline.

use super::*;

verus! {

pub open spec fn part2_raw_timeline_instruction(value: crate::jp2::CompositionInstruction) -> Part2TimelineInstruction {
    ((0, value.target_x, value.target_y, value.target_width, value.target_height,
        value.source_x, value.source_y, value.source_width, value.source_height,
        value.persistent, value.next_reuse), value.life)
}

pub open spec fn part2_raw_timeline_sets(sets: Seq<Part2RawInstructionSet>) -> Seq<Part2TimelineSet> {
    Seq::new(sets.len(), |i: int|
        (sets[i].1, Seq::new(sets[i].3.len(), |j: int| part2_raw_timeline_instruction(sets[i].3[j]))))
}

pub open spec fn part2_raw_inspection_layer(layer: Part2RawCompositingLayer) -> Part2InspectionLayerConfig {
    Part2InspectionLayerConfig {
        grid: (layer.horizontal, layer.vertical), registrations: layer.registrations,
        has_color_group: layer.colors.len() > 0, has_opacity_box: layer.opacity.is_some(),
        nested_metadata_boxes: layer.nested_metadata,
    }
}

pub open spec fn part2_raw_inspection_composition(composition: Part2RawComposition) -> Part2InspectionCompositionConfig {
    Part2InspectionCompositionConfig {
        width: composition.0, height: composition.1, loop_count: composition.2,
        sets: part2_raw_timeline_sets(composition.3), has_unknown_boxes: composition.4,
    }
}

pub open spec fn part2_raw_inspection_file(file: Part2RawJp2File) -> Part2InspectionFileInput {
    Part2InspectionFileInput {
        layers: Seq::new(file.layers.len(), |i: int| part2_raw_inspection_layer(file.layers[i])),
        codestreams: file.streams.len() as usize,
        composition: match file.composition { None => None, Some(value) => Some(part2_raw_inspection_composition(value)) },
        metadata: (file.metadata_boxes, file.metadata_depth),
    }
}

pub(crate) open spec fn part2_raw_inspection_geometries(infos: Seq<Part2RawCodestreamInfo>) -> Seq<(u32, u32)> {
    Seq::new(infos.len(), |i: int| (infos[i].0.image_size.geometry.0, infos[i].0.image_size.geometry.1))
}

pub open spec fn part2_ensure_raw_jpx(file_type: Part2FileType) -> Result<(), crate::DecodeError> {
    if part2_file_type_jpx(file_type) { Ok(()) }
    else { Err(part2_container_error(0, crate::MalformedKind::InvalidProfile)) }
}

pub closed spec fn part2_inspect_raw_jpx_layers(input: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part2JpxInspection, crate::DecodeError>
{
    match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)),
        },
    }
}

pub(crate) proof fn part2_inspect_raw_jpx_layers_unfold(input: Seq<u8>, limits: &crate::ResourceLimits)
    ensures part2_inspect_raw_jpx_layers(input, limits) == match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)),
        },
    },
{
}

}
