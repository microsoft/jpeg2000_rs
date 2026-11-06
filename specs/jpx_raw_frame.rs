//! Raw source composition into the checked source-derived frame renderer.

use super::*;

verus! {

pub open spec fn part2_raw_associated_header(header: Part2RawJp2Header) -> Part2AssociatedHeader {
    ((header.palette, Seq::new(header.mappings.len(), |i: int|
        (header.mappings[i].component, header.mappings[i].mapping_type)), header.definitions),
        header.image, header.color.0)
}

pub open spec fn part2_raw_codestream_source(stream: Part2RawCodestream) -> Part2CodestreamSource {
    (stream.1, stream.0.1, match stream.2 {
        None => None,
        Some(association) => Some((association.0.1, match association.2 {
            None => None, Some(header) => Some(part2_raw_associated_header(header)),
        })),
    })
}

pub open spec fn part2_raw_jpx_decode_input(file: Part2RawJp2File) -> Part2JpxDecodeInput {
    (file.file_type, Seq::new(file.streams.len(), |i: int| part2_raw_codestream_source(file.streams[i])),
        part2_raw_associated_header(file.header))
}

pub open spec fn part2_raw_layer_routing(file: Part2RawJp2File, layer: Part2RawCompositingLayer) -> Part2LayerRoutingConfig {
    let color = if layer.colors.len() == 0 { None } else { Some(layer.colors[0].0) };
    (Part2GeneralLayerConfig {
        color: match color { None => file.header.color.0, Some(value) => value },
        horizontal_grid: layer.horizontal, vertical_grid: layer.vertical,
        registrations: layer.registrations, definitions: layer.definitions, opacity: layer.opacity,
    }, color, (layer.header.1, layer.horizontal, layer.vertical))
}

pub open spec fn part2_raw_layer_routings(file: Part2RawJp2File) -> Seq<Part2LayerRoutingConfig> {
    Seq::new(file.layers.len(), |i: int| part2_raw_layer_routing(file, file.layers[i]))
}

pub closed spec fn part2_render_raw_jpx_layer(input: Seq<u8>, requested: usize, limits: &crate::ResourceLimits)
    -> Part2ConvertedImageResult
{
    match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => match part2_decode_effective_layer(part2_raw_jpx_decode_input(inspected.0),
                part2_raw_layer_routings(inspected.0), requested, limits) {
                Err(error) => Err(error),
                Ok(owned) => part2_owned_layer_image(owned),
            },
        },
    }
}

pub(crate) proof fn part2_render_raw_jpx_layer_unfold(input: Seq<u8>, requested: usize, limits: &crate::ResourceLimits)
    ensures part2_render_raw_jpx_layer(input, requested, limits) == match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => match part2_decode_effective_layer(part2_raw_jpx_decode_input(inspected.0),
                part2_raw_layer_routings(inspected.0), requested, limits) {
                Err(error) => Err(error),
                Ok(owned) => part2_owned_layer_image(owned),
            },
        },
    },
{
}

pub closed spec fn part2_render_raw_jpx_frame(input: Seq<u8>, requested: usize, limits: &crate::ResourceLimits)
    -> Part2ConvertedImageResult
{
    match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => match part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)) {
                Err(error) => Err(error),
                Ok(metadata) => part2_render_inspected_source_frame(part2_raw_jpx_decode_input(inspected.0),
                    part2_raw_layer_routings(inspected.0),
                    match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits),
            },
        },
    }
}

pub(crate) proof fn part2_render_raw_jpx_frame_unfold(input: Seq<u8>, requested: usize, limits: &crate::ResourceLimits)
    ensures part2_render_raw_jpx_frame(input, requested, limits) == match part2_parse_and_inspect_container(input, limits) {
        Err(error) => Err(error),
        Ok(inspected) => match part2_ensure_raw_jpx(inspected.0.file_type) {
            Err(error) => Err(error),
            Ok(()) => match part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)) {
                Err(error) => Err(error),
                Ok(metadata) => part2_render_inspected_source_frame(part2_raw_jpx_decode_input(inspected.0),
                    part2_raw_layer_routings(inspected.0),
                    match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits),
            },
        },
    },
{
}

}
