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

pub(crate) open spec fn part2_render_after_inspection_cold(
    inspected: Part2RawInspectedContainer, kind: u8, requested: usize, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    match part2_ensure_raw_jpx(inspected.0.file_type) {
        Err(error) => Some((Err(error), events)),
        Ok(()) => {
            let file = part2_raw_jpx_decode_input(inspected.0);
            let layers = part2_raw_layer_routings(inspected.0);
            if kind == 0 {
                part2_jpip_snapshot_bind(part2_effective_layer_cold_run(file, layers, requested, limits, events),
                    |owned, tail| Some((part2_owned_layer_image(owned), tail)))
            } else {
                part2_jpip_snapshot_bind(part2_inspect_file_cold_run(part2_raw_inspection_file(inspected.0),
                    part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits), events),
                    |metadata: Part2JpxInspection, rest| if kind == 1 {
                        part2_render_inspected_cold_run(file, layers,
                            match metadata.composition { None => None, Some(value) => Some(value.source) },
                            requested, limits, rest)
                    } else { part2_render_composition_cold_run(file, layers, metadata, limits, rest) })
            }
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_render_raw_jpx_cold_run(
    input: Seq<u8>, kind: u8, requested: usize, limits: &crate::ResourceLimits,
    events: Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<Part2ConvertedImage> {
    part2_jpip_snapshot_bind(part2_inspection_cold_run(input, limits, false, events),
        |inspected, tail| part2_render_after_inspection_cold(inspected, kind, requested, limits, tail))
}

pub closed spec fn part2_render_raw_jpx_cold_result(
    input: Seq<u8>, kind: u8, requested: usize, limits: &crate::ResourceLimits, result: Part2ConvertedImageResult,
) -> bool {
    part2_cold_framed(|events| part2_render_raw_jpx_cold_run(input, kind, requested, limits, events), result)
}

pub(crate) open spec fn part2_render_after_inspection_normal(
    inspected: Part2RawInspectedContainer, kind: u8, requested: usize, limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    match part2_ensure_raw_jpx(inspected.0.file_type) {
        Err(error) => Err(error),
        Ok(()) => {
            let file = part2_raw_jpx_decode_input(inspected.0);
            let layers = part2_raw_layer_routings(inspected.0);
            if kind == 0 {
                match part2_decode_effective_layer(file, layers, requested, limits) {
                    Err(error) => Err(error), Ok(owned) => part2_owned_layer_image(owned),
                }
            } else {
                match part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                    part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits)) {
                    Err(error) => Err(error),
                    Ok(metadata) => if kind == 1 {
                        part2_render_inspected_source_frame(file, layers,
                            match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits)
                    } else { part2_render_source_composition(file, layers, metadata, limits) },
                }
            }
        },
    }
}

pub(crate) proof fn part2_render_after_inspection_cold_normal(
    inspected: Part2RawInspectedContainer, kind: u8, requested: usize, limits: &crate::ResourceLimits,
)
    ensures part2_cold_framed(
        |events| part2_render_after_inspection_cold(inspected, kind, requested, limits, events),
        part2_render_after_inspection_normal(inspected, kind, requested, limits)),
        forall|run: spec_fn(Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part2ConvertedImage>|
            (forall|events: Seq<Part2JpipSnapshotEvent>| #[trigger] run(events)
                == part2_render_after_inspection_cold(inspected, kind, requested, limits, events))
                ==> #[trigger] part2_cold_framed(run,
                    part2_render_after_inspection_normal(inspected, kind, requested, limits)),
{
    match part2_ensure_raw_jpx(inspected.0.file_type) {
        Err(error) => { part2_cold_pure::<Part2ConvertedImage>(Err(error)); },
        Ok(()) => {
            let file = part2_raw_jpx_decode_input(inspected.0);
            let layers = part2_raw_layer_routings(inspected.0);
            if kind == 0 {
                let owned = part2_decode_effective_layer(file, layers, requested, limits);
                part2_effective_layer_cold_normal(file, layers, requested, limits);
                if let Ok(value) = owned { part2_cold_pure(part2_owned_layer_image(value)); }
                part2_cold_bind(
                    |events| part2_effective_layer_cold_run(file, layers, requested, limits, events),
                    |value, tail| Some((part2_owned_layer_image(value), tail)),
                    owned, part2_render_after_inspection_normal(inspected, kind, requested, limits));
            } else {
                let metadata = part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0),
                    part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits));
                part2_inspect_file_cold_normal(part2_raw_inspection_file(inspected.0),
                    part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits));
                match metadata {
                    Err(_) => {},
                    Ok(metadata) => if kind == 1 {
                        let composition = match metadata.composition { None => None, Some(value) => Some(value.source) };
                        part2_render_inspected_cold_normal(file, layers, composition, requested, limits);
                        part2_cold_framed_extensional(
                            |events| part2_render_inspected_cold_run(file, layers, composition, requested, limits, events),
                            |events| if kind == 1 { part2_render_inspected_cold_run(file, layers,
                                match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, events) }
                                else { part2_render_composition_cold_run(file, layers, metadata, limits, events) },
                            part2_render_after_inspection_normal(inspected, kind, requested, limits));
                    } else {
                        part2_render_composition_cold_normal(file, layers, metadata, limits);
                        part2_cold_framed_extensional(
                            |events| part2_render_composition_cold_run(file, layers, metadata, limits, events),
                            |events| if kind == 1 { part2_render_inspected_cold_run(file, layers,
                                match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, events) }
                                else { part2_render_composition_cold_run(file, layers, metadata, limits, events) },
                            part2_render_after_inspection_normal(inspected, kind, requested, limits));
                    },
                }
                part2_cold_bind(
                    |events| part2_inspect_file_cold_run(part2_raw_inspection_file(inspected.0),
                        part2_raw_inspection_geometries(inspected.1), crate::limits::resource_frame_limit(limits), events),
                    |metadata: Part2JpxInspection, rest| if kind == 1 {
                        part2_render_inspected_cold_run(file, layers,
                            match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, rest)
                    } else { part2_render_composition_cold_run(file, layers, metadata, limits, rest) },
                    metadata, part2_render_after_inspection_normal(inspected, kind, requested, limits));
            }
        },
    }
}

pub(crate) open spec fn part2_render_raw_normal(
    input: Seq<u8>, kind: u8, requested: usize, limits: &crate::ResourceLimits,
) -> Part2ConvertedImageResult {
    if kind == 0 { part2_render_raw_jpx_layer(input, requested, limits) }
    else if kind == 1 { part2_render_raw_jpx_frame(input, requested, limits) }
    else { part2_render_raw_jpx_composition(input, limits) }
}

pub(crate) proof fn part2_render_raw_jpx_cold_normal(
    input: Seq<u8>, kind: u8, requested: usize, limits: &crate::ResourceLimits,
)
    ensures part2_render_raw_jpx_cold_result(input, kind, requested, limits,
        part2_render_raw_normal(input, kind, requested, limits)),
{
    reveal(part2_render_raw_jpx_cold_result);
    reveal(part2_render_raw_jpx_cold_run);
    part2_render_raw_jpx_layer_unfold(input, requested, limits);
    part2_render_raw_jpx_frame_unfold(input, requested, limits);
    part2_render_raw_jpx_composition_unfold(input, limits);
    let inspected = part2_parse_and_inspect_container(input, limits);
    part2_parse_and_inspect_container_unfold(input, limits);
    part2_inspection_cold_normal(input, limits, false);
    part2_inspection_cold_frames(input, limits, false, inspected);
    if let Ok(value) = inspected { part2_render_after_inspection_cold_normal(value, kind, requested, limits); }
    part2_cold_bind(
        |events| part2_inspection_cold_run(input, limits, false, events),
        |value, tail| part2_render_after_inspection_cold(value, kind, requested, limits, tail),
        inspected, part2_render_raw_normal(input, kind, requested, limits));
}

pub(crate) proof fn part2_render_raw_cold_inspection_error(
    input: Seq<u8>, kind: u8, requested: usize, limits: &crate::ResourceLimits, error: crate::DecodeError,
)
    requires part2_inspection_cold_result(input, limits, false, Err(error)),
    ensures part2_render_raw_jpx_cold_result(input, kind, requested, limits, Err(error)),
{
    reveal(part2_render_raw_jpx_cold_result);
    reveal(part2_render_raw_jpx_cold_run);
    part2_inspection_cold_frames(input, limits, false, Err(error));
    part2_cold_bind(
        |events| part2_inspection_cold_run(input, limits, false, events),
        |value, tail| part2_render_after_inspection_cold(value, kind, requested, limits, tail), Err(error), Err(error));
}

pub(crate) proof fn part2_render_raw_cold_layer_actual(
    input: Seq<u8>, requested: usize, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer, owned: Part2OwnedLayerResult,
)
    requires part2_inspection_cold_result(input, limits, false, Ok(inspected)),
        part2_ensure_raw_jpx(inspected.0.file_type) == Ok(()),
        part2_effective_layer_cold_result(part2_raw_jpx_decode_input(inspected.0),
            part2_raw_layer_routings(inspected.0), requested, limits, owned),
    ensures part2_render_raw_jpx_cold_result(input, 0, requested, limits, match owned {
        Err(error) => Err(error), Ok(value) => part2_owned_layer_image(value),
    }),
{
    reveal(part2_render_raw_jpx_cold_result);
    reveal(part2_render_raw_jpx_cold_run);
    let result = match owned { Err(error) => Err(error), Ok(value) => part2_owned_layer_image(value) };
    if let Ok(value) = owned { part2_cold_pure(part2_owned_layer_image(value)); }
    part2_cold_bind(
        |events| part2_effective_layer_cold_run(part2_raw_jpx_decode_input(inspected.0),
            part2_raw_layer_routings(inspected.0), requested, limits, events),
        |value, tail| Some((part2_owned_layer_image(value), tail)), owned, result);
    part2_inspection_cold_frames(input, limits, false, Ok(inspected));
    part2_cold_bind(
        |events| part2_inspection_cold_run(input, limits, false, events),
        |value, tail| part2_render_after_inspection_cold(value, 0, requested, limits, tail), Ok(inspected), result);
}

pub(crate) proof fn part2_render_raw_cold_final_actual(
    input: Seq<u8>, kind: u8, requested: usize, limits: &crate::ResourceLimits,
    inspected: Part2RawInspectedContainer, metadata: Part2JpxInspection, result: Part2ConvertedImageResult,
)
    requires kind != 0, part2_inspection_cold_result(input, limits, false, Ok(inspected)),
        part2_ensure_raw_jpx(inspected.0.file_type) == Ok(()),
        part2_inspect_jpx_file(part2_raw_inspection_file(inspected.0), part2_raw_inspection_geometries(inspected.1),
            crate::limits::resource_frame_limit(limits)) == Ok(metadata),
        if kind == 1 {
            part2_render_inspected_cold_result(part2_raw_jpx_decode_input(inspected.0), part2_raw_layer_routings(inspected.0),
                match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, result)
        } else {
            part2_render_composition_cold_result(part2_raw_jpx_decode_input(inspected.0),
                part2_raw_layer_routings(inspected.0), metadata, limits, result)
        },
    ensures part2_render_raw_jpx_cold_result(input, kind, requested, limits, result),
{
    reveal(part2_render_raw_jpx_cold_result);
    reveal(part2_render_raw_jpx_cold_run);
    let file = part2_raw_jpx_decode_input(inspected.0);
    let layers = part2_raw_layer_routings(inspected.0);
    part2_inspect_file_cold_normal(part2_raw_inspection_file(inspected.0), part2_raw_inspection_geometries(inspected.1),
        crate::limits::resource_frame_limit(limits));
    if kind == 1 {
        let composition = match metadata.composition { None => None, Some(value) => Some(value.source) };
        assert(part2_render_inspected_cold_result(file, layers, composition, requested, limits, result));
        reveal(part2_render_inspected_cold_result);
        assert(part2_cold_framed(
            |events| part2_render_inspected_cold_run(file, layers, composition, requested, limits, events), result));
        part2_cold_framed_extensional(
            |events| part2_render_inspected_cold_run(file, layers, composition, requested, limits, events),
            |events| if kind == 1 { part2_render_inspected_cold_run(file, layers,
                match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, events) }
                else { part2_render_composition_cold_run(file, layers, metadata, limits, events) }, result);
    } else {
        part2_cold_framed_extensional(
            |events| part2_render_composition_cold_run(file, layers, metadata, limits, events),
            |events| if kind == 1 { part2_render_inspected_cold_run(file, layers,
                match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, events) }
                else { part2_render_composition_cold_run(file, layers, metadata, limits, events) }, result);
    }
    part2_cold_bind(
        |events| part2_inspect_file_cold_run(part2_raw_inspection_file(inspected.0), part2_raw_inspection_geometries(inspected.1),
            crate::limits::resource_frame_limit(limits), events),
        |metadata: Part2JpxInspection, rest| if kind == 1 {
            part2_render_inspected_cold_run(file, layers, match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, rest)
        } else { part2_render_composition_cold_run(file, layers, metadata, limits, rest) },
        Ok(metadata), result);
    part2_inspection_cold_frames(input, limits, false, Ok(inspected));
    part2_cold_bind(
        |events| part2_inspection_cold_run(input, limits, false, events),
        |value, tail| part2_render_after_inspection_cold(value, kind, requested, limits, tail), Ok(inspected), result);
}

pub(crate) proof fn part2_render_raw_cold_metadata_error(input: Seq<u8>, kind: u8, requested: usize,
    limits: &crate::ResourceLimits, inspected: Part2RawInspectedContainer, error: crate::DecodeError)
    requires kind != 0, part2_inspection_cold_result(input, limits, false, Ok(inspected)),
        part2_ensure_raw_jpx(inspected.0.file_type) == Ok(()),
        part2_inspect_file_cold_result(part2_raw_inspection_file(inspected.0), part2_raw_inspection_geometries(inspected.1),
            crate::limits::resource_frame_limit(limits), Err(error)),
    ensures part2_render_raw_jpx_cold_result(input, kind, requested, limits, Err(error)),
{
    reveal(part2_render_raw_jpx_cold_result); reveal(part2_render_raw_jpx_cold_run);
    let file = part2_raw_jpx_decode_input(inspected.0); let layers = part2_raw_layer_routings(inspected.0);
    part2_inspect_file_cold_frames(part2_raw_inspection_file(inspected.0), part2_raw_inspection_geometries(inspected.1),
        crate::limits::resource_frame_limit(limits), Err(error));
    part2_cold_bind(
        |events| part2_inspect_file_cold_run(part2_raw_inspection_file(inspected.0), part2_raw_inspection_geometries(inspected.1),
            crate::limits::resource_frame_limit(limits), events),
        |metadata: Part2JpxInspection, rest| if kind == 1 {
            part2_render_inspected_cold_run(file, layers, match metadata.composition { None => None, Some(value) => Some(value.source) }, requested, limits, rest)
        } else { part2_render_composition_cold_run(file, layers, metadata, limits, rest) }, Err(error), Err(error));
    part2_inspection_cold_frames(input, limits, false, Ok(inspected));
    part2_cold_bind(|events| part2_inspection_cold_run(input, limits, false, events),
        |value, rest| part2_render_after_inspection_cold(value, kind, requested, limits, rest), Ok(inspected), Err(error));
}

}
