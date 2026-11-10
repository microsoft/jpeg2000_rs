use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;

mod mq;
pub use mq::*;
mod legacy;
pub use legacy::*;
mod packet;
pub use packet::*;
mod packet_orchestration;
pub use packet_orchestration::*;
mod packet_progression;
pub use packet_progression::*;
mod packet_tile;
pub use packet_tile::*;
mod packet_boundaries;
pub use packet_boundaries::*;
mod header;
pub use header::*;
mod tag_tree;
pub use tag_tree::*;
mod packet_input;
pub use packet_input::*;
mod layout_input;
pub use layout_input::*;
mod tile_header_traversal;
pub use tile_header_traversal::*;
mod tile_part;
pub use tile_part::*;
mod persistent_tile_configuration;
pub use persistent_tile_configuration::*;
mod codestream_profile;
pub use codestream_profile::*;
mod main_header;
pub use main_header::*;
mod raw_layout;
pub use raw_layout::*;
mod decoder_input;
pub use decoder_input::*;
mod raw_decode;
pub use raw_decode::*;
mod container_images;
pub use container_images::*;
mod container_colors;
pub use container_colors::*;
mod jpx_public_images;
pub use jpx_public_images::*;
mod jpip_message;
pub use jpip_message::*;
mod jpip_fragment;
pub use jpip_fragment::*;
mod jpip_cache_views;
pub use jpip_cache_views::*;
mod jpip_cache_insert;
pub use jpip_cache_insert::*;
mod jpip_layout;
pub use jpip_layout::*;
mod jpip_response;
pub use jpip_response::*;
mod jpip_ranges;
pub use jpip_ranges::*;
mod jpip_planned_packets;
pub use jpip_planned_packets::*;
mod jpip_transcode;
pub use jpip_transcode::*;
mod jpx_source;
pub use jpx_source::*;
mod jpx_opacity;
pub use jpx_opacity::*;
mod jpx_normalization;
pub use jpx_normalization::*;
mod jpx_general;
pub use jpx_general::*;
mod jpx_dispatch;
pub use jpx_dispatch::*;
mod jpx_frame;
pub use jpx_frame::*;
mod jpx_inspection;
pub use jpx_inspection::*;
mod jpx_raw_inspection;
pub use jpx_raw_inspection::*;
mod jpx_raw_frame;
pub use jpx_raw_frame::*;
mod jpx_raw_composition;
pub use jpx_raw_composition::*;
mod jp2_box_reader;
pub use jp2_box_reader::*;
mod jp2_file_type;
pub use jp2_file_type::*;
mod jp2_image_header;
pub use jp2_image_header::*;
mod jp2_color_header;
pub use jp2_color_header::*;
mod jp2_channel_header;
pub use jp2_channel_header::*;
mod jp2_resolution;
pub use jp2_resolution::*;
mod jp2_palette;
pub use jp2_palette::*;
mod jp2_header;
pub use jp2_header::*;
mod jp2_associated_header;
pub use jp2_associated_header::*;
mod jp2_metadata;
pub use jp2_metadata::*;
mod jp2_layer;
pub use jp2_layer::*;
mod jp2_composition;
pub use jp2_composition::*;
mod jp2_container;
pub use jp2_container::*;
mod jp2_inspection;
pub use jp2_inspection::*;

pub use crate::proofs::internal_specs::{
    part2_composition_layer_prefix_matches, part2_composition_layer_prefix_safe,
};

verus! {

pub type Part2ExecutionHeader = (
    crate::codestream::ComponentCodingStyles, (Seq<u8>, Seq<u8>),
    Seq<(u8, Part2RawKernel)>, Seq<(u8, bool)>,
);

pub open spec fn part2_validate_execution_component(header: Part2ExecutionHeader, component: u16)
    -> Result<(), crate::DecodeError>
{
    match crate::codestream::component_coding_style_result(&header.0, component) {
        Err(error) => Err(error),
        Ok(style) => part2_validate_execution_style(style, header.1, header.2),
    }
}

#[verifier::opaque]
pub open spec fn part2_execution_components_prefix(header: Part2ExecutionHeader, count: nat)
    -> Result<(), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(()) }
    else {
        match part2_execution_components_prefix(header, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => part2_validate_execution_component(header, (count - 1) as u16),
        }
    }
}

pub open spec fn part2_validate_execution_tile(header: Part2ExecutionHeader, main_depths: Seq<(u8, bool)>, components: u16)
    -> Result<(), crate::DecodeError>
{
    match part2_execution_components_prefix(header, components as nat) {
        Err(error) => Err(error),
        Ok(()) => if header.3.len() > 0 && !part2_component_depths_equal(header.3, main_depths) {
            Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidMarkerOrder })
        } else { Ok(()) },
    }
}

#[verifier::opaque]
pub open spec fn part2_execution_tiles_prefix(
    headers: Seq<Part2ExecutionHeader>, main_depths: Seq<(u8, bool)>, components: u16, count: nat,
) -> Result<(), crate::DecodeError>
    recommends count <= headers.len(),
    decreases count,
{
    if count == 0 { Ok(()) }
    else {
        match part2_execution_tiles_prefix(headers, main_depths, components, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => part2_validate_execution_tile(headers[(count - 1) as int], main_depths, components),
        }
    }
}

pub open spec fn part2_validate_execution_layout(
    components: u16, main: Part2ExecutionHeader, tiles: Seq<Part2ExecutionHeader>,
) -> Result<(), crate::DecodeError> {
    match part2_execution_components_prefix(main, components as nat) {
        Err(error) => Err(error),
        Ok(()) => part2_execution_tiles_prefix(tiles, main.3, components, tiles.len()),
    }
}

pub open spec fn part2_validate_execution_style(
    style: crate::codestream::CodingStyle, decompositions: (Seq<u8>, Seq<u8>), kernels: Seq<(u8, Part2RawKernel)>,
) -> Result<(), crate::DecodeError> {
    let missing = match style.decomposition_structure {
        None => false,
        Some(index) => !decompositions.0.contains(index) && !decompositions.1.contains(index),
    };
    if missing {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::MissingRequiredStructure })
    } else {
        match style.transform {
            crate::codestream::WaveletTransform::Arbitrary(index) => match part2_kernel_registry_lookup(kernels, index) {
                None => Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::MissingRequiredStructure }),
                Some(_) => Ok(()),
            },
            _ => Ok(()),
        }
    }
}

pub open spec fn part2_component_depths_equal(left: Seq<(u8, bool)>, right: Seq<(u8, bool)>) -> bool {
    left == right
}

pub type Part2MctArray = (u8, crate::codestream::MctArrayKind, crate::codestream::MctNumericFormat, u8, Seq<i64>);
pub type Part2MctWavelet = (crate::codestream::MctWaveletType, u8, i32);
pub type Part2MctCollection = (
    bool, Seq<u16>, Seq<u16>, crate::codestream::MctCollectionKind,
    Option<Part2MctArray>, Option<Part2MctArray>, Option<Part2MctWavelet>,
);
pub type Part2MctStage = (u8, Seq<Part2MctCollection>);
pub type Part2MctComponent = (u16, (u32, u32, u32, u32, u8, u8), u8, Seq<i64>);
pub type Part2MctDecorrelationPreparation = (Seq<usize>, Seq<usize>, Seq<u8>, usize, usize, usize);
pub type Part2MctDependencyPreparation = (Seq<usize>, Seq<usize>, usize, usize);
pub type Part2MctWaveletPreparation = (
    Seq<usize>, Seq<usize>, Seq<bool>, Seq<usize>, usize, usize, usize, Part2MctWavelet, Seq<u8>,
);
pub type Part2MctWaveletInterval = (i64, i64, Seq<bool>, Seq<usize>);

#[verifier::opaque]
pub open spec fn part2_kernel_registry_prefix(kernels: Seq<(u8, Part2RawKernel)>, index: u8, count: nat) -> Option<Part2RawKernel>
    decreases count,
{
    if count == 0 { None }
    else {
        let previous = part2_kernel_registry_prefix(kernels, index, (count - 1) as nat);
        match previous {
            Some(_) => previous,
            None => if count - 1 >= kernels.len() { None }
                else if kernels[count as int - 1].0 == index { Some(kernels[count as int - 1].1) } else { None },
        }
    }
}

pub open spec fn part2_kernel_registry_lookup(kernels: Seq<(u8, Part2RawKernel)>, index: u8) -> Option<Part2RawKernel> {
    part2_kernel_registry_prefix(kernels, index, kernels.len())
}

pub open spec fn part2_reconstruct_component(
    plan: Part1PreparePlan, precincts: Seq<Seq<Tier1RawPlane>>, styles: crate::codestream::ComponentCodingStyles,
    kernels: Seq<(u8, Part2RawKernel)>, maximum_bytes: u64,
) -> Result<Part1AssemblyTile, crate::DecodeError> {
    match crate::codestream::component_coding_style_result(&styles, plan.component) {
        Err(error) => Err(error),
        Ok(style) => {
            let kernel = match style.transform {
                crate::codestream::WaveletTransform::Arbitrary(index) => part2_kernel_registry_lookup(kernels, index),
                _ => None,
            };
            part2_prepare_component(plan, precincts, crate::decode::prepare_style_view(style), kernel, maximum_bytes)
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_reconstruct_components_prefix(
    initial: Seq<Part1AssemblyTile>, plans: Seq<Part1PreparePlan>, precincts: Seq<Seq<Tier1RawPlane>>,
    styles: crate::codestream::ComponentCodingStyles, kernels: Seq<(u8, Part2RawKernel)>, maximum_bytes: u64, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>)
    decreases count,
{
    if count == 0 { (Ok(()), initial) }
    else {
        let previous = part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum_bytes, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 >= plans.len() { (Err(part1_block_placement_error(false)), previous.1) }
                else { match part2_reconstruct_component(plans[count as int - 1], precincts, styles, kernels, maximum_bytes) {
                    Err(error) => (Err(error), previous.1), Ok(component) => (Ok(()), previous.1.push(component)),
                } },
        }
    }
}

pub open spec fn part2_finish_prepared_tile(
    before: Seq<Part1AssemblyTile>, component_count: u16, infos: Seq<crate::codestream::ComponentInfo>,
    mct: Option<Seq<Part2MctStage>>, standard: (bool, bool), work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>, u64) {
    let transformed = match mct {
        None => (Ok(()), before, work),
        Some(stages) => part2_mct_prepared_tiles(before, component_count, infos, stages, work, maximum_work, maximum_bytes),
    };
    match transformed.0 {
        Err(_) => transformed,
        Ok(()) => {
            let standard_result = part1_prepared_standard_transform(transformed.1, standard);
            (standard_result.0, standard_result.1, transformed.2)
        },
    }
}

pub open spec fn part2_reconstruct_planned_tile(
    initial: Seq<Part1AssemblyTile>, plans: Seq<Part1PreparePlan>, precincts: Seq<Seq<Tier1RawPlane>>,
    styles: crate::codestream::ComponentCodingStyles, kernels: Seq<(u8, Part2RawKernel)>,
    component_count: u16, infos: Seq<crate::codestream::ComponentInfo>, mct: Option<Seq<Part2MctStage>>,
    standard: (bool, bool), work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>, u64) {
    let prepared = part2_reconstruct_components_prefix(initial, plans, precincts, styles, kernels, maximum_bytes, plans.len());
    match prepared.0 {
        Err(error) => (Err(error), prepared.1, work),
        Ok(()) => {
            let finished = part2_finish_prepared_tile(prepared.1.skip(initial.len() as int),
                component_count, infos, mct, standard, work, maximum_work, maximum_bytes);
            (finished.0, initial + finished.1, finished.2)
        },
    }
}

pub open spec fn part1_decode_prepared_image(
    size: Part1AssemblySize, tiles: Seq<Part1AssemblyTile>, transform: crate::decode::ComponentTransform, maximum: u64,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part1_assemble_image(size, tiles, maximum) {
        Err(error) => Err(error),
        Ok(image) => {
            let transformed = match transform {
                crate::decode::ComponentTransform::None => (Ok(()), image),
                crate::decode::ComponentTransform::Reversible => part1_apply_component_transform(image, false),
                crate::decode::ComponentTransform::Irreversible => part1_apply_component_transform(image, true),
            };
            match transformed.0 { Err(error) => Err(error), Ok(()) => Ok(transformed.1) }
        },
    }
}

pub open spec fn part2_assemble_prepared(
    size: Part1AssemblySize, prepared: Seq<Part1AssemblyTile>, selection: Option<([u32; 4], u8)>, maximum: u64,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match selection {
        None => part1_assemble_image(size, prepared, maximum),
        Some((region, levels)) => part1_assemble_selected_image(size, prepared, region, levels, maximum),
    }
}

pub open spec fn part1_progression_prepared_image(
    size: Part1AssemblySize, plans: Seq<Part1PreparePlan>, precincts: Seq<Seq<Tier1RawPlane>>,
    styles: crate::codestream::ComponentCodingStyles, global: crate::codestream::CodingStyle, maximum: u64,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    let prepared = part2_reconstruct_components_prefix(Seq::empty(), plans, precincts, styles, Seq::empty(), maximum, plans.len());
    match prepared.0 {
        Err(error) => Err(error),
        Ok(()) => if !global.multiple_component_transform {
            part1_decode_prepared_image(size, prepared.1, crate::decode::ComponentTransform::None, maximum)
        } else { match global.transform {
            crate::codestream::WaveletTransform::Reversible5x3 =>
                part1_decode_prepared_image(size, prepared.1, crate::decode::ComponentTransform::Reversible, maximum),
            crate::codestream::WaveletTransform::Irreversible9x7 =>
                part1_decode_prepared_image(size, prepared.1, crate::decode::ComponentTransform::Irreversible, maximum),
            crate::codestream::WaveletTransform::Arbitrary(_) => Err(crate::DecodeError::MalformedInput {
                offset: 0, kind: crate::MalformedKind::MissingRequiredStructure,
            }),
        } },
    }
}

pub open spec fn part2_mct_decoded_inputs(before: Seq<Part1DecodedComponentModel>) -> Seq<Part2MctComponent> {
    Seq::new(before.len(), |index: int| (index as u16,
        (0u32, 0u32, before[index].0, before[index].1, before[index].2.x_subsampling, before[index].2.y_subsampling),
        before[index].3, before[index].4))
}

pub open spec fn part2_mct_prepared_input(
    before: Part1AssemblyTile, component_count: u16, infos: Seq<crate::codestream::ComponentInfo>,
) -> Result<Part2MctComponent, crate::DecodeError> {
    match part1_image_size_component(component_count, infos, before.0) {
        Err(error) => Err(error),
        Ok(info) => Ok((before.0, (before.1, before.2, before.3, before.4, info.x_subsampling, info.y_subsampling),
            before.5, before.6)),
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_prepared_inputs(
    before: Seq<Part1AssemblyTile>, component_count: u16, infos: Seq<crate::codestream::ComponentInfo>,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>)
    decreases before.len(),
{
    if before.len() == 0 { (Ok(()), Seq::empty()) }
    else { match part2_mct_prepared_input(before[0], component_count, infos) {
        Err(error) => (Err(error), Seq::empty()),
        Ok(component) => {
            let tail = part2_mct_prepared_inputs(before.drop_first(), component_count, infos);
            (tail.0, seq![component] + tail.1)
        },
    } }
}

pub open spec fn part2_mct_prepared_result(before: Seq<Part1AssemblyTile>, transformed: Seq<Part2MctComponent>)
    -> Seq<Part1AssemblyTile> {
    Seq::new(before.len(), |index: int| (before[index].0, before[index].1, before[index].2,
        before[index].3, before[index].4, transformed[index].2, transformed[index].3))
}

pub open spec fn part2_mct_prepared_tiles(
    before: Seq<Part1AssemblyTile>, component_count: u16, infos: Seq<crate::codestream::ComponentInfo>,
    stages: Seq<Part2MctStage>, work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>, u64) {
    let collected = part2_mct_prepared_inputs(before, component_count, infos);
    match collected.0 {
        Err(error) => (Err(error), before, work),
        Ok(()) => {
            let transformed = part2_mct_transform(collected.1, stages, work, maximum_work, maximum_bytes);
            (transformed.0, part2_mct_prepared_result(before, transformed.1), transformed.2)
        },
    }
}

pub open spec fn part1_prepared_standard_admission(before: Seq<Part1AssemblyTile>, irreversible: bool)
    -> Result<usize, crate::DecodeError> {
    if before.len() < 3 { Err(part1_transform_error(false)) }
    else if (before[0].1, before[0].2, before[0].3, before[0].4) != (before[1].1, before[1].2, before[1].3, before[1].4)
        || (before[0].1, before[0].2, before[0].3, before[0].4) != (before[2].1, before[2].2, before[2].3, before[2].4)
        || before[0].6.len() != before[1].6.len() || before[0].6.len() != before[2].6.len()
        || before[0].5 != before[1].5 || before[0].5 != before[2].5
        || (!irreversible && before[0].5 != 0) || (irreversible && before[0].5 != 16) {
        Err(part1_transform_error(false))
    } else { Ok(before[0].6.len() as usize) }
}

pub open spec fn part1_prepared_sample(before: Seq<Part1AssemblyTile>, component: usize, index: usize)
    -> Result<i64, crate::DecodeError> {
    if component >= before.len() || index >= before[component as int].6.len() {
        Err(part1_block_placement_error(false))
    } else { Ok(before[component as int].6[index as int]) }
}

pub open spec fn part1_prepared_store_sample(before: Seq<Part1AssemblyTile>, component: usize, index: usize, value: i64)
    -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>) {
    if component >= before.len() || index >= before[component as int].6.len() {
        (Err(part1_block_placement_error(false)), before)
    } else {
        let entry = before[component as int];
        (Ok(()), before.update(component as int, (entry.0, entry.1, entry.2, entry.3, entry.4, entry.5, entry.6.update(index as int, value))))
    }
}

pub open spec fn part1_prepared_standard_pixel(before: Seq<Part1AssemblyTile>, index: usize, irreversible: bool)
    -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>) {
    match part1_prepared_sample(before, 0, index) {
        Err(error) => (Err(error), before),
        Ok(y) => match part1_prepared_sample(before, 1, index) {
            Err(error) => (Err(error), before),
            Ok(cb) => match part1_prepared_sample(before, 2, index) {
                Err(error) => (Err(error), before),
                Ok(cr) => match part1_component_values(y, cb, cr, irreversible) {
                    Err(error) => (Err(error), before),
                    Ok((red, green, blue)) => {
                        let r = part1_prepared_store_sample(before, 0, index, red);
                        match r.0 { Err(_) => r, Ok(()) => {
                            let g = part1_prepared_store_sample(r.1, 1, index, green);
                            match g.0 { Err(_) => g, Ok(()) => part1_prepared_store_sample(g.1, 2, index, blue) }
                        } }
                    },
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_prepared_standard_prefix(before: Seq<Part1AssemblyTile>, irreversible: bool, count: nat)
    -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>)
    decreases count,
{
    if count == 0 { (Ok(()), before) }
    else {
        let previous = part1_prepared_standard_prefix(before, irreversible, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 > usize::MAX { (Err(part1_transform_error(true)), previous.1) }
                else { part1_prepared_standard_pixel(previous.1, (count - 1) as usize, irreversible) },
        }
    }
}

pub open spec fn part1_prepared_standard_transform(before: Seq<Part1AssemblyTile>, transform: (bool, bool))
    -> (Result<(), crate::DecodeError>, Seq<Part1AssemblyTile>) {
    if !transform.0 { (Ok(()), before) }
    else { match part1_prepared_standard_admission(before, transform.1) {
        Err(error) => (Err(error), before),
        Ok(length) => part1_prepared_standard_prefix(before, transform.1, length as nat),
    } }
}

pub open spec fn part2_mct_decoded_result(
    before: Part1DecodedImageModel, transformed: Seq<Part2MctComponent>,
) -> Part1DecodedImageModel {
    (before.0, before.1, before.2, before.3,
        Seq::new(before.4.len(), |index: int|
            (before.4[index].0, before.4[index].1, before.4[index].2, transformed[index].2, transformed[index].3)))
}

pub open spec fn part2_mct_decoded_image(
    before: Part1DecodedImageModel, stages: Seq<Part2MctStage>, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Part1DecodedImageModel) {
    if before.4.len() > u16::MAX { (Err(part1_transform_error(true)), before) }
    else {
        let transformed = part2_mct_transform(part2_mct_decoded_inputs(before.4), stages, 0, maximum_work, maximum_bytes);
        (transformed.0, part2_mct_decoded_result(before, transformed.1))
    }
}

pub open spec fn part2_mct_collection(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection, work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64) {
    match collection.3 {
        crate::codestream::MctCollectionKind::Dependency => part2_mct_dependency(before, collection, work, maximum_work, maximum_bytes),
        crate::codestream::MctCollectionKind::Decorrelation => part2_mct_decorrelation(before, collection, work, maximum_work, maximum_bytes),
        crate::codestream::MctCollectionKind::Wavelet => part2_mct_wavelet(before, collection, work, maximum_work, maximum_bytes),
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_stage_prefix(
    before: Seq<Part2MctComponent>, collections: Seq<Part2MctCollection>, work: u64,
    maximum_work: u64, maximum_bytes: u64, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64)
    decreases count,
{
    if count == 0 { (Ok(()), before, work) }
    else {
        let previous = part2_mct_stage_prefix(before, collections, work, maximum_work, maximum_bytes, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 >= collections.len() { (Err(part1_transform_error(false)), previous.1, previous.2) }
                else { part2_mct_collection(previous.1, collections[count as int - 1], previous.2, maximum_work, maximum_bytes) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_transform_prefix(
    before: Seq<Part2MctComponent>, stages: Seq<Part2MctStage>, work: u64,
    maximum_work: u64, maximum_bytes: u64, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64)
    decreases count,
{
    if count == 0 { (Ok(()), before, work) }
    else {
        let previous = part2_mct_transform_prefix(before, stages, work, maximum_work, maximum_bytes, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count > stages.len() { (Err(part1_transform_error(false)), previous.1, previous.2) }
                else {
                    let stage = stages[stages.len() - count];
                    part2_mct_stage_prefix(previous.1, stage.1, previous.2, maximum_work, maximum_bytes, stage.1.len())
                },
        }
    }
}

pub open spec fn part2_mct_transform(
    before: Seq<Part2MctComponent>, stages: Seq<Part2MctStage>, work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64) {
    part2_mct_transform_prefix(before, stages, work, maximum_work, maximum_bytes, stages.len())
}

pub open spec fn part2_mct_wavelet_reversible(wavelet: Part2MctWavelet) -> bool {
    matches!(wavelet.0, crate::codestream::MctWaveletType::Reversible5x3)
}

pub open spec fn part2_mct_ceil_half(value: i64) -> Result<i64, crate::DecodeError> {
    let quotient = vstd::arithmetic::div_mod::rust_div(value as int, 2);
    let increment = if vstd::arithmetic::div_mod::rust_rem(value as int, 2) > 0 { 1int } else { 0int };
    let result = quotient + increment;
    if result < i64::MIN || result > i64::MAX { Err(part1_transform_error(true)) }
    else { Ok(result as i64) }
}

pub open spec fn part2_mct_wavelet_interval_step(
    previous: Result<Part2MctWaveletInterval, crate::DecodeError>,
) -> Result<Part2MctWaveletInterval, crate::DecodeError> {
    match previous {
        Err(error) => Err(error),
        Ok((start, end, first, high)) => match part2_mct_ceil_half(start) {
            Err(error) => Err(error),
            Ok(next_start) => match part2_mct_ceil_half(end) {
                Err(error) => Err(error),
                Ok(next_end) => {
                    let low = next_end as int - next_start as int;
                    let current = end as int - start as int;
                    if low < i64::MIN || low > i64::MAX { Err(part1_transform_error(true)) }
                    else if low < 0 || low > usize::MAX { Err(part1_transform_error(false)) }
                    else if current < i64::MIN || current > i64::MAX { Err(part1_transform_error(true)) }
                    else if current < 0 || current > usize::MAX { Err(part1_transform_error(false)) }
                    else if current < low { Err(part1_transform_error(true)) }
                    else { Ok((next_start, next_end,
                        first.push(vstd::arithmetic::div_mod::rust_rem(start as int, 2) == 0),
                        high.push((current - low) as usize))) }
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_wavelet_intervals(start: i64, end: i64, count: nat)
    -> Result<Part2MctWaveletInterval, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((start, end, Seq::empty(), Seq::empty())) }
    else { part2_mct_wavelet_interval_step(part2_mct_wavelet_intervals(start, end, (count - 1) as nat)) }
}

pub open spec fn part2_mct_wavelet_partition(count: usize, wavelet: Part2MctWavelet)
    -> Result<(Seq<bool>, Seq<usize>, usize), crate::DecodeError> {
    let start = wavelet.2 as i64;
    if count > i64::MAX { Err(part1_transform_error(true)) }
    else {
        let end = start as int + count as int;
        if end < i64::MIN || end > i64::MAX { Err(part1_transform_error(true)) }
        else { match part2_mct_wavelet_intervals(start, end as i64, wavelet.1 as nat) {
            Err(error) => Err(error),
            Ok((final_start, final_end, first, high)) => {
                let low = final_end as int - final_start as int;
                if low < i64::MIN || low > i64::MAX { Err(part1_transform_error(true)) }
                else if low < 0 || low > usize::MAX { Err(part1_transform_error(false)) }
                else { Ok((first, high, low as usize)) }
            },
        } }
    }
}

pub open spec fn part2_mct_wavelet_admission(
    samples: usize, count: usize, levels: u8, before: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, u64) {
    let product = (samples as u64) as nat * (count as u64) as nat;
    let level_product = product * (levels as nat + 1);
    if product > u64::MAX || level_product > u64::MAX || level_product * 8 > u64::MAX {
        (Err(part1_transform_error(true)), before)
    } else {
        let charged = part2_mct_charge_work(before, (level_product * 8) as u64, maximum_work);
        match charged.0 {
            Err(error) => (Err(error), charged.1),
            Ok(()) => {
                let scratch = if count as nat * 3 > usize::MAX { usize::MAX as nat } else { count as nat * 3 };
                (part1_image_byte_budget(scratch, 8, maximum_bytes), charged.1)
            },
        }
    }
}

pub open spec fn part2_mct_prepare_wavelet(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection, work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<Part2MctWaveletPreparation, crate::DecodeError>, u64) {
    match collection.6 {
        None => (Err(part1_transform_error(false)), work),
        Some(wavelet) => if collection.1.len() == 0 || collection.1.len() != collection.2.len() {
            (Err(part1_transform_error(false)), work)
        } else if collection.1.len() > usize::MAX { (Err(part1_transform_error(true)), work) }
        else {
            let count = collection.1.len() as usize;
            match part2_mct_component_pairs(before, collection.1, collection.2, count as nat) {
                Err(error) => (Err(error), work),
                Ok((source, destination)) => match part2_mct_validate_dependency_layout(before, source, destination, part2_mct_wavelet_reversible(wavelet)) {
                    Err(error) => (Err(error), work),
                    Ok(samples) => match part2_mct_wavelet_partition(count, wavelet) {
                        Err(error) => (Err(error), work),
                        Ok((first, high, low)) => {
                            let admitted = part2_mct_wavelet_admission(samples, count, wavelet.1, work, maximum_work, maximum_bytes);
                            match admitted.0 {
                                Err(error) => (Err(error), admitted.1),
                                Ok(()) => (Ok((source, destination, first, high, low, samples, count, wavelet,
                                    Seq::new(source.len(), |index: int| before[source[index] as int].2))), admitted.1),
                            }
                        },
                    },
                },
            }
        },
    }
}

pub open spec fn part2_mct_wavelet_source_value(
    before: Seq<Part2MctComponent>, indexes: Seq<usize>, fractions: Seq<u8>,
    sample: usize, index: nat, reversible: bool,
) -> Result<i64, crate::DecodeError> {
    if index >= indexes.len() { Err(part1_transform_error(false)) }
    else { match part2_mct_source_sample(before, indexes[index as int], sample) {
        Err(error) => Err(error),
        Ok(value) => if reversible { Ok(value) }
            else if index >= fractions.len() { Err(part1_transform_error(false)) }
            else { match part2_mct_rescale(value as i128, fractions[index as int], 32) {
                Err(error) => Err(error), Ok(scaled) => part1_checked_sample(scaled as int),
            } },
    } }
}

#[verifier::opaque]
pub open spec fn part2_mct_wavelet_snapshot(
    before: Seq<Part2MctComponent>, indexes: Seq<usize>, fractions: Seq<u8>,
    sample: usize, reversible: bool, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<i64>)
    decreases count,
{
    if count == 0 { (Ok(()), Seq::empty()) }
    else {
        let previous = part2_mct_wavelet_snapshot(before, indexes, fractions, sample, reversible, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => match part2_mct_wavelet_source_value(before, indexes, fractions, sample, (count - 1) as nat, reversible) {
                Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
            },
        }
    }
}

pub open spec fn part2_mct_wavelet_reconstruction_step(
    previous: Result<(usize, Seq<i64>), crate::DecodeError>, source: Seq<i64>, high: Seq<usize>,
    first: Seq<bool>, reversible: bool, index: nat,
) -> Result<(usize, Seq<i64>), crate::DecodeError> {
    match previous {
        Err(error) => Err(error),
        Ok((cursor, low)) => if index >= high.len() { Err(part1_transform_error(false)) }
            else if cursor as nat + high[index as int] as nat > usize::MAX { Err(part1_transform_error(true)) }
            else {
                let end = (cursor as nat + high[index as int] as nat) as usize;
                if cursor > end || end > source.len() { Err(part1_transform_error(false)) }
                else if index >= first.len() { Err(part1_transform_error(false)) }
                else {
                    let next = if reversible { part1_inverse_five_three(low, source.subrange(cursor as int, end as int), first[index as int]) }
                        else { part1_inverse_nine_seven(low, source.subrange(cursor as int, end as int), first[index as int]) };
                    match next { Err(error) => Err(error), Ok(values) => Ok((end, values)) }
                }
            },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_wavelet_reconstruction_steps(
    source: Seq<i64>, high: Seq<usize>, first: Seq<bool>, reversible: bool, low: usize, count: nat,
) -> Result<(usize, Seq<i64>), crate::DecodeError>
    decreases count,
{
    if count == 0 {
        if low > source.len() { Err(part1_transform_error(false)) }
        else { Ok((low, source.take(low as int))) }
    } else if count > high.len() { Err(part1_transform_error(false)) }
    else { part2_mct_wavelet_reconstruction_step(
        part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, (count - 1) as nat),
        source, high, first, reversible, (high.len() - count) as nat) }
}

pub open spec fn part2_mct_wavelet_reconstruction(
    source: Seq<i64>, high: Seq<usize>, first: Seq<bool>, reversible: bool, low: usize, count: usize,
) -> Result<Seq<i64>, crate::DecodeError> {
    match part2_mct_wavelet_reconstruction_steps(source, high, first, reversible, low, high.len()) {
        Err(error) => Err(error),
        Ok((cursor, values)) => if cursor != count || values.len() != count { Err(part1_transform_error(false)) }
            else { Ok(values) },
    }
}

pub open spec fn part2_mct_wavelet_pixel(
    before: Seq<Part2MctComponent>, prepared: Part2MctWaveletPreparation, sample: usize,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, Seq<i64>) {
    let snapshot = part2_mct_wavelet_snapshot(before, prepared.0, prepared.8, sample,
        part2_mct_wavelet_reversible(prepared.7), prepared.6 as nat);
    match snapshot.0 {
        Err(error) => (Err(error), before, snapshot.1),
        Ok(()) => match part2_mct_wavelet_reconstruction(snapshot.1, prepared.3, prepared.2,
            part2_mct_wavelet_reversible(prepared.7), prepared.4, prepared.6) {
            Err(error) => (Err(error), before, snapshot.1),
            Ok(values) => {
                let stored = part2_mct_store_output_rows(before, prepared.1, values, sample, prepared.6 as nat);
                (stored.0, stored.1, snapshot.1)
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_wavelet_pixels(before: Seq<Part2MctComponent>, prepared: Part2MctWaveletPreparation, count: nat)
    -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>)
    decreases count,
{
    if count == 0 { (Ok(()), before) }
    else {
        let previous = part2_mct_wavelet_pixels(before, prepared, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 > usize::MAX { (Err(part1_transform_error(true)), previous.1) }
                else {
                    let pixel = part2_mct_wavelet_pixel(previous.1, prepared, (count - 1) as usize);
                    (pixel.0, pixel.1)
                },
        }
    }
}

pub open spec fn part2_mct_wavelet(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection, work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64) {
    let preparation = part2_mct_prepare_wavelet(before, collection, work, maximum_work, maximum_bytes);
    match preparation.0 {
        Err(error) => (Err(error), before, preparation.1),
        Ok(prepared) => {
            let pixels = part2_mct_wavelet_pixels(before, prepared, prepared.5 as nat);
            match pixels.0 {
                Err(error) => (Err(error), pixels.1, preparation.1),
                Ok(()) => {
                    let tagged = part2_mct_destination_precisions(pixels.1, prepared.1,
                        if part2_mct_wavelet_reversible(prepared.7) { 0 } else { 32 }, prepared.1.len());
                    (tagged.0, tagged.1, preparation.1)
                },
            }
        },
    }
}

pub open spec fn part2_mct_dependency_coefficients(count: usize, reversible: bool)
    -> Result<usize, crate::DecodeError> {
    if reversible {
        if count as nat + 1 > usize::MAX || count as nat * (count as nat + 1) > usize::MAX
            || count as nat * (count as nat + 1) / 2 < 1 {
            Err(part1_transform_error(true))
        } else { Ok((count as nat * (count as nat + 1) / 2 - 1) as usize) }
    } else {
        let previous = if count == 0 { 0nat } else { (count - 1) as nat };
        if count as nat * previous > usize::MAX { Err(part1_transform_error(true)) }
        else { Ok((count as nat * previous / 2) as usize) }
    }
}

pub open spec fn part2_mct_dependency_dimensions(collection: Part2MctCollection)
    -> Result<(usize, usize), crate::DecodeError> {
    let count = collection.1.len();
    if count == 0 || count != collection.2.len() { Err(part1_transform_error(false)) }
    else if count > usize::MAX { Err(part1_transform_error(true)) }
    else { match part2_mct_dependency_coefficients(count as usize, collection.0) {
        Err(error) => Err(error),
        Ok(coefficients) => if (collection.4.is_some() && collection.4.unwrap().4.len() != coefficients)
            || (collection.5.is_some() && collection.5.unwrap().4.len() != count) {
            Err(part1_transform_error(false))
        } else { Ok((count as usize, coefficients)) },
    } }
}

pub open spec fn part2_mct_component_pair_step(
    previous: Result<(Seq<usize>, Seq<usize>), crate::DecodeError>,
    components: Seq<Part2MctComponent>, source: Seq<u16>, destination: Seq<u16>, index: nat,
) -> Result<(Seq<usize>, Seq<usize>), crate::DecodeError> {
    match previous {
        Err(error) => Err(error),
        Ok((inputs, outputs)) => if index >= source.len() { Err(part1_transform_error(false)) }
            else { match part2_mct_find_component(components, source[index as int]) {
                Err(error) => Err(error),
                Ok(input) => if index >= destination.len() { Err(part1_transform_error(false)) }
                    else { match part2_mct_find_component(components, destination[index as int]) {
                        Err(error) => Err(error), Ok(output) => Ok((inputs.push(input), outputs.push(output))),
                    } },
            } },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_component_pairs(
    components: Seq<Part2MctComponent>, source: Seq<u16>, destination: Seq<u16>, count: nat,
) -> Result<(Seq<usize>, Seq<usize>), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), Seq::empty())) }
    else { part2_mct_component_pair_step(
        part2_mct_component_pairs(components, source, destination, (count - 1) as nat),
        components, source, destination, (count - 1) as nat) }
}

pub open spec fn part2_mct_dependency_layout_index_valid(
    components: Seq<Part2MctComponent>, first: usize, index: usize, reversible: bool,
) -> bool {
    part2_mct_layout_index_valid(components, first, index)
        && (!reversible || components[index as int].2 == 0)
}

pub open spec fn part2_mct_validate_dependency_layout(
    components: Seq<Part2MctComponent>, source: Seq<usize>, destination: Seq<usize>, reversible: bool,
) -> Result<usize, crate::DecodeError> {
    if source.len() == 0 || source[0] >= components.len() { Err(part1_transform_error(false)) }
    else if !(forall |index: int| 0 <= index < source.len()
        ==> part2_mct_dependency_layout_index_valid(components, source[0], source[index], reversible)) {
        Err(part1_transform_error(false))
    } else if !(forall |index: int| 0 <= index < destination.len()
        ==> part2_mct_dependency_layout_index_valid(components, source[0], destination[index], reversible)) {
        Err(part1_transform_error(false))
    } else { Ok(components[source[0] as int].3.len() as usize) }
}

pub open spec fn part2_mct_dependency_admission(
    samples: usize, coefficients: usize, count: usize, before: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, u64) {
    let twice = (coefficients as u64) as nat * 2;
    let per_sample = twice + (count as u64) as nat;
    let operations = (samples as u64) as nat * per_sample;
    if twice > u64::MAX || per_sample > u64::MAX || operations > u64::MAX {
        (Err(part1_transform_error(true)), before)
    } else {
        let charged = part2_mct_charge_work(before, operations as u64, maximum_work);
        match charged.0 {
            Err(error) => (Err(error), charged.1),
            Ok(()) => {
                let scratch = if count as nat * 3 > usize::MAX { usize::MAX as nat } else { count as nat * 3 };
                (part1_image_byte_budget(scratch, 8, maximum_bytes), charged.1)
            },
        }
    }
}

pub open spec fn part2_mct_prepare_dependency(
    components: Seq<Part2MctComponent>, collection: Part2MctCollection,
    before: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<Part2MctDependencyPreparation, crate::DecodeError>, u64) {
    match part2_mct_dependency_dimensions(collection) {
        Err(error) => (Err(error), before),
        Ok((count, coefficients)) => match part2_mct_component_pairs(components, collection.1, collection.2, count as nat) {
            Err(error) => (Err(error), before),
            Ok((source, destination)) => match part2_mct_validate_dependency_layout(components, source, destination, collection.0) {
                Err(error) => (Err(error), before),
                Ok(samples) => if collection.0
                    && ((collection.4.is_some() && collection.4.unwrap().3 != 0)
                        || (collection.5.is_some() && collection.5.unwrap().3 != 0)) {
                    (Err(part1_transform_error(false)), before)
                } else {
                    let admitted = part2_mct_dependency_admission(samples, coefficients, count, before, maximum_work, maximum_bytes);
                    match admitted.0 {
                        Err(error) => (Err(error), admitted.1),
                        Ok(()) => (Ok((source, destination, samples, count)), admitted.1),
                    }
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_dependency_rows(
    initial: Seq<i64>, collection: Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<i64>)
    decreases count,
{
    if count == 0 { (Ok(()), initial) }
    else {
        let previous = part2_mct_dependency_rows(initial, collection, source, fractions, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 > usize::MAX { (Err(part1_transform_error(true)), previous.1) }
                else { match part2_mct_dependency_row(collection.4, collection.5, source,
                    if collection.0 { None } else { Some(fractions) }, previous.1, (count - 1) as usize) {
                    Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
                } },
        }
    }
}

pub open spec fn part2_mct_dependency_pixel(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection,
    prepared: Part2MctDependencyPreparation, fractions: Seq<u8>, sample: usize,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, Seq<i64>, Seq<i64>) {
    let snapshot = part2_mct_source_snapshot(before, prepared.0, sample, prepared.3 as nat);
    match snapshot.0 {
        Err(error) => (Err(error), before, snapshot.1, Seq::empty()),
        Ok(()) => {
            let computed = part2_mct_dependency_rows(Seq::empty(), collection, snapshot.1, fractions, prepared.3 as nat);
            match computed.0 {
                Err(error) => (Err(error), before, snapshot.1, computed.1),
                Ok(()) => {
                    let stored = part2_mct_store_output_rows(before, prepared.1, computed.1, sample, prepared.3 as nat);
                    (stored.0, stored.1, snapshot.1, computed.1)
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_dependency_pixels(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection,
    prepared: Part2MctDependencyPreparation, fractions: Seq<u8>, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>)
    decreases count,
{
    if count == 0 { (Ok(()), before) }
    else {
        let previous = part2_mct_dependency_pixels(before, collection, prepared, fractions, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 > usize::MAX { (Err(part1_transform_error(true)), previous.1) }
                else {
                    let pixel = part2_mct_dependency_pixel(previous.1, collection, prepared, fractions, (count - 1) as usize);
                    (pixel.0, pixel.1)
                },
        }
    }
}

pub open spec fn part2_mct_dependency(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection,
    work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64) {
    let preparation = part2_mct_prepare_dependency(before, collection, work, maximum_work, maximum_bytes);
    match preparation.0 {
        Err(error) => (Err(error), before, preparation.1),
        Ok(prepared) => {
            let fractions = Seq::new(prepared.0.len(), |index: int| before[prepared.0[index] as int].2);
            let pixels = part2_mct_dependency_pixels(before, collection, prepared, fractions, prepared.2 as nat);
            match pixels.0 {
                Err(error) => (Err(error), pixels.1, preparation.1),
                Ok(()) => {
                    let tagged = part2_mct_destination_precisions(pixels.1, prepared.1,
                        if collection.0 { 0 } else { 32 }, prepared.1.len());
                    (tagged.0, tagged.1, preparation.1)
                },
            }
        },
    }
}

pub open spec fn part2_mct_source_sample(
    components: Seq<Part2MctComponent>, component: usize, sample: usize,
) -> Result<i64, crate::DecodeError> {
    if component >= components.len() || sample >= components[component as int].3.len() {
        Err(part1_transform_error(false))
    } else { Ok(components[component as int].3[sample as int]) }
}

pub open spec fn part2_mct_snapshot_step(
    previous: (Result<(), crate::DecodeError>, Seq<i64>),
    components: Seq<Part2MctComponent>, indexes: Seq<usize>, sample: usize, position: nat,
) -> (Result<(), crate::DecodeError>, Seq<i64>) {
    match previous.0 {
        Err(_) => previous,
        Ok(()) => if position >= indexes.len() { (Err(part1_transform_error(false)), previous.1) }
            else { match part2_mct_source_sample(components, indexes[position as int], sample) {
                Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
            } },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_source_snapshot(
    components: Seq<Part2MctComponent>, indexes: Seq<usize>, sample: usize, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<i64>)
    decreases count,
{
    if count == 0 { (Ok(()), Seq::empty()) }
    else { part2_mct_snapshot_step(
        part2_mct_source_snapshot(components, indexes, sample, (count - 1) as nat),
        components, indexes, sample, (count - 1) as nat) }
}

pub open spec fn part2_mct_begin_pixel(
    components: Seq<Part2MctComponent>, indexes: Seq<usize>, sample: usize, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<i64>, Seq<i64>) {
    let snapshot = part2_mct_source_snapshot(components, indexes, sample, count);
    (snapshot.0, snapshot.1, Seq::empty())
}

pub open spec fn part2_mct_store_output_row(
    previous: (Result<(), crate::DecodeError>, Seq<Part2MctComponent>),
    destinations: Seq<usize>, values: Seq<i64>, sample: usize, row: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>) {
    match previous.0 {
        Err(_) => previous,
        Ok(()) => if row >= destinations.len() || row >= values.len() {
            (Err(part1_transform_error(false)), previous.1)
        } else { part2_mct_store_sample(previous.1, destinations[row as int], sample, values[row as int]) },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_store_output_rows(
    before: Seq<Part2MctComponent>, destinations: Seq<usize>, values: Seq<i64>, sample: usize, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>)
    decreases count,
{
    if count == 0 { (Ok(()), before) }
    else { part2_mct_store_output_row(
        part2_mct_store_output_rows(before, destinations, values, sample, (count - 1) as nat),
        destinations, values, sample, (count - 1) as nat) }
}

pub open spec fn part2_mct_decorrelation_pixel(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection,
    prepared: Part2MctDecorrelationPreparation, sample: usize,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, Seq<i64>, Seq<i64>) {
    let snapshot = part2_mct_source_snapshot(before, prepared.0, sample, prepared.0.len());
    match snapshot.0 {
        Err(error) => (Err(error), before, snapshot.1, Seq::empty()),
        Ok(()) => {
            let computed = part2_mct_decorrelation_rows(Seq::empty(), collection, snapshot.1, prepared.2, prepared.4 as nat);
            match computed.0 {
                Err(error) => (Err(error), before, snapshot.1, computed.1),
                Ok(()) => {
                    let stored = part2_mct_store_output_rows(before, prepared.1, computed.1, sample, prepared.4 as nat);
                    (stored.0, stored.1, snapshot.1, computed.1)
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_decorrelation_pixels(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection,
    prepared: Part2MctDecorrelationPreparation, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>)
    decreases count,
{
    if count == 0 { (Ok(()), before) }
    else {
        let previous = part2_mct_decorrelation_pixels(before, collection, prepared, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 > usize::MAX { (Err(part1_transform_error(true)), previous.1) }
                else {
                    let pixel = part2_mct_decorrelation_pixel(previous.1, collection, prepared, (count - 1) as usize);
                    (pixel.0, pixel.1)
                },
        }
    }
}

pub open spec fn part2_mct_component_precision(before: Part2MctComponent, precision: u8) -> Part2MctComponent {
    (before.0, before.1, precision, before.3)
}

pub open spec fn part2_mct_set_precision(
    before: Seq<Part2MctComponent>, destination: usize, precision: u8,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>) {
    if destination >= before.len() { (Err(part1_transform_error(false)), before) }
    else { (Ok(()), before.update(destination as int, part2_mct_component_precision(before[destination as int], precision))) }
}

#[verifier::opaque]
pub open spec fn part2_mct_destination_precisions(
    before: Seq<Part2MctComponent>, destinations: Seq<usize>, precision: u8, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>)
    decreases count,
{
    if count == 0 { (Ok(()), before) }
    else {
        let previous = part2_mct_destination_precisions(before, destinations, precision, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 >= destinations.len() { (Err(part1_transform_error(false)), previous.1) }
                else { part2_mct_set_precision(previous.1, destinations[count as int - 1], precision) },
        }
    }
}

pub open spec fn part2_mct_decorrelation(
    before: Seq<Part2MctComponent>, collection: Part2MctCollection,
    work: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>, u64) {
    let preparation = part2_mct_prepare_decorrelation(before, collection, work, maximum_work, maximum_bytes);
    match preparation.0 {
        Err(error) => (Err(error), before, preparation.1),
        Ok(prepared) => {
            let pixels = part2_mct_decorrelation_pixels(before, collection, prepared, prepared.3 as nat);
            match pixels.0 {
                Err(error) => (Err(error), pixels.1, preparation.1),
                Ok(()) => {
                    let tagged = part2_mct_destination_precisions(pixels.1, prepared.1,
                        if collection.0 { 0 } else { 32 }, prepared.1.len());
                    (tagged.0, tagged.1, preparation.1)
                },
            }
        },
    }
}

pub open spec fn part2_mct_decorrelation_row(
    collection: Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>, row: usize,
) -> Result<i64, crate::DecodeError> {
    match collection.4 {
        Some(matrix) => part2_mct_matrix_row(
            matrix, collection.5, source, if collection.0 { None } else { Some(fractions) }, row),
        None => if row >= source.len() { Err(part1_transform_error(false)) }
        else if collection.0 {
            match part2_mct_offset(collection.5, row) {
                Err(error) => Err(error),
                Ok(offset) => part1_checked_sample(source[row as int] as int + offset as int),
            }
        } else if row >= fractions.len() { Err(part1_transform_error(false)) }
        else {
            match part2_mct_rescale(source[row as int] as i128, fractions[row as int], 32) {
                Err(error) => Err(error),
                Ok(value) => match part2_mct_offset_scaled(collection.5, row) {
                    Err(error) => Err(error),
                    Ok(offset) => match part2_atk_checked_i128(value as int + offset as int) {
                        Err(error) => Err(error), Ok(sum) => part1_checked_sample(sum as int),
                    },
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_decorrelation_rows(
    initial: Seq<i64>, collection: Part2MctCollection, source: Seq<i64>, fractions: Seq<u8>, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<i64>)
    decreases count,
{
    if count == 0 { (Ok(()), initial) }
    else {
        let previous = part2_mct_decorrelation_rows(initial, collection, source, fractions, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => if count - 1 > usize::MAX { (Err(part1_transform_error(true)), previous.1) }
                else { match part2_mct_decorrelation_row(collection, source, fractions, (count - 1) as usize) {
                    Err(error) => (Err(error), previous.1), Ok(value) => (Ok(()), previous.1.push(value)),
                } },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_component_indices(
    components: Seq<Part2MctComponent>, references: Seq<u16>,
) -> Result<Seq<usize>, crate::DecodeError>
    decreases references.len(),
{
    if references.len() == 0 { Ok(Seq::empty()) }
    else {
        match part2_mct_component_indices(components, references.drop_last()) {
            Err(error) => Err(error),
            Ok(previous) => match part2_mct_find_component(components, references.last()) {
                Err(error) => Err(error), Ok(index) => Ok(previous.push(index)),
            },
        }
    }
}

pub open spec fn part2_mct_decorrelation_dimensions(collection: Part2MctCollection)
    -> Result<(usize, usize), crate::DecodeError> {
    let rows = collection.1.len();
    let columns = collection.2.len();
    if rows == 0 || rows != columns { Err(part1_transform_error(false)) }
    else if rows > usize::MAX || columns > usize::MAX
        || (collection.4.is_some() && rows * columns > usize::MAX) {
        Err(part1_transform_error(true))
    } else if match collection.4 { None => false, Some(matrix) => matrix.4.len() != rows * columns } {
        Err(part1_transform_error(false))
    } else if match collection.5 { None => false, Some(offsets) => offsets.4.len() != rows } {
        Err(part1_transform_error(false))
    } else { Ok((rows as usize, columns as usize)) }
}

pub open spec fn part2_mct_prepare_decorrelation(
    components: Seq<Part2MctComponent>, collection: Part2MctCollection,
    before: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<Part2MctDecorrelationPreparation, crate::DecodeError>, u64) {
    match part2_mct_decorrelation_dimensions(collection) {
        Err(error) => (Err(error), before),
        Ok((rows, columns)) => match part2_mct_component_indices(components, collection.2) {
            Err(error) => (Err(error), before),
            Ok(source) => match part2_mct_component_indices(components, collection.1) {
                Err(error) => (Err(error), before),
                Ok(destination) => match part2_mct_validate_layout(components, source, destination, collection.0) {
                    Err(error) => (Err(error), before),
                    Ok(samples) => {
                        let admitted = part2_mct_decorrelation_admission(
                            samples, rows as usize, columns as usize, before, maximum_work, maximum_bytes);
                        match admitted.0 {
                            Err(error) => (Err(error), admitted.1),
                            Ok(()) => (Ok((source, destination,
                                Seq::new(source.len(), |index: int| components[source[index] as int].2),
                                samples, rows as usize, columns as usize)), admitted.1),
                        }
                    },
                },
            },
        },
    }
}

pub open spec fn part2_mct_decorrelation_admission(
    samples: usize, rows: usize, columns: usize, before: u64, maximum_work: u64, maximum_bytes: u64,
) -> (Result<(), crate::DecodeError>, u64) {
    let sample_rows = (samples as u64) as nat * (rows as u64) as nat;
    let products = sample_rows * (columns as u64) as nat;
    if sample_rows > u64::MAX || products > u64::MAX || products + sample_rows > u64::MAX {
        (Err(part1_transform_error(true)), before)
    } else {
        let charged = part2_mct_charge_work(before, (products + sample_rows) as u64, maximum_work);
        match charged.0 {
            Err(error) => (Err(error), charged.1),
            Ok(()) => if rows as nat + columns as nat > usize::MAX
                || (rows as nat + columns as nat) * 8 > usize::MAX {
                (Err(part1_transform_error(true)), charged.1)
            } else {
                let bytes = ((rows as nat + columns as nat) * 8) as u64;
                (if bytes > maximum_bytes { Err(crate::DecodeError::LimitExceeded {
                    resource: crate::Resource::DecodedBytes, limit: maximum_bytes, actual: bytes,
                }) } else { Ok(()) }, charged.1)
            },
        }
    }
}

pub open spec fn part2_mct_layout_index_valid(
    components: Seq<Part2MctComponent>, first: usize, index: usize,
) -> bool {
    if first >= components.len() || index >= components.len() { false }
    else { components[index as int].1 == components[first as int].1
        && components[index as int].3.len() == components[first as int].3.len()
        && components[index as int].2 <= 32 }
}

pub open spec fn part2_mct_validate_layout(
    components: Seq<Part2MctComponent>, source: Seq<usize>, destination: Seq<usize>, reversible: bool,
) -> Result<usize, crate::DecodeError> {
    if source.len() == 0 { Err(part1_transform_error(false)) }
    else if source[0] >= components.len() { Err(part1_transform_error(false)) }
    else {
        let first = source[0];
        if !(forall |position: int| 0 <= position < source.len()
            ==> part2_mct_layout_index_valid(components, first, source[position])) {
            Err(part1_transform_error(false))
        } else if !(forall |position: int| 0 <= position < destination.len()
            ==> part2_mct_layout_index_valid(components, first, destination[position])) {
            Err(part1_transform_error(false))
        } else if reversible && !(forall |position: int| 0 <= position < source.len()
            ==> components[source[position] as int].2 == 0) {
            Err(part1_transform_error(false))
        } else { Ok(components[first as int].3.len() as usize) }
    }
}

pub open spec fn part2_mct_store_component_sample(
    before: Part2MctComponent, index: usize, value: i64,
) -> (Result<(), crate::DecodeError>, Part2MctComponent) {
    if index >= before.3.len() { (Err(part1_transform_error(false)), before) }
    else { (Ok(()), (before.0, before.1, before.2, before.3.update(index as int, value))) }
}

pub open spec fn part2_mct_store_sample(
    before: Seq<Part2MctComponent>, component: usize, index: usize, value: i64,
) -> (Result<(), crate::DecodeError>, Seq<Part2MctComponent>) {
    if component >= before.len() { (Err(part1_transform_error(false)), before) }
    else {
        let stored = part2_mct_store_component_sample(before[component as int], index, value);
        (stored.0, before.update(component as int, stored.1))
    }
}

pub open spec fn part2_mct_component_tags(components: Seq<Part2MctComponent>) -> Seq<u16> {
    Seq::new(components.len(), |index: int| components[index].0)
}

pub open spec fn part2_mct_find_component(components: Seq<Part2MctComponent>, reference: u16)
    -> Result<usize, crate::DecodeError>
{
    match part2_mct_component_tags(components).index_of_first(reference) {
        None => Err(part1_transform_error(false)),
        Some(index) => if index < 0 || index > usize::MAX { Err(part1_transform_error(true)) }
            else { Ok(index as usize) },
    }
}

pub open spec fn part2_mct_dependency_initial(
    offsets: Option<Part2MctArray>, source: Seq<i64>, fractions: Option<Seq<u8>>, row: usize,
) -> Result<i128, crate::DecodeError> {
    if row >= source.len() { Err(part1_transform_error(false)) }
    else {
        match fractions {
            None => match part2_mct_offset(offsets, row) {
                Err(error) => Err(error),
                Ok(offset) => match part1_checked_sample(source[row as int] as int + offset as int) {
                    Err(error) => Err(error), Ok(base) => Ok(base as i128),
                },
            },
            Some(bits) => if row >= bits.len() { Err(part1_transform_error(false)) } else {
                match part2_mct_rescale(source[row as int] as i128, bits[row as int], 32) {
                    Err(error) => Err(error),
                    Ok(base) => match part2_mct_offset_scaled(offsets, row) {
                        Err(error) => Err(error), Ok(offset) => part2_atk_checked_i128(base as int + offset as int),
                    },
                }
            },
        }
    }
}

pub open spec fn part2_mct_dependency_row(
    matrix: Option<Part2MctArray>, offsets: Option<Part2MctArray>, source: Seq<i64>,
    fractions: Option<Seq<u8>>, output: Seq<i64>, row: usize,
) -> Result<i64, crate::DecodeError> {
    match part2_mct_dependency_initial(offsets, source, fractions, row) {
        Err(error) => Err(error),
        Ok(base) => match matrix {
            None => part1_checked_sample(base as int),
            Some(matrix) => match fractions {
                None => {
                    if row == 0 { part1_checked_sample(base as int) }
                    else if row as nat + 1 > usize::MAX || row as nat * (row as nat + 1) > usize::MAX {
                        Err(part1_transform_error(true))
                    } else {
                        let start = (row as nat * (row as nat + 1) / 2 - 1) as usize;
                        if start as nat + row as nat > usize::MAX { Err(part1_transform_error(true)) }
                        else if start as nat + row as nat >= matrix.4.len() { Err(part1_transform_error(false)) }
                        else {
                            let scale = matrix.4[start as int + row as int];
                            if scale <= 0 { Err(part1_transform_error(false)) }
                            else {
                                match part2_mct_dot_prefix((scale / 2) as i128, matrix, output, None, start, row as nat) {
                                    Err(error) => Err(error),
                                    Ok(prediction) => {
                                        let quotient = vstd::arithmetic::div_mod::rust_div(prediction as int, scale as int);
                                        let predicted = if vstd::arithmetic::div_mod::rust_rem(prediction as int, scale as int) < 0 {
                                            part2_atk_checked_i128(quotient - 1)
                                        } else { Ok(quotient as i128) };
                                        match predicted {
                                            Err(error) => Err(error),
                                            Ok(predicted) => match part2_atk_checked_i128(base as int + predicted as int) {
                                                Err(error) => Err(error), Ok(sum) => part1_checked_sample(sum as int),
                                            },
                                        }
                                    },
                                }
                            }
                        }
                    }
                },
                Some(_) => {
                    let previous = if row == 0 { 0nat } else { (row - 1) as nat };
                    if row as nat * previous > usize::MAX { Err(part1_transform_error(true)) }
                    else {
                        match part2_mct_dot_prefix(base, matrix, output, Some(Seq::new(output.len(), |index: int| 32u8)),
                            (row as nat * previous / 2) as usize, row as nat) {
                            Err(error) => Err(error), Ok(sum) => part1_checked_sample(sum as int),
                        }
                    }
                },
            },
        },
    }
}

pub open spec fn part2_mct_row_initial(
    matrix: Part2MctArray, offsets: Option<Part2MctArray>, width: nat,
    fractions: Option<Seq<u8>>, row: usize,
) -> Result<i128, crate::DecodeError> {
    match fractions {
        None => {
            if matrix.3 != 0 || match offsets { None => false, Some(array) => array.3 != 0 } {
                Err(part1_transform_error(false))
            } else {
                match part2_mct_offset(offsets, row) {
                    Err(error) => Err(error), Ok(value) => Ok(value as i128),
                }
            }
        },
        Some(bits) => {
            if width != bits.len() || matrix.3 > 32
                || match offsets { None => false, Some(array) => array.3 > 32 } {
                Err(part1_transform_error(false))
            } else { part2_mct_offset_scaled(offsets, row) }
        },
    }
}

pub open spec fn part2_mct_dot_term(
    matrix: Part2MctArray, source: Seq<i64>, fractions: Option<Seq<u8>>,
    start: usize, column: usize,
) -> Result<i128, crate::DecodeError> {
    if start as nat + column as nat > usize::MAX { Err(part1_transform_error(true)) }
    else if start as nat + column as nat >= matrix.4.len() || column >= source.len() { Err(part1_transform_error(false)) }
    else {
        let coefficient = matrix.4[start as int + column as int];
        let sample = source[column as int];
        match fractions {
            None => part2_atk_checked_i128(coefficient as int * sample as int),
            Some(bits) => {
                if column >= bits.len() { Err(part1_transform_error(false)) }
                else if matrix.3 as nat + bits[column as int] as nat > u8::MAX { Err(part1_transform_error(true)) }
                else {
                    match part2_atk_checked_i128(coefficient as int * sample as int) {
                        Err(error) => Err(error),
                        Ok(product) => part2_mct_rescale(product, (matrix.3 + bits[column as int]) as u8, 32),
                    }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_mct_dot_prefix(
    initial: i128, matrix: Part2MctArray, source: Seq<i64>, fractions: Option<Seq<u8>>,
    start: usize, count: nat,
) -> Result<i128, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) }
    else {
        match part2_mct_dot_prefix(initial, matrix, source, fractions, start, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_mct_dot_term(matrix, source, fractions, start, (count - 1) as usize) {
                Err(error) => Err(error),
                Ok(product) => part2_atk_checked_i128(previous as int + product as int),
            },
        }
    }
}

pub open spec fn part2_mct_matrix_row(
    matrix: Part2MctArray, offsets: Option<Part2MctArray>, source: Seq<i64>,
    fractions: Option<Seq<u8>>, row: usize,
) -> Result<i64, crate::DecodeError> {
    match part2_mct_row_initial(matrix, offsets, source.len(), fractions, row) {
        Err(error) => Err(error),
        Ok(initial) => {
            if row as nat * source.len() > usize::MAX { Err(part1_transform_error(true)) }
            else {
                match part2_mct_dot_prefix(initial, matrix, source, fractions, (row as nat * source.len()) as usize, source.len()) {
                    Err(error) => Err(error), Ok(sum) => part1_checked_sample(sum as int),
                }
            }
        },
    }
}

pub open spec fn part2_mct_round_shift(value: i128, bits: u8) -> Result<i128, crate::DecodeError> {
    if bits == 0 { Ok(value) }
    else if bits > 126 { Err(part1_transform_error(true)) }
    else {
        let half = 1i128 << ((bits - 1) as u32);
        let divisor = 1i128 << (bits as u32);
        if divisor == 0 || divisor == -1 { Err(part1_transform_error(true)) }
        else if value < 0 {
            match part2_atk_checked_i128(-(value as int)) {
                Err(error) => Err(error),
                Ok(magnitude) => match part2_atk_checked_i128(magnitude as int + half as int) {
                    Err(error) => Err(error),
                    Ok(biased) => part2_atk_checked_i128(-((biased / divisor) as int)),
                },
            }
        } else {
            match part2_atk_checked_i128(value as int + half as int) {
                Err(error) => Err(error), Ok(biased) => Ok((biased / divisor) as i128),
            }
        }
    }
}

pub open spec fn part2_mct_rescale(value: i128, from_bits: u8, to_bits: u8) -> Result<i128, crate::DecodeError> {
    if from_bits == to_bits { Ok(value) }
    else if from_bits < to_bits {
        let shift = (to_bits - from_bits) as u8;
        if shift > 126 { Err(part1_transform_error(true)) }
        else { part2_atk_checked_i128(value as int * (1i128 << (shift as u32)) as int) }
    } else { part2_mct_round_shift(value, (from_bits - to_bits) as u8) }
}

pub open spec fn part2_mct_offset(offsets: Option<Part2MctArray>, row: usize) -> Result<i64, crate::DecodeError> {
    match offsets {
        None => Ok(0),
        Some(array) => if array.3 != 0 || row >= array.4.len() { Err(part1_transform_error(false)) }
            else { Ok(array.4[row as int]) },
    }
}

pub open spec fn part2_mct_offset_scaled(offsets: Option<Part2MctArray>, row: usize) -> Result<i128, crate::DecodeError> {
    match offsets {
        None => Ok(0),
        Some(array) => if array.3 > 32 || row >= array.4.len() { Err(part1_transform_error(false)) }
            else { part2_mct_rescale(array.4[row as int] as i128, array.3, 32) },
    }
}

pub open spec fn part2_mct_charge_work(before: u64, operations: u64, maximum: u64)
    -> (Result<(), crate::DecodeError>, u64)
{
    if before as nat + operations as nat > u64::MAX { (Err(part1_transform_error(true)), before) }
    else {
        let next = (before as nat + operations as nat) as u64;
        (if next > maximum { Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::WorkUnits, limit: maximum, actual: next,
        }) } else { Ok(()) }, next)
    }
}

pub open spec fn part1_tier1_block_coding_byte(value: u8) -> Result<crate::tier1::Tier1BlockCoding, crate::DecodeError> {
    match value >> 6 {
        0 => Ok(crate::tier1::Tier1BlockCoding::Legacy),
        1 if value & 0x37 == 0 => Ok(crate::tier1::Tier1BlockCoding::HighThroughput),
        1 | 2 => Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
        3 if value & 0x05 == 0 => Ok(crate::tier1::Tier1BlockCoding::Mixed),
        _ => Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
    }
}

pub open spec fn part1_tier1_coding_style_byte(value: u8) -> Result<crate::tier1::Tier1CodingStyle, crate::DecodeError> {
    match part1_tier1_block_coding_byte(value) {
        Err(error) => Err(error),
        Ok(block_coding) => Ok(crate::tier1::Tier1CodingStyle {
            block_coding,
            force_high_throughput: matches!(block_coding, crate::tier1::Tier1BlockCoding::HighThroughput),
            selective_arithmetic_coding_bypass: value & 0x01 != 0,
            reset_contexts: value & 0x02 != 0,
            terminate_all_passes: value & 0x04 != 0,
            vertical_causal_context: value & 0x08 != 0,
            predictable_termination: value & 0x10 != 0,
            segmentation_symbols: value & 0x20 != 0,
        }),
    }
}

pub type Part2RawKernelCoefficient = (Seq<u8>, u8);
pub type Part2RawKernelStep = (i8, u8, Option<Part2RawKernelCoefficient>, Seq<Part2RawKernelCoefficient>);
pub type Part2RawKernel = (bool, u8, bool, bool, bool, Option<Part2RawKernelCoefficient>, Seq<Part2RawKernelStep>);
pub type Part2AtkMutation = (Result<(), crate::DecodeError>, Seq<i64>);

pub enum Part2TileSelection {
    All,
    Index(u16),
    Set(Seq<u16>),
}

pub type Part2DecodeSelection = (Part2TileSelection, Option<crate::ImageRegion>, u8);
pub type Part2ValidatedSelection = (Seq<u16>, Seq<u32>, u8);
pub type Part2SelectionGeometry = (u32, u32, u32, u32, u32, u32, u32, u32, u32, u32);
pub type Part2TileRectangle = (u32, u32, u32, u32);
pub type Part2AssociatedHeader = (Part2OutputHeader, crate::jp2::ImageHeader, crate::jp2::ColorMethod);

pub open spec fn part2_finish_associated_selected_output(
    image: Part1DecodedTypedImage, header: Option<Part2AssociatedHeader>, target: [u32; 4],
    maximum_components: u16, maximum_bytes: u64, maximum_work: u64,
) -> Part2ConvertedImageResult {
    match part2_apply_associated_output(image, header, maximum_components, maximum_bytes) {
        Err(error) => Err(error),
        Ok(mapped) => part2_convert_associated_selected(mapped.0, mapped.1, target, maximum_bytes, maximum_work),
    }
}

pub open spec fn part2_selection_from_parts(
    tiles: Part2TileSelection, region: Option<crate::ImageRegion>, discard: u8,
) -> Part2DecodeSelection { (tiles, region, discard) }

pub open spec fn part2_tile_list_contains(tiles: Seq<u16>, tile: u16) -> Result<bool, crate::DecodeError> {
    Ok(tiles.contains(tile))
}

pub open spec fn part2_apply_associated_output(
    image: Part1DecodedTypedImage, header: Option<Part2AssociatedHeader>, maximum_components: u16, maximum_bytes: u64,
) -> Result<(Part1DecodedTypedImage, Option<Part2AssociatedHeader>), crate::DecodeError> {
    match header {
        None => Ok((image, None)),
        Some(header) => match part2_apply_output_header(image, header.0, maximum_components, maximum_bytes) {
            Err(error) => Err(error), Ok(mapped) => Ok((mapped, Some(header))),
        },
    }
}

pub open spec fn part2_convert_associated_selected(
    image: Part1DecodedTypedImage, header: Option<Part2AssociatedHeader>, target: [u32; 4], maximum_bytes: u64, maximum_work: u64,
) -> Part2ConvertedImageResult {
    match header {
        None => Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::MissingRequiredStructure }),
        Some(header) => color_convert_selected(image.1, image.2, image.0, header.2, target, maximum_bytes, maximum_work),
    }
}

pub open spec fn part2_convert_associated(
    image: Part1DecodedTypedImage, header: Option<Part2AssociatedHeader>, maximum_bytes: u64, maximum_work: u64,
) -> Part2ConvertedImageResult {
    match header {
        None => Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::MissingRequiredStructure }),
        Some(header) => color_convert_jp2(image.1, image.2, image.0, header.2, maximum_bytes, maximum_work),
    }
}

pub open spec fn part2_associated_codestream_header(
    association: Option<(u64, Option<Part2AssociatedHeader>)>, fallback: Part2AssociatedHeader,
) -> Result<Part2AssociatedHeader, crate::DecodeError> {
    match association {
        None => Ok(fallback),
        Some(association) => match association.1 {
            Some(header) => Ok(header),
            None => Err(crate::DecodeError::MalformedInput {
                offset: association.0, kind: crate::MalformedKind::MissingRequiredStructure,
            }),
        },
    }
}

pub open spec fn part2_validate_selected_header(
    image: crate::jp2::ImageHeader, width: u32, height: u32, components: u16,
    uniform: Option<u8>, signed: Option<bool>, offset: u64,
) -> Result<(), crate::DecodeError> {
    let mismatch = crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::ContainerCodestreamMismatch };
    if image.width != width || image.height != height || image.components != components { Err(mismatch) }
    else {
        match image.bit_depth {
            crate::jp2::ComponentBitDepth::Variable => Ok(()),
            crate::jp2::ComponentBitDepth::Uniform { bits, signed: sign } => {
                if uniform == Some(bits) && signed == Some(sign) { Ok(()) } else { Err(mismatch) }
            },
        }
    }
}

pub open spec fn part2_color_selection_requested(
    size: Part2SelectionGeometry, components: Seq<crate::codestream::ComponentInfo>, count: u16, requested: Part2DecodeSelection,
) -> Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError> {
    match part2_validate_selection(size, requested) {
        Err(error) => Err(error),
        Ok(selected) => part2_color_selection_context(size.2, size.3, components, count, selected),
    }
}

#[verifier::opaque]
pub open spec fn part2_selected_region_prefix(
    size: Part2SelectionGeometry, tiles: Seq<u16>, image_x1: u32, image_y1: u32, count: nat,
) -> Result<Part2TileRectangle, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((image_x1, image_y1, size.2, size.3)) }
    else {
        match part2_selected_region_prefix(size, tiles, image_x1, image_y1, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_selection_tile_bounds(size, tiles[count - 1]) {
                Err(error) => Err(error),
                Ok(bounds) => Ok((if previous.0 < bounds.x0 { previous.0 } else { bounds.x0 },
                    if previous.1 < bounds.y0 { previous.1 } else { bounds.y0 },
                    if previous.2 > bounds.x1 { previous.2 } else { bounds.x1 },
                    if previous.3 > bounds.y1 { previous.3 } else { bounds.y1 })),
            },
        }
    }
}

pub open spec fn part2_selection_region(
    size: Part2SelectionGeometry, tiles: Seq<u16>, requested: Option<crate::ImageRegion>, image_x1: u32, image_y1: u32,
) -> Result<Seq<u32>, crate::DecodeError> {
    match requested {
        Some(region) => {
            if region.width == 0 || region.height == 0 {
                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::EmptyRegion })
            } else if region.x as nat + region.width as nat > u32::MAX || region.y as nat + region.height as nat > u32::MAX {
                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::RegionOutOfBounds })
            } else {
                let x1 = (region.x + region.width) as u32;
                let y1 = (region.y + region.height) as u32;
                if region.x < size.2 || region.y < size.3 || x1 > image_x1 || y1 > image_y1 {
                    Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::RegionOutOfBounds })
                } else { Ok(seq![region.x, region.y, x1, y1]) }
            }
        },
        None => if tiles.len() == 0 { Ok(seq![size.2, size.3, image_x1, image_y1]) }
            else {
                match part2_selected_region_prefix(size, tiles, image_x1, image_y1, tiles.len()) {
                    Err(error) => Err(error), Ok(bounds) => Ok(seq![bounds.0, bounds.1, bounds.2, bounds.3]),
                }
            },
    }
}

#[verifier::opaque]
pub open spec fn part2_selected_tiles_prefix(size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: nat)
    -> Result<Seq<u16>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match part2_selected_tiles_prefix(size, explicit, region, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => if count - 1 > u16::MAX { Err(part1_block_placement_error(true)) }
                else {
                    let index = (count - 1) as u16;
                    match part2_selection_tile_bounds(size, index) {
                        Err(error) => Err(error),
                        Ok(bounds) => if bounds.x0 < region[2] && bounds.x1 > region[0] && bounds.y0 < region[3] && bounds.y1 > region[1] {
                            if explicit.len() > 0 && !explicit.contains(index) {
                                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::RegionOutsideSelectedTiles })
                            } else { Ok(previous.push(index)) }
                        } else { Ok(previous) },
                    }
                },
        }
    }
}

pub open spec fn part2_select_intersecting_tiles(size: Part2SelectionGeometry, explicit: Seq<u16>, region: Seq<u32>, count: u64)
    -> Result<Seq<u16>, crate::DecodeError> {
    match part2_selected_tiles_prefix(size, explicit, region, count as nat) {
        Err(error) => Err(error),
        Ok(tiles) => if tiles.len() == 0 {
            Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::RegionOutsideSelectedTiles })
        } else { Ok(tiles) },
    }
}

pub open spec fn part2_selection_explicit(tiles: Part2TileSelection) -> Result<Seq<u16>, crate::DecodeError> {
    match tiles {
        Part2TileSelection::All => Ok(Seq::empty()),
        Part2TileSelection::Index(index) => Ok(seq![index]),
        Part2TileSelection::Set(indices) => if indices.len() == 0 {
            Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::EmptyTileSet })
        } else { Ok(indices) },
    }
}

#[verifier::opaque]
pub open spec fn part2_validate_selection(size: Part2SelectionGeometry, selection: Part2DecodeSelection)
    -> Result<Part2ValidatedSelection, crate::DecodeError> {
    match part1_image_checked_u32(size.2 as int + size.0 as int) {
        Err(error) => Err(error),
        Ok(image_x1) => match part1_image_checked_u32(size.3 as int + size.1 as int) {
            Err(error) => Err(error),
            Ok(image_y1) => match part2_selection_tile_count(size) {
                Err(error) => Err(error),
                Ok(count) => if size.8 == 0 || count > u16::MAX as u64 + 1 { Err(part1_image_error(false)) }
                    else {
                        match part2_selection_explicit(selection.0) {
                            Err(error) => Err(error),
                            Ok(explicit) => match part2_explicit_tile_prefix(explicit, count, explicit.len()) {
                                Err(error) => Err(error),
                                Ok(()) => {
                                    let rectangle = if explicit.len() > 1 { part2_validate_tile_rectangle(explicit, size.8) } else { Ok(()) };
                                    match rectangle {
                                        Err(error) => Err(error),
                                        Ok(()) => match part2_selection_region(size, explicit, selection.1, image_x1, image_y1) {
                                            Err(error) => Err(error),
                                            Ok(region) => match part2_select_intersecting_tiles(size, explicit, region, count) {
                                                Err(error) => Err(error), Ok(tiles) => Ok((tiles, region, selection.2)),
                                            },
                                        },
                                    }
                                },
                            },
                        }
                    },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_tile_rectangle_prefix(tiles: Seq<u16>, across: u32, count: nat) -> Part2TileRectangle
    decreases count,
{
    if count <= 1 {
        (((tiles[0] as u32) / across) as u32, ((tiles[0] as u32) % across) as u32,
            ((tiles[0] as u32) / across) as u32, ((tiles[0] as u32) % across) as u32)
    } else {
        let previous = part2_tile_rectangle_prefix(tiles, across, (count - 1) as nat);
        let row = ((tiles[count - 1] as u32) / across) as u32;
        let column = ((tiles[count - 1] as u32) % across) as u32;
        (if row < previous.0 { row } else { previous.0 },
            if column < previous.1 { column } else { previous.1 },
            if row > previous.2 { row } else { previous.2 },
            if column > previous.3 { column } else { previous.3 })
    }
}

pub open spec fn part2_rectangle_area(bounds: Part2TileRectangle) -> Result<u32, crate::DecodeError> {
    let error = crate::DecodeError::InvalidSelection { reason: crate::SelectionError::NonRectangularTileSet };
    if bounds.2 < bounds.0 || bounds.3 < bounds.1 { Err(error) }
    else {
        let rows = bounds.2 as nat - bounds.0 as nat + 1;
        let columns = bounds.3 as nat - bounds.1 as nat + 1;
        if rows > u32::MAX || columns > u32::MAX || rows * columns > u32::MAX { Err(error) }
        else { Ok((rows * columns) as u32) }
    }
}

pub open spec fn part2_rectangle_cell(tiles: Seq<u16>, across: u32, row: u32, column: u32)
    -> Result<(), crate::DecodeError>
{
    if row as nat * across as nat > u32::MAX || row as nat * across as nat + column as nat > u32::MAX {
        Err(part1_block_placement_error(true))
    } else {
        let index = row as nat * across as nat + column as nat;
        if index > u16::MAX { Err(part1_block_placement_error(true)) }
        else if !tiles.contains(index as u16) {
            Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::NonRectangularTileSet })
        } else { Ok(()) }
    }
}

#[verifier::opaque]
pub open spec fn part2_rectangle_columns(tiles: Seq<u16>, across: u32, bounds: Part2TileRectangle, row: u32, count: nat)
    -> Result<(), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(()) } else {
        match part2_rectangle_columns(tiles, across, bounds, row, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => part2_rectangle_cell(tiles, across, row, (bounds.1 as nat + count - 1) as u32),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_rectangle_rows(tiles: Seq<u16>, across: u32, bounds: Part2TileRectangle, count: nat)
    -> Result<(), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(()) } else {
        match part2_rectangle_rows(tiles, across, bounds, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => part2_rectangle_columns(tiles, across, bounds, (bounds.0 as nat + count - 1) as u32,
                (bounds.3 as nat - bounds.1 as nat + 1) as nat),
        }
    }
}

pub open spec fn part2_validate_tile_rectangle(tiles: Seq<u16>, across: u32) -> Result<(), crate::DecodeError> {
    let bounds = part2_tile_rectangle_prefix(tiles, across, tiles.len());
    match part2_rectangle_area(bounds) {
        Err(error) => Err(error),
        Ok(expected) => if expected as nat > usize::MAX { Err(part1_block_placement_error(true)) }
            else if expected as nat != tiles.len() {
                Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::NonRectangularTileSet })
            } else { part2_rectangle_rows(tiles, across, bounds, (bounds.2 as nat - bounds.0 as nat + 1) as nat) },
    }
}

#[verifier::opaque]
pub open spec fn part2_explicit_tile_prefix(tiles: Seq<u16>, count: u64, prefix: nat)
    -> Result<(), crate::DecodeError>
    decreases prefix,
{
    if prefix == 0 { Ok(()) }
    else {
        match part2_explicit_tile_prefix(tiles, count, (prefix - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => {
                let tile = tiles[prefix - 1];
                if tile as u64 >= count {
                    Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::TileOutOfRange })
                } else if tiles.take((prefix - 1) as int).contains(tile) {
                    Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::DuplicateTile })
                } else { Ok(()) }
            },
        }
    }
}

pub open spec fn part2_selection_tile_count(size: Part2SelectionGeometry) -> Result<u64, crate::DecodeError> {
    let count = size.8 as nat * size.9 as nat;
    if count > u64::MAX { Err(part1_image_error(true)) } else { Ok(count as u64) }
}

pub open spec fn part2_selection_nominal(origin: u32, step: u32, index: u32) -> Result<u32, crate::DecodeError> {
    match part1_image_checked_u32(index as int * step as int) {
        Err(error) => Err(error),
        Ok(offset) => part1_image_checked_u32(origin as int + offset as int),
    }
}

pub open spec fn part2_selection_tile_bounds(size: Part2SelectionGeometry, index: u16)
    -> Result<crate::codestream::TileBounds, crate::DecodeError>
{
    match part2_selection_tile_count(size) {
        Err(error) => Err(error),
        Ok(count) => if index as u64 >= count || size.8 == 0 { Err(part1_image_error(false)) } else {
            match part2_selection_nominal(size.6, size.4, ((index as u32) % size.8) as u32) {
                Err(error) => Err(error),
                Ok(nx) => match part2_selection_nominal(size.7, size.5, ((index as u32) / size.8) as u32) {
                    Err(error) => Err(error),
                    Ok(ny) => match part1_image_checked_u32(size.2 as int + size.0 as int) {
                        Err(error) => Err(error),
                        Ok(ix) => match part1_image_checked_u32(size.3 as int + size.1 as int) {
                            Err(error) => Err(error),
                            Ok(iy) => match part1_image_checked_u32(nx as int + size.4 as int) {
                                Err(error) => Err(error),
                                Ok(nex) => match part1_image_checked_u32(ny as int + size.5 as int) {
                                    Err(error) => Err(error),
                                    Ok(ney) => {
                                        let x0 = if nx >= size.2 { nx } else { size.2 };
                                        let y0 = if ny >= size.3 { ny } else { size.3 };
                                        let x1 = if nex <= ix { nex } else { ix };
                                        let y1 = if ney <= iy { ney } else { iy };
                                        if x0 >= x1 || y0 >= y1 { Err(part1_image_error(false)) }
                                        else { Ok(crate::codestream::TileBounds { tile_index: index, x0, y0, x1, y1 }) }
                                    },
                                },
                            },
                        },
                    },
                },
            }
        },
    }
}

pub open spec fn part2_selection_ceil(value: u32, divisor: u32) -> Result<u32, crate::DecodeError> {
    if divisor == 0 { Err(part1_block_placement_error(false)) }
    else {
        let total = value as nat / divisor as nat + if value as nat % divisor as nat == 0 { 0nat } else { 1nat };
        if total > u32::MAX { Err(part1_block_placement_error(true)) } else { Ok(total as u32) }
    }
}

pub open spec fn part2_selection_floor(value: u32, divisor: u32) -> Result<u32, crate::DecodeError> {
    if divisor == 0 { Err(part1_block_placement_error(false)) }
    else { Ok((value / divisor) as u32) }
}

#[verifier::opaque]
pub open spec fn part2_subband_count_run(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, stage: u8, count: u16,
) -> u16
    decreases if stage < 32 { 32int - stage as int } else { 0int },
{
    if stage >= levels || stage >= 32 || stage as nat >= directions.len() { count } else {
        let next = count as nat + part1_direction_detail_count(directions[stage as int]);
        if next > u16::MAX { count }
        else { part2_subband_count_run(levels, directions, (stage + 1) as u8, next as u16) }
    }
}

pub open spec fn part2_subband_count(levels: u8, directions: Seq<crate::codestream::DecompositionDirection>) -> u16 {
    part2_subband_count_run(levels, directions, 0, 1)
}

pub type Part2Quantization = (crate::codestream::QuantizationStyle, u8, u16, Seq<crate::transform::QuantizationStep>);

pub open spec fn part2_quantization_lookup(value: Part2Quantization, index: u16)
    -> Result<crate::transform::QuantizationStep, crate::DecodeError>
{
    if index >= value.2 || index as nat >= value.3.len() {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidQuantization })
    } else { Ok(value.3[index as int]) }
}

pub open spec fn part2_quantization_step_at_index(
    value: Part2Quantization, resolution: u8, index: u16,
) -> Result<crate::transform::QuantizationStep, crate::DecodeError> {
    match value.0 {
        crate::codestream::QuantizationStyle::None | crate::codestream::QuantizationStyle::ScalarExpounded => {
            part2_quantization_lookup(value, index)
        },
        crate::codestream::QuantizationStyle::ScalarDerived => match part2_quantization_lookup(value, 0) {
            Err(error) => Err(error),
            Ok(base) => {
                let reduction = if resolution <= 1 { 0int } else { resolution as int - 1 };
                Ok(crate::transform::QuantizationStep {
                    exponent: if base.exponent as int <= reduction { 0u8 } else { (base.exponent as int - reduction) as u8 },
                    mantissa: base.mantissa,
                })
            },
        },
    }
}

pub open spec fn part2_quantization_for_subband(
    value: Part2Quantization, resolution: u8, orientation: crate::tier1::SubbandOrientation,
) -> Result<(u16, crate::transform::QuantizationStep), crate::DecodeError> {
    let index = if resolution == 0 {
        match orientation {
            crate::tier1::SubbandOrientation::Ll => Ok(0u16),
            _ => Err(part1_block_placement_error(false)),
        }
    } else {
        match orientation {
            crate::tier1::SubbandOrientation::Ll => Err(part1_block_placement_error(false)),
            crate::tier1::SubbandOrientation::Hl => Ok(((resolution as int - 1) * 3 + 1) as u16),
            crate::tier1::SubbandOrientation::Lh => Ok(((resolution as int - 1) * 3 + 2) as u16),
            crate::tier1::SubbandOrientation::Hh => Ok(((resolution as int - 1) * 3 + 3) as u16),
        }
    };
    match index {
        Err(error) => Err(error),
        Ok(index) => match part2_quantization_step_at_index(value, resolution, index) {
            Err(error) => Err(error), Ok(step) => Ok((index, step)),
        },
    }
}

pub open spec fn part2_make_subband_geometry(
    resolution: u8, orientation: crate::tier1::SubbandOrientation, bounds: [u32; 4],
    dimensions: [u32; 2], phase: [bool; 2], depth: [u8; 2],
    quantization: Part2Quantization, index: u16,
) -> Result<crate::decode::SubbandGeometry, crate::DecodeError> {
    let gain = match orientation {
        crate::tier1::SubbandOrientation::Ll => 0int,
        crate::tier1::SubbandOrientation::Hl | crate::tier1::SubbandOrientation::Lh => 1int,
        crate::tier1::SubbandOrientation::Hh => 2int,
    };
    let dynamic = depth[0] as int + gain;
    if dynamic > u8::MAX { Err(part1_block_placement_error(true)) }
    else if dynamic == 0 {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidQuantization })
    } else {
        match part2_quantization_step_at_index(quantization, resolution, index) {
            Err(error) => Err(error),
            Ok(step) => {
                let exponent = quantization.1 as int + step.exponent as int;
                let significant = exponent - 1 + depth[1] as int;
                if exponent == 0 || significant == 0 || significant > crate::tier1::MAX_TIER1_BITPLANES {
                    Err(part1_block_placement_error(false))
                } else {
                    match part1_image_checked_u32(bounds[2] as int - bounds[0] as int) {
                        Err(error) => Err(error),
                        Ok(width) => match part1_image_checked_u32(bounds[3] as int - bounds[1] as int) {
                            Err(error) => Err(error),
                            Ok(height) => Ok(crate::decode::SubbandGeometry {
                                resolution, orientation, x0: bounds[0], y0: bounds[1], width, height,
                                resolution_width: dimensions[0], resolution_height: dimensions[1],
                                quantization_index: index, quantization_step: step, dynamic_range: dynamic as u8,
                                significant_bitplanes: significant as u16, roi_shift: depth[1],
                                low_pass_first_x: phase[0], low_pass_first_y: phase[1],
                            }),
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn part2_append_subband(
    before: Seq<crate::decode::SubbandGeometry>, resolution: u8, orientation: crate::tier1::SubbandOrientation,
    bounds: [u32; 4], dimensions: [u32; 2], phase: [bool; 2], depth: [u8; 2],
    quantization: Part2Quantization, index: nat,
) -> Result<Seq<crate::decode::SubbandGeometry>, crate::DecodeError> {
    if index > u16::MAX { Err(part1_block_placement_error(true)) } else {
        match part2_make_subband_geometry(resolution, orientation, bounds, dimensions, phase, depth, quantization, index as u16) {
            Err(error) => Err(error), Ok(value) => Ok(before.push(value)),
        }
    }
}

pub open spec fn part2_subband_resolution_bands(
    style: crate::codestream::CodingStyle, quantization: Part2Quantization, resolution: u8,
    bounds: [u32; 4], dimensions: [u32; 2], depth: [u8; 2], before: Seq<crate::decode::SubbandGeometry>,
) -> Result<Seq<crate::decode::SubbandGeometry>, crate::DecodeError> {
    if resolution == 0 {
        part2_append_subband(before, resolution, crate::tier1::SubbandOrientation::Ll,
            bounds, dimensions, [true, true], depth, quantization, 0)
    } else {
        match (part2_selection_ceil(bounds[0], 2), part2_selection_ceil(bounds[1], 2),
            part2_selection_ceil(bounds[2], 2), part2_selection_ceil(bounds[3], 2)) {
            (Err(error), _, _, _) => Err(error),
            (_, Err(error), _, _) => Err(error),
            (_, _, Err(error), _) => Err(error),
            (_, _, _, Err(error)) => Err(error),
            (Ok(lx0), Ok(ly0), Ok(lx1), Ok(ly1)) => {
                let selector = crate::codestream::decomposition_selector_view(style);
                let phase = [bounds[0] % 2 == 0, bounds[1] % 2 == 0];
                match part1_direction_for_resolution(selector.0, selector.1, resolution) {
                    Err(error) => Err(error),
                    Ok(direction) => {
                        let horizontal = match direction {
                            crate::codestream::DecompositionDirection::Horizontal
                            | crate::codestream::DecompositionDirection::TwoDimensional => true, _ => false,
                        };
                        let vertical = match direction {
                            crate::codestream::DecompositionDirection::Vertical
                            | crate::codestream::DecompositionDirection::TwoDimensional => true, _ => false,
                        };
                        let both = horizontal && vertical;
                        let first = if horizontal {
                            part2_append_subband(before, resolution, crate::tier1::SubbandOrientation::Hl,
                                [(bounds[0] / 2) as u32, if both { ly0 } else { bounds[1] },
                                 (bounds[2] / 2) as u32, if both { ly1 } else { bounds[3] }],
                                dimensions, phase, depth, quantization, before.len())
                        } else { Ok(before) };
                        match first {
                            Err(error) => Err(error),
                            Ok(first) => {
                                let second = if vertical {
                                    part2_append_subband(first, resolution, crate::tier1::SubbandOrientation::Lh,
                                        [if both { lx0 } else { bounds[0] }, (bounds[1] / 2) as u32,
                                         if both { lx1 } else { bounds[2] }, (bounds[3] / 2) as u32],
                                        dimensions, phase, depth, quantization, first.len())
                                } else { Ok(first) };
                                match second {
                                    Err(error) => Err(error),
                                    Ok(second) => if both {
                                        part2_append_subband(second, resolution, crate::tier1::SubbandOrientation::Hh,
                                            [(bounds[0] / 2) as u32, (bounds[1] / 2) as u32,
                                             (bounds[2] / 2) as u32, (bounds[3] / 2) as u32],
                                            dimensions, phase, depth, quantization, second.len())
                                    } else { Ok(second) },
                                }
                            },
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn part2_subband_resolution(
    style: crate::codestream::CodingStyle, bounds: [u32; 4], depth: [u8; 2],
    quantization: Part2Quantization, resolution: u8, before: Seq<crate::decode::SubbandGeometry>,
) -> Result<Seq<crate::decode::SubbandGeometry>, crate::DecodeError> {
    let selector = crate::codestream::decomposition_selector_view(style);
    match part2_resolution_downsampling(selector.0, selector.1, resolution) {
        Err(error) => Err(error),
        Ok(scale) => match (
            part2_selection_ceil(bounds[0], scale.0), part2_selection_ceil(bounds[1], scale.1),
            part2_selection_ceil(bounds[2], scale.0), part2_selection_ceil(bounds[3], scale.1),
        ) {
            (Err(error), _, _, _) => Err(error),
            (_, Err(error), _, _) => Err(error),
            (_, _, Err(error), _) => Err(error),
            (_, _, _, Err(error)) => Err(error),
            (Ok(x0), Ok(y0), Ok(x1), Ok(y1)) => match part1_image_checked_u32(x1 as int - x0 as int) {
                Err(error) => Err(error),
                Ok(width) => match part1_image_checked_u32(y1 as int - y0 as int) {
                    Err(error) => Err(error),
                    Ok(height) => part2_subband_resolution_bands(style, quantization, resolution,
                        [x0, y0, x1, y1], [width, height], depth, before),
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_subband_vector_run(
    style: crate::codestream::CodingStyle, bounds: [u32; 4], depth: [u8; 2],
    quantization: Part2Quantization, expected: u16, resolution: u8, before: Seq<crate::decode::SubbandGeometry>,
) -> Result<Seq<crate::decode::SubbandGeometry>, crate::DecodeError>
    decreases if resolution <= style.decomposition_levels { style.decomposition_levels as int + 1 - resolution as int } else { 0int },
{
    if resolution > style.decomposition_levels {
        if before.len() != expected { Err(part1_block_placement_error(false)) } else { Ok(before) }
    } else {
        match part2_subband_resolution(style, bounds, depth, quantization, resolution, before) {
            Err(error) => Err(error),
            Ok(next) => if resolution == u8::MAX { Err(part1_block_placement_error(true)) }
                else { part2_subband_vector_run(style, bounds, depth, quantization, expected, (resolution + 1) as u8, next) },
        }
    }
}

pub open spec fn part2_component_subbands(
    size: &crate::codestream::ImageSize, style: crate::codestream::CodingStyle,
    quantization: &crate::codestream::Quantization, component: u16, tile: Option<u16>, roi: u8,
) -> Result<Seq<crate::decode::SubbandGeometry>, crate::DecodeError> {
    match part1_image_size_component(crate::codestream::image_size_component_count(size),
        crate::codestream::image_size_component_infos(size), component) {
        Err(error) => Err(error),
        Ok(info) => match part2_component_coordinate_bounds(
            crate::codestream::selection_geometry_view(size), crate::codestream::image_size_component_count(size),
            crate::codestream::image_size_component_infos(size), component, tile) {
            Err(error) => Err(error),
            Ok(bounds) => {
                let selector = crate::codestream::decomposition_selector_view(style);
                part2_subband_vector_run(style, bounds, [info.precision, roi], crate::codestream::quantization_view(quantization),
                    part2_subband_count(selector.0, selector.1), 0, Seq::empty())
            },
        },
    }
}

pub open spec fn part2_component_quantization(values: &crate::codestream::ComponentQuantizations, component: u16)
    -> Result<crate::codestream::Quantization, crate::DecodeError>
{
    part2_component_quantization_owned(crate::codestream::quantization_owner_view(values), component)
}

pub open spec fn part2_component_quantization_owned(values: (u16, Seq<crate::codestream::Quantization>), component: u16)
    -> Result<crate::codestream::Quantization, crate::DecodeError> {
    if component >= values.0 || component as nat >= values.1.len() {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidQuantization })
    } else { Ok(values.1[component as int]) }
}

pub open spec fn part2_roi_shift(shifts: Seq<u8>, component: u16) -> Result<u8, crate::DecodeError> {
    if component as nat >= shifts.len() {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidRegionOfInterest })
    } else { Ok(shifts[component as int]) }
}

pub struct Part2ComponentPlanMetadata {
    pub coding_style: crate::codestream::CodingStyle,
    pub output_resolution: u8,
    pub tier1_style: crate::tier1::Tier1CodingStyle,
    pub bounds: crate::codestream::TileComponentBounds,
    pub width: u32,
    pub height: u32,
    pub x: u32,
    pub y: u32,
    pub subbands: Seq<crate::decode::SubbandGeometry>,
}

pub open spec fn part2_component_plan_metadata(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    quantizations: &crate::codestream::ComponentQuantizations, roi: &crate::codestream::RoiShifts,
    component: u16, selection: (u16, u8), force: bool,
) -> Result<Part2ComponentPlanMetadata, crate::DecodeError> {
    part2_component_plan_metadata_owned(size, styles, crate::codestream::quantization_owner_view(quantizations),
        roi, component, selection, force)
}

pub open spec fn part2_component_plan_metadata_owned(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    quantizations: (u16, Seq<crate::codestream::Quantization>), roi: &crate::codestream::RoiShifts,
    component: u16, selection: (u16, u8), force: bool,
) -> Result<Part2ComponentPlanMetadata, crate::DecodeError> {
    match crate::codestream::component_coding_style_result(styles, component) {
        Err(error) => Err(error),
        Ok(style) => if selection.1 > style.decomposition_levels {
            Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
        } else {
            let output = (style.decomposition_levels - selection.1) as u8;
            match part2_component_quantization_owned(quantizations, component) {
                Err(error) => Err(error),
                Ok(quantization) => match crate::codestream::coding_style_tier1_result(style) {
                    Err(error) => Err(error),
                    Ok(initial_style) => {
                        let tier1_style = if force && ht_block_coding_enabled(initial_style.block_coding) {
                            part2_tier1_force_style(initial_style, true).1
                        } else { initial_style };
                        match part2_tile_component_bounds(crate::codestream::selection_geometry_view(size),
                            crate::codestream::image_size_component_count(size),
                            crate::codestream::image_size_component_infos(size), selection.0, component) {
                            Err(error) => Err(error),
                            Ok(bounds) => match part2_resolution_geometry(
                                crate::codestream::selection_geometry_view(size),
                                crate::codestream::image_size_component_count(size),
                                crate::codestream::image_size_component_infos(size),
                                crate::decode::resolution_geometry_style(style), component, output, Some(selection.0),
                            ) {
                                Err(error) => Err(error),
                                Ok(geometry) => {
                                    let selector = crate::codestream::decomposition_selector_view(style);
                                    match part2_resolution_downsampling(selector.0, selector.1, output) {
                                        Err(error) => Err(error),
                                        Ok(scale) => match part1_image_size_component(
                                            crate::codestream::image_size_component_count(size),
                                            crate::codestream::image_size_component_infos(size), component) {
                                            Err(error) => Err(error),
                                            Ok(info) => {
                                                let size_view = crate::codestream::selection_geometry_view(size);
                                                match part2_selection_ceil(size_view.2, info.x_subsampling as u32) {
                                                    Err(error) => Err(error),
                                                    Ok(origin_x) => match part2_selection_ceil(size_view.3, info.y_subsampling as u32) {
                                                        Err(error) => Err(error),
                                                        Ok(origin_y) => match part2_selection_ceil(bounds.x0, scale.0) {
                                                            Err(error) => Err(error),
                                                            Ok(x0) => match part2_selection_ceil(origin_x, scale.0) {
                                                                Err(error) => Err(error),
                                                                Ok(ix0) => match part1_image_checked_u32(x0 as int - ix0 as int) {
                                                                    Err(error) => Err(error),
                                                                    Ok(x) => match part2_selection_ceil(bounds.y0, scale.1) {
                                                                        Err(error) => Err(error),
                                                                        Ok(y0) => match part2_selection_ceil(origin_y, scale.1) {
                                                                            Err(error) => Err(error),
                                                                            Ok(iy0) => match part1_image_checked_u32(y0 as int - iy0 as int) {
                                                                                Err(error) => Err(error),
                                                                                Ok(y) => match part2_roi_shift(crate::codestream::roi_shifts_view(roi), component) {
                                                                                    Err(error) => Err(error),
                                                                                    Ok(shift) => match part2_component_subbands(
                                                                                        size, style, &quantization, component, Some(selection.0), shift) {
                                                                                        Err(error) => Err(error),
                                                                                        Ok(subbands) => Ok(Part2ComponentPlanMetadata {
                                                                                            coding_style: style, output_resolution: output,
                                                                                            tier1_style, bounds, width: geometry.width, height: geometry.height,
                                                                                            x, y, subbands,
                                                                                        }),
                                                                                    },
                                                                                },
                                                                            },
                                                                        },
                                                                    },
                                                                },
                                                            },
                                                        },
                                                    },
                                                }
                                            },
                                        },
                                    }
                                },
                            },
                        }
                    },
                },
            }
        },
    }
}

pub type Part2ResolutionStyle = (u8, Seq<crate::codestream::DecompositionDirection>, u16, u16, Seq<(u8, u8)>);
pub type Part2ComponentResolutionCounts = (u8, Seq<u8>, Seq<u8>);

#[verifier::opaque]
pub open spec fn part2_component_resolution_counts_run(
    components: u16, styles: &crate::codestream::ComponentCodingStyles, discard: u8,
    component: u16, maximum: u8, resolutions: Seq<u8>, selected: Seq<u8>,
) -> Result<Part2ComponentResolutionCounts, crate::DecodeError>
    decreases if component < components { (components as nat - component as nat) as nat } else { 0nat },
{
    if component >= components { Ok((maximum, resolutions, selected)) } else {
        match crate::codestream::component_coding_style_result(styles, component) {
            Err(error) => Err(error),
            Ok(style) => if style.decomposition_levels == u8::MAX {
                Err(part1_block_placement_error(true))
            } else {
                let count = (style.decomposition_levels + 1) as u8;
                let maximum = if count > maximum { count } else { maximum };
                let resolutions = resolutions.push(count);
                if discard >= count {
                    Err(crate::DecodeError::InvalidSelection {
                        reason: crate::SelectionError::ReductionTooLarge,
                    })
                } else {
                    part2_component_resolution_counts_run(
                        components, styles, discard, (component + 1) as u16,
                        maximum, resolutions, selected.push((count - discard) as u8),
                    )
                }
            },
        }
    }
}

pub open spec fn part2_component_resolution_counts(
    components: u16, styles: &crate::codestream::ComponentCodingStyles, discard: u8,
) -> Result<Part2ComponentResolutionCounts, crate::DecodeError> {
    part2_component_resolution_counts_run(components, styles, discard, 0, 0, Seq::empty(), Seq::empty())
}

pub open spec fn part2_packet_grid_subband_delta(style: crate::codestream::CodingStyle, resolution: u8)
    -> Result<usize, crate::DecodeError>
{
    let selector = crate::codestream::decomposition_selector_view(style);
    match part1_subband_count_through_resolution(selector.0, selector.1, resolution) {
        Err(error) => Err(error),
        Ok(current) => match if resolution == 0 { Ok(0usize) } else {
            part1_subband_count_through_resolution(selector.0, selector.1, (resolution - 1) as u8)
        } {
            Err(error) => Err(error),
            Ok(previous) => if current < previous { Err(part1_block_placement_error(true)) }
                else { Ok((current - previous) as usize) },
        },
    }
}

pub open spec fn part2_packet_grid_codeblocks(total: u64, blocks: u64, selected: bool, limits: &crate::ResourceLimits)
    -> Result<u64, crate::DecodeError>
{
    if !selected { Ok(total) } else {
        let next = total as int + blocks as int;
        if next > u64::MAX { Err(part1_block_placement_error(true)) }
        else if next > crate::limits::resource_code_block_limit(limits) {
            Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::CodeBlocks,
                limit: crate::limits::resource_code_block_limit(limits), actual: next as u64,
            })
        } else { Ok(next as u64) }
    }
}

#[verifier::opaque]
pub open spec fn part2_packet_grid_components_run(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    layers: u16, limits: &crate::ResourceLimits, tile: Option<u16>, discard: u8,
    descriptors: Part2ComponentResolutionCounts, component: u16, counts: Seq<u32>, total: u64,
) -> Result<Part1PacketGrid, crate::DecodeError>
    decreases if component < crate::codestream::image_size_component_count(size) {
        (crate::codestream::image_size_component_count(size) as nat - component as nat) as nat
    } else { 0nat }, 1nat, 0nat,
{
    if component >= crate::codestream::image_size_component_count(size) {
        part1_packet_grid_new(layers, crate::codestream::image_size_component_count(size), descriptors.1, counts,
            if discard == 0 { None } else { Some(descriptors.2) }, limits)
    } else {
        match crate::codestream::component_coding_style_result(styles, component) {
            Err(error) => Err(error),
            Ok(style) => if style.decomposition_levels == u8::MAX {
                Err(part1_block_placement_error(true))
            } else {
                part2_packet_grid_resolutions_run(
                    size, styles, layers, limits, tile, discard, descriptors, component,
                    style, (style.decomposition_levels + 1) as u8, 0, counts, total,
                )
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_packet_grid_resolutions_run(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    layers: u16, limits: &crate::ResourceLimits, tile: Option<u16>, discard: u8,
    descriptors: Part2ComponentResolutionCounts, component: u16,
    style: crate::codestream::CodingStyle, resolutions: u8, resolution: u8, counts: Seq<u32>, total: u64,
) -> Result<Part1PacketGrid, crate::DecodeError>
    decreases if component < crate::codestream::image_size_component_count(size) {
        (crate::codestream::image_size_component_count(size) as nat - component as nat) as nat
    } else { 0nat },
        0nat, if resolution < descriptors.0 { (descriptors.0 as nat - resolution as nat) as nat } else { 0nat },
{
    if component >= crate::codestream::image_size_component_count(size) { Err(part1_block_placement_error(false)) }
    else if resolution >= descriptors.0 {
        part2_packet_grid_components_run(size, styles, layers, limits, tile, discard,
            descriptors, (component + 1) as u16, counts, total)
    } else if resolution >= resolutions {
        part2_packet_grid_resolutions_run(size, styles, layers, limits, tile, discard,
            descriptors, component, style, resolutions, (resolution + 1) as u8, counts.push(0), total)
    } else {
        match part2_resolution_geometry(
            crate::codestream::selection_geometry_view(size), crate::codestream::image_size_component_count(size),
            crate::codestream::image_size_component_infos(size), crate::decode::resolution_geometry_style(style),
            component, resolution, tile,
        ) {
            Err(error) => Err(error),
            Ok(geometry) => match part2_packet_grid_subband_delta(style, resolution) {
                Err(error) => Err(error),
                Ok(subbands) => if discard > resolutions {
                    Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
                } else {
                    match part2_packet_grid_codeblocks(total, geometry.code_blocks,
                        resolution < resolutions - discard, limits) {
                        Err(error) => Err(error),
                        Ok(next_total) => {
                            if subbands != 0 && geometry.precincts > u32::MAX {
                                Err(part1_block_placement_error(true))
                            } else {
                                part2_packet_grid_resolutions_run(size, styles, layers, limits, tile, discard,
                                    descriptors, component, style, resolutions, (resolution + 1) as u8,
                                    counts.push(if subbands == 0 { 0u32 } else { geometry.precincts as u32 }), next_total)
                            }
                        },
                    }
                },
            },
        }
    }
}

pub open spec fn part2_packet_grid_from_components(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    layers: u16, limits: &crate::ResourceLimits, tile: Option<u16>, discard: u8,
) -> Result<Part1PacketGrid, crate::DecodeError> {
    match part2_component_resolution_counts(crate::codestream::image_size_component_count(size), styles, discard) {
        Err(error) => Err(error),
        Ok(descriptors) => if crate::codestream::image_size_component_count(size) as int * descriptors.0 as int > usize::MAX {
            Err(part1_block_placement_error(true))
        } else {
            part2_packet_grid_components_run(size, styles, layers, limits, tile, discard,
                descriptors, 0, Seq::empty(), 0)
        },
    }
}

pub open spec fn part2_component_coordinate_bounds(
    size: Part2SelectionGeometry, count: u16, infos: Seq<crate::codestream::ComponentInfo>,
    component: u16, tile_index: Option<u16>,
) -> Result<[u32; 4], crate::DecodeError> {
    match tile_index {
        Some(tile) => match part2_tile_component_bounds(size, count, infos, tile, component) {
            Err(error) => Err(error),
            Ok(bounds) => Ok([bounds.x0, bounds.y0, bounds.x1, bounds.y1]),
        },
        None => match part1_image_size_component(count, infos, component) {
            Err(error) => Err(error),
            Ok(info) => match part1_image_checked_u32(size.2 as int + size.0 as int) {
                Err(error) => Err(error),
                Ok(x1) => match part1_image_checked_u32(size.3 as int + size.1 as int) {
                    Err(error) => Err(error),
                    Ok(y1) => match (
                        part2_selection_ceil(size.2, info.x_subsampling as u32),
                        part2_selection_ceil(size.3, info.y_subsampling as u32),
                        part2_selection_ceil(x1, info.x_subsampling as u32),
                        part2_selection_ceil(y1, info.y_subsampling as u32),
                    ) {
                        (Err(error), _, _, _) => Err(error),
                        (_, Err(error), _, _) => Err(error),
                        (_, _, Err(error), _) => Err(error),
                        (_, _, _, Err(error)) => Err(error),
                        (Ok(x0), Ok(y0), Ok(x1), Ok(y1)) => Ok([x0, y0, x1, y1]),
                    },
                },
            },
        },
    }
}

pub open spec fn part2_geometry_grid_product(across: u32, down: u32)
    -> Result<(u32, u32, u64), crate::DecodeError>
{
    let total = across as int * down as int;
    if total > u64::MAX { Err(part1_block_placement_error(true)) }
    else { Ok((across, down, total as u64)) }
}

pub open spec fn part2_resolution_codeblock_grid(bounds: [u32; 4], width: u32, height: u32)
    -> Result<(u32, u32, u64), crate::DecodeError>
{
    match part2_selection_ceil(bounds[2], width) {
        Err(error) => Err(error),
        Ok(x1) => match part2_selection_floor(bounds[0], width) {
            Err(error) => Err(error),
            Ok(x0) => match part1_image_checked_u32(x1 as int - x0 as int) {
                Err(error) => Err(error),
                Ok(across) => match part2_selection_ceil(bounds[3], height) {
                    Err(error) => Err(error),
                    Ok(y1) => match part2_selection_floor(bounds[1], height) {
                        Err(error) => Err(error),
                        Ok(y0) => match part1_image_checked_u32(y1 as int - y0 as int) {
                            Err(error) => Err(error),
                            Ok(down) => part2_geometry_grid_product(across, down),
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn part2_resolution_precinct_grid(bounds: [u32; 4], width: u32, height: u32)
    -> Result<(u32, u32, u64), crate::DecodeError>
{
    match part2_selection_floor(bounds[0], width) {
        Err(error) => Err(error),
        Ok(x0) => match part2_selection_floor(bounds[1], height) {
            Err(error) => Err(error),
            Ok(y0) => match part2_selection_ceil(bounds[2], width) {
                Err(error) => Err(error),
                Ok(x1) => match part2_selection_ceil(bounds[3], height) {
                    Err(error) => Err(error),
                    Ok(y1) => match part1_image_checked_u32(x1 as int - x0 as int) {
                        Err(error) => Err(error),
                        Ok(across) => match part1_image_checked_u32(y1 as int - y0 as int) {
                            Err(error) => Err(error),
                            Ok(down) => part2_geometry_grid_product(across, down),
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn part2_resolution_geometry_counts(
    bounds: [u32; 4], style: Part2ResolutionStyle, component: u16, resolution: u8,
) -> Result<crate::decode::ComponentResolutionGeometry, crate::DecodeError> {
    match part1_image_checked_u32(bounds[2] as int - bounds[0] as int) {
        Err(error) => Err(error),
        Ok(width) => match part1_image_checked_u32(bounds[3] as int - bounds[1] as int) {
            Err(error) => Err(error),
            Ok(height) => if style.2 == 0 || style.3 == 0 { Err(part1_block_placement_error(false)) } else {
                match part2_resolution_codeblock_grid(bounds, style.2 as u32, style.3 as u32) {
                    Err(error) => Err(error),
                    Ok(blocks) => match part2_precinct_exponents(style.0, style.4, resolution) {
                        Err(error) => Err(error),
                        Ok(exponents) => if exponents.0 > 31 || exponents.1 > 31 {
                            Err(part1_block_placement_error(false))
                        } else {
                            match part2_resolution_precinct_grid(
                                bounds, 1u32 << (exponents.0 as u32), 1u32 << (exponents.1 as u32),
                            ) {
                                Err(error) => Err(error),
                                Ok(precincts) => Ok(crate::decode::ComponentResolutionGeometry {
                                    component, resolution, width, height,
                                    subbands: if resolution == 0 { 1u8 } else { 3u8 },
                                    code_blocks_across: blocks.0, code_blocks_down: blocks.1, code_blocks: blocks.2,
                                    precincts_across: precincts.0, precincts_down: precincts.1, precincts: precincts.2,
                                }),
                            }
                        },
                    },
                }
            },
        },
    }
}

pub open spec fn part2_resolution_geometry(
    size: Part2SelectionGeometry, count: u16, infos: Seq<crate::codestream::ComponentInfo>,
    style: Part2ResolutionStyle, component: u16, resolution: u8, tile_index: Option<u16>,
) -> Result<crate::decode::ComponentResolutionGeometry, crate::DecodeError> {
    if resolution > style.0 { Err(part1_block_placement_error(false)) } else {
        match part2_component_coordinate_bounds(size, count, infos, component, tile_index) {
            Err(error) => Err(error),
            Ok(bounds) => match part2_resolution_downsampling(style.0, style.1, resolution) {
                Err(error) => Err(error),
                Ok(scale) => match (
                    part2_selection_ceil(bounds[0], scale.0),
                    part2_selection_ceil(bounds[1], scale.1),
                    part2_selection_ceil(bounds[2], scale.0),
                    part2_selection_ceil(bounds[3], scale.1),
                ) {
                    (Err(error), _, _, _) => Err(error),
                    (_, Err(error), _, _) => Err(error),
                    (_, _, Err(error), _) => Err(error),
                    (_, _, _, Err(error)) => Err(error),
                    (Ok(x0), Ok(y0), Ok(x1), Ok(y1)) => {
                        part2_resolution_geometry_counts([x0, y0, x1, y1], style, component, resolution)
                    },
                },
            },
        }
    }
}

pub open spec fn part2_color_target(region: Seq<u32>, discard: u8) -> Result<Seq<u32>, crate::DecodeError> {
    if discard >= 32 {
        Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
    } else {
        let scale = 1u32 << (discard as u32);
        match part2_selection_ceil(region[0], scale) {
            Err(error) => Err(error),
            Ok(x0) => match part2_selection_ceil(region[1], scale) {
                Err(error) => Err(error),
                Ok(y0) => match part2_selection_ceil(region[2], scale) {
                    Err(error) => Err(error),
                    Ok(x1) => match part2_selection_ceil(region[3], scale) {
                        Err(error) => Err(error), Ok(y1) => Ok(seq![x0, y0, x1, y1]),
                    },
                },
            },
        }
    }
}

pub open spec fn part2_color_sampling_step(previous: (u32, u32), info: crate::codestream::ComponentInfo, target: Seq<u32>)
    -> Result<(u32, u32), crate::DecodeError>
{
    if info.x_subsampling == 0 || info.y_subsampling == 0 { Err(part1_block_placement_error(false)) }
    else {
        let x = if target[0] as nat * 65536 <= info.x_registration as nat { 0nat }
            else { (target[0] as nat * 65536 - info.x_registration as nat) as nat };
        let y = if target[1] as nat * 65536 <= info.y_registration as nat { 0nat }
            else { (target[1] as nat * 65536 - info.y_registration as nat) as nat };
        Ok((
            if x % (info.x_subsampling as nat * 65536) == 0 { previous.0 } else { if previous.0 >= info.x_subsampling as u32 { previous.0 } else { info.x_subsampling as u32 } },
            if y % (info.y_subsampling as nat * 65536) == 0 { previous.1 } else { if previous.1 >= info.y_subsampling as u32 { previous.1 } else { info.y_subsampling as u32 } },
        ))
    }
}

#[verifier::opaque]
pub open spec fn part2_color_sampling_prefix(components: Seq<crate::codestream::ComponentInfo>, count: u16, target: Seq<u32>, prefix: nat)
    -> Result<(u32, u32), crate::DecodeError>
    decreases prefix,
{
    if prefix == 0 { Ok((0, 0)) }
    else {
        match part2_color_sampling_prefix(components, count, target, (prefix - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_image_size_component(count, components, (prefix - 1) as u16) {
                Err(error) => Err(error), Ok(info) => part2_color_sampling_step(previous, info, target),
            },
        }
    }
}

pub open spec fn part2_color_selection_context(
    x_origin: u32, y_origin: u32, components: Seq<crate::codestream::ComponentInfo>, count: u16,
    selected: Part2ValidatedSelection,
) -> Result<(Part2DecodeSelection, Seq<u32>), crate::DecodeError> {
    match part2_color_target(selected.1, selected.2) {
        Err(error) => Err(error),
        Ok(target) => match part2_color_sampling_prefix(components, count, target, count as nat) {
            Err(error) => Err(error),
            Ok(context) => {
                let scale = 1u32 << (selected.2 as u32);
                let horizontal = if context.0 as nat * scale as nat > u32::MAX { u32::MAX } else { (context.0 as nat * scale as nat) as u32 };
                let vertical = if context.1 as nat * scale as nat > u32::MAX { u32::MAX } else { (context.1 as nat * scale as nat) as u32 };
                let x0 = if selected.1[0] <= horizontal { 0u32 } else { (selected.1[0] - horizontal) as u32 };
                let y0 = if selected.1[1] <= vertical { 0u32 } else { (selected.1[1] - vertical) as u32 };
                let x0 = if x0 >= x_origin { x0 } else { x_origin };
                let y0 = if y0 >= y_origin { y0 } else { y_origin };
                if selected.1[2] < x0 || selected.1[3] < y0 { Err(part1_block_placement_error(true)) }
                else {
                    Ok(((Part2TileSelection::All, Some(crate::ImageRegion {
                        x: x0, y: y0, width: (selected.1[2] - x0) as u32, height: (selected.1[3] - y0) as u32,
                    }), selected.2), target))
                }
            },
        },
    }
}

pub open spec fn part2_atk_checked_isize(value: int) -> Result<isize, crate::DecodeError> {
    if value < isize::MIN || value > isize::MAX { Err(part1_transform_error(true)) } else { Ok(value as isize) }
}

pub open spec fn part2_atk_checked_i128(value: int) -> Result<i128, crate::DecodeError> {
    if value < i128::MIN || value > i128::MAX { Err(part1_transform_error(true)) } else { Ok(value as i128) }
}

pub open spec fn part2_atk_round_shift(value: i128, shift: u32) -> Result<i128, crate::DecodeError> {
    if shift == 0 || shift >= 128 { Err(part1_transform_error(true)) }
    else {
        let half = 1i128 << (shift - 1);
        let adjusted = if value >= 0 { value as int + half as int } else { value as int - half as int };
        match part2_atk_checked_i128(adjusted) {
            Err(error) => Err(error),
            Ok(adjusted) => Ok(adjusted >> shift),
        }
    }
}

pub open spec fn part2_atk_fixed_mul(value: i64, factor: i64) -> Result<i64, crate::DecodeError> {
    match part2_atk_checked_i128(value as int * factor as int) {
        Err(error) => Err(error),
        Ok(product) => match part2_atk_round_shift(product, 32) {
            Err(error) => Err(error),
            Ok(rounded) => part1_checked_sample(rounded as int),
        },
    }
}

pub open spec fn part2_atk_fixed_div(value: i64, divisor: i64) -> Result<i64, crate::DecodeError> {
    if divisor == 0 { Err(part1_transform_error(true)) }
    else {
        match part2_atk_checked_i128(value as int * 0x1_0000_0000int) {
            Err(error) => Err(error),
            Ok(numerator) => {
                if numerator == i128::MIN && divisor == -1 { Err(part1_transform_error(true)) }
                else { part1_checked_sample((vstd::arithmetic::div_mod::rust_div(numerator as int, divisor as int) as i128) as int) }
            },
        }
    }
}

pub open spec fn part2_atk_checked_i32(value: int) -> Result<i32, crate::DecodeError> {
    if value < i32::MIN || value > i32::MAX { Err(part1_transform_error(true)) } else { Ok(value as i32) }
}

pub open spec fn part2_atk_binary_magnitude(significand: u128, binary_exponent: i32)
    -> Result<u128, crate::DecodeError>
{
    match part2_atk_checked_i32(binary_exponent as int + 32) {
        Err(error) => Err(error),
        Ok(shift) => {
            if shift >= 0 {
                let left = shift as u32;
                if left >= 128 || significand > (u128::MAX >> left) { Err(part1_transform_error(true)) }
                else { Ok(significand << left) }
            } else {
                match part2_atk_checked_i32(-(shift as int)) {
                    Err(error) => Err(error),
                    Ok(right) => {
                        let right = right as u32;
                        if right >= 128 { Ok(0) }
                        else {
                            let truncated = significand >> right;
                            let mask = if right == 0 { 0u128 } else { ((1u128 << right) - 1) as u128 };
                            let remainder = significand & mask;
                            let half = if right == 0 { 0u128 } else { 1u128 << (right - 1) };
                            let rounded = truncated as int + if remainder > half || (remainder == half && truncated & 1 != 0) { 1int } else { 0int };
                            if rounded > u128::MAX { Err(part1_transform_error(true)) } else { Ok(rounded as u128) }
                        }
                    },
                }
            }
        },
    }
}

pub open spec fn part2_atk_binary_q32(negative: bool, significand: u128, binary_exponent: i32)
    -> Result<i64, crate::DecodeError>
{
    match part2_atk_binary_magnitude(significand, binary_exponent) {
        Err(error) => Err(error),
        Ok(magnitude) => {
            if magnitude > i128::MAX as u128 { Err(part1_transform_error(true)) }
            else { part1_checked_sample(if negative { -(magnitude as int) } else { magnitude as int }) }
        },
    }
}

pub open spec fn part2_atk_binary_format(
    bits: u128, total_bits: u32, exponent_bits: u32, fraction_bits: u32, bias: i32,
) -> Result<i64, crate::DecodeError> {
    if total_bits == 0 || total_bits > 128 || exponent_bits == 0 || exponent_bits >= 128 || fraction_bits >= 128 {
        Err(part1_transform_error(false))
    } else {
        let negative = bits >> (total_bits - 1) != 0;
        let mask = ((1u128 << exponent_bits) - 1) as u128;
        let exponent = (bits >> fraction_bits) & mask;
        let fraction = bits & ((1u128 << fraction_bits) - 1) as u128;
        if exponent == mask { Err(part1_transform_error(false)) }
        else if exponent == 0 && fraction == 0 { Ok(0) }
        else {
            let base = if exponent == 0 { Ok(1i32) }
                else if exponent > i32::MAX as u128 { Err(part1_transform_error(true)) }
                else { Ok(exponent as i32) };
            match base {
                Err(error) => Err(error),
                Ok(base) => match part2_atk_checked_i32(base as int - bias as int) {
                    Err(error) => Err(error),
                    Ok(unbiased) => match part2_atk_checked_i32(unbiased as int - fraction_bits as int) {
                        Err(error) => Err(error),
                        Ok(binary_exponent) => part2_atk_binary_q32(negative,
                            if exponent == 0 { fraction } else { (1u128 << fraction_bits) | fraction },
                            binary_exponent),
                    },
                },
            }
        }
    }
}

pub open spec fn part2_atk_fixed_coefficient(coefficient: Part2RawKernelCoefficient, kind: u8)
    -> Result<i64, crate::DecodeError>
{
    let bits = part2_atk_bytes_prefix(coefficient.0, 16);
    if kind <= 1 {
        match part2_atk_integer(coefficient, kind) {
            Err(error) => Err(error),
            Ok(integer) => match part2_atk_checked_i128(integer as int * 0x1_0000_0000int) {
                Err(error) => Err(error), Ok(scaled) => part1_checked_sample(scaled as int),
            },
        }
    } else if kind == 2 { part2_atk_binary_format(bits, 32, 8, 23, 127) }
    else if kind == 3 { part2_atk_binary_format(bits, 64, 11, 52, 1023) }
    else if kind == 4 { part2_atk_binary_format(bits, 128, 15, 112, 16383) }
    else { Err(part1_transform_error(false)) }
}

pub open spec fn part2_atk_bytes_prefix(bytes: Seq<u8>, count: nat) -> u128
    decreases count,
{
    if count == 0 { 0u128 }
    else { (part2_atk_bytes_prefix(bytes, (count - 1) as nat) << 8u32) | bytes[count - 1] as u128 }
}

pub open spec fn part2_atk_integer(coefficient: Part2RawKernelCoefficient, kind: u8) -> Result<i128, crate::DecodeError> {
    if kind > 1 { Err(part1_transform_error(false)) }
    else { Ok(part2_atk_bytes_prefix(coefficient.0, 16) as i128) }
}

#[verifier::opaque]
pub open spec fn part2_atk_extended(samples: Seq<i64>, index: isize, whole: bool) -> Result<i64, crate::DecodeError> {
    if samples.len() == 0 { Err(part1_transform_error(false)) }
    else if samples.len() == 1 { Ok(samples[0]) }
    else if samples.len() > isize::MAX { Err(part1_transform_error(true)) }
    else {
        let length = samples.len() as isize;
        let adjusted = if whole {
            if index < 0 { part2_atk_checked_isize(-(index as int)) } else { Ok(index) }
        } else { Ok(index) };
        match adjusted {
            Err(error) => Err(error),
            Ok(position) => {
                let mapped = if whole {
                    if position < length { Ok(position) } else {
                        match part2_atk_checked_isize(2 * (length as int - 1)) {
                            Err(error) => Err(error),
                            Ok(period) => {
                                let wrapped = (position as int) % (period as int);
                                Ok((if wrapped < length { wrapped } else { period as int - wrapped }) as isize)
                            },
                        }
                    }
                } else {
                    let parity = index & 1isize;
                    let end = length - 1;
                    let last = if (end as isize & 1isize) == parity { end } else { length - 2 };
                    Ok((if position < parity { parity as int } else if position > last { last } else { position as int }) as isize)
                };
                match mapped {
                    Err(error) => Err(error),
                    Ok(final_index) => if final_index < 0 || final_index > usize::MAX { Err(part1_transform_error(true)) }
                        else if final_index >= samples.len() { Err(part1_transform_error(false)) }
                        else { Ok(samples[final_index as int]) },
                }
            },
        }
    }
}

pub open spec fn part2_atk_half_index(target: isize, coefficient: isize, offset: i8) -> Result<isize, crate::DecodeError> {
    match part2_atk_checked_isize(coefficient as int + offset as int) {
        Err(error) => Err(error),
        Ok(position) => match part2_atk_checked_isize(2 * position as int) {
            Err(error) => Err(error),
            Ok(distance) => match part2_atk_checked_isize(1 - 2 * (target & 1isize) as int + distance as int) {
                Err(error) => Err(error),
                Ok(delta) => part2_atk_checked_isize(target as int + delta as int),
            },
        },
    }
}

pub open spec fn part2_atk_source_sum(samples: Seq<i64>, target: usize, coefficient: usize, offset: i8, filter: bool, extension: bool)
    -> Result<i64, crate::DecodeError>
{
    if target > isize::MAX || coefficient > isize::MAX { Err(part1_transform_error(true)) } else {
        let position = target as isize;
        let tap = coefficient as isize;
        if filter {
            match part2_atk_checked_isize(2 * tap as int) {
                Err(error) => Err(error),
                Ok(doubled) => match part2_atk_checked_isize(doubled as int + 1) {
                    Err(error) => Err(error),
                    Ok(distance) => match part2_atk_checked_isize(position as int - distance as int) {
                        Err(error) => Err(error),
                        Ok(left_index) => match part2_atk_extended(samples, left_index, extension) {
                            Err(error) => Err(error),
                            Ok(left) => match part2_atk_checked_isize(position as int + distance as int) {
                                Err(error) => Err(error),
                                Ok(right_index) => match part2_atk_extended(samples, right_index, extension) {
                                    Err(error) => Err(error),
                                    Ok(right) => part1_checked_sample(left as int + right as int),
                                },
                            },
                        },
                    },
                },
            }
        } else {
            match part2_atk_half_index(position, tap, offset) {
                Err(error) => Err(error), Ok(index) => part2_atk_extended(samples, index, extension),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_atk_sum(samples: Seq<i64>, target: usize, step: Part2RawKernelStep, kind: u8, filter: bool, extension: bool, count: nat)
    -> Result<i128, crate::DecodeError>
    decreases count,
{
    if count == 0 {
        match step.2 { None => Err(part1_transform_error(false)), Some(residue) => part2_atk_integer(residue, kind) }
    } else {
        match part2_atk_sum(samples, target, step, kind, filter, extension, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => if count > step.3.len() { Err(part1_transform_error(false)) } else {
                match part2_atk_integer(step.3[count - 1], kind) {
                    Err(error) => Err(error),
                    Ok(alpha) => match part2_atk_source_sum(samples, target, (count - 1) as usize, step.0, filter, extension) {
                        Err(error) => Err(error),
                        Ok(contribution) => match part2_atk_checked_i128(alpha as int * contribution as int) {
                            Err(error) => Err(error),
                            Ok(product) => part2_atk_checked_i128(previous as int + product as int),
                        },
                    },
                }
            },
        }
    }
}

pub open spec fn part2_atk_reversible_target(samples: Seq<i64>, target: usize, step: Part2RawKernelStep, kernel: Part2RawKernel)
    -> Result<i64, crate::DecodeError> {
    match part2_atk_sum(samples, target, step, kernel.1, kernel.2, kernel.4, step.3.len()) {
        Err(error) => Err(error),
        Ok(sum) => if step.1 >= 127 { Err(part1_transform_error(false)) } else {
            match part2_atk_checked_i128(samples[target as int] as int - (sum >> (step.1 as u32)) as int) {
                Err(error) => Err(error), Ok(updated) => part1_checked_sample(updated as int),
            }
        },
    }
}

pub open spec fn part2_atk_target_passes(length: nat, start: usize) -> Result<usize, crate::DecodeError> {
    if length < start || length - start + 1 > usize::MAX { Err(part1_transform_error(true)) }
    else { Ok(((length - start + 1) / 2) as usize) }
}

#[verifier::opaque]
pub open spec fn part2_atk_irreversible_sum(
    samples: Seq<i64>, target: usize, step: Part2RawKernelStep, kernel: Part2RawKernel, count: nat,
) -> Result<i128, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(0) }
    else {
        match part2_atk_irreversible_sum(samples, target, step, kernel, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                if count - 1 >= step.3.len() { Err(part1_transform_error(false)) }
                else {
                    match part2_atk_fixed_coefficient(step.3[count - 1], kernel.1) {
                        Err(error) => Err(error),
                        Ok(alpha) => match part2_atk_source_sum(samples, target, (count - 1) as usize, step.0, kernel.2, kernel.4) {
                            Err(error) => Err(error),
                            Ok(contribution) => match part2_atk_checked_i128(alpha as int * contribution as int) {
                                Err(error) => Err(error),
                                Ok(product) => part2_atk_checked_i128(previous as int + product as int),
                            },
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn part2_atk_irreversible_target(
    samples: Seq<i64>, target: usize, step: Part2RawKernelStep, kernel: Part2RawKernel,
) -> Result<i64, crate::DecodeError> {
    match part2_atk_irreversible_sum(samples, target, step, kernel, step.3.len()) {
        Err(error) => Err(error),
        Ok(adjustment) => match part2_atk_round_shift(adjustment, 32) {
            Err(error) => Err(error),
            Ok(rounded) => match part1_checked_sample(rounded as int) {
                Err(error) => Err(error),
                Ok(converted) => part1_checked_sample(samples[target as int] as int - converted as int),
            },
        },
    }
}

pub open spec fn part2_atk_target(
    samples: Seq<i64>, target: usize, step: Part2RawKernelStep, kernel: Part2RawKernel,
) -> Result<i64, crate::DecodeError> {
    if kernel.0 { part2_atk_reversible_target(samples, target, step, kernel) }
    else { part2_atk_irreversible_target(samples, target, step, kernel) }
}

#[verifier::opaque]
pub open spec fn part2_atk_target_prefix(
    original: Seq<i64>, step: Part2RawKernelStep, kernel: Part2RawKernel, start: usize, count: nat,
) -> Part2AtkMutation
    decreases count,
{
    if count == 0 { (Ok(()), original) } else {
        let previous = part2_atk_target_prefix(original, step, kernel, start, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => {
                let target = (start as nat + 2 * (count - 1)) as usize;
                match part2_atk_target(previous.1, target, step, kernel) {
                    Err(error) => (Err(error), previous.1),
                    Ok(value) => {
                        let updated = previous.1.update(target as int, value);
                        if target as nat + 2 > usize::MAX { (Err(part1_transform_error(true)), updated) }
                        else { (Ok(()), updated) }
                    },
                }
            },
        }
    }
}

pub open spec fn part2_atk_step(samples: Seq<i64>, step: Part2RawKernelStep, kernel: Part2RawKernel, low_first: bool, update_odd: bool) -> Part2AtkMutation {
    let start = if (if low_first { update_odd } else { !update_odd }) { 1usize } else { 0usize };
    match part2_atk_target_passes(samples.len(), start) {
        Err(error) => (Err(error), samples),
        Ok(count) => part2_atk_target_prefix(samples, step, kernel, start, count as nat),
    }
}

#[verifier::opaque]
pub open spec fn part2_atk_steps(original: Seq<i64>, kernel: Part2RawKernel, low_first: bool, count: nat) -> Part2AtkMutation
    decreases count,
{
    if count == 0 { (Ok(()), original) } else {
        let previous = part2_atk_steps(original, kernel, low_first, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_atk_step(previous.1, kernel.6[kernel.6.len() - count], kernel, low_first,
                if count % 2 == 1 { kernel.3 } else { !kernel.3 }),
        }
    }
}

pub open spec fn part2_atk_half(value: i64) -> i64 {
    (if value < 0 { -(-(value as int) / 2) } else { value as int / 2 }) as i64
}

pub open spec fn part2_atk_scale_sample(value: i64, factor: i64, low_first: bool, index: usize)
    -> Result<i64, crate::DecodeError>
{
    if (index & 1 == 0) == low_first { part2_atk_fixed_mul(value, factor) }
    else { part2_atk_fixed_div(value, factor) }
}

#[verifier::opaque]
pub open spec fn part2_atk_scale_prefix(original: Seq<i64>, factor: i64, low_first: bool, count: nat)
    -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(original) }
    else {
        match part2_atk_scale_prefix(original, factor, low_first, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_atk_scale_sample(previous[count - 1], factor, low_first, (count - 1) as usize) {
                Err(error) => Err(error),
                Ok(value) => Ok(previous.update((count - 1) as int, value)),
            },
        }
    }
}

pub open spec fn part2_atk_scaled_input(original: Seq<i64>, low_first: bool, kernel: Part2RawKernel)
    -> Result<Seq<i64>, crate::DecodeError>
{
    if kernel.0 { Ok(original) }
    else {
        match kernel.5 {
            None => Err(part1_transform_error(false)),
            Some(coefficient) => match part2_atk_fixed_coefficient(coefficient, kernel.1) {
                Err(error) => Err(error),
                Ok(factor) => if factor == 0 { Err(part1_transform_error(false)) }
                    else { part2_atk_scale_prefix(original, factor, low_first, original.len()) },
            },
        }
    }
}

pub open spec fn part2_inverse_arbitrary(low: Seq<i64>, high: Seq<i64>, low_first: bool, kernel: Part2RawKernel)
    -> Result<Seq<i64>, crate::DecodeError>
{
    match part1_interleaved(low, high, low_first) {
        Err(error) => Err(error),
        Ok(samples) => if samples.len() == 1 {
            Ok(if low_first { samples } else { samples.update(0, part2_atk_half(samples[0])) })
        } else {
            match part2_atk_scaled_input(samples, low_first, kernel) {
                Err(error) => Err(error),
                Ok(scaled) => {
                    let result = part2_atk_steps(scaled, kernel, low_first, kernel.6.len());
                    match result.0 { Err(error) => Err(error), Ok(()) => Ok(result.1) }
                },
            }
        },
    }
}

    pub open spec fn part2_atk_horizontal_row(low: Part1WaveletBand, high: Part1WaveletBand, y: u32, low_first: bool, kernel: Part2RawKernel)
        -> Result<Seq<i64>, crate::DecodeError> {
        match part1_band_row(low, y) {
            Err(error) => Err(error),
            Ok(a) => match part1_band_row(high, y) {
                Err(error) => Err(error), Ok(b) => part2_inverse_arbitrary(a, b, low_first, kernel),
            },
        }
    }

    pub open spec fn part2_atk_horizontal_prefix(low: Part1WaveletBand, high: Part1WaveletBand, low_first: bool, kernel: Part2RawKernel, count: nat)
        -> Result<Seq<i64>, crate::DecodeError>
        decreases count,
    {
        if count == 0 { Ok(Seq::empty()) } else {
            match part2_atk_horizontal_prefix(low, high, low_first, kernel, (count - 1) as nat) {
                Err(error) => Err(error),
                Ok(previous) => match part2_atk_horizontal_row(low, high, (count - 1) as u32, low_first, kernel) {
                    Err(error) => Err(error), Ok(row) => Ok(previous + row),
                },
            }
        }
    }

    pub open spec fn part2_atk_inverse_horizontal(low: Part1WaveletBand, high: Part1WaveletBand, width: u32, low_first: bool, irreversible: bool, kernel: Part2RawKernel, maximum: u64)
        -> Part1ReconstructionResult {
        match part1_horizontal_geometry(low, high, width, low_first) {
            Err(error) => Err(error),
            Ok(()) => match part1_transform_area(width, low.1) {
                Err(error) => Err(error),
                Ok(length) => match part1_quantization_budget(length as nat, maximum) {
                    Err(error) => Err(error),
                    Ok(()) => match part2_atk_horizontal_prefix(low, high, low_first, kernel, low.1 as nat) {
                        Err(error) => Err(error), Ok(samples) => Ok((width, low.1, if irreversible { 16u8 } else { 0u8 }, samples)),
                    },
                },
            },
        }
    }

    pub open spec fn part2_atk_vertical_column(low: Part1WaveletBand, high: Part1WaveletBand, x: u32, low_first: bool, kernel: Part2RawKernel)
        -> Result<Seq<i64>, crate::DecodeError> {
        match part1_collect_column(low, x) {
            Err(error) => Err(error),
            Ok(a) => match part1_collect_column(high, x) {
                Err(error) => Err(error), Ok(b) => part2_inverse_arbitrary(a, b, low_first, kernel),
            },
        }
    }

    pub open spec fn part2_atk_vertical_prefix(low: Part1WaveletBand, high: Part1WaveletBand, height: u32, low_first: bool, kernel: Part2RawKernel, length: usize, count: nat)
        -> Result<Seq<i64>, crate::DecodeError>
        decreases count,
    {
        if count == 0 { Ok(Seq::new(length as nat, |i: int| 0i64)) } else {
            match part2_atk_vertical_prefix(low, high, height, low_first, kernel, length, (count - 1) as nat) {
                Err(error) => Err(error),
                Ok(previous) => match part2_atk_vertical_column(low, high, (count - 1) as u32, low_first, kernel) {
                    Err(error) => Err(error),
                    Ok(column) => {
                        let stored = part1_store_column_prefix(previous, low.0, (count - 1) as u32, column, height as nat);
                        match stored.0 { Err(error) => Err(error), Ok(()) => Ok(stored.1) }
                    },
                },
            }
        }
    }

    pub open spec fn part2_atk_inverse_vertical(low: Part1WaveletBand, high: Part1WaveletBand, height: u32, low_first: bool, irreversible: bool, kernel: Part2RawKernel, maximum: u64)
        -> Part1ReconstructionResult {
        match part1_vertical_geometry(low, high, height, low_first) {
            Err(error) => Err(error),
            Ok(()) => match part1_transform_area(low.0, height) {
                Err(error) => Err(error),
                Ok(length) => match part1_quantization_budget(length as nat, maximum) {
                    Err(error) => Err(error),
                    Ok(()) => match part2_atk_vertical_prefix(low, high, height, low_first, kernel, length, low.0 as nat) {
                        Err(error) => Err(error), Ok(samples) => Ok((low.0, height, if irreversible { 16u8 } else { 0u8 }, samples)),
                    },
                },
            },
        }
    }

    pub open spec fn part2_atk_level_rows_and_columns(level: Part1WaveletLevel, irreversible: bool, kernel: Part2RawKernel, length: usize) -> Part1ReconstructionResult {
        match part1_transform_area(level.4, level.0.1) {
            Err(error) => Err(error),
            Ok(_) => match part2_atk_horizontal_prefix(level.0, level.1, level.6, kernel, level.0.1 as nat) {
                Err(error) => Err(error),
                Ok(low) => match part1_transform_area(level.4, level.2.1) {
                    Err(error) => Err(error),
                    Ok(_) => match part2_atk_horizontal_prefix(level.2, level.3, level.6, kernel, level.2.1 as nat) {
                        Err(error) => Err(error),
                        Ok(high) => match part2_atk_vertical_prefix(
                            (level.4, level.0.1, low), (level.4, level.2.1, high), level.5, level.7, kernel, length, level.4 as nat,
                        ) {
                            Err(error) => Err(error), Ok(samples) => Ok((level.4, level.5, if irreversible { 16u8 } else { 0u8 }, samples)),
                        },
                    },
                },
            },
        }
    }

    pub open spec fn part2_atk_inverse_level(level: Part1WaveletLevel, irreversible: bool, kernel: Part2RawKernel, maximum: u64) -> Part1ReconstructionResult {
        match part1_validate_level(level) {
            Err(error) => Err(error),
            Ok(()) => match part1_transform_area(level.4, level.5) {
                Err(error) => Err(error),
                Ok(length) => if !part1_wavelet_sample_count(level.4, level.5, length) { Err(part1_transform_error(false)) }
                    else { match part1_quantization_budget(length as nat, maximum) {
                        Err(error) => Err(error), Ok(()) => part2_atk_level_rows_and_columns(level, irreversible, kernel, length),
                    } },
            },
        }
    }
pub type Part1DecodedComponentModel = (u32, u32, crate::codestream::ComponentInfo, u8, Seq<i64>);
pub type Part1DecodedImageModel = (u32, u32, u32, u32, Seq<Part1DecodedComponentModel>);
pub type Part1DecodedImageState = (Result<(), crate::DecodeError>, Part1DecodedImageModel);
pub type Part1WorkingSubbandModel = (u32, u32, u8, Seq<i64>, Seq<bool>);
pub type Part1WorkingSubbandState = (Result<(), crate::DecodeError>, Part1WorkingSubbandModel);
pub type Part1PrepareWorking = (Seq<Part1WorkingSubbandModel>, u64);
pub type Part1PrepareWorkingState = (Result<(), crate::DecodeError>, Part1PrepareWorking);
pub type Part1PrepareStyle = (crate::codestream::WaveletTransform, u8, Seq<crate::codestream::DecompositionDirection>);
pub type Part1PrepareFold = (u32, u32, Seq<i64>, usize);
pub open spec fn part1_prepared_as_tile(prepared: Part1AssemblyTile) -> Part1AssemblyTile { prepared }
pub struct Part1PreparePlan {
    pub component: u16,
    pub x: u32,
    pub y: u32,
    pub width: u32,
    pub height: u32,
    pub resolution: u8,
    pub subbands: Seq<crate::decode::SubbandGeometry>,
    pub placements: Seq<crate::decode::ProgressionCodeBlockPlacement>,
}

pub open spec fn part1_prepare_fraction(reversible: bool) -> u8 {
    if reversible { 0u8 } else { 16u8 }
}

pub open spec fn part1_prepare_append_band(
    before: Part1PrepareWorking, bands: Seq<crate::decode::SubbandGeometry>, index: usize, fraction: u8, maximum: u64,
) -> Part1PrepareWorkingState {
    if index >= bands.len() { (Err(part1_block_placement_error(false)), before) } else {
        let geometry = bands[index as int];
        match part1_transform_area(geometry.width, geometry.height) {
            Err(error) => (Err(error), before),
            Ok(length) => {
                let bytes = length as nat * 9;
                if bytes > u64::MAX || before.1 as nat + bytes > u64::MAX { (Err(part1_block_placement_error(true)), before) }
                else {
                    let total = (before.1 as nat + bytes) as u64;
                    if total > maximum {
                        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::DecodedBytes, limit: maximum, actual: total }), (before.0, total))
                    } else {
                        (Ok(()), (before.0.push((geometry.width, geometry.height, fraction,
                            Seq::new(length as nat, |i: int| 0i64), Seq::new(length as nat, |i: int| false))), total))
                    }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_init_prefix(
    bands: Seq<crate::decode::SubbandGeometry>, fraction: u8, maximum: u64, count: nat,
) -> Result<Part1PrepareWorking, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), 0)) } else {
        match part1_prepare_init_prefix(bands, fraction, maximum, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => if count > bands.len() { Err(part1_block_placement_error(false)) } else {
                let geometry = bands[count - 1];
                match part1_transform_area(geometry.width, geometry.height) {
                    Err(error) => Err(error),
                    Ok(length) => {
                        let bytes = length as nat * 9;
                        if bytes > u64::MAX || previous.1 as nat + bytes > u64::MAX {
                            Err(part1_block_placement_error(true))
                        } else {
                            let total = (previous.1 as nat + bytes) as u64;
                            if total > maximum {
                                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::DecodedBytes, limit: maximum, actual: total })
                            } else {
                                Ok((previous.0.push((geometry.width, geometry.height, fraction,
                                    Seq::new(length as nat, |i: int| 0i64), Seq::new(length as nat, |i: int| false))), total))
                            }
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn part1_prepare_signed_cell(plane: Tier1RawPlane, x: u16, y: u16)
    -> Result<Part1QuantizedCoefficient, crate::DecodeError>
{
    match tier1_raw_plane_coefficient(plane, x, y) {
        Err(error) => Err(error),
        Ok(coefficient) => match tier1_raw_signed_coefficient(coefficient) {
            Err(error) => Err(error), Ok(signed) => Ok((signed.0, signed.2)),
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_coefficient_row(
    plane: Tier1RawPlane, y: u16, initial: Seq<Part1QuantizedCoefficient>, count: nat,
) -> Result<Seq<Part1QuantizedCoefficient>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) } else {
        match part1_prepare_coefficient_row(plane, y, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(values) => match part1_prepare_signed_cell(plane, (count - 1) as u16, y) {
                Err(error) => Err(error), Ok(value) => Ok(values.push(value)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_coefficient_rows(plane: Tier1RawPlane, count: nat)
    -> Result<Seq<Part1QuantizedCoefficient>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match part1_prepare_coefficient_rows(plane, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(values) => part1_prepare_coefficient_row(plane, (count - 1) as u16, values, plane.width as nat),
        }
    }
}

pub open spec fn part1_prepare_collect_coefficients(plane: Tier1RawPlane)
    -> Result<Seq<Part1QuantizedCoefficient>, crate::DecodeError>
{
    if plane.width as nat * plane.height as nat > usize::MAX { Err(part1_block_placement_error(true)) }
    else { part1_prepare_coefficient_rows(plane, plane.height as nat) }
}

pub open spec fn part1_prepare_place_plane(
    working: Part1PrepareWorking, geometry: crate::decode::SubbandGeometry,
    placement: crate::decode::ProgressionCodeBlockPlacement, plane: Tier1RawPlane, reversible: bool, maximum: u64,
) -> Part1PrepareWorkingState {
    match part1_image_checked_u32(placement.x as int + plane.width as int) {
        Err(error) => (Err(error), working),
        Ok(x1) => if x1 > geometry.width { (Err(part1_block_placement_error(false)), working) } else {
            match part1_image_checked_u32(placement.y as int + plane.height as int) {
                Err(error) => (Err(error), working),
                Ok(y1) => if y1 > geometry.height { (Err(part1_block_placement_error(false)), working) } else {
                    match part1_prepare_collect_coefficients(plane) {
                        Err(error) => (Err(error), working),
                        Ok(coefficients) => match part1_inverse_quantization(
                            coefficients, geometry.quantization_step.exponent, geometry.quantization_step.mantissa,
                            geometry.dynamic_range, reversible, geometry.roi_shift, maximum,
                        ) {
                            Err(error) => (Err(error), working),
                            Ok(quantized) => if quantized.2 != part1_prepare_fraction(reversible) {
                                (Err(part1_block_placement_error(false)), working)
                            } else if placement.subband_index >= working.0.len() {
                                (Err(part1_block_placement_error(false)), working)
                            } else {
                                let written = part1_quantized_block_rows(
                                    working.0[placement.subband_index as int], quantized.3, plane.width as u32,
                                    placement.x, placement.y, plane.height as nat,
                                );
                                (written.0, (working.0.update(placement.subband_index as int, written.1), working.1))
                            },
                        },
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_placement(
    working: Part1PrepareWorking, bands: Seq<crate::decode::SubbandGeometry>,
    precincts: Seq<Seq<Tier1RawPlane>>, placement: crate::decode::ProgressionCodeBlockPlacement,
    reversible: bool, maximum: u64,
) -> Part1PrepareWorkingState {
    if placement.subband_index >= working.0.len() { (Ok(()), working) }
    else if placement.subband_index >= bands.len() || placement.precinct_index >= precincts.len() {
        (Err(part1_block_placement_error(false)), working)
    } else if placement.decoder_index >= precincts[placement.precinct_index as int].len() {
        (Err(part1_packet_header_error()), working)
    } else {
        part1_prepare_place_plane(working, bands[placement.subband_index as int], placement,
            precincts[placement.precinct_index as int][placement.decoder_index as int], reversible, maximum)
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_placements(
    initial: Part1PrepareWorking, plan: Part1PreparePlan, precincts: Seq<Seq<Tier1RawPlane>>,
    reversible: bool, maximum: u64, count: nat,
) -> Part1PrepareWorkingState
    decreases count,
{
    if count == 0 { (Ok(()), initial) } else {
        let previous = part1_prepare_placements(initial, plan, precincts, reversible, maximum, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_prepare_placement(previous.1, plan.subbands, precincts, plan.placements[count - 1], reversible, maximum),
        }
    }
}

pub open spec fn part1_prepare_coverage(bands: Seq<Part1WorkingSubbandModel>) -> Result<(), crate::DecodeError> {
    if forall |b: int, i: int| 0 <= b < bands.len() && 0 <= i < bands[b].4.len() ==> bands[b].4[i] {
        Ok(())
    } else { Err(part1_block_placement_error(false)) }
}

pub open spec fn part1_prepare_band(band: Part1WorkingSubbandModel) -> Part1WaveletBand {
    (band.0, band.1, band.3)
}

#[verifier::opaque]
pub open spec fn part2_kernel_inverse_horizontal(
    low: Part1WaveletBand, high: Part1WaveletBand, width: u32, low_first: bool,
    reversible: bool, kernel: Option<Part2RawKernel>, maximum: u64,
) -> Part1ReconstructionResult {
    match kernel {
        None => part1_inverse_horizontal(low, high, width, low_first, !reversible, maximum),
        Some(kernel) => part2_atk_inverse_horizontal(low, high, width, low_first, !kernel.0, kernel, maximum),
    }
}

pub open spec fn part2_kernel_inverse_vertical(
    low: Part1WaveletBand, high: Part1WaveletBand, height: u32, low_first: bool,
    reversible: bool, kernel: Option<Part2RawKernel>, maximum: u64,
) -> Part1ReconstructionResult {
    match kernel {
        None => part1_inverse_vertical(low, high, height, low_first, !reversible, maximum),
        Some(kernel) => part2_atk_inverse_vertical(low, high, height, low_first, !kernel.0, kernel, maximum),
    }
}

pub open spec fn part2_kernel_inverse_level(
    level: Part1WaveletLevel, reversible: bool, kernel: Option<Part2RawKernel>, maximum: u64,
) -> Part1ReconstructionResult {
    match kernel {
        None => part1_inverse_level(level, !reversible, maximum),
        Some(kernel) => part2_atk_inverse_level(level, !kernel.0, kernel, maximum),
    }
}

pub open spec fn part1_prepare_resolution(
    before: Part1PrepareFold, bands: Seq<Part1WorkingSubbandModel>, geometry: Seq<crate::decode::SubbandGeometry>,
    direction: crate::codestream::DecompositionDirection, reversible: bool, maximum: u64,
) -> Result<Part1PrepareFold, crate::DecodeError> {
    part2_prepare_resolution(before, bands, geometry, direction, reversible, None, maximum)
}

pub open spec fn part2_prepare_resolution(
    before: Part1PrepareFold, bands: Seq<Part1WorkingSubbandModel>, geometry: Seq<crate::decode::SubbandGeometry>,
    direction: crate::codestream::DecompositionDirection, reversible: bool, kernel: Option<Part2RawKernel>, maximum: u64,
) -> Result<Part1PrepareFold, crate::DecodeError> {
    use crate::codestream::DecompositionDirection::*;
    let first = before.3 as nat;
    if first >= bands.len() { Err(part1_block_placement_error(false)) }
    else if bands[first as int].2 != part1_prepare_fraction(reversible) || first >= geometry.len() {
        Err(part1_block_placement_error(false))
    } else {
        let detail = bands[first as int];
        let shape = geometry[first as int];
        let low = (before.0, before.1, before.2);
        let transformed = match direction {
            None => Err(part1_block_placement_error(false)),
            Horizontal | Vertical => if first + 1 > usize::MAX { Err(part1_block_placement_error(true)) } else {
                if matches!(direction, Horizontal) {
                    part2_kernel_inverse_horizontal(low, part1_prepare_band(detail), shape.resolution_width, shape.low_pass_first_x, reversible, kernel, maximum)
                } else {
                    part2_kernel_inverse_vertical(low, part1_prepare_band(detail), shape.resolution_height, shape.low_pass_first_y, reversible, kernel, maximum)
                }
            },
            TwoDimensional => if first + 1 > usize::MAX { Err(part1_block_placement_error(true)) }
                else if first + 1 >= bands.len() { Err(part1_block_placement_error(false)) }
                else if first + 2 > usize::MAX { Err(part1_block_placement_error(true)) }
                else if first + 2 >= bands.len() { Err(part1_block_placement_error(false)) }
                else if bands[(first + 1) as int].2 != part1_prepare_fraction(reversible)
                    || bands[(first + 2) as int].2 != part1_prepare_fraction(reversible) { Err(part1_block_placement_error(false)) }
                else if first + 3 > usize::MAX { Err(part1_block_placement_error(true)) }
                else {
                    part2_kernel_inverse_level((low, part1_prepare_band(detail),
                        part1_prepare_band(bands[(first + 1) as int]), part1_prepare_band(bands[(first + 2) as int]),
                        shape.resolution_width, shape.resolution_height, shape.low_pass_first_x, shape.low_pass_first_y), reversible, kernel, maximum)
                },
        };
        match transformed {
            Err(error) => Err(error),
            Ok(plane) => if plane.2 != part1_prepare_fraction(reversible) { Err(part1_block_placement_error(false)) }
                else { Ok((plane.0, plane.1, plane.3, (first + if matches!(direction, TwoDimensional) { 3nat } else { 1nat }) as usize)) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_fold(
    initial: Part1PrepareFold, bands: Seq<Part1WorkingSubbandModel>, geometry: Seq<crate::decode::SubbandGeometry>,
    style: Part1PrepareStyle, reversible: bool, maximum: u64, count: nat,
) -> Result<Part1PrepareFold, crate::DecodeError> {
    part2_prepare_fold(initial, bands, geometry, style, reversible, None, maximum, count)
}

#[verifier::opaque]
pub open spec fn part2_prepare_fold(
    initial: Part1PrepareFold, bands: Seq<Part1WorkingSubbandModel>, geometry: Seq<crate::decode::SubbandGeometry>,
    style: Part1PrepareStyle, reversible: bool, kernel: Option<Part2RawKernel>, maximum: u64, count: nat,
) -> Result<Part1PrepareFold, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) } else {
        match part2_prepare_fold(initial, bands, geometry, style, reversible, kernel, maximum, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_direction_for_resolution(style.1, style.2, count as u8) {
                Err(error) => Err(error),
                Ok(direction) => {
                    let transformed = if matches!(direction, crate::codestream::DecompositionDirection::None) { Ok(previous) }
                        else { part2_prepare_resolution(previous, bands, geometry, direction, reversible, kernel, maximum) };
                    match transformed {
                        Err(error) => Err(error),
                        Ok(after) => if count >= 255 { Err(part1_block_placement_error(true)) } else { Ok(after) },
                    }
                },
            },
        }
    }
}

pub open spec fn part1_prepare_copy_plane(plane: Part1ReconstructedPlane, first_detail: usize) -> Result<Part1PrepareFold, crate::DecodeError> {
    Ok((plane.0, plane.1, plane.3, first_detail))
}

pub open spec fn part1_prepare_reconstruct(
    bands: Seq<Part1WorkingSubbandModel>, plan: Part1PreparePlan, style: Part1PrepareStyle, reversible: bool, maximum: u64,
) -> Result<Part1PrepareFold, crate::DecodeError> {
    part2_prepare_reconstruct(bands, plan, style, reversible, None, maximum)
}

pub open spec fn part2_prepare_reconstruct(
    bands: Seq<Part1WorkingSubbandModel>, plan: Part1PreparePlan, style: Part1PrepareStyle,
    reversible: bool, kernel: Option<Part2RawKernel>, maximum: u64,
) -> Result<Part1PrepareFold, crate::DecodeError> {
    if bands.len() == 0 { Err(part1_block_placement_error(false)) } else {
        let ll = bands[0];
        part2_prepare_fold((ll.0, ll.1, ll.3, 1usize), bands, plan.subbands, style, reversible, kernel, maximum, plan.resolution as nat)
    }
}

pub open spec fn part1_prepare_finish(plan: Part1PreparePlan, fraction: u8, folded: Part1PrepareFold)
    -> Result<Part1AssemblyTile, crate::DecodeError>
{
    if folded.0 != plan.width || folded.1 != plan.height { Err(part1_block_placement_error(false)) }
    else {
        match part1_transform_area(plan.width, plan.height) {
            Err(error) => Err(error),
            Ok(length) => if folded.2.len() != length { Err(part1_block_placement_error(false)) }
                else { Ok((plan.component, plan.x, plan.y, plan.width, plan.height, fraction, folded.2)) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_prepare_standard_component(
    plan: Part1PreparePlan, precincts: Seq<Seq<Tier1RawPlane>>, style: Part1PrepareStyle, maximum: u64,
) -> Result<Part1AssemblyTile, crate::DecodeError> {
    part2_prepare_component(plan, precincts, style, None, maximum)
}

pub open spec fn part2_prepare_reversible(style: Part1PrepareStyle, kernel: Option<Part2RawKernel>)
    -> Result<bool, crate::DecodeError>
{
    match style.0 {
        crate::codestream::WaveletTransform::Reversible5x3 => Ok(true),
        crate::codestream::WaveletTransform::Irreversible9x7 => Ok(false),
        crate::codestream::WaveletTransform::Arbitrary(_) => match kernel {
            None => Err(part1_block_placement_error(false)), Some(kernel) => Ok(kernel.0),
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_prepare_component(
    plan: Part1PreparePlan, precincts: Seq<Seq<Tier1RawPlane>>, style: Part1PrepareStyle,
    kernel: Option<Part2RawKernel>, maximum: u64,
) -> Result<Part1AssemblyTile, crate::DecodeError> {
    if plan.subbands.len() == 0 { Err(part1_block_placement_error(false)) } else {
        match part2_prepare_reversible(style, kernel) {
            Err(error) => Err(error),
            Ok(reversible) => {
                match part1_subband_count_through_resolution(style.1, style.2, plan.resolution) {
                    Err(error) => Err(error),
                    Ok(selected) => if selected > plan.subbands.len() { Err(part1_block_placement_error(false)) } else {
                        match part1_prepare_init_prefix(plan.subbands, part1_prepare_fraction(reversible), maximum, selected as nat) {
                            Err(error) => Err(error),
                            Ok(initial) => {
                                let placed = part1_prepare_placements(initial, plan, precincts, reversible, maximum, plan.placements.len());
                                match placed.0 {
                                    Err(error) => Err(error),
                                    Ok(()) => match part1_prepare_coverage(placed.1.0) {
                                        Err(error) => Err(error),
                                        Ok(()) => if placed.1.0.len() == 0 { Err(part1_block_placement_error(false)) } else {
                                            let ll = placed.1.0[0];
                                            match part2_prepare_fold((ll.0, ll.1, ll.3, 1usize), placed.1.0, plan.subbands,
                                                style, reversible, kernel, maximum, plan.resolution as nat) {
                                                Err(error) => Err(error),
                                                Ok(folded) => part1_prepare_finish(plan, part1_prepare_fraction(reversible), folded),
                                            }
                                        },
                                    },
                                }
                            },
                        }
                    },
                }
            },
        }
    }
}
pub type Part1AssemblySize = (u32, u32, u32, u32, u16, Seq<crate::codestream::ComponentInfo>);
pub type Part1AssemblyTile = (u16, u32, u32, u32, u32, u8, Seq<i64>);
pub type Part1AssemblyPlane = (u32, u32, Option<u8>, Seq<i64>, Seq<bool>);
pub type Part1AssemblyPlaneState = (Result<(), crate::DecodeError>, Part1AssemblyPlane);
pub type Part1AssemblyState = (Result<(), crate::DecodeError>, Part1DecodedImageModel, u64);
pub type Part1AssemblyDimensions = (crate::codestream::ComponentInfo, u32, u32, u32, u32, u32, u32);
pub type Part1AssemblySelection = Option<([u32; 4], u32)>;

pub const PART2_NORMALIZED_SAMPLE_BITS: u32 = 16;
pub const PART2_NORMALIZED_SAMPLE_MAX: u16 = u16::MAX;
pub const PART2_NORMALIZED_SAMPLE_HALF: u16 = PART2_NORMALIZED_SAMPLE_MAX / 2;

pub const COLOR_FIXED_SCALE: u32 = 65_536;
pub const COLOR_FIXED_HALF: u32 = COLOR_FIXED_SCALE / 2;

pub open spec fn color_fixed_round(value: int) -> int {
    if value < 0 { -((-value + COLOR_FIXED_HALF) / (COLOR_FIXED_SCALE as int)) }
    else { (value + COLOR_FIXED_HALF) / (COLOR_FIXED_SCALE as int) }
}

pub open spec fn color_rounded_fixed(value: i128) -> Result<i128, crate::DecodeError> {
    if (value as int) < (i128::MIN as int) + COLOR_FIXED_HALF
        || (value as int) > (i128::MAX as int) - COLOR_FIXED_HALF {
        Err(part2_composition_error(true))
    } else { Ok(color_fixed_round(value as int) as i128) }
}

pub open spec fn color_clamp_u16(value: int) -> u16 {
    if value <= 0 { 0 } else if value >= PART2_NORMALIZED_SAMPLE_MAX as int {
        PART2_NORMALIZED_SAMPLE_MAX
    } else { value as u16 }
}

pub open spec fn color_sycc_to_srgb(y: u16, cb: i32, cr: i32)
    -> Result<(u16, u16, u16), crate::DecodeError>
{
    Ok((
        color_clamp_u16((y as int) + color_fixed_round(91881 * (cr as int))),
        color_clamp_u16((y as int) - color_fixed_round(22554 * (cb as int))
            - color_fixed_round(46802 * (cr as int))),
        color_clamp_u16((y as int) + color_fixed_round(116130 * (cb as int))),
    ))
}

pub enum Part1TypedSampleSequence {
    Signed(Seq<i64>),
    Unsigned(Seq<u64>),
}

pub struct Part1TypedComponentModel {
    pub width: u32,
    pub height: u32,
    pub info: crate::codestream::ComponentInfo,
    pub samples: Part1TypedSampleSequence,
}

pub type Part1DecodedTypedImage = (
    ColorGeometry, Seq<Part1TypedComponentModel>,
    Seq<Seq<(crate::image::ChannelType, crate::image::ChannelAssociation)>>,
);

pub type Part2TypedComponentOutput = (Part1TypedComponentModel, Seq<ColorDefinition>);
pub type Part2OutputHeader = (
    Option<Part2PaletteModel>,
    Seq<(u16, crate::jp2::MappingType)>,
    Seq<(u16, ColorDefinition)>,
);

pub open spec fn part2_typed_image_component(components: Seq<Part2TypedComponentOutput>, index: u16)
    -> Result<Part2TypedComponentOutput, crate::DecodeError>
{
    if index as nat >= components.len() { Err(part1_image_error(false)) }
    else { Ok(components[index as int]) }
}

pub open spec fn part2_output_mapped_component(
    components: Seq<Part2TypedComponentOutput>, palette: Option<Part2PaletteModel>, mapping: (u16, crate::jp2::MappingType),
) -> Result<Part2TypedComponentOutput, crate::DecodeError> {
    match part2_typed_image_component(components, mapping.0) {
        Err(error) => Err(error),
        Ok(source) => match mapping.1 {
            crate::jp2::MappingType::Direct => part2_typed_component_copy(source),
            crate::jp2::MappingType::Palette { column } => match palette {
                None => Err(part2_color_input_error()),
                Some(palette) => part2_palette_component(source.0, palette, column),
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_output_mapping_prefix(
    components: Seq<Part2TypedComponentOutput>, header: Part2OutputHeader, count: nat,
) -> Result<Seq<Part2TypedComponentOutput>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) }
    else {
        match part2_output_mapping_prefix(components, header, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part2_output_mapped_component(components, header.0, header.1[count - 1]) {
                Err(error) => Err(error),
                Ok(component) => Ok(previous.push(component)),
            },
        }
    }
}

pub open spec fn part2_output_apply_definition(
    components: Seq<Part2TypedComponentOutput>, record: (u16, ColorDefinition),
) -> Result<Seq<Part2TypedComponentOutput>, crate::DecodeError> {
    if record.0 as nat >= components.len() { Err(part2_color_input_error()) }
    else {
        let previous = components[record.0 as int];
        Ok(components.update(record.0 as int, (previous.0, previous.1.push(record.1))))
    }
}

#[verifier::opaque]
pub open spec fn part2_output_definition_prefix(
    components: Seq<Part2TypedComponentOutput>, definitions: Seq<(u16, ColorDefinition)>, count: nat,
) -> Result<Seq<Part2TypedComponentOutput>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(components) }
    else {
        match part2_output_definition_prefix(components, definitions, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_output_apply_definition(previous, definitions[count - 1]),
        }
    }
}

pub open spec fn part2_apply_output_header(
    image: Part1DecodedTypedImage, header: Part2OutputHeader, maximum_components: u16, maximum_bytes: u64,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    let components = Seq::new(image.1.len(), |i: int| (image.1[i], image.2[i]));
    let mapped = if header.1.len() == 0 { Ok(components) }
        else { part2_output_mapping_prefix(components, header, header.1.len()) };
    match mapped {
        Err(error) => Err(error),
        Ok(mapped) => match part2_output_definition_prefix(mapped, header.2, header.2.len()) {
            Err(error) => Err(error),
            Ok(defined) => part2_typed_image_from_parts(
                image.0.0, image.0.1, image.0.2, image.0.3, defined, maximum_components, maximum_bytes,
            ),
        },
    }
}

pub open spec fn part2_typed_image_admit_component(
    component: Part2TypedComponentOutput, previous: u64, maximum: u64,
) -> Result<u64, crate::DecodeError> {
    match part1_transform_area(component.0.width, component.0.height) {
        Err(error) => Err(error),
        Ok(expected) => {
            let count = part2_typed_sample_count(component.0.samples);
            if count != expected { Err(part1_image_error(false)) }
            else {
                let charged = part1_accumulate_decoded_bytes(count, previous, maximum);
                match charged.0 { Err(error) => Err(error), Ok(()) => Ok(charged.1) }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_typed_image_admission_prefix(
    components: Seq<Part2TypedComponentOutput>, maximum: u64, count: nat,
) -> Result<u64, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(0) }
    else {
        match part2_typed_image_admission_prefix(components, maximum, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_typed_image_admit_component(components[count - 1], previous, maximum),
        }
    }
}

pub open spec fn part2_typed_image_from_parts(
    width: u32, height: u32, x_origin: u32, y_origin: u32,
    components: Seq<Part2TypedComponentOutput>, maximum_components: u16, maximum_bytes: u64,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    if x_origin as nat + width as nat > u32::MAX || y_origin as nat + height as nat > u32::MAX {
        Err(part1_image_error(true))
    } else if components.len() > u16::MAX {
        Err(part1_image_error(true))
    } else if components.len() > maximum_components {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::Components, limit: maximum_components as u64, actual: components.len() as u64,
        })
    } else {
        match part2_typed_image_admission_prefix(components, maximum_bytes, components.len()) {
            Err(error) => Err(error),
            Ok(_) => Ok(((width, height, x_origin, y_origin),
                Seq::new(components.len(), |i: int| components[i].0),
                Seq::new(components.len(), |i: int| components[i].1))),
        }
    }
}

pub open spec fn part2_typed_sample_count(samples: Part1TypedSampleSequence) -> nat {
    match samples {
        Part1TypedSampleSequence::Signed(values) => values.len(),
        Part1TypedSampleSequence::Unsigned(values) => values.len(),
    }
}

pub open spec fn part2_typed_component_from_parts(
    width: u32, height: u32, info: crate::codestream::ComponentInfo, samples: Part1TypedSampleSequence,
) -> Part2TypedComponentOutput {
    (Part1TypedComponentModel { width, height, info, samples }, Seq::empty())
}

pub open spec fn part2_typed_component_copy(source: Part2TypedComponentOutput)
    -> Result<Part2TypedComponentOutput, crate::DecodeError>
{
    Ok(source)
}

pub open spec fn part2_palette_modulus(precision: u8) -> Result<u64, crate::DecodeError> {
    if precision == 0 || precision > 38 { Err(part2_color_input_error()) }
    else { Ok(1u64 << precision) }
}

pub open spec fn part2_palette_source_index(samples: Part1TypedSampleSequence, index: usize)
    -> Result<u16, crate::DecodeError>
{
    let value = match samples {
        Part1TypedSampleSequence::Signed(values) =>
            if index < values.len() { Some(values[index as int] as int) } else { None },
        Part1TypedSampleSequence::Unsigned(values) =>
            if index < values.len() { Some(values[index as int] as int) } else { None },
    };
    match value {
        None => Err(part2_color_input_error()),
        Some(value) => if value < 0 || value > u16::MAX { Err(part2_color_input_error()) }
            else { Ok(value as u16) },
    }
}

pub open spec fn part2_palette_sample(
    samples: Part1TypedSampleSequence, palette: Part2PaletteModel, column: u8, index: usize,
) -> Result<i64, crate::DecodeError> {
    if column >= palette.1.len() { Err(part2_color_input_error()) }
    else {
        let descriptor = palette.1[column as int];
        if descriptor.precision == 0 || descriptor.precision > 38 { Err(part2_color_input_error()) }
        else {
            match part2_palette_source_index(samples, index) {
                Err(error) => Err(error),
                Ok(entry) => if entry >= palette.0 { Err(part2_color_input_error()) } else {
                    match part2_palette_value(palette, entry, column) {
                        Err(error) => Err(error),
                        Ok(value) =>
                            if value < part1_output_minimum(descriptor.precision, descriptor.signed)
                                || value > part1_output_maximum(descriptor.precision, descriptor.signed) {
                                Err(part2_color_input_error())
                            } else { Ok(value) },
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_palette_samples(
    samples: Part1TypedSampleSequence, palette: Part2PaletteModel, column: u8, count: nat,
) -> Result<Part1TypedSampleSequence, crate::DecodeError>
    decreases count,
{
    if column >= palette.1.len() { Err(part2_color_input_error()) }
    else {
        let descriptor = palette.1[column as int];
        if descriptor.precision == 0 || descriptor.precision > 38 { Err(part2_color_input_error()) }
        else if count == 0 {
            Ok(if descriptor.signed { Part1TypedSampleSequence::Signed(Seq::empty()) }
                else { Part1TypedSampleSequence::Unsigned(Seq::empty()) })
        } else {
            match part2_palette_samples(samples, palette, column, (count - 1) as nat) {
                Err(error) => Err(error),
                Ok(previous) => match part2_palette_sample(samples, palette, column, (count - 1) as usize) {
                    Err(error) => Err(error),
                    Ok(value) => Ok(match previous {
                        Part1TypedSampleSequence::Signed(values) =>
                            Part1TypedSampleSequence::Signed(values.push(value)),
                        Part1TypedSampleSequence::Unsigned(values) =>
                            Part1TypedSampleSequence::Unsigned(values.push(value as u64)),
                    }),
                },
            }
        }
    }
}

pub open spec fn part2_palette_component(
    source: Part1TypedComponentModel, palette: Part2PaletteModel, column: u8,
) -> Result<Part2TypedComponentOutput, crate::DecodeError> {
    if column >= palette.1.len() { Err(part2_color_input_error()) }
    else {
        let descriptor = palette.1[column as int];
        if descriptor.precision == 0 || descriptor.precision > 38 { Err(part2_color_input_error()) }
        else {
            match part2_palette_samples(source.samples, palette, column, part2_typed_sample_count(source.samples)) {
                Err(error) => Err(error),
                Ok(samples) => Ok(part2_typed_component_from_parts(source.width, source.height,
                    crate::codestream::ComponentInfo {
                        precision: descriptor.precision, signed: descriptor.signed, ..source.info
                    }, samples)),
            }
        }
    }
}

pub open spec fn part1_packet_header_error() -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidPacketHeader }
}

pub struct Part2PacketSubbandExecution {
    pub orientation: crate::tier1::SubbandOrientation,
    pub across: u32,
    pub down: u32,
    pub maximum_zero: u16,
    pub decoders: Seq<Tier1DecoderState>,
}

pub open spec fn part2_precinct_contexts(
    states: Seq<Part1CodeBlockPacketState>, contexts: Seq<crate::packet::CodeBlockPacketContext>,
    count: usize, across: u32, maximum_zero: u16, style: crate::tier1::Tier1CodingStyle,
) -> Result<(Seq<Part1CodeBlockPacketState>, Seq<crate::packet::CodeBlockPacketContext>), crate::DecodeError> {
    if count as nat > u32::MAX as nat + 1 || (count != 0 && across == 0) {
        Err(part1_block_placement_error(true))
    } else {
        Ok((states + Seq::new(count as nat, |index: int| part1_code_block_packet_initial()),
            contexts + Seq::new(count as nat, |index: int| crate::packet::CodeBlockPacketContext {
                leaf_x: if across == 0 { 0u32 } else { (index % across as int) as u32 },
                leaf_y: if across == 0 { 0u32 } else { (index / across as int) as u32 },
                layer: 0, maximum_zero_bitplanes: maximum_zero, tier1_style: style,
            })))
    }
}

pub open spec fn part2_precinct_execution(
    before: Part1PacketPrecinctState, total: u64, execution: Part2PacketSubbandExecution,
    style: crate::tier1::Tier1CodingStyle, limits: &crate::ResourceLimits,
) -> Result<(Part1PacketPrecinctState, u64), crate::DecodeError> {
    if execution.across == 0 || execution.down == 0 || execution.maximum_zero == 0
        || execution.maximum_zero > crate::tier1::MAX_TIER1_BITPLANES {
        Err(part1_packet_header_error())
    } else {
        let count = execution.across as nat * execution.down as nat;
        let next = total as nat + count;
        if count > u64::MAX || next > u64::MAX { Err(part1_block_placement_error(true)) }
        else if next > crate::limits::resource_code_block_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlocks,
                limit: crate::limits::resource_code_block_limit(limits), actual: next as u64 })
        } else if next > crate::limits::resource_work_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                limit: crate::limits::resource_work_limit(limits), actual: next as u64 })
        } else if count > usize::MAX { Err(part1_block_placement_error(true)) }
        else if execution.decoders.len() != count { Err(part1_packet_header_error()) }
        else {
            match part2_precinct_contexts(before.states, before.contexts, count as usize,
                execution.across, execution.maximum_zero, style) {
                Err(error) => Err(error),
                Ok(contexts) => match part1_tag_initial(execution.across, execution.down,
                    crate::limits::resource_tag_tree_node_limit(limits)) {
                    Err(error) => Err(error),
                    Ok(inclusion) => match part1_tag_initial(execution.across, execution.down,
                        crate::limits::resource_tag_tree_node_limit(limits)) {
                        Err(error) => Err(error),
                        Ok(zero) => Ok((Part1PacketPrecinctState {
                            states: contexts.0, contexts: contexts.1,
                            decoders: before.decoders + execution.decoders,
                            subbands: before.subbands.push(Part1PacketSubbandState {
                                orientation: execution.orientation, first_decoder: before.decoders.len() as usize,
                                decoder_count: count as usize, code_blocks_across: execution.across,
                                code_blocks_down: execution.down, inclusion_tree: inclusion, zero_bitplane_tree: zero,
                            }), ..before
                        }, next as u64)),
                    },
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_precinct_initialization_run(
    executions: Seq<Part2PacketSubbandExecution>, style: crate::tier1::Tier1CodingStyle,
    limits: &crate::ResourceLimits, index: nat, state: Part1PacketPrecinctState, total: u64,
) -> Result<Part1PacketPrecinctState, crate::DecodeError>
    decreases if index < executions.len() { (executions.len() - index) as nat } else { 0nat },
{
    if index >= executions.len() { Ok(state) } else {
        match part2_precinct_execution(state, total, executions[index as int], style, limits) {
            Err(error) => Err(error),
            Ok(next) => part2_precinct_initialization_run(executions, style, limits, index + 1, next.0, next.1),
        }
    }
}

pub open spec fn part2_precinct_from_executions(
    component: u16, resolution: u8, precinct: u32, style: crate::tier1::Tier1CodingStyle,
    executions: Seq<Part2PacketSubbandExecution>, limits: &crate::ResourceLimits,
) -> Result<Part1PacketPrecinctState, crate::DecodeError> {
    if executions.len() > 3 { Err(part1_packet_header_error()) } else {
        part2_precinct_initialization_run(executions, style, limits, 0, Part1PacketPrecinctState {
            component, resolution, precinct, states: Seq::empty(), contexts: Seq::empty(),
            decoders: Seq::empty(), subbands: Seq::empty(),
        }, 0)
    }
}

pub open spec fn part1_packet_decoder_count(decoders: Seq<crate::tier1::Tier1CodeBlockDecoder>) -> nat {
    decoders.len()
}

pub open spec fn part1_packet_precinct_decoder(
    decoders: Seq<crate::tier1::Tier1CodeBlockDecoder>, index: usize,
) -> Result<crate::tier1::Tier1CodeBlockDecoder, crate::DecodeError> {
    if index < decoders.len() { Ok(decoders[index as int]) } else { Err(part1_packet_header_error()) }
}

pub open spec fn part1_image_round_fixed(value: i64, fraction_bits: u8) -> Result<i64, crate::DecodeError> {
    if fraction_bits > 62 { Err(part1_image_error(false)) }
    else { part1_round_fixed(value, fraction_bits) }
}

pub open spec fn part1_image_byte_budget(samples: nat, bytes_per_sample: u64, maximum: u64)
    -> Result<(), crate::DecodeError>
{
    let bytes = samples * bytes_per_sample;
    if bytes > u64::MAX { Err(part1_image_error(true)) }
    else if bytes > maximum {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::DecodedBytes, limit: maximum, actual: bytes as u64,
        })
    } else { Ok(()) }
}

pub open spec fn part1_decoded_signed_value(value: i64, fraction_bits: u8, minimum: i64, maximum: i64)
    -> Result<i64, crate::DecodeError>
{
    match part1_image_round_fixed(value, fraction_bits) {
        Err(error) => Err(error),
        Ok(rounded) => {
            let raised = if rounded < minimum { minimum } else { rounded };
            Ok(if raised > maximum { maximum } else { raised })
        },
    }
}

pub open spec fn part1_decoded_unsigned_value(value: i64, fraction_bits: u8, level_shift: i64, maximum: u64)
    -> Result<u64, crate::DecodeError>
{
    match part1_image_round_fixed(value, fraction_bits) {
        Err(error) => Err(error),
        Ok(rounded) => match part1_checked_sample((rounded as int) + (level_shift as int)) {
            Err(error) => Err(error),
            Ok(shifted) => {
                let nonnegative = if shifted < 0 { 0u64 } else { shifted as u64 };
                Ok(if nonnegative < maximum { nonnegative } else { maximum })
            },
        },
    }
}

pub open spec fn part1_decoded_signed_sample(value: i64, fraction_bits: u8, precision: u8)
    -> Result<i64, crate::DecodeError>
{
    if precision == 0 || precision > 38 { Err(part1_image_error(false)) } else {
        part1_decoded_signed_value(value, fraction_bits, part1_output_minimum(precision, true), part1_output_maximum(precision, true))
    }
}

pub open spec fn part1_decoded_unsigned_sample(value: i64, fraction_bits: u8, precision: u8)
    -> Result<u64, crate::DecodeError>
{
    if precision == 0 || precision > 38 { Err(part1_image_error(false)) } else {
        part1_decoded_unsigned_value(value, fraction_bits, 1i64 << ((precision - 1) as u8), ((1u64 << precision) - 1) as u64)
    }
}

#[verifier::opaque]
pub open spec fn part1_decoded_signed_prefix(samples: Seq<i64>, fraction_bits: u8, precision: u8, count: nat)
    -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match part1_decoded_signed_prefix(samples, fraction_bits, precision, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => match part1_decoded_signed_sample(samples[count - 1], fraction_bits, precision) {
                Err(error) => Err(error),
                Ok(value) => Ok(output.push(value)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_decoded_unsigned_prefix(samples: Seq<i64>, fraction_bits: u8, precision: u8, count: nat)
    -> Result<Seq<u64>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match part1_decoded_unsigned_prefix(samples, fraction_bits, precision, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => match part1_decoded_unsigned_sample(samples[count - 1], fraction_bits, precision) {
                Err(error) => Err(error),
                Ok(value) => Ok(output.push(value)),
            },
        }
    }
}

pub open spec fn part1_decoded_component_typed_samples(component: Part1DecodedComponentModel, maximum: u64)
    -> Result<Part1TypedSampleSequence, crate::DecodeError>
{
    if component.2.precision == 0 || component.2.precision > 38 { Err(part1_image_error(false)) } else {
        match part1_image_byte_budget(component.4.len(), 8, maximum) {
            Err(error) => Err(error),
            Ok(()) => if component.2.signed {
                match part1_decoded_signed_prefix(component.4, component.3, component.2.precision, component.4.len()) {
                    Err(error) => Err(error), Ok(values) => Ok(Part1TypedSampleSequence::Signed(values)),
                }
            } else {
                match part1_decoded_unsigned_prefix(component.4, component.3, component.2.precision, component.4.len()) {
                    Err(error) => Err(error), Ok(values) => Ok(Part1TypedSampleSequence::Unsigned(values)),
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_decoded_typed_components(
    components: Seq<Part1DecodedComponentModel>, maximum: u64, count: nat,
) -> Result<(Seq<Part1TypedComponentModel>, u64), crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), 0)) } else {
        match part1_decoded_typed_components(components, maximum, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let component = components[count - 1];
                let charged = part1_accumulate_decoded_bytes(component.4.len(), previous.1, maximum);
                match charged.0 {
                    Err(error) => Err(error),
                    Ok(()) => match part1_decoded_component_typed_samples(component, maximum) {
                        Err(error) => Err(error),
                        Ok(samples) => Ok((previous.0.push(Part1TypedComponentModel {
                            width: component.0, height: component.1, info: component.2, samples,
                        }), charged.1)),
                    },
                }
            },
        }
    }
}

pub open spec fn part1_decoded_image_typed(image: Part1DecodedImageModel, maximum: u64)
    -> Result<Part1DecodedTypedImage, crate::DecodeError>
{
    match part1_decoded_typed_components(image.4, maximum, image.4.len()) {
        Err(error) => Err(error),
        Ok(converted) => Ok(((image.0, image.1, image.2, image.3), converted.0,
            Seq::new(converted.0.len(), |i: int| Seq::empty()))),
    }
}

pub open spec fn color_registered_coordinate(value: u32, divisor: u32, registration: u16, ceil: bool)
    -> Result<u32, crate::DecodeError>
{
    if divisor == 0 {
        Err(part2_color_input_error())
    } else {
        let numerator = (value as nat) * 65536;
        if numerator <= registration as nat {
            Ok(0)
        } else {
            let adjusted = (numerator - registration as nat) as nat;
            let denominator = (divisor as nat) * 65536;
            let coordinate = if ceil { part1_ceil_div(adjusted, denominator) }
                else { adjusted / denominator };
            if coordinate > u32::MAX as nat {
                Err(part2_composition_error(true))
            } else { Ok(coordinate as u32) }
        }
    }
}

pub open spec fn color_normalize_unsigned(value: u64, precision: u8)
    -> Result<u16, crate::DecodeError>
{
    if precision == 0 || precision > 38 {
        Err(part2_color_input_error())
    } else {
        let maximum = ((1u64 << precision) - 1) as nat;
        if value as nat > maximum {
            Err(part2_color_input_error())
        } else {
            Ok((((value as nat) * (PART2_NORMALIZED_SAMPLE_MAX as nat) + maximum / 2) / maximum) as u16)
        }
    }
}

pub open spec fn color_component_index(
    component: Part1TypedComponentModel, x_origin: u32, y_origin: u32, x: u32, y: u32,
) -> Result<usize, crate::DecodeError> {
    let info = component.info;
    if info.precision == 0 || info.precision > 38 || info.x_subsampling == 0
        || info.y_subsampling == 0 || component.width == 0 || component.height == 0 {
        Err(part2_color_input_error())
    } else if (x_origin as nat) + x as nat > u32::MAX as nat
        || (y_origin as nat) + y as nat > u32::MAX as nat {
        Err(part2_composition_error(true))
    } else {
        match (
            color_registered_coordinate(x_origin, info.x_subsampling as u32, info.x_registration, true),
            color_registered_coordinate(y_origin, info.y_subsampling as u32, info.y_registration, true),
        ) {
            (Err(error), _) => Err(error),
            (_, Err(error)) => Err(error),
            (Ok(x0), Ok(y0)) => {
                if (x0 as nat) + component.width as nat > u32::MAX as nat
                    || (y0 as nat) + component.height as nat > u32::MAX as nat {
                    Err(part2_composition_error(true))
                } else {
                    match (
                        color_registered_coordinate((x_origin + x) as u32, info.x_subsampling as u32, info.x_registration, false),
                        color_registered_coordinate((y_origin + y) as u32, info.y_subsampling as u32, info.y_registration, false),
                    ) {
                        (Err(error), _) => Err(error),
                        (_, Err(error)) => Err(error),
                        (Ok(raw_x), Ok(raw_y)) => {
                            let x1 = (x0 as nat) + component.width as nat;
                            let y1 = (y0 as nat) + component.height as nat;
                            let cx = if raw_x < x0 { x0 as nat } else if raw_x as nat >= x1 { (x1 - 1) as nat } else { raw_x as nat };
                            let cy = if raw_y < y0 { y0 as nat } else if raw_y as nat >= y1 { (y1 - 1) as nat } else { raw_y as nat };
                            let index = ((cy - y0 as nat) as nat) * (component.width as nat) + (cx - x0 as nat);
                            if index > usize::MAX as nat { Err(part2_composition_error(true)) }
                            else { Ok(index as usize) }
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn color_component_nominal(
    component: Part1TypedComponentModel, x_origin: u32, y_origin: u32, x: u32, y: u32,
) -> Result<u64, crate::DecodeError> {
    match color_component_index(component, x_origin, y_origin, x, y) {
        Err(error) => Err(error),
        Ok(index) => match component.samples {
            Part1TypedSampleSequence::Unsigned(samples) => {
                let maximum = ((1u64 << component.info.precision) - 1) as nat;
                if component.info.signed || index >= samples.len() || samples[index as int] as nat > maximum {
                    Err(part2_color_input_error())
                } else { Ok(samples[index as int]) }
            },
            Part1TypedSampleSequence::Signed(samples) => {
                let level = 1i64 << ((component.info.precision - 1) as u8);
                if !component.info.signed || index >= samples.len()
                    || samples[index as int] < -(level as int)
                    || samples[index as int] >= level {
                    Err(part2_color_input_error())
                } else if samples[index as int] > (i64::MAX - level) as int {
                    Err(part2_composition_error(true))
                } else { Ok((samples[index as int] + level) as u64) }
            },
        },
    }
}

pub open spec fn color_component_normalized(
    component: Part1TypedComponentModel, x_origin: u32, y_origin: u32, x: u32, y: u32,
) -> Result<u16, crate::DecodeError> {
    match color_component_nominal(component, x_origin, y_origin, x, y) {
        Err(error) => Err(error),
        Ok(value) => color_normalize_unsigned(value, component.info.precision),
    }
}

pub open spec fn color_normalize_difference(value: u64, precision: u8)
    -> Result<i32, crate::DecodeError>
{
    if precision == 0 || precision > 38 {
        Err(part2_color_input_error())
    } else {
        let maximum = ((1u64 << precision) - 1) as nat;
        if value as nat > maximum { Err(part2_color_input_error()) }
        else {
            let midpoint = 1u64 << ((precision - 1) as u8);
            let scaled = ((value as int) - midpoint as int) * (PART2_NORMALIZED_SAMPLE_MAX as int);
            let rounded = if scaled < 0 {
                -((-scaled + maximum / 2) / (maximum as int))
            } else { (scaled + maximum / 2) / (maximum as int) };
            if rounded < i32::MIN || rounded > i32::MAX {
                Err(part2_composition_error(true))
            } else { Ok(rounded as i32) }
        }
    }
}

pub open spec fn color_image_normalized(
    components: Seq<Part1TypedComponentModel>, x_origin: u32, y_origin: u32,
    component_index: usize, x: u32, y: u32,
) -> Result<u16, crate::DecodeError> {
    if component_index >= components.len() { Err(part2_color_input_error()) }
    else { color_component_normalized(components[component_index as int], x_origin, y_origin, x, y) }
}

pub open spec fn color_image_difference(
    components: Seq<Part1TypedComponentModel>, x_origin: u32, y_origin: u32,
    component_index: usize, x: u32, y: u32,
) -> Result<i32, crate::DecodeError> {
    if component_index >= components.len() { Err(part2_color_input_error()) }
    else {
        let component = components[component_index as int];
        if component.info.precision == 0 || component.info.precision > 38 {
            Err(part2_color_input_error())
        } else {
            match color_component_nominal(component, x_origin, y_origin, x, y) {
                Err(error) => Err(error),
                Ok(value) => color_normalize_difference(value, component.info.precision),
            }
        }
    }
}

pub type ColorGeometry = (u32, u32, u32, u32);

pub open spec fn color_registered_span(start: u32, end: u32, step: u8, registration: u16)
    -> Result<u32, crate::DecodeError>
{
    match (
        color_registered_coordinate(end, step as u32, registration, true),
        color_registered_coordinate(start, step as u32, registration, true),
    ) {
        (Err(error), _) => Err(error),
        (_, Err(error)) => Err(error),
        (Ok(last), Ok(first)) => if last < first { Err(part2_composition_error(true)) }
            else { Ok((last - first) as u32) },
    }
}

pub open spec fn color_validate_component(component: Part1TypedComponentModel, geometry: ColorGeometry)
    -> Result<(), crate::DecodeError>
{
    let info = component.info;
    let signed = match component.samples {
        Part1TypedSampleSequence::Signed(_) => true,
        Part1TypedSampleSequence::Unsigned(_) => false,
    };
    if info.precision == 0 || info.precision > 38 || info.signed != signed
        || info.x_subsampling == 0 || info.y_subsampling == 0 {
        Err(part2_color_input_error())
    } else if (geometry.2 as nat) + geometry.0 as nat > u32::MAX as nat
        || (geometry.3 as nat) + geometry.1 as nat > u32::MAX as nat {
        Err(part2_composition_error(true))
    } else {
        match (
            color_registered_span(geometry.2, (geometry.2 + geometry.0) as u32,
                info.x_subsampling, info.x_registration),
            color_registered_span(geometry.3, (geometry.3 + geometry.1) as u32,
                info.y_subsampling, info.y_registration),
        ) {
            (Err(error), _) => Err(error),
            (_, Err(error)) => Err(error),
            (Ok(width), Ok(height)) => {
                if component.width != width || component.height != height {
                    Err(part2_color_input_error())
                } else {
                    match part2_layer_area(width, height) {
                        Err(error) => Err(error),
                        Ok(area) => {
                            let samples = match component.samples {
                                Part1TypedSampleSequence::Signed(values) => values.len(),
                                Part1TypedSampleSequence::Unsigned(values) => values.len(),
                            };
                            if samples != area { Err(part2_color_input_error()) } else { Ok(()) }
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn color_validate_component_index(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry, index: usize,
) -> Result<(), crate::DecodeError> {
    if index >= components.len() { Err(part2_color_input_error()) }
    else { color_validate_component(components[index as int], geometry) }
}

#[verifier::opaque]
pub open spec fn color_validate_indices_prefix(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry, indices: Seq<usize>, count: nat,
) -> Result<(), crate::DecodeError>
    recommends count <= indices.len(),
    decreases count,
{
    if count == 0 { Ok(()) } else {
        match color_validate_indices_prefix(components, geometry, indices, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(()) => color_validate_component_index(components, geometry, indices[count - 1]),
        }
    }
}

pub open spec fn color_validate_components(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry, layout: ColorLayoutState,
) -> Result<(), crate::DecodeError> {
    match color_validate_indices_prefix(components, geometry, layout.0, layout.0.len()) {
        Err(error) => Err(error),
        Ok(()) => {
            let indices = Seq::new(layout.1.len(), |i: int| layout.1[i].0);
            color_validate_indices_prefix(components, geometry, indices, indices.len())
        },
    }
}

pub open spec fn color_validate_output_size(
    width: u32, height: u32, colors: usize, alphas: usize, byte_limit: u64, work_limit: u64,
) -> Result<(), crate::DecodeError> {
    if (colors as nat) + alphas as nat > usize::MAX as nat {
        Err(part2_composition_error(true))
    } else {
        match part2_layer_area(width, height) {
            Err(error) => Err(error),
            Ok(area) => {
                let samples = (area as nat) * ((colors as nat) + alphas as nat);
                let bytes = ((samples as u64) as nat) * 2;
                if samples > usize::MAX as nat || bytes > u64::MAX as nat {
                    Err(part2_composition_error(true))
                } else if bytes > byte_limit as nat {
                    Err(crate::DecodeError::LimitExceeded {
                        resource: crate::Resource::DecodedBytes, limit: byte_limit, actual: bytes as u64,
                    })
                } else if samples > u64::MAX as nat {
                    Err(part2_composition_error(true))
                } else if samples > work_limit as nat {
                    Err(crate::DecodeError::LimitExceeded {
                        resource: crate::Resource::WorkUnits, limit: work_limit, actual: samples as u64,
                    })
                } else { Ok(()) }
            },
        }
    }
}

pub type ColorChannelModel = (crate::color::ConvertedChannelType, Seq<u16>);
pub type ColorSyccPlanes = (Seq<u16>, Seq<u16>, Seq<u16>);
pub type ColorImageModel = (u32, u32, crate::color::ConvertedColorSpace, u8, Seq<ColorChannelModel>);

pub open spec fn color_convert_channel(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry,
    colors: Seq<usize>, color_count: usize, index: usize,
) -> Result<ColorChannelModel, crate::DecodeError> {
    if index >= colors.len() || colors[index as int] >= components.len() {
        Err(part2_color_input_error())
    } else {
        match color_normalize_component(components[colors[index as int] as int],
            geometry.0, geometry.1, geometry.2, geometry.3) {
            Err(error) => Err(error),
            Ok(samples) => match (color_count, index) {
                (1, 0) => Ok((crate::color::ConvertedChannelType::Gray, samples)),
                (3, 0) => Ok((crate::color::ConvertedChannelType::Red, samples)),
                (3, 1) => Ok((crate::color::ConvertedChannelType::Green, samples)),
                (3, 2) => Ok((crate::color::ConvertedChannelType::Blue, samples)),
                _ => Err(part2_color_input_error()),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn color_convert_channels_prefix(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry,
    colors: Seq<usize>, color_count: usize, count: nat,
) -> Result<Seq<ColorChannelModel>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match color_convert_channels_prefix(components, geometry, colors, color_count, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(channels) => if count - 1 > usize::MAX {
                Err(part2_composition_error(true))
            } else {
                match color_convert_channel(components, geometry, colors, color_count, (count - 1) as usize) {
                    Err(error) => Err(error),
                    Ok(channel) => Ok(channels.push(channel)),
                }
            },
        }
    }
}

pub open spec fn color_convert_alpha(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry,
    alpha: (usize, bool, crate::image::ChannelAssociation),
) -> Result<ColorChannelModel, crate::DecodeError> {
    if alpha.0 >= components.len() { Err(part2_color_input_error()) } else {
        match color_normalize_component(components[alpha.0 as int],
            geometry.0, geometry.1, geometry.2, geometry.3) {
            Err(error) => Err(error),
            Ok(samples) => Ok((crate::color::ConvertedChannelType::Alpha {
                premultiplied: alpha.1, association: alpha.2,
            }, samples)),
        }
    }
}

#[verifier::opaque]
pub open spec fn color_append_alphas_prefix(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry,
    alphas: Seq<(usize, bool, crate::image::ChannelAssociation)>,
    initial: Seq<ColorChannelModel>, count: nat,
) -> Result<Seq<ColorChannelModel>, crate::DecodeError>
    recommends count <= alphas.len(),
    decreases count,
{
    if count == 0 { Ok(initial) } else {
        match color_append_alphas_prefix(components, geometry, alphas, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(channels) => match color_convert_alpha(components, geometry, alphas[count - 1]) {
                Err(error) => Err(error),
                Ok(channel) => Ok(channels.push(channel)),
            },
        }
    }
}

pub open spec fn color_sycc_pixel(
    components: Seq<Part1TypedComponentModel>, x_origin: u32, y_origin: u32,
    colors: Seq<usize>, pixel: usize, width: usize,
) -> Result<(u16, u16, u16), crate::DecodeError> {
    match color_pixel_coordinates(pixel, width) {
        Err(error) => Err(error),
        Ok((x, y)) => {
            if colors.len() == 0 { Err(part2_color_input_error()) } else {
                match color_image_normalized(components, x_origin, y_origin, colors[0], x, y) {
                    Err(error) => Err(error),
                    Ok(y_sample) => if colors.len() <= 1 { Err(part2_color_input_error()) } else {
                        match color_image_difference(components, x_origin, y_origin, colors[1], x, y) {
                            Err(error) => Err(error),
                            Ok(cb) => if colors.len() <= 2 { Err(part2_color_input_error()) } else {
                                match color_image_difference(components, x_origin, y_origin, colors[2], x, y) {
                                    Err(error) => Err(error),
                                    Ok(cr) => color_sycc_to_srgb(y_sample, cb, cr),
                                }
                            },
                        }
                    },
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn color_sycc_planes_prefix(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry,
    colors: Seq<usize>, width: usize, count: nat,
) -> Result<ColorSyccPlanes, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok((Seq::empty(), Seq::empty(), Seq::empty())) } else {
        match color_sycc_planes_prefix(components, geometry, colors, width, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(planes) => if count - 1 > usize::MAX {
                Err(part2_composition_error(true))
            } else {
                match color_sycc_pixel(components, geometry.2, geometry.3, colors, (count - 1) as usize, width) {
                    Err(error) => Err(error),
                    Ok((r, g, b)) => Ok((planes.0.push(r), planes.1.push(g), planes.2.push(b))),
                }
            },
        }
    }
}

pub open spec fn color_convert_colors(
    components: Seq<Part1TypedComponentModel>, geometry: ColorGeometry,
    colors: Seq<usize>, color_count: usize, sycc: bool,
) -> Result<Seq<ColorChannelModel>, crate::DecodeError> {
    if sycc {
        if geometry.0 as nat > usize::MAX as nat { Err(part2_composition_error(true)) }
        else if geometry.0 == 0 { Err(part2_color_input_error()) }
        else {
            match part2_layer_area(geometry.0, geometry.1) {
                Err(error) => Err(error),
                Ok(area) => match color_sycc_planes_prefix(components, geometry, colors, geometry.0 as usize, area as nat) {
                    Err(error) => Err(error),
                    Ok(planes) => Ok(seq![
                        (crate::color::ConvertedChannelType::Red, planes.0),
                        (crate::color::ConvertedChannelType::Green, planes.1),
                        (crate::color::ConvertedChannelType::Blue, planes.2),
                    ]),
                },
            }
        }
    } else { color_convert_channels_prefix(components, geometry, colors, color_count, color_count as nat) }
}

pub open spec fn color_output_format(method: crate::jp2::ColorMethod)
    -> Result<(usize, crate::color::ConvertedColorSpace, bool), crate::DecodeError>
{
    match method {
        crate::jp2::ColorMethod::Enumerated { color_space: crate::jp2::ENUMERATED_SRGB } =>
            Ok((3, crate::color::ConvertedColorSpace::Srgb, false)),
        crate::jp2::ColorMethod::Enumerated { color_space: crate::jp2::ENUMERATED_GRAYSCALE } =>
            Ok((1, crate::color::ConvertedColorSpace::Grayscale, false)),
        crate::jp2::ColorMethod::Enumerated { color_space: crate::jp2::ENUMERATED_SYCC } =>
            Ok((3, crate::color::ConvertedColorSpace::Srgb, true)),
        crate::jp2::ColorMethod::Enumerated { .. } => Err(crate::DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::EnumeratedColorSpace,
        }),
        _ => Err(crate::DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::IccProfile,
        }),
    }
}

pub open spec fn color_convert_jp2(
    components: Seq<Part1TypedComponentModel>, definitions: Seq<Seq<ColorDefinition>>,
    geometry: ColorGeometry, method: crate::jp2::ColorMethod, byte_limit: u64, work_limit: u64,
) -> Part2ConvertedImageResult {
    if geometry.0 == 0 || geometry.1 == 0 { Err(part2_color_input_error()) }
    else {
        match color_output_format(method) {
            Err(error) => Err(error),
            Ok((color_count, space, sycc)) => match color_channel_layout(definitions, color_count) {
                Err(error) => Err(error),
                Ok(layout) => match color_validate_components(components, geometry, layout) {
                    Err(error) => Err(error),
                    Ok(()) => match color_validate_output_size(
                        geometry.0, geometry.1, color_count, layout.1.len() as usize, byte_limit, work_limit,
                    ) {
                        Err(error) => Err(error),
                        Ok(()) => match part2_layer_area(geometry.0, geometry.1) {
                            Err(error) => Err(error),
                            Ok(_) => match color_convert_colors(components, geometry, layout.0, color_count, sycc) {
                                Err(error) => Err(error),
                                Ok(channels) => match color_append_alphas_prefix(
                                    components, geometry, layout.1, channels, layout.1.len(),
                                ) {
                                    Err(error) => Err(error),
                                    Ok(output) => Ok((geometry.0, geometry.1, space, 16, output)),
                                },
                            },
                        },
                    },
                },
            },
        }
    }
}

pub open spec fn color_crop_sample(samples: Seq<u16>, width: u32, row: u32, column: u32)
    -> Result<u16, crate::DecodeError>
{
    let index = (row as nat) * (width as nat) + column as nat;
    if index > usize::MAX as nat { Err(part2_composition_error(true)) }
    else if index >= samples.len() { Err(part2_color_input_error()) }
    else { Ok(samples[index as int]) }
}

#[verifier::opaque]
pub open spec fn color_crop_columns(
    samples: Seq<u16>, source_width: u32, row: u32, x: u32, initial: Seq<u16>, count: nat,
) -> Result<Seq<u16>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(initial) } else {
        match color_crop_columns(samples, source_width, row, x, initial, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => {
                let column = (x as nat) + count - 1;
                if column > u32::MAX as nat { Err(part2_composition_error(true)) }
                else {
                    match color_crop_sample(samples, source_width, row, column as u32) {
                        Err(error) => Err(error),
                        Ok(value) => Ok(output.push(value)),
                    }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn color_crop_rows(
    samples: Seq<u16>, source_width: u32, x: u32, y: u32, width: u32, count: nat,
) -> Result<Seq<u16>, crate::DecodeError>
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match color_crop_rows(samples, source_width, x, y, width, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => {
                let row = (y as nat) + count - 1;
                if row > u32::MAX as nat { Err(part2_composition_error(true)) }
                else { color_crop_columns(samples, source_width, row as u32, x, output, width as nat) }
            },
        }
    }
}

pub open spec fn color_crop_plane(
    samples: Seq<u16>, source_width: u32, x: u32, y: u32, x1: u32, y1: u32,
) -> Result<Seq<u16>, crate::DecodeError> {
    if x > x1 || y > y1 { Err(part2_color_input_error()) }
    else { color_crop_rows(samples, source_width, x, y, (x1 - x) as u32, (y1 - y) as nat) }
}

#[verifier::opaque]
pub open spec fn color_crop_channels(
    channels: Seq<ColorChannelModel>, source_width: u32, x: u32, y: u32, x1: u32, y1: u32, count: nat,
) -> Result<Seq<ColorChannelModel>, crate::DecodeError>
    recommends count <= channels.len(),
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match color_crop_channels(channels, source_width, x, y, x1, y1, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(output) => {
                let channel = channels[count - 1];
                match color_crop_plane(channel.1, source_width, x, y, x1, y1) {
                    Err(error) => Err(error),
                    Ok(samples) => Ok(output.push((channel.0, samples))),
                }
            },
        }
    }
}

pub open spec fn color_crop_image(image: ColorImageModel, x: u32, y: u32, width: u32, height: u32)
    -> Part2ConvertedImageResult
{
    if width == 0 || height == 0 { Err(part2_color_input_error()) }
    else if (x as nat) + width as nat > u32::MAX as nat
        || (y as nat) + height as nat > u32::MAX as nat {
        Err(part2_composition_error(true))
    } else {
        let x1 = (x + width) as u32;
        let y1 = (y + height) as u32;
        if x1 > image.0 || y1 > image.1 { Err(part2_color_input_error()) }
        else if x == 0 && y == 0 && width == image.0 && height == image.1 { Ok(image) }
        else {
            match part2_layer_area(width, height) {
                Err(error) => Err(error),
                Ok(_) => match color_crop_channels(image.4, image.0, x, y, x1, y1, image.4.len()) {
                    Err(error) => Err(error),
                    Ok(channels) => Ok((width, height, image.2, image.3, channels)),
                },
            }
        }
    }
}

pub open spec fn color_selection_target_error() -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidCodeBlock }
}

pub open spec fn color_convert_selected(
    components: Seq<Part1TypedComponentModel>, definitions: Seq<Seq<ColorDefinition>>,
    geometry: ColorGeometry, method: crate::jp2::ColorMethod, target: [u32; 4],
    byte_limit: u64, work_limit: u64,
) -> Part2ConvertedImageResult {
    match color_convert_jp2(components, definitions, geometry, method, byte_limit, work_limit) {
        Err(error) => Err(error),
        Ok(image) => {
            if target[0] < geometry.2 || target[1] < geometry.3
                || target[2] < target[0] || target[3] < target[1] {
                Err(color_selection_target_error())
            } else {
                color_crop_image(image, (target[0] - geometry.2) as u32, (target[1] - geometry.3) as u32,
                    (target[2] - target[0]) as u32, (target[3] - target[1]) as u32)
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn color_normalize_component_prefix(
    component: Part1TypedComponentModel, width: u32, x_origin: u32, y_origin: u32, count: nat,
) -> Result<Seq<u16>, crate::DecodeError>
    recommends width > 0,
    decreases count,
{
    if count == 0 { Ok(Seq::empty()) } else {
        match color_normalize_component_prefix(component, width, x_origin, y_origin, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(samples) => {
                let pixel = (count - 1) as nat;
                if pixel > usize::MAX as nat {
                    Err(part2_composition_error(true))
                } else {
                    match color_pixel_coordinates(pixel as usize, width as usize) {
                        Err(error) => Err(error),
                        Ok((x, y)) => match color_component_normalized(component, x_origin, y_origin, x, y) {
                            Err(error) => Err(error),
                            Ok(value) => Ok(samples.push(value)),
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn color_normalize_component(
    component: Part1TypedComponentModel, width: u32, height: u32, x_origin: u32, y_origin: u32,
) -> Result<Seq<u16>, crate::DecodeError> {
    if width == 0 { Err(part2_color_input_error()) }
    else if width as nat > usize::MAX as nat { Err(part2_composition_error(true)) }
    else {
        match part2_layer_area(width, height) {
            Err(error) => Err(error),
            Ok(area) => color_normalize_component_prefix(component, width, x_origin, y_origin, area as nat),
        }
    }
}

pub open spec fn color_pixel_coordinates(pixel: usize, width: usize)
    -> Result<(u32, u32), crate::DecodeError> {
    if width == 0 { Err(part2_color_input_error()) }
    else if (pixel % width) as nat > u32::MAX as nat || (pixel / width) as nat > u32::MAX as nat {
        Err(part2_composition_error(true))
    } else { Ok(((pixel % width) as u32, (pixel / width) as u32)) }
}

pub type ColorDefinition = (crate::image::ChannelType, crate::image::ChannelAssociation);
pub type ColorLayoutState = (Seq<usize>, Seq<(usize, bool, crate::image::ChannelAssociation)>);
pub type ColorLayoutResult = Result<ColorLayoutState, crate::DecodeError>;

pub open spec fn color_layout_error() -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidChannelLayout }
}

pub open spec fn color_alpha_association(association: crate::image::ChannelAssociation, count: usize)
    -> Result<(), crate::DecodeError>
{
    match association {
        crate::image::ChannelAssociation::Color(value) if value == 0 || value as nat > count as nat =>
            Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidAlphaAssociation }),
        _ => Ok(()),
    }
}

pub open spec fn color_layout_definition_step(
    state: ColorLayoutState, definition: ColorDefinition, component: usize, color_count: usize,
) -> ColorLayoutResult {
    match definition.0 {
        crate::image::ChannelType::Color => match definition.1 {
            crate::image::ChannelAssociation::Color(value) => {
                if value == 0 || value as nat > color_count as nat { Err(color_layout_error()) }
                else {
                    let slot = (value - 1) as int;
                    if slot >= state.0.len() { Err(part2_color_input_error()) }
                    else if state.0[slot] != usize::MAX && state.0[slot] != component {
                        Err(color_layout_error())
                    } else {
                        Ok((state.0.update(slot, component), state.1))
                    }
                }
            },
            _ => Err(color_layout_error()),
        },
        crate::image::ChannelType::Opacity | crate::image::ChannelType::PremultipliedOpacity =>
            match color_alpha_association(definition.1, color_count) {
                Err(error) => Err(error),
                Ok(()) => Ok((state.0, state.1.push((component,
                    matches!(definition.0, crate::image::ChannelType::PremultipliedOpacity), definition.1)))),
            },
        crate::image::ChannelType::Unspecified => Ok(state),
    }
}

#[verifier::opaque]
pub open spec fn color_layout_definitions_prefix(
    initial: ColorLayoutState, definitions: Seq<ColorDefinition>,
    component: usize, color_count: usize, count: nat,
) -> ColorLayoutResult
    recommends count <= definitions.len(),
    decreases count,
{
    if count == 0 { Ok(initial) } else {
        match color_layout_definitions_prefix(initial, definitions, component, color_count, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(state) => color_layout_definition_step(state, definitions[(count - 1) as int], component, color_count),
        }
    }
}

#[verifier::opaque]
pub open spec fn color_layout_components_prefix(
    definitions: Seq<Seq<ColorDefinition>>, color_count: usize, count: nat,
) -> ColorLayoutResult
    recommends count <= definitions.len(),
    decreases count,
{
    if count == 0 { Ok((Seq::new(color_count as nat, |i: int| usize::MAX), Seq::empty())) }
    else {
        match color_layout_components_prefix(definitions, color_count, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(state) => color_layout_definitions_prefix(state, definitions[(count - 1) as int],
                (count - 1) as usize, color_count, definitions[(count - 1) as int].len()),
        }
    }
}

pub open spec fn color_channel_layout(definitions: Seq<Seq<ColorDefinition>>, color_count: usize)
    -> ColorLayoutResult
{
    if !(exists|i: int| #![trigger definitions[i]] 0 <= i < definitions.len() && definitions[i].len() > 0) {
        if definitions.len() != color_count as nat { Err(color_layout_error()) }
        else { Ok((Seq::new(color_count as nat, |i: int| i as usize), Seq::empty())) }
    } else {
        match color_layout_components_prefix(definitions, color_count, definitions.len()) {
            Err(error) => Err(error),
            Ok(state) => if exists|i: int| #![trigger state.0[i]] 0 <= i < state.0.len() && state.0[i] == usize::MAX {
                Err(color_layout_error())
            } else { Ok(state) },
        }
    }
}

pub open spec fn region_fits(parent_length: nat, offset: nat, length: nat) -> bool {
    offset <= parent_length && length <= parent_length - offset
}

pub open spec fn valid_box_lengths(header_length: nat, total_length: nat) -> bool {
    header_length <= total_length
}

pub open spec fn work_within_limit(consumed: nat, limit: nat) -> bool {
    consumed <= limit
}

pub open spec fn valid_selection_region(
    image_x0: nat,
    image_y0: nat,
    image_x1: nat,
    image_y1: nat,
    region_x0: nat,
    region_y0: nat,
    region_x1: nat,
    region_y1: nat,
) -> bool {
    image_x0 <= region_x0
        && image_y0 <= region_y0
        && region_x0 < region_x1
        && region_y0 < region_y1
        && region_x1 <= image_x1
        && region_y1 <= image_y1
}

pub open spec fn reduced_extent(start: nat, end: nat, scale: nat) -> nat
    recommends
        scale > 0,
        start <= end,
{
    (
        (((end + scale - 1) as int) / (scale as int))
            - (((start + scale - 1) as int) / (scale as int))
    ) as nat
}

pub open spec fn selected_packet_work(selected_packets: nat, packet_limit: nat) -> bool {
    selected_packets <= packet_limit
}

pub open spec fn valid_selected_codestream_index(index: nat, codestreams: nat) -> bool {
    codestreams > 0 && index < codestreams
}

pub open spec fn valid_codestream_header_associations(headers: nat, codestreams: nat) -> bool {
    headers <= codestreams
}

pub open spec fn valid_jph_branding(
    primary_is_jph: bool,
    minor_version: nat,
    compatible_brands: nat,
    sole_compatible_is_jph: bool,
) -> bool {
    primary_is_jph
        && minor_version == 0
        && compatible_brands == 1
        && sole_compatible_is_jph
}

pub open spec fn consistent_part15_signaling(
    rsiz_announces_ht: bool,
    cap_announces_ht: bool,
    style_uses_ht: bool,
    has_corresponding_profile: bool,
) -> bool {
    rsiz_announces_ht == cap_announces_ht
        && (!style_uses_ht || cap_announces_ht)
        && (!has_corresponding_profile || cap_announces_ht)
}

pub open spec fn valid_part15_block_mode(mode: nat) -> bool {
    mode == 0 || mode == 2 || mode == 3
}

pub open spec fn valid_part15_capability_word(ccap: nat) -> bool {
    ccap < 65536
        && valid_part15_block_mode(ccap / 16384)
        && ccap % 2048 < 64
}

pub open spec fn valid_ht_style_prefix(prefix: nat) -> bool {
    prefix == 0 || prefix == 1 || prefix == 3
}

pub open spec fn valid_ht_cleanup_partition(cleanup_length: nat, scup: nat) -> bool {
    2 <= scup && scup <= cleanup_length && scup <= 4079
}

pub open spec fn ht_cleanup_byte_claims_valid(
    mel_byte: nat,
    vlc_byte: nat,
    terminal_byte: nat,
    value: u8,
) -> bool {
    mel_byte <= terminal_byte
        && vlc_byte <= terminal_byte
        && (mel_byte < vlc_byte || (mel_byte == vlc_byte && mel_byte < terminal_byte && value != 0xff))
}

pub open spec fn ht_noninitial_vlc_context(
    west_context: u8, north_west: u8, north: u8, north_east: u8,
) -> u8 {
    ((if west_context & 2 != 0 { 2int } else { 0int })
        + (if north_west & 8 != 0 || north & 2 != 0 { 1int } else { 0int })
        + (if north & 8 != 0 || north_east & 2 != 0 { 4int } else { 0int })) as u8
}

pub open spec fn valid_ht_quad_origin(x: nat, y: nat, width: nat, height: nat) -> bool {
    width > 0 && height > 0 && x < width && y < height && x % 2 == 0 && y % 2 == 0
}

pub open spec fn ht_quad_count(width: nat, height: nat) -> nat {
    ((width + 1) / 2) * ((height + 1) / 2)
}

pub open spec fn ht_kappa_extension(gamma: bool, exponent: nat) -> nat {
    if gamma && exponent > 2 {
        (exponent - 2) as nat
    } else {
        0
    }
}

pub open spec fn ht_completed_u(u_base: nat, gamma: bool, exponent: nat) -> nat {
    u_base + ht_kappa_extension(gamma, exponent)
}

pub open spec fn valid_ht_magnitude_width(completed_u: nat) -> bool {
    completed_u > 0 && completed_u <= 75
}

pub open spec fn ht_placeholder_passes(packet_passes: nat) -> nat {
    if packet_passes == 0 {
        0
    } else {
        (((packet_passes - 1) / 3) * 3) as nat
    }
}

pub open spec fn ht_cleanup_passes(packet_passes: nat) -> nat {
    if packet_passes == 0 {
        0
    } else {
        ht_placeholder_passes(packet_passes) + 1
    }
}

pub open spec fn ht_refinement_passes(packet_passes: nat) -> nat {
    (packet_passes - ht_cleanup_passes(packet_passes)) as nat
}

pub open spec fn valid_ht_pass_group(packet_passes: nat) -> bool {
    1 <= packet_passes && packet_passes <= 164
}

pub open spec fn valid_ht_refinement_segment(bytes: nat, passes: nat) -> bool {
    bytes <= 2046 && 1 <= passes && passes <= 2
}

pub open spec fn disjoint_ht_refinement_claims(forward_end: nat, reverse_start: nat) -> bool {
    forward_end <= reverse_start
}

pub open spec fn ht_substantive_passes(packet_passes: nat) -> nat {
    (packet_passes - ht_placeholder_passes(packet_passes)) as nat
}

pub open spec fn mixed_block_selects_ht(lblock: nat, first_length_bit_is_zero: bool) -> bool {
    lblock > 3 && first_length_bit_is_zero
}

pub open spec fn part15_cap_payload_length(capabilities: u8) -> usize {
    (4 + 2 * capabilities as int) as usize
}

pub open spec fn part15_signaling_valid(
    rsiz_ht: bool,
    pcap_ht: bool,
    styles_ht: bool,
    corresponding_profile: bool,
) -> bool {
    rsiz_ht == pcap_ht
        && (!styles_ht || pcap_ht)
        && (!corresponding_profile || pcap_ht)
}

pub open spec fn part15_codestream_class(
    has_legacy: bool,
    has_ht: bool,
    has_mixed: bool,
) -> nat {
    if has_mixed || (has_legacy && has_ht) {
        2
    } else if has_ht {
        1
    } else {
        0
    }
}

pub open spec fn part15_mode_allows(
    mode: nat,
    has_legacy: bool,
    has_mixed: bool,
) -> bool {
    valid_part15_block_mode(mode)
        && (mode != 0 || !has_legacy)
        && (mode != 2 || !has_mixed)
}

pub open spec fn part15_magnitude_bound(parameter: nat) -> nat {
    if parameter == 0 {
        8
    } else if parameter <= 19 {
        parameter + 8
    } else if parameter <= 30 {
        (4 * (parameter - 19) + 27) as nat
    } else {
        74
    }
}

pub open spec fn part15_cleanup_u_bound(
    missing_msbs: nat, placeholder_bitplanes: nat, capability_bound: nat,
) -> nat {
    let bound = missing_msbs + placeholder_bitplanes + 2;
    let capability_limit = if capability_bound < 255 { capability_bound + 1 } else { 255 };
    if bound <= capability_limit { bound } else { capability_limit }
}

pub open spec fn part15_component_allowed(
    roi_allowed: bool,
    has_roi: bool,
    roi_shift: nat,
    irreversible_allowed: bool,
    uses_ht: bool,
    irreversible: bool,
) -> bool {
    (!has_roi || (roi_allowed && roi_shift <= 37))
        && (irreversible_allowed || !uses_ht || !irreversible)
}

pub open spec fn part15_capability_fields_valid(
    mode: nat,
    reserved: nat,
    magnitude_parameter: nat,
) -> bool {
    valid_part15_block_mode(mode) && reserved == 0 && magnitude_parameter < 32
}

pub open spec fn part15_headers_allowed(
    heterogeneous_allowed: bool,
    has_functional_tile_header: bool,
) -> bool {
    heterogeneous_allowed || !has_functional_tile_header
}

pub open spec fn ht_segment_passes(phase: nat, remaining: nat) -> nat {
    if phase == 0 {
        1
    } else if remaining < 3 - phase {
        remaining
    } else {
        (3 - phase) as nat
    }
}

pub open spec fn ht_mixed_selects_legacy(
    segment_length: nat,
    legacy_length: nat,
    cleanup_phase: bool,
    lblock_gt_three: bool,
    leading_zero: bool,
) -> bool {
    (segment_length == 0 && legacy_length != 0)
        || (segment_length != 0 && !(cleanup_phase && lblock_gt_three && leading_zero))
}

pub open spec fn ht_scup(penultimate: u8, last: u8) -> usize {
    (last as int * 16 + penultimate as int % 16) as usize
}

pub open spec fn ht_magsgn_end(cleanup_length: nat, scup: nat) -> nat
    recommends
        scup <= cleanup_length,
{
    (cleanup_length - scup) as nat
}

pub open spec fn ht_forward_data_bits(stuffed: bool) -> nat {
    if stuffed { 7 } else { 8 }
}

pub open spec fn ht_forward_stuffing_valid(stuffed: bool, value: u8) -> bool {
    !stuffed || value < 128
}

pub open spec fn ht_mel_stuffing_valid(previous_ff: bool, value: nat) -> bool {
    !previous_ff || value <= 143
}

pub open spec fn ht_reverse_data_bits(needs_unstuffing: bool, value: u8) -> nat {
    if needs_unstuffing && value % 128 == 127 { 7 } else { 8 }
}

pub open spec fn ht_mel_exponent(state: nat) -> nat {
    if state <= 2 {
        0
    } else if state <= 5 {
        1
    } else if state <= 8 {
        2
    } else if state <= 10 {
        3
    } else if state == 11 {
        4
    } else {
        5
    }
}

pub open spec fn ht_mel_next_state(state: nat, run: bool) -> nat {
    if run {
        if state < 12 { state + 1 } else { 12 }
    } else if state > 0 {
        (state - 1) as nat
    } else {
        0
    }
}

pub open spec fn ht_vlc_table_index(context: nat, lookahead: nat) -> nat {
    context * 128 + lookahead
}

pub open spec fn ht_vlc_word_valid(word: nat, length: nat) -> bool {
    length <= 7 && (word == 0 || length > 0)
}

pub open spec fn ht_uvlc_value(base: nat, suffix: nat, bias: nat) -> nat {
    base + suffix + bias
}

pub open spec fn ht_quad_sample_in_bounds(
    x: nat,
    y: nat,
    sample: nat,
    width: nat,
    height: nat,
) -> bool {
    sample < 4 && x + sample / 2 < width && y + sample % 2 < height
}

pub open spec fn ht_quad_origin_valid(x: nat, y: nat, width: nat, height: nat) -> bool {
    x < width && y < height && x % 2 == 0 && y % 2 == 0
}

pub open spec fn ht_kappa_completion(u_base: nat, gamma: bool, exponent: nat) -> nat {
    u_base + if gamma && exponent > 2 { (exponent - 2) as nat } else { 0 }
}

pub open spec fn ht_magsgn_fill_value() -> nat {
    255
}

pub open spec fn ht_magnitude_payload_bits(completed_u: nat, embedded: bool) -> nat {
    if embedded { (completed_u - 1) as nat } else { completed_u }
}

pub open spec fn ht_magnitude_sign(bit: nat, decoded: bool) -> bool {
    bit == 0 && decoded
}

pub open spec fn ht_bin_center_odd(value: nat) -> nat {
    if value % 2 == 0 { value + 1 } else { value }
}

pub open spec fn ht_claim_available(already_claimed: bool) -> bool {
    !already_claimed
}

pub open spec fn ht_stripe_rows(height: nat, stripe_y: nat) -> nat
    recommends
        stripe_y <= height,
{
    if height - stripe_y < 4 { (height - stripe_y) as nat } else { 4 }
}

pub open spec fn ht_patch_end(patch_x: nat, width: nat) -> nat {
    if patch_x + 4 < width { patch_x + 4 } else { width }
}

pub open spec fn ht_sigprop_eligible(significant: bool, neighbors: nat) -> bool {
    !significant && neighbors > 0
}

pub open spec fn ht_magref_eligible(significant_at_cleanup: bool) -> bool {
    significant_at_cleanup
}

pub open spec fn ht_refinement_pass_total(existing: nat, additional: nat) -> nat {
    existing + additional
}

pub open spec fn ht_multiple_set_allowed(sets_seen: nat, multiple_allowed: bool) -> bool {
    sets_seen == 0 || multiple_allowed
}

pub open spec fn ht_replacement_allowed(
    phase: nat,
    has_cleanup: bool,
    empty_segment: bool,
) -> bool {
    (phase == 0 && empty_segment) || (phase != 0 && has_cleanup)
}

pub open spec fn codestream_count_within_limit(codestreams: nat, limit: nat) -> bool {
    codestreams > 0 && codestreams <= limit
}

pub open spec fn valid_layer_codestream_reference(index: nat, codestreams: nat) -> bool {
    codestreams > 0 && index < codestreams
}

pub open spec fn effective_jpx_layer_count(explicit_layers: nat, codestreams: nat) -> nat {
    if explicit_layers == 0 { codestreams } else { explicit_layers }
}

pub open spec fn valid_jp2_primary_brand(primary_is_jp2: bool, jpx_compatible: bool) -> bool {
    !primary_is_jp2 || !jpx_compatible
}

pub open spec fn valid_jpip_codestream_layout(entries: nat) -> bool {
    entries >= 3 && entries % 2 == 1
}

pub open spec fn tile_transform_scope(start: nat, components: nat, total: nat) -> bool {
    start <= total && components <= total - start
}

pub open spec fn clipped_composition_extent(offset: nat, extent: nat, canvas: nat) -> nat {
    if offset >= canvas {
        0
    } else if extent <= canvas - offset {
        extent
    } else {
        (canvas - offset) as nat
    }
}

pub open spec fn composition_output_bytes(pixels: nat, color_channels: nat) -> nat {
    pixels * (color_channels + 1) * 2
}

pub open spec fn registered_sample_numerator(
    samples: nat,
    subsampling: nat,
    offset: nat,
) -> nat {
    samples * subsampling + offset
}

pub open spec fn composition_instruction_work(frames: nat, layers: nat) -> nat {
    frames * if layers == 0 { 1 } else { layers }
}

pub open spec fn registered_channel_count(
    prior_channels: nat,
    codestream_channels: nat,
) -> nat {
    prior_channels + codestream_channels
}

pub open spec fn nested_metadata_work(boxes: nat, depth: nat) -> nat {
    boxes + depth
}

pub open spec fn bounded_loop_frame(index: nat, frames: nat) -> nat
    recommends frames > 0
{
    index % frames
}

pub open spec fn valid_mct_array_reference(index: nat, arrays: nat) -> bool {
    index > 0 && index <= arrays
}

pub open spec fn valid_mct_dimensions(
    components: nat,
    matrix_elements: nat,
    offset_elements: nat,
) -> bool {
    components > 0
        && matrix_elements == components * components
        && (offset_elements == 0 || offset_elements == components)
}

pub open spec fn mct_work_units(pixels: nat, components: nat) -> nat {
    pixels * components * (components + 1)
}

pub open spec fn valid_mct_collection_count(collections: nat, stages: nat) -> bool {
    collections > 0 && collections <= 64 && stages > 0 && stages <= 255
}

pub open spec fn valid_mct_stage_edge(parent: nat, child: nat, stages: nat) -> bool {
    parent < child && child < stages
}

pub open spec fn valid_mct_matrix_bounds(
    rows: nat,
    columns: nat,
    elements: nat,
    component_limit: nat,
) -> bool {
    rows > 0
        && rows == columns
        && rows <= component_limit
        && elements == rows * columns
}

pub open spec fn valid_mct_fragment_index(index: nat, expected: nat, final_index: nat) -> bool {
    index == expected && index <= final_index
}

pub open spec fn complete_mct_fragment_series(next_index: nat, final_index: nat) -> bool {
    next_index == final_index + 1
}

pub open spec fn mct_dependency_coefficients(components: nat, reversible: bool) -> nat {
    if components == 0 {
        0
    } else if reversible {
        ((components * (components + 1) / 2 - 1) as nat)
    } else {
        ((components * (components - 1) / 2) as nat)
    }
}

pub open spec fn valid_mct_wavelet_partition(
    low_components: nat,
    high_components: nat,
    output_components: nat,
) -> bool {
    low_components + high_components == output_components
}

pub open spec fn mct_wavelet_work_units(
    pixels: nat,
    components: nat,
    levels: nat,
) -> nat {
    pixels * components * (levels + 1) * 8
}

pub open spec fn valid_maxshift_roi(component: nat, components: nat, style: nat, shift: nat) -> bool {
    component < components && style == 0 && shift <= 255
}

pub open spec fn valid_magnitude_bit(bit: nat) -> bool {
    bit < 384
}

pub open spec fn magnitude_limb_index(bit: nat) -> nat {
    bit / 64
}

pub open spec fn magnitude_limb_offset(bit: nat) -> nat {
    bit % 64
}

pub open spec fn magnitude_shift_fits(highest_bit: nat, shift: nat) -> bool {
    highest_bit < 384 && shift < 384 && highest_bit + shift < 384
}

pub open spec fn magnitude_less(left: nat, right: nat) -> bool {
    left < right
}

pub open spec fn magnitude_addition(left: nat, right: nat) -> nat {
    left + right
}

pub open spec fn maxshift_restored_magnitude(magnitude: nat, threshold: nat) -> nat
    recommends
        threshold > 0,
{
    if magnitude < threshold {
        magnitude
    } else {
        magnitude / threshold
    }
}

pub open spec fn component_index_width(components: nat) -> nat {
    if components < 257 { 1 } else { 2 }
}

pub open spec fn valid_component_override_index(component: nat, components: nat) -> bool {
    components > 0 && component < components
}

pub open spec fn palette_linear_index(entry: nat, column: nat, columns: nat) -> nat {
    entry * columns + column
}

pub open spec fn valid_palette_lookup(entry: nat, entries: nat, column: nat, columns: nat) -> bool {
    entries > 0
        && columns > 0
        && entry < entries
        && column < columns
        && palette_linear_index(entry, column, columns) < entries * columns
}

pub open spec fn valid_component_mapping(
    component: nat,
    components: nat,
    mapping_type: nat,
    palette_column: nat,
    palette_columns: nat,
) -> bool {
    component < components
        && ((mapping_type == 0 && palette_column == 0)
            || (mapping_type == 1 && palette_column < palette_columns))
}

pub open spec fn valid_channel_association(association: nat, output_channels: nat) -> bool {
    association <= output_channels || association == 0xffff
}

pub open spec fn valid_color_sample(value: nat, maximum: nat) -> bool {
    maximum > 0 && value <= maximum
}

pub open spec fn color_output_bytes(pixels: nat, channels: nat) -> nat {
    pixels * channels * 2
}

pub open spec fn clamp_color_sample(value: int) -> int {
    if value < 0 {
        0
    } else if value > 65535 {
        65535
    } else {
        value
    }
}

pub open spec fn valid_signed_color_sample(value: int, level: nat) -> bool {
    level > 0 && -(level as int) <= value && value < level
}

pub open spec fn signed_color_to_nominal(value: int, level: nat) -> int {
    value + level as int
}

pub open spec fn resampled_component_coordinate(
    grid_coordinate: nat,
    sampling_step: nat,
    first_component_coordinate: nat,
    component_count: nat,
) -> nat
    recommends
        sampling_step > 0,
        component_count > 0,
{
    let last = (first_component_coordinate + component_count - 1) as nat;
    let nearest = grid_coordinate / sampling_step;
    if nearest < first_component_coordinate {
        first_component_coordinate
    } else if nearest > last {
        last
    } else {
        nearest
    }
}

pub open spec fn packet_length_step(prefix: nat, group: nat) -> nat {
    prefix * 128 + group
}

pub open spec fn packet_length_index_continuous(expected: nat, actual: nat) -> bool {
    expected == actual && actual < 256
}

pub open spec fn packet_lengths_cover_payload(declared: nat, payload: nat) -> bool {
    declared == payload
}

pub open spec fn part9_header_form_valid(form: nat) -> bool {
    1 <= form && form <= 3
}

pub open spec fn part9_header_has_explicit_class(form: nat) -> bool {
    form >= 2
}

pub open spec fn part9_header_has_explicit_codestream(form: nat) -> bool {
    form == 3
}

pub open spec fn part9_vbas_first_is_canonical(payload: nat, continued: bool) -> bool {
    !continued || payload > 0
}

pub open spec fn part9_vbas_step(value: nat, group: nat) -> nat {
    value * 128 + group
}

pub open spec fn part9_auxiliary_present(class_identifier: nat) -> bool {
    class_identifier % 2 == 1
}

pub open spec fn part9_eor_extent(header_length: nat, body_length: nat) -> nat {
    header_length + body_length
}

pub open spec fn part9_class_identifier_valid(class_identifier: nat) -> bool {
    class_identifier <= 8
}

pub open spec fn part9_databin_identity(
    first_class: nat,
    first_codestream: nat,
    first_in_class: nat,
    second_class: nat,
    second_codestream: nat,
    second_in_class: nat,
) -> bool {
    first_class / 2 == second_class / 2
        && first_codestream == second_codestream
        && first_in_class == second_in_class
}

pub open spec fn valid_jpip_fragment(offset: nat, length: nat, limit: nat) -> bool {
    offset <= limit && length <= limit - offset
}

pub open spec fn consistent_jpip_final_length(existing: nat, announced: nat) -> bool {
    existing == announced
}

pub open spec fn jpip_ranges_overlap(
    first_offset: nat,
    first_length: nat,
    second_offset: nat,
    second_length: nat,
) -> bool {
    first_offset < second_offset + second_length
        && second_offset < first_offset + first_length
}

pub open spec fn part9_overlap_consistent(bytes_equal: bool) -> bool {
    bytes_equal
}

pub open spec fn part9_transaction_commit(validation_complete: bool) -> bool {
    validation_complete
}

pub open spec fn part9_merge_start(first: nat, second: nat) -> nat {
    if first < second { first } else { second }
}

pub open spec fn part9_merge_end(first: nat, second: nat) -> nat {
    if first > second { first } else { second }
}

pub open spec fn complete_jpip_databin(contiguous_prefix: nat, final_length: nat) -> bool {
    contiguous_prefix == final_length
}

pub open spec fn complete_jpip_range(available: nat, required: nat) -> bool {
    available == required
}

pub open spec fn part9_missing_length(required_end: nat, available_end: nat) -> nat
    recommends
        available_end <= required_end,
{
    (required_end - available_end) as nat
}

pub open spec fn part9_available_bytes(required: nat, missing: nat) -> nat
    recommends
        missing <= required,
{
    (required - missing) as nat
}

pub open spec fn valid_jpip_progressive_update(
    previous_layers: nat,
    available_layers: nat,
    planned_layers: nat,
) -> bool {
    previous_layers <= available_layers && available_layers <= planned_layers
}

pub open spec fn bounded_jpip_transcode(
    main_header: nat,
    tile_header: nat,
    packet_bytes: nat,
    limit: nat,
) -> bool {
    main_header + tile_header + packet_bytes + 2 <= limit
}

pub open spec fn jpip_precinct_in_class(
    tile: nat,
    tile_count: nat,
    component: nat,
    components: nat,
    precinct_index: nat,
) -> nat {
    tile + tile_count * (component + components * precinct_index)
}

pub open spec fn valid_jpip_precinct_coordinate(
    tile: nat,
    tile_count: nat,
    component: nat,
    components: nat,
) -> bool {
    tile < tile_count && component < components && tile_count > 0 && components > 0
}

pub open spec fn jpip_quality_prefix_available(available: nat, requested: nat) -> bool {
    requested <= available
}

pub open spec fn jpip_reconstructed_box_length(header: nat, payload: nat) -> nat {
    header + payload
}

pub open spec fn part9_metadata_descent_allowed(
    depth: nat,
    maximum_depth: nat,
    cycle: bool,
) -> bool {
    depth <= maximum_depth && !cycle
}

pub open spec fn part9_reconstruction_length(
    main_header: nat,
    tile_headers: nat,
    packet_data: nat,
    eoc: nat,
) -> nat {
    main_header + tile_headers + packet_data + eoc
}

pub open spec fn part9_precinct_flat_identity(
    tile: nat,
    tile_count: nat,
    component_precinct: nat,
) -> nat {
    tile + component_precinct * tile_count
}

pub open spec fn part9_reframed_marker_removed(marker: nat, tile_header: bool) -> bool {
    if tile_header {
        marker == 0xff58 || marker == 0xff61
    } else {
        marker == 0xff55 || marker == 0xff57 || marker == 0xff60
    }
}

pub open spec fn part9_progression_supported(order: nat) -> bool {
    order <= 4
}

pub open spec fn part9_packet_reframed_length(payload: nat, sop: bool, eph: bool) -> nat {
    payload + (if sop { 6 as nat } else { 0 as nat })
        + (if eph { 2 as nat } else { 0 as nat })
}

pub open spec fn jpip_tile_transition_sufficient(
    later_functional: bool,
    preceding_packet_count_known: bool,
    preceding_exact_consumption_known: bool,
) -> bool {
    !later_functional || preceding_packet_count_known || preceding_exact_consumption_known
}

pub open spec fn jpip_packet_boundary_step(
    consumed: nat,
    packet_length: nat,
    tile_part_length: nat,
) -> bool {
    consumed + packet_length <= tile_part_length
}

pub open spec fn jpip_packet_boundary_exact(consumed: nat, tile_part_length: nat) -> bool {
    consumed == tile_part_length
}

pub open spec fn packed_header_index_continuous(expected: nat, actual: nat) -> bool {
    expected == actual && actual < 256
}

pub open spec fn ppm_frame_fits(total: nat, position: nat, length: nat) -> bool {
    position <= total && length <= total - position
}

pub open spec fn packed_packet_length_matches(
    declared: nat,
    tile_body: nat,
    packed_header: nat,
) -> bool {
    declared == tile_body + packed_header
}

pub open spec fn valid_poc_record(
    resolution_start: nat,
    resolution_end: nat,
    component_start: nat,
    component_end: nat,
    layer_end: nat,
    components: nat,
    layers: nat,
    resolutions: nat,
    order: nat,
) -> bool {
    resolution_start < resolution_end
        && resolution_end <= resolutions
        && component_start < component_end
        && component_end <= components
        && 0 < layer_end
        && layer_end <= layers
        && order < 5
}

pub open spec fn poc_contains(
    layer: nat,
    resolution: nat,
    component: nat,
    resolution_start: nat,
    resolution_end: nat,
    component_start: nat,
    component_end: nat,
    layer_end: nat,
) -> bool {
    layer < layer_end
        && resolution_start <= resolution
        && resolution < resolution_end
        && component_start <= component
        && component < component_end
}

pub open spec fn effective_component_override(
    main_default: int,
    main_component: int,
    has_main_component: bool,
    tile_default: int,
    has_tile_default: bool,
    tile_component: int,
    has_tile_component: bool,
) -> int {
    if has_tile_component {
        tile_component
    } else if has_tile_default {
        tile_default
    } else if has_main_component {
        main_component
    } else {
        main_default
    }
}

pub open spec fn decomposition_stage_subbands(direction: nat) -> nat {
    if direction == 0 {
        0
    } else if direction == 1 {
        3
    } else {
        1
    }
}

pub open spec fn valid_decomposition_direction(direction: nat) -> bool {
    direction < 4
}

pub open spec fn decomposition_graph_cardinality(
    no_dwt_stages: nat,
    one_axis_stages: nat,
    bidirectional_stages: nat,
) -> nat {
    1 + one_axis_stages + 3 * bidirectional_stages
}

pub open spec fn decomposition_axis_scale(horizontal_splits: nat) -> nat {
    pow2(horizontal_splits)
}

pub open spec fn valid_decomposition_dimensions(
    parent_width: nat,
    parent_height: nat,
    low_width: nat,
    low_height: nat,
    high_width: nat,
    high_height: nat,
    split_horizontal: bool,
    split_vertical: bool,
) -> bool {
    (!split_horizontal
        || (low_width + high_width == parent_width && low_height == parent_height))
        && (!split_vertical
            || (low_height + high_height == parent_height && low_width == parent_width))
}

pub open spec fn inverse_stage_order(stage: nat, stages: nat) -> nat
    recommends
        stage < stages,
{
    (stages - stage - 1) as nat
}

pub open spec fn packed_two_bit_bytes(elements: nat) -> nat {
    (elements + 3) / 4
}

pub open spec fn ads_payload_bytes(depth_elements: nat, split_elements: nat) -> nat {
    3 + packed_two_bit_bytes(depth_elements) + packed_two_bit_bytes(split_elements)
}

pub open spec fn atk_reconstruction_step(step: nat, steps: nat) -> nat
    recommends
        step < steps,
{
    (steps - step - 1) as nat
}

pub open spec fn atk_update_parity(initial_odd: bool, reverse_step: nat) -> bool {
    if reverse_step % 2 == 0 {
        initial_odd
    } else {
        !initial_odd
    }
}

pub open spec fn valid_cbd_scope(in_main_header: bool) -> bool {
    in_main_header
}

// Selected Part 2 and JPX functional semantics used by executable production contracts.
pub open spec fn part2_tlm_tile_index_bytes(style: u8) -> usize {
    (((style >> 4) & 3) as int) as usize
}

pub open spec fn part2_tlm_length_bytes(style: u8) -> usize {
    if style & 0x40 == 0 { 2 } else { 4 }
}

pub open spec fn part2_crg_payload_bytes(components: u16) -> usize {
    ((components as int) * 4) as usize
}

pub open spec fn part2_packed_two_bit_bytes(elements: usize) -> usize {
    ((elements + 3) / 4) as usize
}

pub open spec fn part2_dfs_direction_code(byte: u8, slot: u8) -> u8
    recommends slot < 4,
{
    (byte >> (6 - 2 * slot)) & 3
}

pub open spec fn part2_cbd_precision(encoded: u8) -> u8 {
    (((encoded & 0x7f) as int) + 1) as u8
}

pub open spec fn part2_cbd_signed(encoded: u8) -> bool {
    encoded & 0x80 != 0
}

pub open spec fn part2_nlt_binary_complement(source: i128, half: i128) -> i128 {
    if source < 0 {
        (-(source as int) - ((half as int) + 1)) as i128
    } else {
        source
    }
}

pub open spec fn part2_atk_reconstruction_step(remaining: usize) -> usize
    recommends remaining > 0,
{
    (remaining - 1) as usize
}

pub open spec fn part2_atk_next_parity(current: bool) -> bool {
    !current
}

pub open spec fn part2_fragment_next(index: u16) -> u16
    recommends index < u16::MAX,
{
    ((index as int) + 1) as u16
}

pub open spec fn part2_fragment_complete(next: u16, final_index: u16) -> bool {
    next as int == final_index as int + 1
}

pub open spec fn part2_mct_reverse_stage(remaining: usize) -> usize
    recommends remaining > 0,
{
    (remaining - 1) as usize
}

pub open spec fn part2_binary_fixed_shift(binary_exponent: i32) -> i32
    recommends
        i32::MIN + 32 <= binary_exponent,
        binary_exponent <= i32::MAX - 32,
{
    ((binary_exponent as int) + 32) as i32
}

pub open spec fn part2_palette_coordinates_valid(
    entry: u16,
    entries: u16,
    column: u8,
    columns: u8,
) -> bool {
    entry < entries && column < columns
}

pub type Part2PaletteModel = (u16, Seq<crate::jp2::PaletteColumn>, Seq<i64>);

pub open spec fn part2_palette_value(
    palette: Part2PaletteModel, entry: u16, column: u8,
) -> Result<i64, crate::DecodeError> {
    if palette.1.len() > u8::MAX {
        Err(part2_composition_error(true))
    } else if !part2_palette_coordinates_valid(
        entry, palette.0, column, palette.1.len() as u8,
    ) {
        Err(part2_composition_error(false))
    } else {
        let index = (entry as nat) * palette.1.len() + (column as nat);
        if index > usize::MAX {
            Err(part2_composition_error(true))
        } else if index >= palette.2.len() {
            Err(part2_composition_error(false))
        } else { Ok(palette.2[index as int]) }
    }
}

pub open spec fn part2_component_mapping_valid(
    component: u16,
    components: u16,
    mapping_type: u8,
    palette_column: u8,
    palette_columns: u8,
) -> bool {
    component < components
        && ((mapping_type == 0 && palette_column == 0)
            || (mapping_type == 1
                && palette_columns > 0
                && palette_column < palette_columns))
}

pub open spec fn part2_channel_definition_valid(
    channel: u16,
    channel_type: u16,
    association: u16,
    output_channels: u16,
) -> bool {
    channel < output_channels
        && (channel_type == 0
            || channel_type == 1
            || channel_type == 2
            || channel_type == 0xffff)
        && (association <= output_channels || association == 0xffff)
}

pub open spec fn part2_first_override_allowed(already_overridden: bool) -> bool {
    !already_overridden
}

pub open spec fn part2_signed_to_nominal(value: i64, level: i64) -> i64 {
    ((value as int) + (level as int)) as i64
}

pub open spec fn part2_effective_layer_count(
    explicit_layers: usize,
    codestreams: usize,
) -> usize {
    if explicit_layers == 0 { codestreams } else { explicit_layers }
}

pub open spec fn part2_registered_extent(numerator: u64, grid: u64) -> u64
    recommends grid > 0,
{
    if numerator == 0 {
        0
    } else {
        (1 + ((numerator - 1) as int) / (grid as int)) as u64
    }
}

pub type Part2LayerRegistration = (u16, u8, u8, u32, u32);
pub type Part2RegistrationContext = (Part2OwnedLayer, Part2LayerRegistration, (u16, u16), u32);
pub type Part2RegistrationExecution = (Result<(), crate::DecodeError>, Seq<Seq<u16>>, Seq<u16>);

pub open spec fn part2_registered_column(
    context: Part2RegistrationContext, y: u32, source_y: u32, x: u32,
    colors: Seq<Seq<u16>>, alpha: Seq<u16>,
) -> Part2RegistrationExecution {
    if context.1.1 == 0 {
        (Err(part2_composition_error(false)), colors, alpha)
    } else {
        let numerator = (x as nat) * (context.2.0 as nat);
        if numerator > u32::MAX as nat {
            (Err(part2_composition_error(true)), colors, alpha)
        } else if numerator < context.1.3 {
            (Ok(()), colors, alpha)
        } else {
            let source_x = part2_registered_source_coordinate(numerator as u32, context.1.3, context.1.1 as u32);
            if source_x >= context.0.0 { (Ok(()), colors, alpha) }
            else { part2_registered_pixel(context.0, colors, alpha, source_x, source_y, context.3, x, y) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_registered_columns_prefix(
    context: Part2RegistrationContext, y: u32, source_y: u32,
    initial_colors: Seq<Seq<u16>>, initial_alpha: Seq<u16>, count: nat,
) -> Part2RegistrationExecution
    decreases count,
{
    if count == 0 { (Ok(()), initial_colors, initial_alpha) }
    else {
        let previous = part2_registered_columns_prefix(context, y, source_y, initial_colors, initial_alpha, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_registered_column(context, y, source_y, (count - 1) as u32, previous.1, previous.2),
        }
    }
}

pub open spec fn part2_registered_row(
    context: Part2RegistrationContext, y: u32, colors: Seq<Seq<u16>>, alpha: Seq<u16>,
) -> Part2RegistrationExecution {
    if context.1.2 == 0 {
        (Err(part2_composition_error(false)), colors, alpha)
    } else {
        let numerator = (y as nat) * (context.2.1 as nat);
        if numerator > u32::MAX as nat {
            (Err(part2_composition_error(true)), colors, alpha)
        } else if numerator < context.1.4 {
            (Ok(()), colors, alpha)
        } else {
            let source_y = part2_registered_source_coordinate(numerator as u32, context.1.4, context.1.2 as u32);
            if source_y >= context.0.1 { (Ok(()), colors, alpha) }
            else if context.1.1 == 0 { (Err(part2_composition_error(false)), colors, alpha) }
            else { part2_registered_columns_prefix(context, y, source_y, colors, alpha, context.3 as nat) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_registered_rows_prefix(
    context: Part2RegistrationContext, initial_colors: Seq<Seq<u16>>, initial_alpha: Seq<u16>, count: nat,
) -> Part2RegistrationExecution
    decreases count,
{
    if count == 0 { (Ok(()), initial_colors, initial_alpha) }
    else {
        let previous = part2_registered_rows_prefix(context, initial_colors, initial_alpha, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_registered_row(context, (count - 1) as u32, previous.1, previous.2),
        }
    }
}

pub open spec fn part2_register_layer(
    source: Part2OwnedLayer, registration: Part2LayerRegistration, horizontal_grid: u16, vertical_grid: u16,
) -> Part2OwnedLayerResult {
    match part2_registered_layer_geometry(source.0, source.1, registration, horizontal_grid, vertical_grid) {
        Err(error) => Err(error),
        Ok((width, height, pixels)) => {
            let context = (source, registration, (horizontal_grid, vertical_grid), width);
            let colors = Seq::new(source.3.len(), |_channel: int| Seq::new(pixels as nat, |_pixel: int| 0u16));
            let alpha = Seq::new(pixels as nat, |_pixel: int| 0u16);
            let copied = part2_registered_rows_prefix(context, colors, alpha, height as nat);
            match copied.0 {
                Err(error) => Err(error),
                Ok(()) => Ok((width, height, source.2, copied.1, Some((copied.2,
                    match source.4 { None => false, Some((_, premultiplied)) => premultiplied })))),
            }
        },
    }
}

pub open spec fn part2_registered_color_store(
    colors: Seq<Seq<u16>>, source: Seq<Seq<u16>>, color: nat, source_index: usize, destination: usize,
) -> (Result<(), crate::DecodeError>, Seq<Seq<u16>>) {
    if color >= colors.len() || color >= source.len() || source_index >= source[color as int].len()
        || destination >= colors[color as int].len() {
        (Err(part2_composition_error(false)), colors)
    } else {
        (Ok(()), colors.update(color as int,
            colors[color as int].update(destination as int, source[color as int][source_index as int])))
    }
}

#[verifier::opaque]
pub open spec fn part2_registered_colors_prefix(
    initial: Seq<Seq<u16>>, source: Seq<Seq<u16>>, source_index: usize, destination: usize, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<Seq<u16>>)
    decreases count,
{
    if count == 0 { (Ok(()), initial) }
    else {
        let previous = part2_registered_colors_prefix(initial, source, source_index, destination, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_registered_color_store(previous.1, source, (count - 1) as nat, source_index, destination),
        }
    }
}

pub open spec fn part2_registered_pixel(
    source: Part2OwnedLayer, colors: Seq<Seq<u16>>, alpha: Seq<u16>,
    source_x: u32, source_y: u32, width: u32, x: u32, y: u32,
) -> (Result<(), crate::DecodeError>, Seq<Seq<u16>>, Seq<u16>) {
    match part2_composition_pixel_index(source.0, source_x, source_y) {
        None => (Err(part2_composition_error(true)), colors, alpha),
        Some(source_index) => match part2_composition_pixel_index(width, x, y) {
            None => (Err(part2_composition_error(true)), colors, alpha),
            Some(destination) => {
                let copied = part2_registered_colors_prefix(colors, source.3, source_index, destination, colors.len());
                match copied.0 {
                    Err(error) => (Err(error), copied.1, alpha),
                    Ok(()) => {
                        let sample = match source.4 {
                            None => Ok(u16::MAX),
                            Some((samples, _)) => if source_index < samples.len() { Ok(samples[source_index as int]) }
                                else { Err(part2_composition_error(false)) },
                        };
                        match sample {
                            Err(error) => (Err(error), copied.1, alpha),
                            Ok(value) => if destination >= alpha.len() {
                                (Err(part2_composition_error(false)), copied.1, alpha)
                            } else { (Ok(()), copied.1, alpha.update(destination as int, value)) },
                        }
                    },
                }
            },
        },
    }
}

pub open spec fn part2_native_registered_extent(samples: u32, subsampling: u32, grid: u32, offset: u32)
    -> Result<u32, crate::DecodeError>
{
    if grid == 0 {
        Err(part2_composition_error(false))
    } else {
        let numerator = (samples as nat) * (subsampling as nat) + offset as nat;
        if numerator > u64::MAX as nat || numerator + grid as nat - 1 > u64::MAX as nat {
            Err(part2_composition_error(true))
        } else {
            let extent = part2_registered_extent(numerator as u64, grid as u64);
            if extent > u32::MAX as u64 { Err(part2_composition_error(true)) }
            else { Ok(extent as u32) }
        }
    }
}

pub open spec fn part2_registered_layer_geometry(
    width: u32, height: u32, registration: Part2LayerRegistration, horizontal_grid: u16, vertical_grid: u16,
) -> Result<(u32, u32, usize), crate::DecodeError> {
    if registration.1 == 0 || registration.2 == 0 || horizontal_grid == 0 || vertical_grid == 0 {
        Err(part2_composition_error(false))
    } else {
        match part2_native_registered_extent(width, registration.1 as u32, horizontal_grid as u32, registration.3) {
            Err(error) => Err(error),
            Ok(registered_width) => match part2_native_registered_extent(
                height, registration.2 as u32, vertical_grid as u32, registration.4,
            ) {
                Err(error) => Err(error),
                Ok(registered_height) => match part2_layer_area(registered_width, registered_height) {
                    Err(error) => Err(error),
                    Ok(pixels) => Ok((registered_width, registered_height, pixels)),
                },
            },
        }
    }
}

pub open spec fn part2_registered_source_coordinate(
    numerator: u32,
    offset: u32,
    subsampling: u32,
) -> u32
    recommends
        subsampling > 0,
        offset <= numerator,
{
    (((numerator as int) - (offset as int)) / (subsampling as int)) as u32
}

pub open spec fn part2_composition_clip(offset: u32, extent: u32, canvas: u32) -> u32 {
    if offset >= canvas {
        0
    } else if extent <= canvas - offset {
        extent
    } else {
        ((canvas as int) - (offset as int)) as u32
    }
}

pub open spec fn part2_composition_mapped_offset(position: u32, source_extent: u32, target_extent: u32) -> nat
    recommends target_extent > 0,
{
    (position as nat) * (source_extent as nat) / (target_extent as nat)
}

pub open spec fn part2_row_major_index(width: u32, x: u32, y: u32) -> nat {
    (y as nat) * (width as nat) + x as nat
}

pub open spec fn part2_composition_pixel_index(width: u32, x: u32, y: u32) -> Option<usize> {
    let index = part2_row_major_index(width, x, y);
    if index <= usize::MAX as nat { Some(index as usize) } else { None }
}

pub open spec fn part2_loop_frame(index: usize, frames: usize) -> usize
    recommends frames > 0,
{
    (index % frames) as usize
}

pub open spec fn part2_inverse_alpha(source_alpha: u16) -> u16 {
    ((PART2_NORMALIZED_SAMPLE_MAX as int) - source_alpha as int) as u16
}

pub type Part2LayerChannel = (crate::color::ConvertedChannelType, Seq<u16>);
pub type Part2LayerAlpha = (Seq<u16>, bool);
pub type Part2LayerInputResult = Result<(u32, u32, Seq<Seq<u16>>, Option<Part2LayerAlpha>), crate::DecodeError>;
pub type Part2OwnedLayerResult = Result<(u32, u32, crate::color::ConvertedColorSpace, Seq<Seq<u16>>, Option<Part2LayerAlpha>), crate::DecodeError>;
pub type Part2OwnedLayer = (u32, u32, crate::color::ConvertedColorSpace, Seq<Seq<u16>>, Option<Part2LayerAlpha>);
pub type Part2OpacityCopyContext = (Seq<u16>, u32, u32);

pub open spec fn part2_opacity_pixel(
    context: Part2OpacityCopyContext, x: u32, y: u32, alpha: Seq<u16>,
) -> (Result<(), crate::DecodeError>, Seq<u16>) {
    match part2_composition_pixel_index(context.2, x, y) {
        None => (Err(part2_composition_error(true)), alpha),
        Some(destination) => match part2_composition_pixel_index(context.1, x, y) {
            None => (Err(part2_composition_error(true)), alpha),
            Some(source) => if source >= context.0.len() || destination >= alpha.len() {
                (Err(part2_composition_error(false)), alpha)
            } else { (Ok(()), alpha.update(destination as int, context.0[source as int])) },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_opacity_columns_prefix(
    context: Part2OpacityCopyContext, y: u32, initial: Seq<u16>, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<u16>)
    decreases count,
{
    if count == 0 { (Ok(()), initial) }
    else {
        let previous = part2_opacity_columns_prefix(context, y, initial, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_opacity_pixel(context, (count - 1) as u32, y, previous.1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_opacity_rows_prefix(
    context: Part2OpacityCopyContext, width: u32, initial: Seq<u16>, count: nat,
) -> (Result<(), crate::DecodeError>, Seq<u16>)
    decreases count,
{
    if count == 0 { (Ok(()), initial) }
    else {
        let previous = part2_opacity_rows_prefix(context, width, initial, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_opacity_columns_prefix(context, (count - 1) as u32, previous.1, width as nat),
        }
    }
}

pub open spec fn part2_copy_registered_opacity(owned: Part2OwnedLayer, source: Part2OwnedLayer, premultiplied: bool)
    -> (Result<(), crate::DecodeError>, Part2OwnedLayer)
{
    if source.3.len() == 0 { (Err(part2_composition_error(false)), owned) }
    else {
        match part2_layer_area(owned.0, owned.1) {
            Err(error) => (Err(error), owned),
            Ok(pixels) => {
                let width = if owned.0 < source.0 { owned.0 } else { source.0 };
                let height = if owned.1 < source.1 { owned.1 } else { source.1 };
                let initial = Seq::new(pixels as nat, |_index: int| 0u16);
                let copied = part2_opacity_rows_prefix((source.3[0], source.0, owned.0), width, initial, height as nat);
                match copied.0 {
                    Err(error) => (Err(error), owned),
                    Ok(()) => (Ok(()), (owned.0, owned.1, owned.2, owned.3, Some((copied.1, premultiplied)))),
                }
            },
        }
    }
}

pub type Part2ComponentKeyAssembly = (Result<(), crate::DecodeError>, Seq<u16>, usize);

#[verifier::opaque]
pub open spec fn part2_chroma_descriptor_bytes(descriptors: Seq<(u8, bool)>, count: nat)
    -> Result<usize, crate::DecodeError>
    recommends count <= descriptors.len(),
    decreases count,
{
    if count == 0 { Ok(0) }
    else {
        match part2_chroma_descriptor_bytes(descriptors, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => {
                let bits = descriptors[(count - 1) as int].0;
                if bits == 0 || bits > 38 { Err(part2_composition_error(false)) }
                else {
                    let bytes = (bits as nat + 7) / 8;
                    if previous as nat + bytes > usize::MAX as nat { Err(part2_composition_error(true)) }
                    else { Ok((previous as nat + bytes) as usize) }
                }
            },
        }
    }
}

pub open spec fn part2_append_component_key(
    values: Seq<u8>, descriptor: (u8, bool), keys: Seq<u16>, offset: usize,
) -> Part2ComponentKeyAssembly {
    let sum = descriptor.0 as nat + 7;
    let bytes = (if sum > 255 { 255nat } else { sum }) / 8;
    if offset as nat + bytes > usize::MAX as nat {
        (Err(part2_composition_error(true)), keys, offset)
    } else {
        let end = (offset as nat + bytes) as usize;
        if end > values.len() { (Err(part2_composition_error(false)), keys, offset) }
        else {
            let normalized = part2_normalized_chroma_keys(values.subrange(offset as int, end as int), 1,
                crate::jp2::ComponentBitDepth::Uniform { bits: descriptor.0, signed: descriptor.1 });
            match normalized {
                Err(error) => (Err(error), keys, offset),
                Ok(new_keys) => if new_keys.len() == 0 { (Err(part2_composition_error(false)), keys, offset) }
                    else { (Ok(()), keys.push(new_keys[0]), end) },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_component_keys_prefix(values: Seq<u8>, descriptors: Seq<(u8, bool)>, count: nat)
    -> Part2ComponentKeyAssembly
    recommends count <= descriptors.len(),
    decreases count,
{
    if count == 0 { (Ok(()), Seq::empty(), 0) }
    else {
        let previous = part2_component_keys_prefix(values, descriptors, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part2_append_component_key(values, descriptors[(count - 1) as int], previous.1, previous.2),
        }
    }
}

pub open spec fn part2_normalized_component_chroma_keys(values: Seq<u8>, descriptors: Seq<(u8, bool)>)
    -> Result<Seq<u16>, crate::DecodeError>
{
    match part2_chroma_descriptor_bytes(descriptors, descriptors.len()) {
        Err(error) => Err(error),
        Ok(expected) => if values.len() != expected { Err(part2_composition_error(false)) }
            else {
                let assembled = part2_component_keys_prefix(values, descriptors, descriptors.len());
                match assembled.0 { Err(error) => Err(error), Ok(()) => Ok(assembled.1) }
            },
    }
}

#[verifier::opaque]
pub open spec fn part2_chroma_key_bytes(values: Seq<u8>, start: nat, count: nat) -> nat
    recommends start + count <= values.len(),
    decreases count,
{
    if count == 0 { 0 }
    else { part2_chroma_key_bytes(values, start, (count - 1) as nat) * 256 + values[(start + count - 1) as int] as nat }
}

pub open spec fn part2_chroma_key_normalize(raw: nat, bits: u8, signed: bool) -> u16
    recommends 0 < bits <= 38,
{
    let maximum = ((1u64 << bits) - 1) as u64;
    let nominal = if signed {
        ((raw as u64) & maximum) ^ (((maximum + 1) / 2) as u64)
    } else { (raw as u64) & maximum };
    (((nominal as nat) * 65535 + maximum as nat / 2) / maximum as nat) as u16
}

pub open spec fn part2_normalized_chroma_keys(values: Seq<u8>, channels: u8, depth: crate::jp2::ComponentBitDepth)
    -> Result<Seq<u16>, crate::DecodeError>
{
    match depth {
        crate::jp2::ComponentBitDepth::Variable => Err(crate::DecodeError::MalformedInput {
            offset: 0, kind: crate::MalformedKind::MissingRequiredStructure,
        }),
        crate::jp2::ComponentBitDepth::Uniform { bits, signed } => {
            if bits == 0 || bits > 38 { Err(part2_composition_error(false)) }
            else {
                let bytes = (bits as nat + 7) / 8;
                if values.len() != bytes * channels as nat { Err(part2_composition_error(false)) }
                else { Ok(Seq::new(channels as nat, |channel: int|
                    part2_chroma_key_normalize(part2_chroma_key_bytes(values, (channel * bytes) as nat, bytes), bits, signed))) }
            }
        },
    }
}

pub open spec fn part2_chroma_key_channel_matches(
    colors: Seq<Seq<u16>>, keys: Seq<u16>, pixel: int, channel: int,
) -> bool {
    0 <= channel < colors.len() && 0 <= pixel < colors[channel].len()
        && channel < keys.len() && colors[channel][pixel] == keys[channel]
}

pub open spec fn part2_chroma_key_pixel(colors: Seq<Seq<u16>>, keys: Seq<u16>, pixel: int) -> u16 {
    if forall|channel: int| 0 <= channel < colors.len() ==>
        #[trigger] part2_chroma_key_channel_matches(colors, keys, pixel, channel) {
        0
    } else {
        u16::MAX
    }
}

pub open spec fn part2_chroma_plane_has_samples(samples: Seq<u16>, count: nat) -> bool {
    samples.len() >= count
}

pub open spec fn part2_chroma_sources_cover(colors: Seq<Seq<u16>>, count: nat) -> bool {
    forall|channel: int| 0 <= channel < colors.len() ==>
        #[trigger] part2_chroma_plane_has_samples(colors[channel], count)
}

pub open spec fn part2_apply_chroma_key_policy(layer: Part2OwnedLayer, keys: Seq<u16>, reject_missing: bool)
    -> (Result<(), crate::DecodeError>, Part2OwnedLayer)
{
    if !reject_missing || keys.len() != layer.3.len() {
        part2_apply_chroma_key(layer, keys)
    } else {
        match part2_layer_area(layer.0, layer.1) {
            Err(_) => part2_apply_chroma_key(layer, keys),
            Ok(pixels) => if part2_chroma_sources_cover(layer.3, pixels as nat) { part2_apply_chroma_key(layer, keys) }
                else { (Err(part2_composition_error(false)), layer) },
        }
    }
}

pub open spec fn part2_set_layer_alpha_mode(layer: Part2OwnedLayer, premultiplied: bool, offset: u64)
    -> (Result<(), crate::DecodeError>, Part2OwnedLayer)
{
    match layer.4 {
        None => (Err(crate::DecodeError::MalformedInput { offset, kind: crate::MalformedKind::MissingRequiredStructure }), layer),
        Some((samples, _)) => (Ok(()), (layer.0, layer.1, layer.2, layer.3, Some((samples, premultiplied)))),
    }
}

pub open spec fn part2_apply_chroma_key(layer: Part2OwnedLayer, keys: Seq<u16>)
    -> (Result<(), crate::DecodeError>, Part2OwnedLayer)
{
    if keys.len() != layer.3.len() {
        (Err(part2_composition_error(false)), layer)
    } else {
        match part2_layer_area(layer.0, layer.1) {
            Err(error) => (Err(error), layer),
            Ok(pixels) => (Ok(()), (layer.0, layer.1, layer.2, layer.3,
                Some((Seq::new(pixels as nat, |pixel: int| part2_chroma_key_pixel(layer.3, keys, pixel)), false)))),
        }
    }
}

pub type Part2ConvertedImage = (u32, u32, crate::color::ConvertedColorSpace, u8, Seq<Part2LayerChannel>);
pub type Part2ConvertedImageResult = Result<Part2ConvertedImage, crate::DecodeError>;
pub type Part2Instruction = (usize, u32, u32, u32, u32, u32, u32, u32, u32, bool, u32);
pub type Part2Placement = (Part2OwnedLayer, Part2Instruction);
pub type Part2Frame = (usize, u64, u32, bool, Seq<Part2Instruction>);
pub type Part2TimelineInstruction = (Part2Instruction, u32);
pub type Part2TimelineSet = (u16, Seq<Part2TimelineInstruction>);
pub type Part2TimelineState = (Seq<Part2Frame>, Seq<Option<usize>>, usize, usize, u64);
pub type Part2TimelineExecution = Result<(bool, Part2TimelineState), crate::DecodeError>;
pub type Part2SuppliedLayer = (usize, Option<Part2OwnedLayerResult>);
pub type Part2GatheredLayers = (Result<(), crate::DecodeError>, Seq<Part2Placement>, Seq<Part2SuppliedLayer>);
pub type Part2RenderState = (Result<(), crate::DecodeError>, Seq<Seq<u16>>, Seq<u16>, nat, nat);
pub type Part2LayerScanResult = Result<(Seq<Option<Seq<u16>>>, Seq<Part2LayerAlpha>), crate::DecodeError>;

pub open spec fn part2_color_input_error() -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::ContainerCodestreamMismatch }
}

pub open spec fn part2_output_channel(space: crate::color::ConvertedColorSpace, index: int)
    -> crate::color::ConvertedChannelType
{
    match space {
        crate::color::ConvertedColorSpace::Grayscale => crate::color::ConvertedChannelType::Gray,
        crate::color::ConvertedColorSpace::Srgb => if index == 0 { crate::color::ConvertedChannelType::Red }
            else if index == 1 { crate::color::ConvertedChannelType::Green }
            else { crate::color::ConvertedChannelType::Blue },
    }
}

pub open spec fn part2_image_from_planes(
    width: u32, height: u32, space: crate::color::ConvertedColorSpace,
    colors: Seq<Seq<u16>>, alpha: Seq<u16>, premultiplied: bool,
) -> Part2ConvertedImageResult {
    match part2_layer_area(width, height) {
        Err(error) => Err(error),
        Ok(area) => if colors.len() != part2_layer_color_count(space) || alpha.len() != area
            || exists|i: int| 0 <= i < colors.len() && colors[i].len() != area {
            Err(part2_color_input_error())
        } else {
            Ok((width, height, space, 16,
                Seq::new(colors.len(), |i: int| (part2_output_channel(space, i), colors[i]))
                    .push((crate::color::ConvertedChannelType::Alpha {
                        premultiplied, association: crate::image::ChannelAssociation::WholeImage,
                    }, alpha))))
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_layer_area(width: u32, height: u32) -> Result<usize, crate::DecodeError> {
    if (width as nat) * (height as nat) <= usize::MAX as nat {
        Ok(((width as nat) * (height as nat)) as usize)
    } else {
        Err(part2_composition_error(true))
    }
}

pub open spec fn part2_layer_color_count(space: crate::color::ConvertedColorSpace) -> nat {
    match space {
        crate::color::ConvertedColorSpace::Srgb => 3,
        crate::color::ConvertedColorSpace::Grayscale => 1,
    }
}

pub open spec fn part2_layer_channel_index(kind: crate::color::ConvertedChannelType) -> Option<nat> {
    match kind {
        crate::color::ConvertedChannelType::Red | crate::color::ConvertedChannelType::Gray => Some(0),
        crate::color::ConvertedChannelType::Green => Some(1),
        crate::color::ConvertedChannelType::Blue => Some(2),
        crate::color::ConvertedChannelType::Alpha { .. } => None,
    }
}

pub open spec fn part2_layer_channel_scan_step(
    colors: Seq<Option<Seq<u16>>>, alphas: Seq<Part2LayerAlpha>, channel: Part2LayerChannel,
) -> Part2LayerScanResult {
    match channel.0 {
        crate::color::ConvertedChannelType::Alpha { premultiplied, .. } =>
            Ok((colors, alphas.push((channel.1, premultiplied)))),
        _ => {
            let slot = part2_layer_channel_index(channel.0).unwrap();
            if slot >= colors.len() || colors[slot as int].is_some() {
                Err(part2_composition_error(false))
            } else {
                Ok((colors.update(slot as int, Some(channel.1)), alphas))
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_layer_channel_scan(
    channels: Seq<Part2LayerChannel>, color_count: nat, count: nat,
) -> Part2LayerScanResult
    recommends count <= channels.len(),
    decreases count,
{
    if count == 0 {
        Ok((Seq::new(color_count, |i: int| None), Seq::empty()))
    } else {
        match part2_layer_channel_scan(channels, color_count, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok((colors, alphas)) => part2_layer_channel_scan_step(colors, alphas, channels[(count - 1) as int]),
        }
    }
}

pub open spec fn part2_layer_resolve_colors(colors: Seq<Option<Seq<u16>>>, area: nat)
    -> Result<Seq<Seq<u16>>, crate::DecodeError>
{
    if exists |i: int| #![trigger colors[i]] 0 <= i < colors.len() && (colors[i].is_none() || colors[i].unwrap().len() != area) {
        Err(part2_composition_error(false))
    } else {
        Ok(Seq::new(colors.len(), |i: int| colors[i].unwrap()))
    }
}

pub open spec fn part2_normalized_sample_product(first: u16, second: u16) -> nat {
    ((first as nat) * (second as nat) + PART2_NORMALIZED_SAMPLE_HALF as nat)
        / PART2_NORMALIZED_SAMPLE_MAX as nat
}

pub open spec fn part2_layer_alpha_merge(
    previous: Option<Part2LayerAlpha>, next: Part2LayerAlpha, area: nat,
) -> Result<Option<Part2LayerAlpha>, crate::DecodeError> {
    if next.0.len() != area {
        Err(part2_composition_error(false))
    } else {
        match previous {
            None => Ok(Some(next)),
            Some((samples, _)) => Ok(Some((
                Seq::new(area, |i: int| part2_normalized_sample_product(samples[i], next.0[i]) as u16),
                false,
            ))),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_layer_alpha_fold(alphas: Seq<Part2LayerAlpha>, area: nat, count: nat)
    -> Result<Option<Part2LayerAlpha>, crate::DecodeError>
    recommends count <= alphas.len(),
    decreases count,
{
    if count == 0 {
        Ok(None)
    } else {
        match part2_layer_alpha_fold(alphas, area, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_layer_alpha_merge(previous, alphas[(count - 1) as int], area),
        }
    }
}

pub open spec fn part2_layer_input(
    width: u32, height: u32, space: crate::color::ConvertedColorSpace, channels: Seq<Part2LayerChannel>,
) -> Part2LayerInputResult {
    match part2_layer_channel_scan(channels, part2_layer_color_count(space), channels.len()) {
        Err(error) => Err(error),
        Ok((colors, alphas)) => {
            let area = (width as nat) * (height as nat);
            if area > usize::MAX as nat {
                Err(part2_composition_error(true))
            } else {
                match part2_layer_resolve_colors(colors, area) {
                    Err(error) => Err(error),
                    Ok(resolved) => match part2_layer_alpha_fold(alphas, area, alphas.len()) {
                        Err(error) => Err(error),
                        Ok(alpha) => Ok((width, height, resolved, alpha)),
                    },
                }
            }
        },
    }
}

pub open spec fn part2_owned_layer_input(
    width: u32, height: u32, space: crate::color::ConvertedColorSpace, channels: Seq<Part2LayerChannel>,
) -> Part2OwnedLayerResult {
    match part2_layer_input(width, height, space, channels) {
        Err(error) => Err(error),
        Ok((width, height, colors, alpha)) => Ok((width, height, space, colors, alpha)),
    }
}

pub open spec fn part2_source_over_alpha_numerator(source_alpha: u16, destination_alpha: u16) -> nat {
    let maximum = PART2_NORMALIZED_SAMPLE_MAX as nat;
    let inverse = ((maximum as int) - source_alpha as int) as nat;
    (source_alpha as nat) * maximum + (destination_alpha as nat) * inverse
}

pub open spec fn part2_source_over_color_numerator(
    source: u16, destination: u16, source_alpha: u16, destination_alpha: u16, premultiplied: bool,
) -> nat {
    let maximum = PART2_NORMALIZED_SAMPLE_MAX as nat;
    let source_term = if premultiplied {
        (source as nat) * maximum * maximum
    } else {
        (source as nat) * (source_alpha as nat) * maximum
    };
    let inverse = ((maximum as int) - source_alpha as int) as nat;
    source_term + (destination as nat) * (destination_alpha as nat) * inverse
}

pub open spec fn part2_source_over_rounded_ratio(numerator: u64, denominator: u64) -> nat {
    if denominator == 0 { 0 } else {
        ((numerator as nat) + (denominator as nat) / 2) / (denominator as nat)
    }
}

pub open spec fn part2_source_over_color_sample(
    source: u16, destination: u16, source_alpha: u16, destination_alpha: u16, premultiplied: bool,
) -> nat {
    let alpha = part2_source_over_alpha_numerator(source_alpha, destination_alpha);
    if alpha == 0 { 0 } else {
        (part2_source_over_color_numerator(
            source, destination, source_alpha, destination_alpha, premultiplied,
        ) + alpha / 2) / alpha
    }
}

pub open spec fn part2_source_over_alpha_sample(source_alpha: u16, destination_alpha: u16) -> nat {
    (part2_source_over_alpha_numerator(source_alpha, destination_alpha)
        + PART2_NORMALIZED_SAMPLE_HALF as nat) / PART2_NORMALIZED_SAMPLE_MAX as nat
}

pub open spec fn part2_composition_store(samples: Seq<u16>, index: nat, value: u16) -> (bool, Seq<u16>) {
    if index < samples.len() { (true, samples.update(index as int, value)) } else { (false, samples) }
}

pub open spec fn part2_composition_gather_channel(
    source: Seq<Seq<u16>>, destination: Seq<Seq<u16>>,
    source_index: nat, destination_index: nat, expand_grayscale: bool, channel: nat,
) -> Option<(u16, u16)> {
    let source_channel = if expand_grayscale { 0nat } else { channel };
    if source_channel >= source.len() || channel >= destination.len() {
        None
    } else if source_index >= source[source_channel as int].len()
        || destination_index >= destination[channel as int].len() {
        None
    } else {
        Some((source[source_channel as int][source_index as int],
            destination[channel as int][destination_index as int]))
    }
}

pub open spec fn part2_composition_gather_pixel(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    source_index: nat, destination_index: nat, expand_grayscale: bool,
) -> Option<([u16; 3], [u16; 3], u16, u16, bool)> {
    let channels = destination.len();
    if channels > 3 || destination_index >= destination_alpha.len()
        || (source_alpha.is_some() && source_index >= source_alpha.unwrap().0.len()) {
        None
    } else {
        let first = part2_composition_gather_channel(source, destination, source_index, destination_index, expand_grayscale, 0);
        let second = part2_composition_gather_channel(source, destination, source_index, destination_index, expand_grayscale, 1);
        let third = part2_composition_gather_channel(source, destination, source_index, destination_index, expand_grayscale, 2);
        if (channels > 0 && first.is_none()) || (channels > 1 && second.is_none())
            || (channels > 2 && third.is_none()) {
            None
        } else {
            Some(([
                if channels > 0 { first.unwrap().0 } else { 0 },
                if channels > 1 { second.unwrap().0 } else { 0 },
                if channels > 2 { third.unwrap().0 } else { 0 },
            ], [
                if channels > 0 { first.unwrap().1 } else { 0 },
                if channels > 1 { second.unwrap().1 } else { 0 },
                if channels > 2 { third.unwrap().1 } else { 0 },
            ], if source_alpha.is_some() { source_alpha.unwrap().0[source_index as int] } else { PART2_NORMALIZED_SAMPLE_MAX },
                destination_alpha[destination_index as int],
                source_alpha.is_some() && source_alpha.unwrap().1))
        }
    }
}

pub open spec fn part2_source_over_pixel_valid(source: [u16; 3], source_alpha: u16, premultiplied: bool, channels: usize) -> bool {
    channels <= 3 && (!premultiplied
        || ((channels == 0 || source[0] <= source_alpha)
            && (channels <= 1 || source[1] <= source_alpha)
            && (channels <= 2 || source[2] <= source_alpha)))
}

pub open spec fn part2_composition_planes(colors: Seq<Vec<u16>>) -> Seq<Seq<u16>> {
    Seq::new(colors.len(), |channel: int| colors[channel]@)
}

pub open spec fn part2_composition_scatter_count(colors: Seq<Seq<u16>>, index: nat) -> nat {
    if colors.len() > 3 || (colors.len() > 0 && index >= colors[0].len()) {
        0
    } else if colors.len() > 1 && index >= colors[1].len() {
        1
    } else if colors.len() > 2 && index >= colors[2].len() {
        2
    } else {
        colors.len()
    }
}

pub open spec fn part2_composition_color_prefix(
    colors: Seq<Seq<u16>>, index: nat, pixel: [u16; 3], count: nat,
) -> Seq<Seq<u16>> {
    Seq::new(colors.len(), |channel: int|
        if channel < count && channel < 3 && index < colors[channel].len() {
            colors[channel].update(index as int, pixel[channel])
        } else {
            colors[channel]
        })
}

pub open spec fn part2_composition_scatter_pixel(
    colors: Seq<Seq<u16>>, alpha: Seq<u16>, index: nat, pixel: [u16; 3], value: u16,
) -> (bool, Seq<Seq<u16>>, Seq<u16>) {
    let count = part2_composition_scatter_count(colors, index);
    let stored = colors.len() <= 3 && count == colors.len() && index < alpha.len();
    (stored, part2_composition_color_prefix(colors, index, pixel, count),
        if stored { alpha.update(index as int, value) } else { alpha })
}

pub open spec fn part2_source_over_pixel(
    source: [u16; 3], destination: [u16; 3], source_alpha: u16, destination_alpha: u16,
    premultiplied: bool, channels: usize,
) -> Option<([u16; 3], u16)> {
    if !part2_source_over_pixel_valid(source, source_alpha, premultiplied, channels) {
        None
    } else {
        Some(([
            if channels > 0 { part2_source_over_color_sample(source[0], destination[0], source_alpha, destination_alpha, premultiplied) as u16 } else { destination[0] },
            if channels > 1 { part2_source_over_color_sample(source[1], destination[1], source_alpha, destination_alpha, premultiplied) as u16 } else { destination[1] },
            if channels > 2 { part2_source_over_color_sample(source[2], destination[2], source_alpha, destination_alpha, premultiplied) as u16 } else { destination[2] },
        ], part2_source_over_alpha_sample(source_alpha, destination_alpha) as u16))
    }
}

pub open spec fn part2_composition_pixel_transition(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    source_index: nat, destination_index: nat, expand_grayscale: bool,
) -> (bool, Seq<Seq<u16>>, Seq<u16>) {
    let input = part2_composition_gather_pixel(
        source, source_alpha, destination, destination_alpha,
        source_index, destination_index, expand_grayscale,
    );
    if input.is_none() {
        (false, destination, destination_alpha)
    } else {
        let (s, d, sa, da, premultiplied) = input.unwrap();
        let pixel = part2_source_over_pixel(s, d, sa, da, premultiplied, destination.len() as usize);
        if pixel.is_none() {
            (false, destination, destination_alpha)
        } else {
            part2_composition_scatter_pixel(
                destination, destination_alpha,
                destination_index, pixel.unwrap().0, pixel.unwrap().1,
            )
        }
    }
}

pub struct Part2CompositionGeometry {
    pub source_width: nat,
    pub source_x: nat,
    pub source_y: nat,
    pub source_crop_width: nat,
    pub source_crop_height: nat,
    pub target_x: nat,
    pub target_y: nat,
    pub target_width: nat,
    pub target_height: nat,
    pub canvas_width: nat,
    pub copy_width: nat,
    pub copy_height: nat,
}

pub open spec fn part2_composition_geometry(
    source_width: u32, source_height: u32, canvas_width: u32, canvas_height: u32,
    target_x: u32, target_y: u32, target_width: u32, target_height: u32,
    source_x: u32, source_y: u32, source_crop_width: u32, source_crop_height: u32,
) -> Part2CompositionGeometry {
    let sx = if source_x < source_width { source_x } else { source_width };
    let sy = if source_y < source_height { source_y } else { source_height };
    let remaining_width = ((source_width as int) - sx as int) as nat;
    let remaining_height = ((source_height as int) - sy as int) as nat;
    Part2CompositionGeometry {
        source_width: source_width as nat,
        source_x: sx as nat,
        source_y: sy as nat,
        source_crop_width: if source_crop_width == 0 || source_crop_width as nat > remaining_width {
            remaining_width
        } else { source_crop_width as nat },
        source_crop_height: if source_crop_height == 0 || source_crop_height as nat > remaining_height {
            remaining_height
        } else { source_crop_height as nat },
        target_x: target_x as nat,
        target_y: target_y as nat,
        target_width: target_width as nat,
        target_height: target_height as nat,
        canvas_width: canvas_width as nat,
        copy_width: part2_composition_clip(target_x, target_width, canvas_width) as nat,
        copy_height: part2_composition_clip(target_y, target_height, canvas_height) as nat,
    }
}

#[verifier::opaque]
pub open spec fn part2_composition_canvas_prefix(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: Part2CompositionGeometry, expand_grayscale: bool, count: nat,
) -> (bool, Seq<Seq<u16>>, Seq<u16>)
    recommends geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
    decreases count,
{
    if count == 0 {
        (true, destination, destination_alpha)
    } else {
        let previous = part2_composition_canvas_prefix(
            source, source_alpha, destination, destination_alpha,
            geometry, expand_grayscale, (count - 1) as nat,
        );
        if !previous.0 {
            previous
        } else {
            let x = ((count - 1) as nat) % geometry.copy_width;
            let y = ((count - 1) as nat) / geometry.copy_width;
            let sx = geometry.source_x + x * geometry.source_crop_width / geometry.target_width;
            let sy = geometry.source_y + y * geometry.source_crop_height / geometry.target_height;
            let source_index = sy * geometry.source_width + sx;
            let destination_index = (geometry.target_y + y) * geometry.canvas_width + geometry.target_x + x;
            part2_composition_pixel_transition(
                source, source_alpha, previous.1, previous.2,
                source_index, destination_index, expand_grayscale,
            )
        }
    }
}

pub open spec fn part2_composition_layer_result(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: Part2CompositionGeometry, expand_grayscale: bool,
) -> (bool, Seq<Seq<u16>>, Seq<u16>) {
    if geometry.source_crop_width == 0 || geometry.source_crop_height == 0 {
        (true, destination, destination_alpha)
    } else if geometry.target_width == 0 || geometry.target_height == 0 {
        (false, destination, destination_alpha)
    } else if geometry.copy_width == 0 || geometry.copy_height == 0 {
        (true, destination, destination_alpha)
    } else {
        part2_composition_canvas_prefix(
            source, source_alpha, destination, destination_alpha,
            geometry, expand_grayscale, geometry.copy_width * geometry.copy_height,
        )
    }
}

pub open spec fn part2_composition_layer_work(geometry: Part2CompositionGeometry, channels: nat) -> nat {
    if geometry.source_crop_width == 0 || geometry.source_crop_height == 0
        || geometry.target_width == 0 || geometry.target_height == 0
        || geometry.copy_width == 0 || geometry.copy_height == 0 {
        0
    } else {
        geometry.copy_width * geometry.copy_height * (channels + 1)
    }
}

pub open spec fn part2_composition_layer_success(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: Part2CompositionGeometry, expand_grayscale: bool, initial_work: nat,
) -> (bool, Seq<Seq<u16>>, Seq<u16>, nat) {
    let result = part2_composition_layer_result(
        source, source_alpha, destination, destination_alpha, geometry, expand_grayscale,
    );
    (result.0, result.1, result.2, initial_work + part2_composition_layer_work(geometry, destination.len()))
}

pub type Part2CompositionBudgetedState = (Result<(), crate::DecodeError>, Seq<Seq<u16>>, Seq<u16>, nat);

pub open spec fn part2_composition_error(arithmetic: bool) -> crate::DecodeError {
    crate::DecodeError::MalformedInput {
        offset: 0,
        kind: if arithmetic { crate::MalformedKind::ArithmeticOverflow } else { crate::MalformedKind::InvalidBoxContents },
    }
}

pub open spec fn part2_composition_budgeted_step(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: Part2CompositionGeometry, expand_grayscale: bool,
    work: nat, work_limit: u64, x: nat, y: nat,
) -> Part2CompositionBudgetedState
    recommends geometry.target_width > 0 && geometry.target_height > 0,
{
    let sx = geometry.source_x + x * geometry.source_crop_width / geometry.target_width;
    let sy = geometry.source_y + y * geometry.source_crop_height / geometry.target_height;
    let si = sy * geometry.source_width + sx;
    let di = (geometry.target_y + y) * geometry.canvas_width + geometry.target_x + x;
    if si > usize::MAX as nat || di > usize::MAX as nat {
        (Err(part2_composition_error(true)), destination, destination_alpha, work)
    } else {
        let pixel = part2_composition_pixel_transition(
            source, source_alpha, destination, destination_alpha, si, di, expand_grayscale,
        );
        if !pixel.0 {
            (Err(part2_composition_error(false)), pixel.1, pixel.2, work)
        } else {
            let next = work + destination.len() + 1;
            if next > u64::MAX as nat {
                (Err(part2_composition_error(true)), pixel.1, pixel.2, work)
            } else if next > work_limit as nat {
                (Err(crate::DecodeError::LimitExceeded {
                    resource: crate::Resource::WorkUnits, limit: work_limit, actual: next as u64,
                }), pixel.1, pixel.2, next)
            } else {
                (Ok(()), pixel.1, pixel.2, next)
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_composition_budgeted_prefix(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: Part2CompositionGeometry, expand_grayscale: bool,
    initial_work: nat, work_limit: u64, count: nat,
) -> Part2CompositionBudgetedState
    recommends geometry.copy_width > 0 && geometry.target_width > 0 && geometry.target_height > 0,
    decreases count,
{
    if count == 0 {
        (Ok(()), destination, destination_alpha, initial_work)
    } else {
        let previous = part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha,
            geometry, expand_grayscale, initial_work, work_limit, (count - 1) as nat,
        );
        if previous.0.is_err() {
            previous
        } else {
            part2_composition_budgeted_step(
                source, source_alpha, previous.1, previous.2, geometry, expand_grayscale,
                previous.3, work_limit, ((count - 1) as nat) % geometry.copy_width,
                ((count - 1) as nat) / geometry.copy_width,
            )
        }
    }
}

pub open spec fn part2_composition_layer_transition(
    source: Seq<Seq<u16>>, source_alpha: Option<(Seq<u16>, bool)>,
    destination: Seq<Seq<u16>>, destination_alpha: Seq<u16>,
    geometry: Part2CompositionGeometry, expand_grayscale: bool, initial_work: nat, work_limit: u64,
) -> Part2CompositionBudgetedState {
    if geometry.source_crop_width == 0 || geometry.source_crop_height == 0 {
        (Ok(()), destination, destination_alpha, initial_work)
    } else if geometry.target_width == 0 || geometry.target_height == 0 {
        (Err(part2_composition_error(false)), destination, destination_alpha, initial_work)
    } else if geometry.copy_width == 0 || geometry.copy_height == 0 {
        (Ok(()), destination, destination_alpha, initial_work)
    } else {
        part2_composition_budgeted_prefix(
            source, source_alpha, destination, destination_alpha,
            geometry, expand_grayscale, initial_work, work_limit, geometry.copy_width * geometry.copy_height,
        )
    }
}

pub open spec fn part2_render_space(layers: Seq<Part2Placement>) -> crate::color::ConvertedColorSpace {
    if exists|i: int| 0 <= i < layers.len() && #[trigger] layers[i].0.2 == crate::color::ConvertedColorSpace::Srgb {
        crate::color::ConvertedColorSpace::Srgb
    } else {
        crate::color::ConvertedColorSpace::Grayscale
    }
}

pub open spec fn part2_render_layer_bytes(layer: Part2OwnedLayer) -> Result<nat, crate::DecodeError> {
    let channels = (layer.3.len() + 1) * 2;
    if layer.3.len() + 1 > u64::MAX as nat || channels > u64::MAX as nat {
        Err(part2_composition_error(true))
    } else {
        match part2_layer_area(layer.0, layer.1) {
            Err(error) => Err(error),
            Ok(area) => if area as nat * channels > u64::MAX as nat {
                Err(part2_composition_error(true))
            } else { Ok(area as nat * channels) },
        }
    }
}

pub open spec fn part2_charge_layer_bytes(layer: Part2OwnedLayer, previous: nat, byte_limit: u64)
    -> (Result<(), crate::DecodeError>, nat)
{
    match part2_render_layer_bytes(layer) {
        Err(error) => (Err(error), previous),
        Ok(bytes) => if previous + bytes > u64::MAX as nat {
            (Err(part2_composition_error(true)), previous)
        } else if previous + bytes > byte_limit as nat {
            (Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::DecodedBytes, limit: byte_limit, actual: (previous + bytes) as u64,
            }), previous + bytes)
        } else { (Ok(()), previous + bytes) },
    }
}

pub open spec fn part2_render_step(
    width: u32, height: u32, space: crate::color::ConvertedColorSpace,
    placement: Part2Placement, previous: Part2RenderState, byte_limit: u64, work_limit: u64,
) -> Part2RenderState {
    if previous.0.is_err() { previous } else {
        let charge = part2_charge_layer_bytes(placement.0, previous.4, byte_limit);
        match charge.0 {
            Err(error) => (Err(error), previous.1, previous.2, previous.3, charge.1),
            Ok(()) => {
                let layer = placement.0;
                let instruction = placement.1;
                let state = part2_composition_layer_transition(
                    layer.3, layer.4, previous.1, previous.2,
                    part2_composition_geometry(layer.0, layer.1, width, height,
                        instruction.1, instruction.2, instruction.3, instruction.4,
                        instruction.5, instruction.6, instruction.7, instruction.8),
                    matches!((space, layer.2), (crate::color::ConvertedColorSpace::Srgb, crate::color::ConvertedColorSpace::Grayscale)),
                    previous.3, work_limit,
                );
                (state.0, state.1, state.2, state.3, charge.1)
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_render_prefix(
    width: u32, height: u32, layers: Seq<Part2Placement>, initial: Part2RenderState,
    byte_limit: u64, work_limit: u64, count: nat,
) -> Part2RenderState
    recommends count <= layers.len(),
    decreases count,
{
    if count == 0 { initial } else {
        part2_render_step(width, height, part2_render_space(layers), layers[count as int - 1],
            part2_render_prefix(width, height, layers, initial, byte_limit, work_limit, (count - 1) as nat),
            byte_limit, work_limit)
    }
}

pub open spec fn part2_render_initial(width: u32, height: u32, layers: Seq<Part2Placement>) -> Part2RenderState {
    match part2_layer_area(width, height) {
        Err(error) => (Err(error), Seq::empty(), Seq::empty(), 0, 0),
        Ok(area) => {
            let colors = part2_layer_color_count(part2_render_space(layers));
            let bytes = area as nat * ((colors + 1) * 2);
            if bytes > u64::MAX as nat {
                (Err(part2_composition_error(true)), Seq::empty(), Seq::empty(), 0, 0)
            } else {
                (Ok(()), Seq::new(colors, |i: int| Seq::new(area as nat, |j: int| 0u16)),
                    Seq::new(area as nat, |j: int| 0u16), area as nat, bytes)
            }
        },
    }
}

pub open spec fn part2_render_layers(
    width: u32, height: u32, layers: Seq<Part2Placement>, byte_limit: u64, work_limit: u64,
) -> Part2ConvertedImageResult {
    if layers.len() == 0 { Err(part2_composition_error(false)) } else {
        let state = part2_render_prefix(width, height, layers,
            part2_render_initial(width, height, layers), byte_limit, work_limit, layers.len());
        match state.0 {
            Err(error) => Err(error),
            Ok(()) => part2_image_from_planes(width, height, part2_render_space(layers), state.1, state.2, false),
        }
    }
}

pub open spec fn part2_frame_index(requested: usize, frames: nat, loop_count: u8) -> Result<usize, crate::DecodeError> {
    if frames == 0 {
        Err(crate::DecodeError::FrameIndexOutOfRange { index: requested, frames: 0 })
    } else if loop_count == 0 {
        Ok((requested as nat % frames) as usize)
    } else if frames * loop_count as nat > usize::MAX as nat {
        Err(part2_composition_error(true))
    } else if requested as nat >= frames * loop_count as nat {
        Err(crate::DecodeError::FrameIndexOutOfRange { index: requested, frames: (frames * loop_count as nat) as usize })
    } else {
        Ok((requested as nat % frames) as usize)
    }
}

#[verifier::opaque]
pub open spec fn part2_frame_instruction_sequence(frames: Seq<Part2Frame>, selected: nat, count: nat) -> Seq<Part2Instruction>
    recommends selected < frames.len(), count <= selected + 1,
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let prior = part2_frame_instruction_sequence(frames, selected, (count - 1) as nat);
        if count - 1 == selected || frames[count as int - 1].3 {
            prior + frames[count as int - 1].4
        } else { prior }
    }
}

pub open spec fn part2_select_frame(frames: Seq<Part2Frame>, requested: usize, loop_count: u8)
    -> Result<Seq<Part2Instruction>, crate::DecodeError>
{
    match part2_frame_index(requested, frames.len(), loop_count) {
        Err(error) => Err(error),
        Ok(selected) => Ok(part2_frame_instruction_sequence(frames, selected as nat, selected as nat + 1)),
    }
}

#[verifier::opaque]
pub open spec fn part2_supply_search(supplied: Seq<Part2SuppliedLayer>, reference: usize, start: nat) -> Option<nat>
    recommends start <= supplied.len(),
    decreases supplied.len() - start,
{
    if start >= supplied.len() { None }
    else if supplied[start as int].0 == reference && supplied[start as int].1.is_some() { Some(start) }
    else { part2_supply_search(supplied, reference, start + 1) }
}

pub open spec fn part2_take_supplied_layer(supplied: Seq<Part2SuppliedLayer>, reference: usize)
    -> (Part2OwnedLayerResult, Seq<Part2SuppliedLayer>)
{
    match part2_supply_search(supplied, reference, 0) {
        None => (Err(part2_composition_error(false)), supplied),
        Some(index) => (supplied[index as int].1.unwrap(), supplied.update(index as int, (reference, None))),
    }
}

pub open spec fn part2_gather_layer_step(instruction: Part2Instruction, prior: Part2GatheredLayers) -> Part2GatheredLayers {
    if prior.0.is_err() { prior } else {
        let taken = part2_take_supplied_layer(prior.2, instruction.0);
        match taken.0 {
            Err(error) => (Err(error), prior.1, taken.1),
            Ok(layer) => (Ok(()), prior.1.push((layer, instruction)), taken.1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_gather_layers(
    instructions: Seq<Part2Instruction>, supplied: Seq<Part2SuppliedLayer>, count: nat,
) -> Part2GatheredLayers
    recommends count <= instructions.len(),
    decreases count,
{
    if count == 0 { (Ok(()), Seq::empty(), supplied) } else {
        part2_gather_layer_step(instructions[count as int - 1], part2_gather_layers(instructions, supplied, (count - 1) as nat))
    }
}

pub open spec fn part2_collect_supplied_layers(instructions: Seq<Part2Instruction>, supplied: Seq<Part2SuppliedLayer>)
    -> Result<Seq<Part2Placement>, crate::DecodeError>
{
    let result = part2_gather_layers(instructions, supplied, instructions.len());
    match result.0 { Err(error) => Err(error), Ok(()) => Ok(result.1) }
}

pub open spec fn part2_render_normalized_frame(
    width: u32, height: u32, frames: Seq<Part2Frame>, loop_count: u8, requested: usize,
    supplied: Seq<Part2SuppliedLayer>, byte_limit: u64, work_limit: u64,
) -> Part2ConvertedImageResult {
    match part2_select_frame(frames, requested, loop_count) {
        Err(error) => Err(error),
        Ok(instructions) => match part2_collect_supplied_layers(instructions, supplied) {
            Err(error) => Err(error),
            Ok(placements) => part2_render_layers(width, height, placements, byte_limit, work_limit),
        },
    }
}

pub open spec fn part2_timeline_limit(layer_count: usize, maximum_frames: u32) -> Result<usize, crate::DecodeError> {
    let layers = if layer_count == 0 { 1nat } else { layer_count as nat };
    let limit = layers * maximum_frames as nat;
    if limit > usize::MAX as nat { Err(part2_composition_error(true)) } else { Ok(limit as usize) }
}

pub open spec fn part2_timeline_work_error(limit: usize, index: nat) -> crate::DecodeError {
    if index + 1 > u64::MAX as nat { part2_composition_error(true) } else {
        crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits, limit: limit as u64, actual: (index + 1) as u64 }
    }
}

pub open spec fn part2_timeline_assign(layer: usize, instruction: Part2TimelineInstruction) -> Part2Instruction {
    let i = instruction.0;
    (layer, i.1, i.2, i.3, i.4, i.5, i.6, i.7, i.8, i.9, i.10)
}

pub open spec fn part2_timeline_frame(
    frames: Seq<Part2Frame>, time: u64, instruction: Part2Instruction, life: u32, maximum_frames: u32,
) -> Result<(Seq<Part2Frame>, u64), crate::DecodeError> {
    let fresh = frames.len() == 0 || frames.last().2 != 0;
    if fresh && frames.len() >= maximum_frames as nat {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Frames,
            limit: maximum_frames as u64, actual: (frames.len() + 1) as u64 })
    } else if time as nat + life as nat > u64::MAX as nat {
        Err(part2_composition_error(true))
    } else {
        let next = if fresh {
            frames.push((frames.len() as usize, time, life, instruction.9, seq![instruction]))
        } else {
            let last = frames.last();
            frames.update(frames.len() as int - 1, (last.0, last.1, life, instruction.9, last.4.push(instruction)))
        };
        Ok((next, (time as nat + life as nat) as u64))
    }
}

pub open spec fn part2_timeline_step(
    state: Part2TimelineState, instruction: Part2TimelineInstruction,
    layer_count: usize, maximum_frames: u32, maximum_instructions: usize,
) -> Part2TimelineExecution {
    let (frames, old_assignments, next_layer, index, time) = state;
    if index >= maximum_instructions {
        Err(part2_timeline_work_error(maximum_instructions, index as nat))
    } else {
        let assignments = if index as nat >= old_assignments.len() { old_assignments.push(None) } else { old_assignments };
        let assigned = if (index as nat) < assignments.len() { assignments[index as int] } else { None };
        if assigned.is_none() && next_layer >= layer_count {
            Ok((false, (frames, assignments, next_layer, index, time)))
        } else {
            let layer = if assigned.is_some() { assigned.unwrap() } else { next_layer };
            let next = if assigned.is_some() { next_layer as nat } else { next_layer as nat + 1 };
            if next > usize::MAX as nat { Err(part2_composition_error(true)) } else {
                match part2_timeline_frame(frames, time, part2_timeline_assign(layer, instruction), instruction.1, maximum_frames) {
                    Err(error) => Err(error),
                    Ok((new_frames, new_time)) => {
                        let target = index as nat + instruction.0.10 as nat;
                        if instruction.0.10 != 0 && target > usize::MAX as nat {
                            Err(part2_composition_error(true))
                        } else if instruction.0.10 != 0 && target >= maximum_instructions as nat {
                            Err(part2_timeline_work_error(maximum_instructions, target))
                        } else if instruction.0.10 != 0 && target < assignments.len()
                            && assignments[target as int].is_some() && assignments[target as int].unwrap() != layer {
                            Err(part2_composition_error(false))
                        } else if index as nat + 1 > usize::MAX as nat {
                            Err(part2_composition_error(true))
                        } else {
                            let extended = if target < assignments.len() { assignments } else {
                                assignments + Seq::new((target + 1 - assignments.len()) as nat, |i: int| None)
                            };
                            let new_assignments = if instruction.0.10 == 0 { assignments }
                                else { extended.update(target as int, Some(layer)) };
                            Ok((true, (new_frames, new_assignments, next as usize, (index + 1) as usize, new_time)))
                        }
                    },
                }
            }
        }
    }
}

pub open spec fn part2_timeline_finished(execution: Part2TimelineExecution) -> bool {
    execution.is_err() || !execution.ok().unwrap().0
}

#[verifier::opaque]
pub open spec fn part2_timeline_instructions(
    instructions: Seq<Part2TimelineInstruction>, initial: Part2TimelineExecution, count: nat,
    layers: usize, maximum_frames: u32, maximum_instructions: usize,
) -> Part2TimelineExecution
    recommends count <= instructions.len(),
    decreases count,
{
    if count == 0 { initial } else {
        let prior = part2_timeline_instructions(instructions, initial, (count - 1) as nat, layers, maximum_frames, maximum_instructions);
        if part2_timeline_finished(prior) { prior } else {
            part2_timeline_step(prior.ok().unwrap().1, instructions[count as int - 1], layers, maximum_frames, maximum_instructions)
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_timeline_repetitions(
    instructions: Seq<Part2TimelineInstruction>, initial: Part2TimelineExecution, count: nat,
    layers: usize, maximum_frames: u32, maximum_instructions: usize,
) -> Part2TimelineExecution
    decreases count,
{
    if count == 0 { initial } else {
        part2_timeline_instructions(instructions,
            part2_timeline_repetitions(instructions, initial, (count - 1) as nat, layers, maximum_frames, maximum_instructions),
            instructions.len(), layers, maximum_frames, maximum_instructions)
    }
}

#[verifier::opaque]
pub open spec fn part2_timeline_sets(
    sets: Seq<Part2TimelineSet>, initial: Part2TimelineExecution, count: nat,
    layers: usize, maximum_frames: u32, maximum_instructions: usize,
) -> Part2TimelineExecution
    recommends count <= sets.len(),
    decreases count,
{
    if count == 0 { initial } else {
        let set = sets[count as int - 1];
        part2_timeline_repetitions(set.1,
            part2_timeline_sets(sets, initial, (count - 1) as nat, layers, maximum_frames, maximum_instructions),
            set.0 as nat + 1, layers, maximum_frames, maximum_instructions)
    }
}

pub open spec fn part2_timeline_frames(execution: Part2TimelineExecution) -> Result<Seq<Part2Frame>, crate::DecodeError> {
    match execution { Err(error) => Err(error), Ok((_, state)) => Ok(state.0) }
}

pub open spec fn part2_build_timeline(sets: Seq<Part2TimelineSet>, layers: usize, maximum_frames: u32)
    -> Result<Seq<Part2Frame>, crate::DecodeError>
{
    match part2_timeline_limit(layers, maximum_frames) {
        Err(error) => Err(error),
        Ok(limit) => part2_timeline_frames(part2_timeline_sets(sets,
            Ok((true, (Seq::empty(), Seq::empty(), 0, 0, 0))), sets.len(), layers, maximum_frames, limit)),
    }
}

pub open spec fn part2_chroma_key_alpha(matches: bool) -> u16 {
    if matches { 0 } else { u16::MAX }
}

pub open spec fn part2_metadata_count(parent: u32, child: u32) -> u32
    recommends parent <= u32::MAX - child,
{
    ((parent as int) + (child as int)) as u32
}

// Part 1 functional semantics used by executable production contracts.
pub open spec fn part1_ceil_div(value: nat, divisor: nat) -> nat
    recommends divisor > 0,
{
    if value == 0 {
        0
    } else {
        ((((value - 1) as int) / (divisor as int)) + 1int) as nat
    }
}

pub open spec fn part1_clip_start(nominal: nat, image_start: nat) -> nat {
    if nominal < image_start { image_start } else { nominal }
}

pub open spec fn part1_clip_end(nominal_end: nat, image_end: nat) -> nat {
    if nominal_end < image_end { nominal_end } else { image_end }
}

pub open spec fn part1_packet_data_bits(previous_was_ff: bool) -> nat {
    if previous_was_ff { 7 } else { 8 }
}

pub open spec fn part1_packet_bit(byte: u8, remaining: u8) -> bool
    recommends remaining < 8,
{
    ((byte >> remaining) & 1) != 0
}

pub struct Tier1RawCoefficient {
    pub limbs: Seq<u64>,
    pub legacy_bitplane: Option<u16>,
    pub negative: bool,
    pub significant: bool,
    pub refined: bool,
}

pub struct Tier1RawPlane {
    pub width: u16,
    pub height: u16,
    pub coefficients: Seq<Tier1RawCoefficient>,
}

pub open spec fn tier1_raw_plane_index(plane: Tier1RawPlane, x: u16, y: u16) -> Result<usize, crate::DecodeError> {
    let index = y as nat * plane.width as nat + x as nat;
    if x >= plane.width || y >= plane.height {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else if index > usize::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else if index >= plane.coefficients.len() {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else { Ok(index as usize) }
}

pub open spec fn tier1_raw_plane_coefficient(plane: Tier1RawPlane, x: u16, y: u16)
    -> Result<Tier1RawCoefficient, crate::DecodeError>
{
    match tier1_raw_plane_index(plane, x, y) {
        Err(error) => Err(error),
        Ok(index) => Ok(plane.coefficients[index as int]),
    }
}

pub open spec fn tier1_value_limbs(value: nat) -> Seq<u64> {
    Seq::new(6, |i: int| ((value / pow2((64 * i) as nat)) % 18446744073709551616) as u64)
}

pub open spec fn tier1_empty_coefficient() -> Tier1RawCoefficient {
    Tier1RawCoefficient {
        limbs: Seq::new(6, |i: int| 0u64), legacy_bitplane: None,
        negative: false, significant: false, refined: false,
    }
}

pub open spec fn tier1_empty_plane(width: u16, height: u16) -> Result<Tier1RawPlane, crate::DecodeError> {
    let samples = width as nat * height as nat;
    if width == 0 || height == 0 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else if samples > usize::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else if samples > 4096 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else { Ok(Tier1RawPlane {
        width, height, coefficients: Seq::new(samples, |i: int| tier1_empty_coefficient()),
    }) }
}

pub open spec fn tier1_new_coefficient(limbs: Seq<u64>, negative: bool, significant: bool, refined: bool)
    -> Tier1RawCoefficient {
    Tier1RawCoefficient { limbs, legacy_bitplane: None, negative, significant, refined }
}

pub open spec fn tier1_coefficient_new_outcome(
    limbs: Seq<u64>, negative: bool, significant: bool, refined: bool,
) -> Result<Tier1RawCoefficient, crate::DecodeError> {
    Ok(tier1_new_coefficient(limbs, negative, significant, refined))
}

pub open spec fn tier1_set_magnitude(coefficient: Tier1RawCoefficient, limbs: Seq<u64>)
    -> (Result<(), crate::DecodeError>, Tier1RawCoefficient)
{
    (Ok(()), Tier1RawCoefficient { limbs, ..coefficient })
}

pub open spec fn tier1_raw_plane_width(plane: Tier1RawPlane) -> u16 { plane.width }
pub open spec fn tier1_raw_plane_height(plane: Tier1RawPlane) -> u16 { plane.height }
pub open spec fn tier1_raw_plane_coefficients(plane: Tier1RawPlane) -> Seq<Tier1RawCoefficient> {
    plane.coefficients
}
pub open spec fn tier1_coefficient_limbs(coefficient: Tier1RawCoefficient) -> Seq<u64> {
    coefficient.limbs
}

pub open spec fn tier1_mark_coefficient(
    plane: Tier1RawPlane, x: u16, y: u16, limbs: Seq<u64>, value: nat, negative: bool,
) -> (Result<(), crate::DecodeError>, Tier1RawPlane) {
    if value == 0 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), plane) }
    else {
        match tier1_raw_plane_index(plane, x, y) {
            Err(error) => (Err(error), plane),
            Ok(index) => if plane.coefficients[index as int].significant {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), plane)
            } else {
                (Ok(()), Tier1RawPlane { coefficients: plane.coefficients.update(index as int,
                    tier1_new_coefficient(limbs, negative, true, false)), ..plane })
            },
        }
    }
}

pub open spec fn tier1_statistics_zero() -> crate::tier1::Tier1PassStatistics {
    crate::tier1::Tier1PassStatistics {
        coefficients_scanned: 0, coding_symbols: 0, newly_significant: 0, refined_coefficients: 0, run_mode_columns: 0,
    }
}

pub open spec fn tier1_statistics_increment(
    state: crate::tier1::Tier1PassStatistics, field: u8, count: u32,
) -> (Result<(), crate::DecodeError>, crate::tier1::Tier1PassStatistics) {
    let value = if field == 0 { state.coefficients_scanned } else if field == 1 { state.coding_symbols }
        else if field == 2 { state.newly_significant } else if field == 3 { state.refined_coefficients }
        else { state.run_mode_columns };
    if value + count > u32::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else {
        let value = (value + count) as u32;
        (Ok(()), if field == 0 { crate::tier1::Tier1PassStatistics { coefficients_scanned: value, ..state } }
            else if field == 1 { crate::tier1::Tier1PassStatistics { coding_symbols: value, ..state } }
            else if field == 2 { crate::tier1::Tier1PassStatistics { newly_significant: value, ..state } }
            else if field == 3 { crate::tier1::Tier1PassStatistics { refined_coefficients: value, ..state } }
            else { crate::tier1::Tier1PassStatistics { run_mode_columns: value, ..state } })
    }
}

pub open spec fn tier1_statistics_merge_step(
    prior: (Result<(), crate::DecodeError>, crate::tier1::Tier1PassStatistics), field: u8, count: u32,
) -> (Result<(), crate::DecodeError>, crate::tier1::Tier1PassStatistics) {
    match prior.0 { Err(_) => prior, Ok(()) => tier1_statistics_increment(prior.1, field, count) }
}

pub open spec fn tier1_statistics_merge(state: crate::tier1::Tier1PassStatistics, other: crate::tier1::Tier1PassStatistics)
    -> (Result<(), crate::DecodeError>, crate::tier1::Tier1PassStatistics) {
    let result = tier1_statistics_increment(state, 0, other.coefficients_scanned);
    let result = tier1_statistics_merge_step(result, 1, other.coding_symbols);
    let result = tier1_statistics_merge_step(result, 2, other.newly_significant);
    let result = tier1_statistics_merge_step(result, 3, other.refined_coefficients);
    tier1_statistics_merge_step(result, 4, other.run_mode_columns)
}

pub open spec fn ht_copy_refinement_bytes(input: Seq<u8>) -> Result<Seq<u8>, crate::DecodeError> { Ok(input) }

pub open spec fn tier1_raw_signed_coefficient(coefficient: Tier1RawCoefficient)
    -> Result<(Seq<u64>, nat, bool), crate::DecodeError>
    recommends coefficient.limbs.len() == 6,
{
    if !coefficient.significant {
        Ok((Seq::new(6, |i: int| 0u64), 0, false))
    } else {
        let base = part1_magnitude_value(coefficient.limbs);
        let delta = match coefficient.legacy_bitplane {
            None => 0nat,
            Some(bitplane) => if bitplane <= 64 { part1_tier1_midpoint_delta(bitplane) as nat }
                else { pow2((bitplane - 1) as nat) },
        };
        if (match coefficient.legacy_bitplane { Some(bitplane) => bitplane > 384, None => false })
            || base + delta >= part1_magnitude_capacity() {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else { Ok((tier1_value_limbs(base + delta), base + delta, coefficient.negative)) }
    }
}

pub type HtNumericMagnitudeResult = (Result<(nat, bool, u8), crate::DecodeError>, HtMagSgnState);

pub open spec fn ht_complete_kappa(base: u8, significance: u8, north_west: u8, north_east: u8, maximum: u8)
    -> Result<u8, crate::DecodeError> {
    let exponent = if north_west > north_east { north_west } else { north_east };
    let gamma = significance & significance.wrapping_sub(1) != 0;
    if base == 0 || significance & 0xf0u8 != 0 || maximum == 0 || maximum > 75 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else if base as nat + exponent as nat > 255 {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else {
        let completed = ht_kappa_completion(base as nat, gamma, exponent as nat);
        if completed > maximum { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
        else { Ok(completed as u8) }
    }
}

pub struct HtPlaneState {
    pub output: Tier1RawPlane,
    pub reader: HtMagSgnState,
    pub previous: Seq<u8>,
    pub current: Seq<u8>,
    pub statistics: crate::tier1::Tier1PassStatistics,
}

pub struct Tier1LegacyFrame {
    pub plane: Tier1RawPlane,
    pub next_pass: u32,
    pub bitplane: u16,
    pub bitplane_state: Option<Part1LegacyBitplane>,
    pub mq_context_state: Option<Seq<Part1MqContext>>,
    pub reset_contexts_before_mq: bool,
    pub decoded_segments: u32,
    pub decoded_bytes: u64,
    pub input: Seq<u8>,
    pub passes: u32,
}

pub open spec fn ht_neighbor_zero() -> crate::tier1::NeighborSummary {
    crate::tier1::NeighborSummary {
        horizontal_significant: 0, vertical_significant: 0, diagonal_significant: 0,
        horizontal_sign_balance: 0, vertical_sign_balance: 0,
    }
}

pub open spec fn ht_significant_neighbor_count(summary: crate::tier1::NeighborSummary) -> nat {
    summary.horizontal_significant as nat + summary.vertical_significant as nat + summary.diagonal_significant as nat
}

pub open spec fn ht_significance_magnitude(decoded: u16) -> Result<(Seq<u64>, nat), crate::DecodeError> {
    if decoded < 2 || decoded > 292 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else {
        let scaled = 3nat * pow2((decoded - 2) as nat);
        if scaled >= part1_magnitude_capacity() { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
        else { Ok((part1_magnitude_shift(part1_magnitude_left(
            Seq::new(6, |i: int| if i == 0 { 3u64 } else { 0u64 }), (decoded - 2) as u16), 1), (scaled / 2) as nat)) }
    }
}

pub open spec fn ht_refinement_delta(decoded: u16) -> Result<(Seq<u64>, nat), crate::DecodeError> {
    if decoded < 2 || decoded > 292 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else if decoded == 2 { Ok((Seq::new(6, |i: int| if i == 0 { 1u64 } else { 0u64 }), 1)) }
    else { Ok((part1_magnitude_bit((decoded - 3) as u16), pow2((decoded - 3) as nat))) }
}

pub open spec fn ht_cleanup_significance(coefficients: Seq<Tier1RawCoefficient>) -> Seq<bool> {
    Seq::new(coefficients.len(), |i: int| coefficients[i].significant)
}

pub open spec fn ht_apply_refinement(
    plane: Tier1RawPlane, x: u16, y: u16, delta: nat, bit: bool,
) -> (Result<(), crate::DecodeError>, Tier1RawPlane)
    recommends forall |i: int| 0 <= i < plane.coefficients.len() ==> plane.coefficients[i].limbs.len() == 6,
{
    if delta == 0 && !bit { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), plane) }
    else {
        match tier1_raw_plane_index(plane, x, y) {
            Err(error) => (Err(error), plane),
            Ok(index) => {
                let coefficient = plane.coefficients[index as int];
                let value = part1_magnitude_value(coefficient.limbs);
                let changed = if bit { value + delta } else { (value - delta) as nat };
                if !coefficient.significant || (!bit && value < delta) || changed == 0 {
                    (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), plane)
                } else if changed >= part1_magnitude_capacity() {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), plane)
                } else {
                    (Ok(()), Tier1RawPlane { coefficients: plane.coefficients.update(index as int,
                        Tier1RawCoefficient { limbs: tier1_value_limbs(changed), refined: true, ..coefficient }), ..plane })
                }
            },
        }
    }
}

pub struct HtRefinementCoreState {
    pub output: Tier1RawPlane,
    pub readers: HtRefinementReadersState,
    pub cleanup_significant: Seq<bool>,
    pub statistics: crate::tier1::Tier1PassStatistics,
}

pub type HtRefinementCoreResult = (Result<(), crate::DecodeError>, HtRefinementCoreState);

pub open spec fn ht_refinement_count(state: HtRefinementCoreState, field: u8) -> HtRefinementCoreResult {
    let count = tier1_statistics_increment(state.statistics, field, 1);
    (count.0, HtRefinementCoreState { statistics: count.1, ..state })
}

pub open spec fn ht_magref_sample(state: HtRefinementCoreState, x: u16, y: u16, delta: nat, bitplanes: u16)
    -> HtRefinementCoreResult
    recommends forall |i: int| 0 <= i < state.output.coefficients.len() ==> state.output.coefficients[i].limbs.len() == 6,
{
    let scanned = ht_refinement_count(state, 0);
    match scanned.0 {
        Err(_) => scanned,
        Ok(()) => match tier1_raw_plane_index(scanned.1.output, x, y) {
            Err(error) => (Err(error), scanned.1),
            Ok(index) => if index >= scanned.1.cleanup_significant.len() {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), scanned.1)
            } else if !scanned.1.cleanup_significant[index as int] { scanned }
            else {
                let read = ht_refinement_read_reverse(scanned.1.readers);
                let state = HtRefinementCoreState { readers: read.1, ..scanned.1 };
                match read.0 {
                    Err(error) => (Err(error), state),
                    Ok(bit) => {
                        let store = ht_apply_refinement(state.output, x, y,
                            if bitplanes == 2 && bit { 0nat } else { delta }, bit);
                        let state = HtRefinementCoreState { output: store.1, ..state };
                        match store.0 {
                            Err(error) => (Err(error), state),
                            Ok(()) => {
                                let counted = ht_refinement_count(state, 1);
                                match counted.0 { Err(_) => counted, Ok(()) => ht_refinement_count(counted.1, 3) }
                            },
                        }
                    },
                }
            },
        },
    }
}

pub type HtDiscoveryResult = (Result<(), crate::DecodeError>, HtRefinementCoreState, Tier1RawPlane, Seq<(u16, u16)>);

pub open spec fn ht_discover_sample_fields(
    state: HtRefinementCoreState, discovery: Tier1RawPlane, pending: Seq<(u16, u16)>,
    x: u16, y: u16, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtDiscoveryResult {
    let scanned = ht_refinement_count(state, 0);
    match scanned.0 {
        Err(error) => (Err(error), scanned.1, discovery, pending),
        Ok(()) => match tier1_raw_plane_coefficient(discovery, x, y) {
            Err(error) => (Err(error), scanned.1, discovery, pending),
            Ok(coefficient) => if coefficient.significant { (Ok(()), scanned.1, discovery, pending) }
            else {
                match ht_neighbors(discovery, x, y, causal) {
                    Err(error) => (Err(error), scanned.1, discovery, pending),
                    Ok(summary) => if ht_significant_neighbor_count(summary) == 0 {
                        (Ok(()), scanned.1, discovery, pending)
                    } else {
                        let read = ht_refinement_read_forward(scanned.1.readers);
                        let state = HtRefinementCoreState { readers: read.1, ..scanned.1 };
                        match read.0 {
                            Err(error) => (Err(error), state, discovery, pending),
                            Ok(bit) => {
                                let counted = ht_refinement_count(state, 1);
                                match counted.0 {
                                    Err(error) => (Err(error), counted.1, discovery, pending),
                                    Ok(()) => if !bit { (Ok(()), counted.1, discovery, pending) } else {
                                        let store = tier1_mark_coefficient(discovery, x, y, magnitude.0, magnitude.1, false);
                                        (store.0, counted.1, store.1, if store.0.is_err() { pending } else { pending.push((x, y)) })
                                    },
                                }
                            },
                        }
                    },
                }
            },
        },
    }
}

pub open spec fn ht_sign_sample(
    state: HtRefinementCoreState, pending: Seq<(u16, u16)>, index: nat, magnitude: (Seq<u64>, nat),
) -> HtRefinementCoreResult {
    if index >= pending.len() { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else {
        let read = ht_refinement_read_forward(state.readers);
        let state = HtRefinementCoreState { readers: read.1, ..state };
        match read.0 {
            Err(error) => (Err(error), state),
            Ok(negative) => {
                let store = tier1_mark_coefficient(state.output, pending[index as int].0, pending[index as int].1,
                    magnitude.0, magnitude.1, negative);
                let state = HtRefinementCoreState { output: store.1, ..state };
                match store.0 {
                    Err(error) => (Err(error), state),
                    Ok(()) => {
                        let counted = ht_refinement_count(state, 1);
                        match counted.0 { Err(_) => counted, Ok(()) => ht_refinement_count(counted.1, 2) }
                    },
                }
            },
        }
    }
}

pub struct HtSignificancePatchState {
    pub core: HtRefinementCoreState,
    pub discovery: Tier1RawPlane,
    pub pending: Seq<(u16, u16)>,
}

pub type HtSignificancePatchResult = (Result<(), crate::DecodeError>, HtSignificancePatchState);

pub open spec fn ht_discover_sample(
    state: HtSignificancePatchState, x: u16, y: u16, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtSignificancePatchResult {
    let result = ht_discover_sample_fields(state.core, state.discovery, state.pending, x, y, magnitude, causal);
    (result.0, HtSignificancePatchState { core: result.1, discovery: result.2, pending: result.3 })
}

pub open spec fn ht_patch_sign_sample(
    state: HtSignificancePatchState, index: nat, magnitude: (Seq<u64>, nat),
) -> HtSignificancePatchResult {
    let result = ht_sign_sample(state.core, state.pending, index, magnitude);
    (result.0, HtSignificancePatchState { core: result.1, ..state })
}

#[verifier::opaque]
pub open spec fn ht_magref_rows(
    state: HtRefinementCoreState, x: u16, stripe_y: u16, rows: nat, row: nat, delta: nat, bitplanes: u16,
) -> HtRefinementCoreResult
    recommends row <= rows <= 4,
    decreases rows - row,
{
    if row >= rows { (Ok(()), state) }
    else if stripe_y as nat + row > u16::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else {
        let step = ht_magref_sample(state, x, (stripe_y as nat + row) as u16, delta, bitplanes);
        match step.0 { Err(_) => step, Ok(()) => ht_magref_rows(step.1, x, stripe_y, rows, row + 1, delta, bitplanes) }
    }
}

#[verifier::opaque]
pub open spec fn ht_magref_columns(
    state: HtRefinementCoreState, width: u16, stripe_y: u16, rows: nat, x: nat, delta: nat, bitplanes: u16,
) -> HtRefinementCoreResult
    recommends x <= width, rows <= 4,
    decreases width as nat - x,
{
    if x >= width { (Ok(()), state) } else {
        let step = ht_magref_rows(state, x as u16, stripe_y, rows, 0, delta, bitplanes);
        match step.0 { Err(_) => step, Ok(()) => ht_magref_columns(step.1, width, stripe_y, rows, x + 1, delta, bitplanes) }
    }
}

#[verifier::opaque]
pub open spec fn ht_magref_stripes(
    state: HtRefinementCoreState, width: u16, height: u16, stripe_y: nat, delta: nat, bitplanes: u16,
) -> HtRefinementCoreResult
    recommends width <= 4096, height <= 4096, stripe_y <= height as nat + 3,
    decreases (height as nat + 3 - stripe_y) / 4,
{
    if stripe_y >= height { (Ok(()), state) } else {
        let rows = ht_stripe_rows(height as nat, stripe_y);
        let step = ht_magref_columns(state, width, stripe_y as u16, rows, 0, delta, bitplanes);
        match step.0 { Err(_) => step, Ok(()) => ht_magref_stripes(step.1, width, height, stripe_y + 4, delta, bitplanes) }
    }
}

#[verifier::opaque]
pub open spec fn ht_discovery_rows(
    state: HtSignificancePatchState, x: u16, stripe_y: u16, rows: nat, row: nat, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtSignificancePatchResult
    recommends row <= rows <= 4,
    decreases rows - row,
{
    if row >= rows { (Ok(()), state) }
    else if stripe_y as nat + row > u16::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else {
        let step = ht_discover_sample(state, x, (stripe_y as nat + row) as u16, magnitude, causal);
        match step.0 { Err(_) => step, Ok(()) => ht_discovery_rows(step.1, x, stripe_y, rows, row + 1, magnitude, causal) }
    }
}

#[verifier::opaque]
pub open spec fn ht_discovery_columns(
    state: HtSignificancePatchState, end: u16, stripe_y: u16, rows: nat, x: nat, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtSignificancePatchResult
    recommends x <= end, rows <= 4,
    decreases end as nat - x,
{
    if x >= end { (Ok(()), state) } else {
        let step = ht_discovery_rows(state, x as u16, stripe_y, rows, 0, magnitude, causal);
        match step.0 { Err(_) => step, Ok(()) => ht_discovery_columns(step.1, end, stripe_y, rows, x + 1, magnitude, causal) }
    }
}

#[verifier::opaque]
pub open spec fn ht_pending_signs(state: HtSignificancePatchState, index: nat, magnitude: (Seq<u64>, nat))
    -> HtSignificancePatchResult
    recommends index <= state.pending.len(),
    decreases state.pending.len() - index,
{
    if index >= state.pending.len() { (Ok(()), state) } else {
        let step = ht_patch_sign_sample(state, index, magnitude);
        match step.0 { Err(_) => step, Ok(()) => ht_pending_signs(step.1, index + 1, magnitude) }
    }
}

pub struct HtSigpropPlaneState {
    pub core: HtRefinementCoreState,
    pub discovery: Tier1RawPlane,
}

pub type HtSigpropPlaneResult = (Result<(), crate::DecodeError>, HtSigpropPlaneState);

pub open spec fn ht_sigprop_patch(
    state: HtSigpropPlaneState, start: u16, end: u16, stripe_y: u16, rows: nat, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtSigpropPlaneResult
    recommends start <= end, rows <= 4,
{
    let patch = HtSignificancePatchState { core: state.core, discovery: state.discovery, pending: Seq::empty() };
    let discovered = ht_discovery_columns(patch, end, stripe_y, rows, start as nat, magnitude, causal);
    let signed = match discovered.0 { Err(_) => discovered, Ok(()) => ht_pending_signs(discovered.1, 0, magnitude) };
    (signed.0, HtSigpropPlaneState { core: signed.1.core, discovery: signed.1.discovery })
}

#[verifier::opaque]
pub open spec fn ht_sigprop_patches(
    state: HtSigpropPlaneState, width: u16, stripe_y: u16, rows: nat, patch_x: nat, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtSigpropPlaneResult
    recommends width <= 4096, patch_x <= width as nat + 3, rows <= 4,
    decreases (width as nat + 3 - patch_x) / 4,
{
    if patch_x >= width { (Ok(()), state) } else {
        let end = ht_patch_end(patch_x, width as nat) as u16;
        let step = ht_sigprop_patch(state, patch_x as u16, end, stripe_y, rows, magnitude, causal);
        match step.0 { Err(_) => step, Ok(()) => ht_sigprop_patches(step.1, width, stripe_y, rows, patch_x + 4, magnitude, causal) }
    }
}

#[verifier::opaque]
pub open spec fn ht_sigprop_stripes(
    state: HtSigpropPlaneState, width: u16, height: u16, stripe_y: nat, magnitude: (Seq<u64>, nat), causal: bool,
) -> HtSigpropPlaneResult
    recommends width <= 4096, height <= 4096, stripe_y <= height as nat + 3,
    decreases (height as nat + 3 - stripe_y) / 4,
{
    if stripe_y >= height { (Ok(()), state) } else {
        let step = ht_sigprop_patches(state, width, stripe_y as u16, ht_stripe_rows(height as nat, stripe_y), 0, magnitude, causal);
        match step.0 { Err(_) => step, Ok(()) => ht_sigprop_stripes(step.1, width, height, stripe_y + 4, magnitude, causal) }
    }
}

pub open spec fn ht_refinement_plane_finish(result: HtSigpropPlaneResult, encoded: Seq<u8>)
    -> Result<(Tier1RawPlane, crate::tier1::Tier1PassStatistics), crate::DecodeError> {
    match result.0 {
        Err(error) => Err(error),
        Ok(()) => match ht_refinement_finish(result.1.core.readers, encoded) {
            Err(error) => Err(error), Ok(()) => Ok((result.1.core.output, result.1.core.statistics)),
        },
    }
}

pub open spec fn ht_refinement_significance(
    state: HtRefinementCoreState, encoded: Seq<u8>, bitplanes: u16, causal: bool,
) -> Result<(Tier1RawPlane, crate::tier1::Tier1PassStatistics), crate::DecodeError> {
    match ht_significance_magnitude(bitplanes) {
        Err(error) => Err(error),
        Ok(magnitude) => match tier1_duplicate_plane(state.output) {
            Err(error) => Err(error),
            Ok(discovery) => ht_refinement_plane_finish(ht_sigprop_stripes(
                HtSigpropPlaneState { core: state, discovery },
                state.output.width, state.output.height, 0, magnitude, causal), encoded),
        },
    }
}

pub open spec fn ht_refinement_plane(
    cleanup: Tier1RawPlane, segment: HtRefinementSegmentState, passes: u8, bitplanes: u16, causal: bool, maximum_work: u64,
) -> Result<(Tier1RawPlane, crate::tier1::Tier1PassStatistics), crate::DecodeError>
    recommends segment.encoded.len() <= usize::MAX,
{
    if passes == 0 || passes > 2 || bitplanes < 2 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else {
        match tier1_duplicate_plane(cleanup) {
            Err(error) => Err(error),
            Ok(output) => match ht_refinement_readers_initial(segment.significance_propagation.bytes,
                segment.magnitude_refinement.bytes, segment.encoded.len() as usize, passes == 2, maximum_work) {
                Err(error) => Err(error),
                Ok(readers) => {
                    let state = HtRefinementCoreState { output, readers,
                        cleanup_significant: ht_cleanup_significance(cleanup.coefficients), statistics: tier1_statistics_zero() };
                    if passes == 2 {
                        match ht_refinement_delta(bitplanes) {
                            Err(error) => Err(error),
                            Ok(delta) => {
                                let refined = ht_magref_stripes(state, output.width, output.height, 0, delta.1, bitplanes);
                                match refined.0 { Err(error) => Err(error),
                                    Ok(()) => ht_refinement_significance(refined.1, segment.encoded, bitplanes, causal) }
                            },
                        }
                    } else { ht_refinement_significance(state, segment.encoded, bitplanes, causal) }
                },
            },
        }
    }
}

pub open spec fn ht_neighbor_update(
    state: crate::tier1::NeighborSummary, kind: u8, negative: bool,
) -> (Result<(), crate::DecodeError>, crate::tier1::NeighborSummary) {
    let sign = if negative { -1int } else { 1int };
    if kind == 0 {
        if state.horizontal_significant == u8::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
        else {
            let state = crate::tier1::NeighborSummary { horizontal_significant: (state.horizontal_significant + 1) as u8, ..state };
            let balance = state.horizontal_sign_balance as int + sign;
            if balance < i8::MIN || balance > i8::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
            else { (Ok(()), crate::tier1::NeighborSummary { horizontal_sign_balance: balance as i8, ..state }) }
        }
    } else if kind == 1 {
        if state.vertical_significant == u8::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
        else {
            let state = crate::tier1::NeighborSummary { vertical_significant: (state.vertical_significant + 1) as u8, ..state };
            let balance = state.vertical_sign_balance as int + sign;
            if balance < i8::MIN || balance > i8::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
            else { (Ok(()), crate::tier1::NeighborSummary { vertical_sign_balance: balance as i8, ..state }) }
        }
    } else if state.diagonal_significant == u8::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else { (Ok(()), crate::tier1::NeighborSummary { diagonal_significant: (state.diagonal_significant + 1) as u8, ..state }) }
}

pub open spec fn ht_accumulate_neighbor(
    plane: Tier1RawPlane, x: u16, y: u16, dx: i8, dy: i8, kind: u8, summary: crate::tier1::NeighborSummary,
) -> (Result<(), crate::DecodeError>, crate::tier1::NeighborSummary) {
    let nx = x as int + dx as int;
    let ny = y as int + dy as int;
    if nx < 0 || ny < 0 || nx >= plane.width || ny >= plane.height { (Ok(()), summary) }
    else {
        match tier1_raw_plane_coefficient(plane, nx as u16, ny as u16) {
            Err(error) => (Err(error), summary),
            Ok(coefficient) => if coefficient.significant { ht_neighbor_update(summary, kind, coefficient.negative) }
                else { (Ok(()), summary) },
        }
    }
}

pub open spec fn ht_neighbor_then(
    previous: (Result<(), crate::DecodeError>, crate::tier1::NeighborSummary),
    plane: Tier1RawPlane, x: u16, y: u16, dx: i8, dy: i8, kind: u8,
) -> (Result<(), crate::DecodeError>, crate::tier1::NeighborSummary) {
    match previous.0 { Err(_) => previous, Ok(()) => ht_accumulate_neighbor(plane, x, y, dx, dy, kind, previous.1) }
}

pub open spec fn ht_neighbors(plane: Tier1RawPlane, x: u16, y: u16, vertical_causal: bool)
    -> Result<crate::tier1::NeighborSummary, crate::DecodeError> {
    match tier1_raw_plane_index(plane, x, y) {
        Err(error) => Err(error),
        Ok(_) => {
            let state = ht_accumulate_neighbor(plane, x, y, (-1int) as i8, 0, 0, ht_neighbor_zero());
            let state = ht_neighbor_then(state, plane, x, y, 1, 0, 0);
            let state = ht_neighbor_then(state, plane, x, y, 0, (-1int) as i8, 1);
            let state = ht_neighbor_then(state, plane, x, y, (-1int) as i8, (-1int) as i8, 2);
            let state = ht_neighbor_then(state, plane, x, y, 1, (-1int) as i8, 2);
            let state = if vertical_causal && y % 4 == 3 { state } else {
                let state = ht_neighbor_then(state, plane, x, y, 0, 1, 1);
                let state = ht_neighbor_then(state, plane, x, y, (-1int) as i8, 1, 2);
                ht_neighbor_then(state, plane, x, y, 1, 1, 2)
            };
            match state.0 { Err(error) => Err(error), Ok(()) => Ok(state.1) }
        },
    }
}

pub open spec fn part2_tier1_force_style(before: crate::tier1::Tier1CodingStyle, required: bool)
    -> ((), crate::tier1::Tier1CodingStyle)
{
    ((), crate::tier1::Tier1CodingStyle { force_high_throughput: required, ..before })
}

pub open spec fn part2_tier1_initial_decoder(
    width: u16, height: u16, significant: u16, orientation: crate::tier1::SubbandOrientation,
    style: crate::tier1::Tier1CodingStyle,
) -> Result<Tier1DecoderState, crate::DecodeError> {
    if significant == 0 || significant > crate::tier1::MAX_TIER1_BITPLANES {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        match tier1_empty_plane(width, height) {
            Err(error) => Err(error),
            Ok(plane) => Ok(Tier1DecoderState {
                plane, orientation, style, maximum_passes: (significant as int * 3 - 2) as u32,
                next_pass: 0, bitplane: (significant - 1) as u16, zero_bitplanes: None,
                bitplane_state: None, mq_context_state: None, reset_contexts_before_mq: false,
                decoded_segments: 0, decoded_bytes: 0, legacy_segment: None, legacy_decode_work: 0,
                ht_cleanup_plane: None, ht_refinement_data: Seq::empty(), ht_refinement_passes: 0,
                ht_decoded_bitplanes: 0, ht_current_set_has_cleanup: false, ht_sets_seen: 0,
                allow_multiple_ht_sets: false, ht_magnitude_bound: crate::tier1::tier1_max_ht_magnitude_bits(),
            }),
        }
    }
}

pub open spec fn part2_tier1_allow_sets(before: Tier1DecoderState, allowed: bool) -> ((), Tier1DecoderState) {
    ((), Tier1DecoderState { allow_multiple_ht_sets: allowed, ..before })
}

pub open spec fn part2_tier1_configured_decoder(
    width: u16, height: u16, significant: u16, orientation: crate::tier1::SubbandOrientation,
    style: crate::tier1::Tier1CodingStyle, allowed: bool, bound: u8,
) -> Result<Tier1DecoderState, crate::DecodeError> {
    match part2_tier1_initial_decoder(width, height, significant, orientation, style) {
        Err(error) => Err(error),
        Ok(initial) => {
            let policy = part2_tier1_allow_sets(initial, allowed).1;
            let configured = part2_tier1_magnitude_bound(policy, bound);
            match configured.0 { Err(error) => Err(error), Ok(()) => Ok(configured.1) }
        },
    }
}

pub open spec fn part2_planned_codeblock_geometry(grid: [u32; 4], clip: [u32; 4], block: [u32; 2])
    -> Result<(u32, u32, u16, u16), crate::DecodeError>
{
    let ix = grid[0] as int + block[0] as int;
    let iy = grid[1] as int + block[1] as int;
    let nx = ix * grid[2] as int;
    let ny = iy * grid[3] as int;
    let x = if nx >= clip[0] as int { nx } else { clip[0] as int };
    let y = if ny >= clip[1] as int { ny } else { clip[1] as int };
    let ex = nx + grid[2] as int;
    let ey = ny + grid[3] as int;
    let width = (if ex <= clip[2] as int { ex } else { clip[2] as int }) - x;
    let height = (if ey <= clip[3] as int { ey } else { clip[3] as int }) - y;
    if ix > u32::MAX || nx > u32::MAX || iy > u32::MAX || ny > u32::MAX
        || ex > u32::MAX || ey > u32::MAX || width < 0 || width > u16::MAX
        || height < 0 || height > u16::MAX {
        Err(part1_block_placement_error(true))
    } else { Ok((x as u32, y as u32, width as u16, height as u16)) }
}

#[verifier::opaque]
pub open spec fn part2_capability_lookup_run(
    p_cap: u32, values: Seq<u16>, part: u8, current: u8, mask: u32, index: usize,
) -> Option<u16>
    decreases if current < part { part as int - current as int } else { 0int },
{
    if current < part {
        let active = p_cap & mask != 0;
        if (active && index == usize::MAX) || current == u8::MAX { None } else {
            part2_capability_lookup_run(p_cap, values, part, (current + 1) as u8, mask >> 1u32,
                if active { (index + 1) as usize } else { index })
        }
    } else if p_cap & mask == 0 || index as nat >= values.len() { None }
    else { Some(values[index as int]) }
}

#[verifier::opaque]
pub open spec fn part2_capability_value(caps: (u32, Seq<u16>), part: u8) -> Option<u16> {
    if part == 0 || part > 32 { None } else { part2_capability_lookup_run(caps.0, caps.1, part, 1, 0x80000000u32, 0) }
}

#[verifier::opaque]
pub open spec fn part2_capability_block_mode(caps: (u32, Seq<u16>)) -> Option<crate::codestream::Part15BlockMode> {
    match part2_capability_value(caps, 15) {
        None => None, Some(word) => match word >> 14u16 {
            0 => Some(crate::codestream::Part15BlockMode::HtOnly),
            2 => Some(crate::codestream::Part15BlockMode::HtDeclared),
            3 => Some(crate::codestream::Part15BlockMode::Mixed), _ => None,
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_capability_multiple_sets(caps: (u32, Seq<u16>)) -> bool {
    match part2_capability_value(caps, 15) { None => false, Some(word) => word & 0x2000u16 != 0 }
}

#[verifier::opaque]
pub open spec fn part2_capability_magnitude_bound(caps: (u32, Seq<u16>)) -> Option<u8> {
    match part2_capability_value(caps, 15) {
        None => None, Some(word) => Some(part15_magnitude_bound((word & 0x1fu16) as nat) as u8),
    }
}

#[verifier::opaque]
pub open spec fn part2_profile_multiple_sets(caps: Option<(u32, Seq<u16>)>) -> bool {
    match caps { None => false, Some(caps) => part2_capability_multiple_sets(caps) }
}

#[verifier::opaque]
pub open spec fn part2_profile_magnitude_bound(caps: Option<(u32, Seq<u16>)>) -> u8 {
    match caps { None => 74, Some(caps) => match part2_capability_magnitude_bound(caps) { None => 74, Some(bound) => bound } }
}

#[verifier::opaque]
pub open spec fn part2_profile_force_ht(caps: Option<(u32, Seq<u16>)>) -> bool {
    match caps { None => false, Some(caps) => matches!(part2_capability_block_mode(caps), Some(crate::codestream::Part15BlockMode::HtOnly)) }
}

pub open spec fn part2_mct_array_identity(left: Part2MctArray, right: Part2MctArray) -> bool { left == right }
pub open spec fn part2_mct_collection_identity(left: Part2MctCollection, right: Part2MctCollection) -> bool { left == right }
pub open spec fn part2_mct_stage_identity(left: Part2MctStage, right: Part2MctStage) -> bool { left == right }
pub open spec fn part2_mct_identity(left: Seq<Part2MctStage>, right: Seq<Part2MctStage>) -> bool { left == right }
pub open spec fn part2_optional_mct_identity(left: Option<Seq<Part2MctStage>>, right: Option<Seq<Part2MctStage>>) -> bool { left == right }

pub open spec fn part2_decode_wavelet_agreement(left: crate::codestream::WaveletTransform, right: crate::codestream::WaveletTransform) -> bool {
    matches!((left, right),
        (crate::codestream::WaveletTransform::Irreversible9x7, crate::codestream::WaveletTransform::Irreversible9x7)
        | (crate::codestream::WaveletTransform::Reversible5x3, crate::codestream::WaveletTransform::Reversible5x3))
}

#[verifier::opaque]
pub open spec fn part2_full_tile_style_admission(
    styles: &crate::codestream::ComponentCodingStyles, main: crate::codestream::CodingStyle, components: u16, component: u16,
) -> Result<(), crate::DecodeError>
    decreases if component < components && component < 3 { 3int - component as int } else { 0int },
{
    if component >= components || component >= 3 { Ok(()) } else {
        match crate::codestream::component_coding_style_result(styles, component) {
            Err(error) => Err(error),
            Ok(style) => if !part2_decode_wavelet_agreement(style.transform, main.transform) {
                Err(part1_selector_error(false))
            } else { part2_full_tile_style_admission(styles, main, components, (component + 1) as u16) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_selected_tile_resolutions(
    styles: &crate::codestream::ComponentCodingStyles, main: crate::codestream::CodingStyle, components: u16,
    discard: u8, component: u16, before: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases if component < components { components as int - component as int } else { 0int },
{
    if component >= components { Ok(before) } else {
        match crate::codestream::component_coding_style_result(styles, component) {
            Err(error) => Err(error),
            Ok(style) => {
                let selector = crate::codestream::decomposition_selector_view(style);
                if discard > part2_maximum_isotropic_reduction(selector.0, selector.1, 0) {
                    Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
                } else if main.multiple_component_transform && component < 3 && !part2_decode_wavelet_agreement(style.transform, main.transform) {
                    Err(part1_selector_error(false))
                } else if style.decomposition_levels == u8::MAX || style.decomposition_levels as int + 1 < discard as int {
                    Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::ReductionTooLarge })
                } else {
                    part2_selected_tile_resolutions(styles, main, components, discard, (component + 1) as u16,
                        before.push((style.decomposition_levels as int + 1 - discard as int) as u8))
                }
            },
        }
    }
}

pub open spec fn part2_tile_component_resolutions(
    styles: &crate::codestream::ComponentCodingStyles, main: crate::codestream::CodingStyle, components: u16, discard: Option<u8>,
) -> Result<Seq<u8>, crate::DecodeError> {
    match discard {
        None => if !main.multiple_component_transform { Ok(Seq::empty()) } else {
            match part2_full_tile_style_admission(styles, main, components, 0) {
                Err(error) => Err(error), Ok(()) => Ok(Seq::empty()),
            }
        },
        Some(levels) => part2_selected_tile_resolutions(styles, main, components, levels, 0, Seq::empty()),
    }
}

pub struct Part2TileDecodeMetadata {
    pub first: Part2OwnedTilePart,
    pub standard: (bool, bool),
    pub resolution_counts: Seq<u8>,
}

pub open spec fn part2_tile_decode_standard(first: &crate::codestream::TilePartPayload<'_>) -> Result<(bool, bool), crate::DecodeError> {
    part2_tile_decode_standard_owned(crate::codestream::tile_part_owned_view(first))
}

pub open spec fn part2_owned_kernel_registry(extensions: Part2OwnedExtensions) -> Seq<(u8, Part2RawKernel)> {
    extensions.kernels.map_values(|entry: (u8, u16, Part2RawKernel)| (entry.0, entry.2))
}

pub open spec fn part2_tile_decode_standard_owned(first: Part2OwnedTilePart) -> Result<(bool, bool), crate::DecodeError> {
    let flag = first.coding_style.multiple_component_transform;
    match first.coding_style.transform {
        crate::codestream::WaveletTransform::Irreversible9x7 => Ok((flag, true)),
        crate::codestream::WaveletTransform::Reversible5x3 => Ok((flag, false)),
        crate::codestream::WaveletTransform::Arbitrary(index) => match part2_kernel_registry_lookup(
            part2_owned_kernel_registry(first.part2_extensions), index) {
            None => Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::MissingRequiredStructure }),
            Some(kernel) => Ok((flag, !kernel.0)),
        },
    }
}

pub open spec fn part2_tile_decode_metadata(
    parts: Seq<crate::codestream::TilePartPayload<'_>>, components: u16, discard: Option<u8>,
) -> Result<Part2TileDecodeMetadata, crate::DecodeError> {
    part2_tile_decode_metadata_owned(crate::codestream::tile_parts_owned_view(parts), components, discard)
}

pub open spec fn part2_tile_decode_metadata_owned(
    parts: Seq<Part2OwnedTilePart>, components: u16, discard: Option<u8>,
) -> Result<Part2TileDecodeMetadata, crate::DecodeError> {
    if parts.len() == 0 {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidTilePart })
    } else if !(forall |i: int| 0 <= i < parts.len() ==> #[trigger] parts[i].multiple_component_transform == parts[0].multiple_component_transform) {
        Err(crate::DecodeError::MalformedInput { offset: 0, kind: crate::MalformedKind::InvalidTransform })
    } else {
        match part2_tile_decode_standard_owned(parts[0]) {
            Err(error) => Err(error),
            Ok(standard) => match part2_tile_component_resolutions(&parts[0].component_coding_styles, parts[0].coding_style, components, discard) {
                Err(error) => Err(error),
                Ok(counts) => Ok(Part2TileDecodeMetadata { first: parts[0], standard, resolution_counts: counts }),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_maximum_isotropic_reduction(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, count: u8,
) -> u8
    decreases if count < 32 { 32int - count as int } else { 0int },
{
    if count >= levels || count >= 32 || count as nat >= directions.len()
        || directions[count as int] != crate::codestream::DecompositionDirection::TwoDimensional {
        count
    } else { part2_maximum_isotropic_reduction(levels, directions, (count + 1) as u8) }
}

#[verifier::opaque]
pub open spec fn part2_selected_component_blocks(plan: Part1PreparePlan, index: nat, total: u64)
    -> Result<u64, crate::DecodeError>
    decreases if index < plan.placements.len() { (plan.placements.len() - index) as nat } else { 0nat },
{
    if index >= plan.placements.len() { Ok(total) } else {
        let placement = plan.placements[index as int];
        if placement.subband_index as nat >= plan.subbands.len() { Err(part1_block_placement_error(false)) }
        else {
            let selected = plan.subbands[placement.subband_index as int].resolution <= plan.resolution;
            if selected && total == u64::MAX { Err(part1_block_placement_error(true)) }
            else { part2_selected_component_blocks(plan, index + 1, if selected { (total + 1) as u64 } else { total }) }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_account_plan_blocks(
    plans: Seq<Part1PreparePlan>, selected: bool, maximum: u64, index: nat, total: u64,
) -> Result<u64, crate::DecodeError>
    decreases if index < plans.len() { (plans.len() - index) as nat } else { 0nat },
{
    if index >= plans.len() {
        if selected && total > maximum {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlocks, limit: maximum, actual: total })
        } else { Ok(total) }
    } else {
        let next = if selected { part2_selected_component_blocks(plans[index as int], 0, total) } else {
            let count = plans[index as int].placements.len() as u64;
            if total as nat + count as nat > u64::MAX { Err(part1_block_placement_error(true)) }
            else { Ok((total + count) as u64) }
        };
        match next {
            Err(error) => Err(error),
            Ok(count) => if !selected && count > maximum {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlocks, limit: maximum, actual: count })
            } else { part2_account_plan_blocks(plans, selected, maximum, index + 1, count) },
        }
    }
}

pub open spec fn part2_planned_tile_accounting(
    plan: Part2ProgressionTilePlan, selection: Option<Seq<u8>>, initial: (u64, u64, u64), limits: &crate::ResourceLimits,
) -> Result<(u64, u64, u64), crate::DecodeError> {
    let packets = match selection {
        None => Ok(plan.grid.packet_count),
        Some(counts) => part1_packet_grid_selected_count(plan.grid, counts),
    };
    match packets {
        Err(error) => Err(error),
        Ok(packets) => if initial.0 as nat + packets as nat > u64::MAX { Err(part1_block_placement_error(true)) } else {
            let total_packets = (initial.0 + packets) as u64;
            if total_packets > crate::limits::resource_packet_limit(limits) {
                Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Packets,
                    limit: crate::limits::resource_packet_limit(limits), actual: total_packets })
            } else {
                let precincts = match selection {
                    None => part1_packet_grid_total_precincts(plan.grid),
                    Some(_) => if plan.coding_style.layers == 0 { Err(part1_block_placement_error(true)) }
                        else { Ok((packets / plan.coding_style.layers as u64) as u64) },
                };
                match precincts {
                    Err(error) => Err(error),
                    Ok(precincts) => if initial.1 as nat + precincts as nat > u64::MAX { Err(part1_block_placement_error(true)) }
                    else {
                        let total_precincts = (initial.1 + precincts) as u64;
                        if total_precincts > crate::limits::resource_precinct_limit(limits) {
                            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Precincts,
                                limit: crate::limits::resource_precinct_limit(limits), actual: total_precincts })
                        } else {
                            match part2_account_plan_blocks(plan.components, selection.is_some(),
                                crate::limits::resource_code_block_limit(limits), 0, initial.2) {
                                Err(error) => Err(error),
                                Ok(blocks) => Ok((total_packets, total_precincts, blocks)),
                            }
                        }
                    },
                }
            }
        },
    }
}

pub struct Part2OwnedNonlinear {
    pub component: Option<u16>,
    pub precision: u8,
    pub signed: bool,
    pub transform_type: u8,
    pub parameters: Seq<u8>,
    pub d_min: Option<u32>,
    pub d_max: Option<u32>,
    pub point_bits: Option<u8>,
    pub points: Seq<u32>,
    pub gamma: Option<[u32; 5]>,
}

pub open spec fn part2_nonlinear_find(
    transforms: Seq<Part2OwnedNonlinear>, component: Option<u16>, position: nat,
) -> Option<Part2OwnedNonlinear>
    decreases transforms.len() - position,
{
    if position >= transforms.len() { None }
    else if transforms[position as int].component == component { Some(transforms[position as int]) }
    else { part2_nonlinear_find(transforms, component, position + 1) }
}

pub open spec fn part2_nlt_round_ratio(numerator: i128, denominator: i128)
    -> Result<i128, crate::DecodeError>
{
    if denominator <= 0 || numerator == i128::MIN {
        Err(part1_transform_error(true))
    } else {
        let magnitude = if numerator < 0 { -(numerator as int) } else { numerator as int };
        match part2_atk_checked_i128(magnitude + denominator as int / 2) {
            Err(error) => Err(error),
            Ok(adjusted) => {
                let rounded = adjusted as int / denominator as int;
                Ok((if numerator < 0 { -rounded } else { rounded }) as i128)
            },
        }
    }
}

pub open spec fn part2_nlt_power_of_two(exponent: u8) -> Result<i128, crate::DecodeError> {
    if exponent > 38 { Err(part1_transform_error(true)) }
    else { Ok(1i128 << exponent) }
}

#[verifier::opaque]
pub open spec fn part2_nlt_lut_interpolate_values(
    left: i128, right: i128, denominator: i128, remainder: i128,
) -> Result<i128, crate::DecodeError>
{
    match part2_atk_checked_i128(left as int * denominator as int) {
        Err(error) => Err(error),
        Ok(base) => match part2_atk_checked_i128(right as int - left as int) {
            Err(error) => Err(error),
            Ok(difference) => match part2_atk_checked_i128(difference as int * remainder as int) {
                Err(error) => Err(error),
                Ok(offset) => match part2_atk_checked_i128(base as int + offset as int) {
                    Err(error) => Err(error),
                    Ok(numerator) => part2_nlt_round_ratio(numerator, denominator),
                },
            },
        },
    }
}

pub open spec fn part2_nlt_lut_interpolate(
    points: Seq<u32>, index: usize, denominator: i128, remainder: i128,
) -> Result<i128, crate::DecodeError>
    recommends points.len() > 0,
{
    if index as nat >= points.len() - 1 {
        Ok(points[points.len() - 1] as i128)
    } else {
        part2_nlt_lut_interpolate_values(points[index as int] as i128,
            points[index as int + 1] as i128, denominator, remainder)
    }
}

pub open spec fn part2_nlt_lut_finish(raw: i128, transform: Part2OwnedNonlinear)
    -> Result<i128, crate::DecodeError>
    recommends transform.precision > 0,
{
    match part2_nlt_power_of_two((transform.precision - 1) as u8) {
        Err(error) => Err(error),
        Ok(half) => match if transform.signed { part2_atk_checked_i128(raw as int - half as int) } else { Ok(raw) } {
            Err(error) => Err(error),
            Ok(value) => if transform.transform_type == 4 && value < 0 {
                match part2_atk_checked_i128(half as int + 1) {
                    Err(error) => Err(error),
                    Ok(bias) => match part2_atk_checked_i128(-(value as int)) {
                        Err(error) => Err(error),
                        Ok(magnitude) => part2_atk_checked_i128(magnitude as int - bias as int),
                    },
                }
            } else { Ok(value) },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_lut_coordinates(
    source_scale: i128, nominal: i128, minimum: u32, maximum: u32, last_index: nat,
) -> Result<(usize, i128, i128), crate::DecodeError> {
    match part2_atk_checked_i128(nominal as int * u32::MAX as int) {
        Err(error) => Err(error),
        Ok(normalized) => match part2_atk_checked_i128(minimum as int * source_scale as int) {
            Err(error) => Err(error),
            Ok(minimum_scaled) => match part2_atk_checked_i128(maximum as int * source_scale as int) {
                Err(error) => Err(error),
                Ok(maximum_scaled) => {
                    let above_minimum = if normalized > minimum_scaled { normalized } else { minimum_scaled };
                    let clamped = if above_minimum < maximum_scaled { above_minimum } else { maximum_scaled };
                    if last_index > i128::MAX { Err(part1_transform_error(true)) } else {
                        let count = last_index as i128;
                        match part2_atk_checked_i128(maximum_scaled as int - minimum_scaled as int) {
                            Err(error) => Err(error),
                            Ok(denominator) => match part2_atk_checked_i128(clamped as int - minimum_scaled as int) {
                                Err(error) => Err(error),
                                Ok(offset) => match part2_atk_checked_i128(offset as int * count as int) {
                                    Err(error) => Err(error),
                                    Ok(position) => if denominator == 0 || (position == i128::MIN && denominator == -1) {
                                        Err(part1_transform_error(true))
                                    } else {
                                        let interval = vstd::arithmetic::div_mod::rust_div(position as int, denominator as int) as i128;
                                        let remainder = vstd::arithmetic::div_mod::rust_rem(position as int, denominator as int) as i128;
                                        if interval < 0 || interval > usize::MAX { Err(part1_transform_error(true)) }
                                        else { Ok((interval as usize, denominator, remainder)) }
                                    },
                                },
                            },
                        }
                    }
                },
            },
        },
    }
}

pub open spec fn part2_nlt_checked_rem(numerator: i128, denominator: i128)
    -> Result<i128, crate::DecodeError>
{
    if denominator == 0 || (numerator == i128::MIN && denominator == -1) {
        Err(part1_transform_error(true))
    } else {
        Ok(vstd::arithmetic::div_mod::rust_rem(numerator as int, denominator as int) as i128)
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_lut_position(
    points: Seq<u32>, source_scale: i128, nominal: i128, minimum: u32, maximum: u32,
) -> Result<i128, crate::DecodeError> {
    if points.len() == 0 { Err(part1_image_error(false)) } else {
        match part2_nlt_lut_coordinates(source_scale, nominal, minimum, maximum, (points.len() - 1) as nat) {
            Err(error) => Err(error),
            Ok((index, denominator, remainder)) => part2_nlt_lut_interpolate(points, index, denominator, remainder),
        }
    }
}

pub open spec fn part2_nlt_lut_sample(
    source: i128, info: crate::codestream::ComponentInfo, transform: Part2OwnedNonlinear,
) -> Result<i128, crate::DecodeError> {
    if transform.precision == 0 || transform.precision > 38 { Err(part1_image_error(false)) }
    else {
        match transform.d_min {
            None => Err(part1_transform_error(false)),
            Some(minimum) => match transform.d_max {
                None => Err(part1_transform_error(false)),
                Some(maximum) => if transform.points.len() < 2 || minimum >= maximum {
                    Err(part1_transform_error(false))
                } else if info.precision == 0 || info.precision > 38 {
                    Err(part1_image_error(false))
                } else {
                    match part2_nlt_power_of_two(info.precision) {
                        Err(error) => Err(error),
                        Ok(source_scale) => match if info.signed { part2_nlt_power_of_two((info.precision - 1) as u8) } else { Ok(0i128) } {
                            Err(error) => Err(error),
                            Ok(source_offset) => match part2_atk_checked_i128(source as int + source_offset as int) {
                                Err(error) => Err(error),
                                Ok(nominal) => if nominal < 0 || nominal >= source_scale { Err(part1_image_error(false)) }
                                else {
                                    match part2_nlt_lut_position(transform.points, source_scale, nominal, minimum, maximum) {
                                        Err(error) => Err(error),
                                        Ok(raw) => part2_nlt_lut_finish(raw, transform),
                                    }
                                },
                            },
                        },
                    }
                },
            },
        }
    }
}

pub open spec fn part2_nlt_fixed_mul_q32(left: i128, right: i128)
    -> Result<i128, crate::DecodeError>
{
    match part2_atk_checked_i128(left as int * right as int) {
        Err(error) => Err(error),
        Ok(product) => part2_nlt_round_ratio(product, 1i128 << 32),
    }
}

pub open spec fn part2_nlt_fixed_div_q32(left: i128, right: i128)
    -> Result<i128, crate::DecodeError>
{
    if right <= 0 { Err(part1_transform_error(false)) } else {
        match part2_atk_checked_i128(left as int * 4294967296) {
            Err(error) => Err(error),
            Ok(product) => Ok(vstd::arithmetic::div_mod::rust_div(product as int, right as int) as i128),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_ln_normalize_low(value: i128, scale: i32, passes: u16)
    -> Result<(i128, i32), crate::DecodeError>
    decreases passes,
{
    if value >= 4294967296 { Ok((value, scale)) } else {
        match part2_atk_checked_i128(value as int * 2) {
            Err(error) => Err(error),
            Ok(next) => match part2_atk_checked_i32(scale as int - 1) {
                Err(error) => Err(error),
                Ok(scale) => if passes == 0 { Err(part1_transform_error(true)) }
                    else { part2_nlt_ln_normalize_low(next, scale, (passes - 1) as u16) },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_ln_normalize_high(value: i128, scale: i32, passes: u16)
    -> Result<(i128, i32), crate::DecodeError>
    decreases passes,
{
    if value < 8589934592 { part2_nlt_ln_normalize_low(value, scale, 128) } else {
        match part2_atk_checked_i32(scale as int + 1) {
            Err(error) => Err(error),
            Ok(scale) => if passes == 0 { Err(part1_transform_error(true)) }
                else { part2_nlt_ln_normalize_high(value >> 1, scale, (passes - 1) as u16) },
        }
    }
}

pub open spec fn part2_nlt_ln_normalize(value: i128)
    -> Result<(i128, i32), crate::DecodeError>
{
    part2_nlt_ln_normalize_high(value, 0, 128)
}

#[verifier::opaque]
pub open spec fn part2_nlt_ln_series(
    squared: i128, scale: i32, iteration: nat, term: i128, sum: i128,
) -> Result<i128, crate::DecodeError>
    decreases 20 - iteration,
{
    if iteration >= 20 {
        match part2_atk_checked_i128(sum as int * 2) {
            Err(error) => Err(error),
            Ok(doubled) => match part2_atk_checked_i128(scale as int * 2977044471) {
                Err(error) => Err(error),
                Ok(shifted) => part2_atk_checked_i128(doubled as int + shifted as int),
            },
        }
    } else {
        let divisor = 2 * iteration + 1;
        let quotient = vstd::arithmetic::div_mod::rust_div(term as int, divisor as int) as i128;
        match part2_atk_checked_i128(sum as int + quotient as int) {
            Err(error) => Err(error),
            Ok(sum) => match part2_nlt_fixed_mul_q32(term, squared) {
                Err(error) => Err(error),
                Ok(term) => part2_nlt_ln_series(squared, scale, iteration + 1, term, sum),
            },
        }
    }
}

pub open spec fn part2_nlt_fixed_ln_q32(value: i128) -> Result<i128, crate::DecodeError> {
    match part2_nlt_ln_normalize(value) {
        Err(error) => Err(error),
        Ok((value, scale)) => match part2_atk_checked_i128(value as int - 4294967296) {
            Err(error) => Err(error),
            Ok(numerator) => match part2_atk_checked_i128(value as int + 4294967296) {
                Err(error) => Err(error),
                Ok(denominator) => match part2_nlt_fixed_div_q32(numerator, denominator) {
                    Err(error) => Err(error),
                    Ok(z) => match part2_nlt_fixed_mul_q32(z, z) {
                        Err(error) => Err(error),
                        Ok(squared) => part2_nlt_ln_series(squared, scale, 0, z, 0),
                    },
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_exp_series(remainder: i128, iteration: nat, term: i128, sum: i128)
    -> Result<i128, crate::DecodeError>
    decreases 25 - iteration,
{
    if iteration > 24 { Ok(sum) } else {
        match part2_nlt_fixed_mul_q32(term, remainder) {
            Err(error) => Err(error),
            Ok(product) => if iteration == 0 { Err(part1_transform_error(true)) } else {
                let term = vstd::arithmetic::div_mod::rust_div(product as int, iteration as int) as i128;
                match part2_atk_checked_i128(sum as int + term as int) {
                    Err(error) => Err(error),
                    Ok(sum) => part2_nlt_exp_series(remainder, iteration + 1, term, sum),
                }
            },
        }
    }
}

pub open spec fn part2_nlt_fixed_exp_q32(value: i128) -> Result<i128, crate::DecodeError> {
    let scale = vstd::arithmetic::div_mod::rust_div(value as int, 2977044471) as i128;
    if scale < -62 || scale > 62 { Err(part1_transform_error(false)) } else {
        let remainder = (value as int - scale as int * 2977044471) as i128;
        match part2_nlt_exp_series(remainder, 1, 4294967296, 4294967296) {
            Err(error) => Err(error),
            Ok(sum) => if scale >= 0 {
                if sum < 0 || sum > (i128::MAX >> scale as u32) { Err(part1_transform_error(true)) }
                else { Ok(sum << scale as u32) }
            } else { Ok(sum >> ((-(scale as int)) as u32)) },
        }
    }
}

pub open spec fn part2_nlt_fixed_pow_reciprocal_q32(base: i128, exponent: i128)
    -> Result<i128, crate::DecodeError>
{
    if base <= 0 || exponent <= 0 { Err(part1_transform_error(false)) } else {
        match part2_nlt_fixed_ln_q32(base) {
            Err(error) => Err(error),
            Ok(logarithm) => match part2_nlt_fixed_div_q32(logarithm, exponent) {
                Err(error) => Err(error),
                Ok(power) => part2_nlt_fixed_exp_q32(power),
            },
        }
    }
}

pub open spec fn part2_nlt_gamma_parameter_value(raw: u32) -> i128 {
    ((raw >> 16) as int * 4294967296 + (raw & 65535) as int * 4294967296 / 65535) as i128
}

pub open spec fn part2_nlt_gamma_parameter(raw: u32) -> Result<i128, crate::DecodeError> {
    Ok(part2_nlt_gamma_parameter_value(raw))
}

pub open spec fn part2_nlt_gamma_scale(precision: u8, signed: bool)
    -> Result<i128, crate::DecodeError>
{
    if signed && precision == 0 { Err(part1_transform_error(true)) } else {
        match part2_nlt_power_of_two(if signed { (precision - 1) as u8 } else { precision }) {
            Err(error) => Err(error),
            Ok(power) => part2_atk_checked_i128(power as int - 1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_gamma_curve(
    normalized: i128, exponent: i128, slope: i128, threshold: i128, a: i128, b: i128,
) -> Result<i128, crate::DecodeError> {
    match part2_atk_checked_i128(-(threshold as int)) {
        Err(error) => Err(error),
        Ok(negative_threshold) => if normalized < negative_threshold {
            match part2_atk_checked_i128(-(normalized as int)) {
                Err(error) => Err(error),
                Ok(magnitude) => match part2_atk_checked_i128(magnitude as int + b as int) {
                    Err(error) => Err(error),
                    Ok(numerator) => match part2_nlt_fixed_div_q32(numerator, a) {
                        Err(error) => Err(error),
                        Ok(base) => match part2_nlt_fixed_pow_reciprocal_q32(base, exponent) {
                            Err(error) => Err(error),
                            Ok(value) => part2_atk_checked_i128(-(value as int)),
                        },
                    },
                },
            }
        } else if normalized <= threshold { part2_nlt_fixed_div_q32(normalized, slope) }
        else {
            match part2_atk_checked_i128(normalized as int + b as int) {
                Err(error) => Err(error),
                Ok(numerator) => match part2_nlt_fixed_div_q32(numerator, a) {
                    Err(error) => Err(error),
                    Ok(base) => part2_nlt_fixed_pow_reciprocal_q32(base, exponent),
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_gamma_sample(
    source: i128, info: crate::codestream::ComponentInfo, transform: Part2OwnedNonlinear,
) -> Result<i128, crate::DecodeError> {
    if info.precision == 0 || info.precision > 38 { Err(part1_image_error(false)) } else {
        match transform.gamma {
            None => Err(part1_transform_error(false)),
            Some(parameters) => {
                let exponent = part2_nlt_gamma_parameter_value(parameters[0]);
                let slope = part2_nlt_gamma_parameter_value(parameters[1]);
                let threshold = part2_nlt_gamma_parameter_value(parameters[2]);
                let a = part2_nlt_gamma_parameter_value(parameters[3]);
                let b = part2_nlt_gamma_parameter_value(parameters[4]);
                if exponent <= 0 || slope <= 0 || a <= 0 { Err(part1_transform_error(false)) } else {
                    match part2_nlt_gamma_scale(info.precision, info.signed) {
                        Err(error) => Err(error),
                        Ok(source_scale) => if transform.precision == 0 { Err(part1_transform_error(false)) } else {
                            match part2_nlt_gamma_scale(transform.precision, transform.signed) {
                                Err(error) => Err(error),
                                Ok(target_scale) => if source_scale <= 0 || target_scale <= 0 {
                                    Err(part1_transform_error(false))
                                } else {
                                    match part2_atk_checked_i128(source as int * 4294967296) {
                                        Err(error) => Err(error),
                                        Ok(product) => {
                                            let normalized = vstd::arithmetic::div_mod::rust_div(product as int, source_scale as int) as i128;
                                            match part2_nlt_gamma_curve(normalized, exponent, slope, threshold, a, b) {
                                                Err(error) => Err(error),
                                                Ok(decoded) => match part2_atk_checked_i128(decoded as int * target_scale as int) {
                                                    Err(error) => Err(error),
                                                    Ok(product) => part2_nlt_round_ratio(product, 4294967296),
                                                },
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn part2_nlt_inverse_value(
    source: i128, info: crate::codestream::ComponentInfo, transform: Part2OwnedNonlinear, half: i128,
) -> Result<i128, crate::DecodeError> {
    if transform.transform_type == 0 || transform.transform_type == 3 {
        if info.precision != transform.precision || info.signed != transform.signed {
            Err(part1_transform_error(false))
        } else if transform.transform_type == 3 && source < 0 {
            if source == i128::MIN || half < 0 || half == i128::MAX { Err(part1_transform_error(true)) }
            else { Ok(part2_nlt_binary_complement(source, half)) }
        } else { Ok(source) }
    } else if transform.transform_type == 2 || transform.transform_type == 4 {
        part2_nlt_lut_sample(source, info, transform)
    } else if transform.transform_type == 1 { part2_nlt_gamma_sample(source, info, transform) }
    else { Err(part1_transform_error(false)) }
}

#[verifier::opaque]
pub open spec fn part2_nlt_inverse_sample(
    source: i128, info: crate::codestream::ComponentInfo, transform: Part2OwnedNonlinear,
) -> Result<i128, crate::DecodeError> {
    if transform.precision == 0 || transform.precision > 38 { Err(part1_image_error(false)) } else {
        match part2_nlt_power_of_two((transform.precision - 1) as u8) {
            Err(error) => Err(error),
            Ok(half) => match if transform.signed { part2_atk_checked_i128(-(half as int)) } else { Ok(0i128) } {
                Err(error) => Err(error),
                Ok(minimum) => match if transform.signed { part2_atk_checked_i128(half as int - 1) } else {
                    match part2_nlt_power_of_two(transform.precision) {
                        Err(error) => Err(error),
                        Ok(power) => part2_atk_checked_i128(power as int - 1),
                    }
                } {
                    Err(error) => Err(error),
                    Ok(maximum) => match part2_nlt_inverse_value(source, info, transform, half) {
                        Err(error) => Err(error),
                        Ok(value) => if value < minimum || value > maximum { Err(part1_transform_error(false)) }
                            else { Ok(value) },
                    },
                },
            },
        }
    }
}

pub open spec fn part2_nonlinear_transform_for(
    transforms: Seq<Part2OwnedNonlinear>, component: u16,
) -> Option<Part2OwnedNonlinear> {
    match part2_nonlinear_find(transforms, Some(component), 0) {
        Some(transform) => Some(transform),
        None => part2_nonlinear_find(transforms, None, 0),
    }
}

pub open spec fn part2_nlt_sample_count(samples: Part1TypedSampleSequence) -> nat {
    match samples {
        Part1TypedSampleSequence::Signed(values) => values.len(),
        Part1TypedSampleSequence::Unsigned(values) => values.len(),
    }
}

pub open spec fn part2_nlt_source_sample(samples: Part1TypedSampleSequence, index: usize)
    -> Result<i128, crate::DecodeError>
{
    match samples {
        Part1TypedSampleSequence::Signed(values) => if index as nat >= values.len() {
            Err(part1_image_error(false))
        } else { Ok(values[index as int] as i128) },
        Part1TypedSampleSequence::Unsigned(values) => if index as nat >= values.len() {
            Err(part1_image_error(false))
        } else { Ok(values[index as int] as i128) },
    }
}

pub struct Part2NltScratch {
    pub output: Seq<Option<i128>>,
    pub target: Option<(u8, bool)>,
    pub work: u64,
}

pub open spec fn part2_nlt_region_pixel(
    source: Part1TypedComponentModel, region: Part2NonlinearRegion,
    y: u32, x: u32, maximum: u64, state: Part2NltScratch,
) -> Result<Part2NltScratch, crate::DecodeError> {
    match part1_transform_offset(y, source.width, x) {
        Err(error) => Err(error),
        Ok(index) => if index as nat >= state.output.len() { Err(part1_image_error(false)) }
        else if state.output[index as int].is_some() { Err(part1_transform_error(false)) }
        else {
            match part2_nlt_source_sample(source.samples, index) {
                Err(error) => Err(error),
                Ok(sample) => match part2_nlt_inverse_sample(sample, source.info, region.transform) {
                    Err(error) => Err(error),
                    Ok(value) => {
                        let charged = part2_mct_charge_work(state.work, 1, maximum);
                        match charged.0 {
                            Err(error) => Err(error),
                            Ok(()) => Ok(Part2NltScratch {
                                output: state.output.update(index as int, Some(value)),
                                target: state.target, work: charged.1,
                            }),
                        }
                    },
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_region_row(
    source: Part1TypedComponentModel, region: Part2NonlinearRegion,
    y: u32, x: u32, maximum: u64, state: Part2NltScratch,
) -> Result<Part2NltScratch, crate::DecodeError>
    decreases region.x1 - x,
{
    if x >= region.x1 { Ok(state) } else {
        match part2_nlt_region_pixel(source, region, y, x, maximum, state) {
            Err(error) => Err(error),
            Ok(state) => part2_nlt_region_row(source, region, y, (x + 1) as u32, maximum, state),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_region_rows(
    source: Part1TypedComponentModel, region: Part2NonlinearRegion,
    y: u32, maximum: u64, state: Part2NltScratch,
) -> Result<Part2NltScratch, crate::DecodeError>
    decreases region.y1 - y,
{
    if y >= region.y1 { Ok(state) } else {
        match part2_nlt_region_row(source, region, y, region.x0, maximum, state) {
            Err(error) => Err(error),
            Ok(state) => part2_nlt_region_rows(source, region, (y + 1) as u32, maximum, state),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_component_regions(
    source: Part1TypedComponentModel, number: u16, regions: Seq<Part2NonlinearRegion>,
    position: nat, maximum: u64, state: Part2NltScratch,
) -> Result<Part2NltScratch, crate::DecodeError>
    decreases regions.len() - position,
{
    if position >= regions.len() { Ok(state) } else {
        let region = regions[position as int];
        if region.component != number {
            part2_nlt_component_regions(source, number, regions, position + 1, maximum, state)
        } else if region.x0 >= region.x1 || region.y0 >= region.y1
            || region.x1 > source.width || region.y1 > source.height {
            Err(part1_image_error(false))
        } else {
            let descriptor = (region.transform.precision, region.transform.signed);
            if state.target.is_some() && state.target != Some(descriptor) {
                Err(part1_transform_error(false))
            } else {
                match part2_nlt_region_rows(source, region, region.y0, maximum, Part2NltScratch {
                    output: state.output, target: Some(descriptor), work: state.work,
                }) {
                    Err(error) => Err(error),
                    Ok(state) => part2_nlt_component_regions(source, number, regions, position + 1, maximum, state),
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_collect_samples(
    output: Seq<Option<i128>>, signed: bool, position: nat, done: Part1TypedSampleSequence,
) -> Result<Part1TypedSampleSequence, crate::DecodeError>
    decreases output.len() - position,
{
    if position >= output.len() { Ok(done) } else {
        match output[position as int] {
            None => Err(part1_image_error(false)),
            Some(value) => match done {
                Part1TypedSampleSequence::Signed(values) => if !signed || value < i64::MIN || value > i64::MAX {
                    Err(part1_image_error(false))
                } else {
                    part2_nlt_collect_samples(output, signed, position + 1,
                        Part1TypedSampleSequence::Signed(values.push(value as i64)))
                },
                Part1TypedSampleSequence::Unsigned(values) => if signed || value < 0 || value > u64::MAX {
                    Err(part1_image_error(false))
                } else {
                    part2_nlt_collect_samples(output, signed, position + 1,
                        Part1TypedSampleSequence::Unsigned(values.push(value as u64)))
                },
            },
        }
    }
}

pub open spec fn part2_nlt_updated_component(
    source: Part1TypedComponentModel, precision: u8, signed: bool, samples: Part1TypedSampleSequence,
) -> Part1TypedComponentModel {
    Part1TypedComponentModel {
        width: source.width, height: source.height,
        info: crate::codestream::ComponentInfo {
            precision, signed,
            x_subsampling: source.info.x_subsampling, y_subsampling: source.info.y_subsampling,
            x_registration: source.info.x_registration, y_registration: source.info.y_registration,
        }, samples,
    }
}

pub open spec fn part2_nlt_finish_component(
    source: Part1TypedComponentModel, state: Part2NltScratch, maximum_bytes: u64,
) -> Result<(Part1TypedComponentModel, u64), crate::DecodeError> {
    match state.target {
        None => Ok((source, state.work)),
        Some((precision, signed)) => match part1_image_byte_budget(state.output.len(), 8, maximum_bytes) {
            Err(error) => Err(error),
            Ok(()) => match part2_nlt_collect_samples(state.output, signed, 0,
                if signed { Part1TypedSampleSequence::Signed(Seq::empty()) }
                else { Part1TypedSampleSequence::Unsigned(Seq::empty()) }) {
                Err(error) => Err(error),
                Ok(samples) => Ok((part2_nlt_updated_component(source, precision, signed, samples), state.work)),
            },
        },
    }
}

pub open spec fn part2_nlt_component(
    source: Part1TypedComponentModel, number: u16, regions: Seq<Part2NonlinearRegion>,
    maximum_bytes: u64, maximum_work: u64, initial_work: u64,
) -> Result<(Part1TypedComponentModel, u64), crate::DecodeError> {
    match part2_nlt_component_regions(source, number, regions, 0, maximum_work, Part2NltScratch {
        output: Seq::new(part2_nlt_sample_count(source.samples), |i: int| None),
        target: None, work: initial_work,
    }) {
        Err(error) => Err(error),
        Ok(state) => part2_nlt_finish_component(source, state, maximum_bytes),
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_component_mutation(
    source: Part1TypedComponentModel, number: u16, regions: Seq<Part2NonlinearRegion>,
    maximum_bytes: u64, maximum_work: u64, initial_work: u64,
) -> (Result<u64, crate::DecodeError>, Part1TypedComponentModel) {
    match part2_nlt_component(source, number, regions, maximum_bytes, maximum_work, initial_work) {
        Err(error) => (Err(error), source),
        Ok((component, work)) => (Ok(work), component),
    }
}

#[verifier::opaque]
pub open spec fn part2_nlt_apply_components(
    image: Part1DecodedTypedImage, position: nat, regions: Seq<Part2NonlinearRegion>,
    maximum_bytes: u64, maximum_work: u64, work: u64,
) -> (Part1DecodedTypedImage, Result<(), crate::DecodeError>)
    decreases image.1.len() - position,
{
    if position >= image.1.len() { (image, Ok(())) }
    else if position > u16::MAX { (image, Err(part1_transform_error(true))) }
    else {
        match part2_nlt_component(image.1[position as int], position as u16, regions, maximum_bytes, maximum_work, work) {
            Err(error) => (image, Err(error)),
            Ok((component, work)) => part2_nlt_apply_components(
                (image.0, image.1.update(position as int, component), image.2),
                position + 1, regions, maximum_bytes, maximum_work, work,
            ),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_apply_nonlinear_regions(
    image: Part1DecodedTypedImage, regions: Seq<Part2NonlinearRegion>,
    maximum_bytes: u64, maximum_work: u64,
) -> (Result<(), crate::DecodeError>, Part1DecodedTypedImage) {
    let outcome = part2_nlt_apply_components(image, 0, regions, maximum_bytes, maximum_work, 0);
    (outcome.1, outcome.0)
}

pub open spec fn part2_nonlinear_tile_extensions(
    main: Part2OwnedExtensions, parts: Seq<Part2OwnedTilePart>, tile: u16, count: nat,
) -> Part2OwnedExtensions
    recommends count <= parts.len(),
    decreases count,
{
    if count == 0 { main }
    else if parts[count - 1].tile_index == tile { parts[count - 1].part2_extensions }
    else { part2_nonlinear_tile_extensions(main, parts, tile, (count - 1) as nat) }
}

pub struct Part2NonlinearRegion {
    pub component: u16,
    pub x0: u32,
    pub y0: u32,
    pub x1: u32,
    pub y1: u32,
    pub transform: Part2OwnedNonlinear,
}

pub open spec fn part2_nonlinear_component_extent(
    size: &crate::codestream::ImageSize, image: Part1DecodedTypedImage, component: u16,
) -> Result<((u32, u32, u32, u32), u64), crate::DecodeError> {
    match part1_image_size_component(crate::codestream::image_size_component_count(size),
        crate::codestream::image_size_component_infos(size), component) {
        Err(error) => Err(error),
        Ok(info) => if component as nat >= image.1.len() { Err(part1_image_error(false)) } else {
            let output = image.1[component as int];
            match part2_registered_decode_ceil(image.0.2, info.x_subsampling as u32, info.x_registration) {
                Err(error) => Err(error),
                Ok(x0) => match part2_registered_decode_ceil(image.0.3, info.y_subsampling as u32, info.y_registration) {
                    Err(error) => Err(error),
                    Ok(y0) => if x0 as int + output.width as int > u32::MAX {
                        Err(part1_block_placement_error(true))
                    } else if y0 as int + output.height as int > u32::MAX {
                        Err(part1_block_placement_error(true))
                    } else {
                        match part2_selection_tile_count(crate::codestream::selection_geometry_view(size)) {
                            Err(error) => Err(error),
                            Ok(count) => Ok(((x0, y0, (x0 + output.width) as u32, (y0 + output.height) as u32), count)),
                        }
                    }
                },
            }
        },
    }
}

pub(crate) open spec fn part2_nonlinear_tile_region(
    layout: &crate::codestream::CodestreamLayout<'_>, component: u16, tile: u16,
    extent: (u32, u32, u32, u32),
) -> Result<Option<Part2NonlinearRegion>, crate::DecodeError> {
    part2_nonlinear_tile_region_input(crate::codestream::decoder_layout_input_view(layout), component, tile, extent)
}

pub(crate) open spec fn part2_nonlinear_tile_regions(
    layout: &crate::codestream::CodestreamLayout<'_>, component: u16,
    extent: (u32, u32, u32, u32), count: u64, tile: nat, regions: Seq<Part2NonlinearRegion>,
) -> Result<Seq<Part2NonlinearRegion>, crate::DecodeError>
    decreases count - tile,
{
    part2_nonlinear_tile_regions_input(crate::codestream::decoder_layout_input_view(layout), component, extent, count, tile, regions)
}

pub(crate) open spec fn part2_nonlinear_component_regions(
    layout: &crate::codestream::CodestreamLayout<'_>, image: Part1DecodedTypedImage,
    component: nat, regions: Seq<Part2NonlinearRegion>,
) -> Result<Seq<Part2NonlinearRegion>, crate::DecodeError>
    decreases layout.info.image_size.components - component,
{
    part2_nonlinear_component_regions_input(crate::codestream::decoder_layout_input_view(layout), image, component, regions)
}

pub(crate) open spec fn part2_collect_nonlinear_regions(
    layout: &crate::codestream::CodestreamLayout<'_>, image: Part1DecodedTypedImage,
) -> Result<Seq<Part2NonlinearRegion>, crate::DecodeError> {
    part2_collect_nonlinear_regions_input(crate::codestream::decoder_layout_input_view(layout), image)
}

pub struct Part2OwnedExtensions {
    pub decompositions: Seq<(u8, Seq<crate::codestream::DecompositionDirection>)>,
    pub arbitrary: Seq<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)>,
    pub nonlinear: Seq<Part2OwnedNonlinear>,
    pub depths: Seq<crate::codestream::ComponentBitDepth>,
    pub kernels: Seq<(u8, u16, Part2RawKernel)>,
    pub registrations: Seq<crate::codestream::ComponentRegistration>,
    pub lengths: Seq<crate::codestream::TilePartLength>,
    pub metadata_bytes: u64,
}

pub struct Part2OwnedTilePart {
    pub tile_index: u16,
    pub tile_part_index: u8,
    pub tile_part_count: u8,
    pub coding_style: crate::codestream::CodingStyle,
    pub quantization: crate::codestream::Quantization,
    pub component_coding_styles: crate::codestream::ComponentCodingStyles,
    pub component_quantizations: (u16, Seq<crate::codestream::Quantization>),
    pub roi_shifts: crate::codestream::RoiShifts,
    pub progression_changes: Seq<crate::codestream::ProgressionChange>,
    pub multiple_component_transform: Option<Seq<Part2MctStage>>,
    pub part2_extensions: Part2OwnedExtensions,
    pub packet_lengths: Part1PacketLengths,
    pub packed_packet_headers: Part1PackedHeaders,
    pub has_functional_header_marker: bool,
    pub has_roi_marker: bool,
    pub data: Seq<u8>,
}

pub open spec fn part2_tile_part_copy(value: Part2OwnedTilePart) -> Part2OwnedTilePart { value }

#[verifier::opaque]
pub open spec fn part2_collect_tile_parts_run(
    parts: Seq<Part2OwnedTilePart>, tile: u16, index: nat, before: Seq<Part2OwnedTilePart>,
) -> Seq<Part2OwnedTilePart>
    decreases if index < parts.len() { (parts.len() - index) as nat } else { 0nat },
{
    if index >= parts.len() { before } else {
        let copied = part2_tile_part_copy(parts[index as int]);
        part2_collect_tile_parts_run(parts, tile, index + 1, if copied.tile_index == tile { before.push(copied) } else { before })
    }
}

pub open spec fn part2_collect_tile_parts(parts: Seq<Part2OwnedTilePart>, tile: u16) -> Result<Seq<Part2OwnedTilePart>, crate::DecodeError> {
    Ok(part2_collect_tile_parts_run(parts, tile, 0, Seq::empty()))
}

pub(crate) open spec fn part2_layout_execution_admission(layout: &crate::codestream::CodestreamLayout<'_>)
    -> Result<(), crate::DecodeError>
{
    part2_decoder_execution_admission(crate::codestream::decoder_layout_input_view(layout))
}

#[verifier::opaque]
pub open spec fn part2_full_layout_tiles(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    limits: &crate::ResourceLimits, count: u64, tile: u64, before: Part2DecodedLayoutTile,
) -> Result<Part1DecodedImageModel, crate::DecodeError>
    decreases if tile < count { count as int - tile as int } else { 0int },
{
    if tile >= count {
        part2_assemble_prepared(crate::image::assembly_size_view(size), before.prepared, None,
            crate::limits::resource_decoded_bytes_limit(limits))
    } else if tile > u16::MAX as u64 { Err(part1_block_placement_error(true)) } else {
        match part2_collect_tile_parts(parts, tile as u16) {
            Err(error) => Err(error),
            Ok(selected) => match part2_decode_tile_parts_owned(size, tile as u16, selected, caps, None, limits,
                before.prepared, before.counters, before.mct_work) {
                Err(error) => Err(error),
                Ok(after) => if tile == u64::MAX { Err(part1_block_placement_error(true)) }
                    else { part2_full_layout_tiles(size, parts, caps, limits, count, (tile + 1) as u64, after) },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_selected_layout_tiles(
    size: &crate::codestream::ImageSize, parts: Seq<Part2OwnedTilePart>, caps: Option<(u32, Seq<u16>)>,
    tiles: Seq<u16>, region: [u32; 4], discard: u8, limits: &crate::ResourceLimits,
    index: nat, before: Part2DecodedLayoutTile,
) -> Result<Part1DecodedImageModel, crate::DecodeError>
    decreases if index < tiles.len() { (tiles.len() - index) as nat } else { 0nat },
{
    if index >= tiles.len() {
        part2_assemble_prepared(crate::image::assembly_size_view(size), before.prepared, Some((region, discard)),
            crate::limits::resource_decoded_bytes_limit(limits))
    } else {
        let tile = tiles[index as int];
        match part2_collect_tile_parts(parts, tile) {
            Err(error) => Err(error),
            Ok(selected) => match part2_decode_tile_parts_owned(size, tile, selected, caps, Some(discard), limits,
                before.prepared, before.counters, before.mct_work) {
                Err(error) => Err(error),
                Ok(after) => part2_selected_layout_tiles(size, parts, caps, tiles, region, discard, limits, index + 1, after),
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part2_typed_layout(
    layout: &crate::codestream::CodestreamLayout<'_>, decoded: Part1DecodedImageModel,
    limits: &crate::ResourceLimits,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    part2_typed_layout_input(crate::codestream::decoder_layout_input_view(layout), decoded, limits)
}

#[verifier::opaque]
pub(crate) open spec fn part2_decode_typed_layout(
    input_bytes: usize, layout: &crate::codestream::CodestreamLayout<'_>, limits: &crate::ResourceLimits,
    requested: Option<&crate::DecodeSelection>,
) -> Result<Part1DecodedTypedImage, crate::DecodeError> {
    part2_decode_typed_layout_input(input_bytes, crate::codestream::decoder_layout_input_view(layout), limits, requested)
}

pub(crate) open spec fn part2_decode_layout(layout: &crate::codestream::CodestreamLayout<'_>, limits: &crate::ResourceLimits)
    -> Result<Part1DecodedImageModel, crate::DecodeError>
{
    part2_decode_layout_input(crate::codestream::decoder_layout_input_view(layout), limits)
}

pub(crate) open spec fn part2_decode_layout_selected(
    layout: &crate::codestream::CodestreamLayout<'_>, requested: &crate::DecodeSelection, limits: &crate::ResourceLimits,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    part2_decode_layout_selected_input(crate::codestream::decoder_layout_input_view(layout), requested, limits)
}

pub struct Part2DecodedLayoutTile {
    pub prepared: Seq<Part1AssemblyTile>,
    pub counters: (u64, u64, u64),
    pub mct_work: u64,
}

pub open spec fn part2_decode_tile_parts_at(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<crate::codestream::TilePartPayload<'_>>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits,
    prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64), work: u64,
) -> Result<Part2DecodedLayoutTile, crate::DecodeError> {
    part2_decode_tile_parts_owned(size, tile, crate::codestream::tile_parts_owned_view(parts), caps, discard, limits, prepared, initial, work)
}

pub open spec fn part2_decode_tile_parts_owned(
    size: &crate::codestream::ImageSize, tile: u16, parts: Seq<Part2OwnedTilePart>,
    caps: Option<(u32, Seq<u16>)>, discard: Option<u8>, limits: &crate::ResourceLimits,
    prepared: Seq<Part1AssemblyTile>, initial: (u64, u64, u64), work: u64,
) -> Result<Part2DecodedLayoutTile, crate::DecodeError> {
    match part2_tile_decode_metadata_owned(parts, crate::codestream::image_size_component_count(size), discard) {
        Err(error) => Err(error),
        Ok(metadata) => {
            let maximum = match discard { None => None, Some(_) => Some(metadata.resolution_counts) };
            let levels = match discard { None => 0u8, Some(levels) => levels };
            match part2_progression_tile_plan_owned(
                size, metadata.first.coding_style, &metadata.first.component_coding_styles,
                metadata.first.component_quantizations, &metadata.first.roi_shifts, (tile, levels),
                (part2_profile_multiple_sets(caps), part2_profile_magnitude_bound(caps), part2_profile_force_ht(caps)), limits,
            ) {
                Err(error) => Err(error),
                Ok(plan) => match part2_planned_tile_accounting(plan, maximum, initial, limits) {
                    Err(error) => Err(error),
                    Ok(counters) => match part2_decode_planned_tile_components_owned(
                        plan, parts, metadata.first, size, metadata.standard, maximum, limits, prepared, work,
                    ) {
                        Err(error) => Err(error),
                        Ok(decoded) => Ok(Part2DecodedLayoutTile {
                            prepared: decoded.prepared, counters, mct_work: decoded.mct_work,
                        }),
                    },
                },
            }
        },
    }
}

pub struct Part2DecodedTileComponents {
    pub prepared: Seq<Part1AssemblyTile>,
    pub mct_work: u64,
}

pub open spec fn part2_precinct_decoder_planes(precincts: Seq<Part1PacketPrecinctState>) -> Seq<Seq<Tier1RawPlane>> {
    Seq::new(precincts.len(), |i: int| precincts[i].decoders.map_values(|decoder: Tier1DecoderState| decoder.plane))
}

pub open spec fn part2_decode_planned_tile_components(
    plan: Part2ProgressionTilePlan, parts: Seq<crate::codestream::TilePartPayload<'_>>,
    first: &crate::codestream::TilePartPayload<'_>, size: &crate::codestream::ImageSize, standard: (bool, bool),
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64,
) -> Result<Part2DecodedTileComponents, crate::DecodeError> {
    part2_decode_planned_tile_components_owned(plan, crate::codestream::tile_parts_owned_view(parts),
        crate::codestream::tile_part_owned_view(first), size, standard, selection, limits, prepared, work)
}

pub open spec fn part2_decode_planned_tile_components_owned(
    plan: Part2ProgressionTilePlan, parts: Seq<Part2OwnedTilePart>, first: Part2OwnedTilePart,
    size: &crate::codestream::ImageSize, standard: (bool, bool),
    selection: Option<Seq<u8>>, limits: &crate::ResourceLimits, prepared: Seq<Part1AssemblyTile>, work: u64,
) -> Result<Part2DecodedTileComponents, crate::DecodeError> {
    let execution = part1_progression_tile_decode_owned(parts, plan.grid, plan.precincts, selection, limits);
    match execution.0 {
        Err(error) => Err(error),
        Ok(_) => {
            let reconstructed = part2_reconstruct_planned_tile(
                prepared, plan.components, part2_precinct_decoder_planes(execution.1), first.component_coding_styles,
                part2_owned_kernel_registry(first.part2_extensions),
                crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
                first.multiple_component_transform, standard, work,
                crate::limits::resource_work_limit(limits), crate::limits::resource_decoded_bytes_limit(limits),
            );
            match reconstructed.0 {
                Err(error) => Err(error),
                Ok(()) => Ok(Part2DecodedTileComponents { prepared: reconstructed.1, mct_work: reconstructed.2 }),
            }
        },
    }
}

pub struct Part2TilePlanBuffers {
    pub precincts: Seq<Part1PacketPrecinctState>,
    pub components: Seq<Part1PreparePlan>,
    pub planned_code_blocks: u64,
}

pub struct Part2ProgressionTilePlan {
    pub tile: u16,
    pub coding_style: crate::codestream::CodingStyle,
    pub coding_styles: crate::codestream::ComponentCodingStyles,
    pub grid: Part1PacketGrid,
    pub precincts: Seq<Part1PacketPrecinctState>,
    pub components: Seq<Part1PreparePlan>,
}

#[verifier::opaque]
pub open spec fn part2_tile_plan_components(
    size: &crate::codestream::ImageSize, coding_style: crate::codestream::CodingStyle,
    styles: &crate::codestream::ComponentCodingStyles, quantizations: (u16, Seq<crate::codestream::Quantization>),
    roi: &crate::codestream::RoiShifts, selection: (u16, u8), policy: (bool, u8, bool),
    limits: &crate::ResourceLimits, grid: Part1PacketGrid, component: u16, before: Part2TilePlanBuffers,
) -> Result<Part2ProgressionTilePlan, crate::DecodeError>
    decreases if component < crate::codestream::image_size_component_count(size) {
        (crate::codestream::image_size_component_count(size) as int - component as int) as nat
    } else { 0nat },
{
    if component >= crate::codestream::image_size_component_count(size) {
        Ok(Part2ProgressionTilePlan {
            tile: selection.0, coding_style, coding_styles: *styles, grid,
            precincts: before.precincts, components: before.components,
        })
    } else {
        match part2_planned_component_owned(size, styles, quantizations, roi, component, selection, policy,
            before.precincts, before.planned_code_blocks, limits) {
            Err(error) => Err(error),
            Ok(planned) => part2_tile_plan_components(size, coding_style, styles, quantizations, roi, selection, policy, limits, grid,
                (component + 1) as u16, Part2TilePlanBuffers {
                    precincts: planned.precincts, components: before.components.push(planned.component),
                    planned_code_blocks: planned.planned_code_blocks,
                }),
        }
    }
}

pub open spec fn part2_progression_tile_plan(
    size: &crate::codestream::ImageSize, coding_style: crate::codestream::CodingStyle,
    styles: &crate::codestream::ComponentCodingStyles, quantizations: &crate::codestream::ComponentQuantizations,
    roi: &crate::codestream::RoiShifts, selection: (u16, u8), policy: (bool, u8, bool), limits: &crate::ResourceLimits,
) -> Result<Part2ProgressionTilePlan, crate::DecodeError> {
    part2_progression_tile_plan_owned(size, coding_style, styles, crate::codestream::quantization_owner_view(quantizations),
        roi, selection, policy, limits)
}

pub open spec fn part2_progression_tile_plan_owned(
    size: &crate::codestream::ImageSize, coding_style: crate::codestream::CodingStyle,
    styles: &crate::codestream::ComponentCodingStyles, quantizations: (u16, Seq<crate::codestream::Quantization>),
    roi: &crate::codestream::RoiShifts, selection: (u16, u8), policy: (bool, u8, bool), limits: &crate::ResourceLimits,
) -> Result<Part2ProgressionTilePlan, crate::DecodeError> {
    match part2_selection_tile_bounds(crate::codestream::selection_geometry_view(size), selection.0) {
        Err(error) => Err(error),
        Ok(_) => match part2_packet_grid_from_components(size, styles, coding_style.layers, limits, Some(selection.0), selection.1) {
            Err(error) => Err(error),
            Ok(grid) => part2_tile_plan_components(size, coding_style, styles, quantizations, roi, selection, policy, limits, grid, 0,
                Part2TilePlanBuffers { precincts: Seq::empty(), components: Seq::empty(), planned_code_blocks: 0 }),
        },
    }
}

pub struct Part2ComponentPlanBuffers {
    pub precincts: Seq<Part1PacketPrecinctState>,
    pub placements: Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub planned_code_blocks: u64,
}

pub struct Part2PlannedComponent {
    pub component: Part1PreparePlan,
    pub precincts: Seq<Part1PacketPrecinctState>,
    pub planned_code_blocks: u64,
}

pub open spec fn part2_component_plan_precinct(
    component: u16, resolution: u8, meta: Part2ComponentPlanMetadata, data: Part2ResolutionPlanMetadata,
    policy: (bool, u8, bool), limits: &crate::ResourceLimits, precinct: u32, before: Part2ComponentPlanBuffers,
) -> Result<Part2ComponentPlanBuffers, crate::DecodeError> {
    match part2_planned_precinct_origin(data.first_precinct, data.geometry.precincts_across, precinct, data.band_size) {
        Err(error) => Err(error),
        Ok(origin) => match part2_planned_precinct(
            [origin[0], origin[1], data.band_size[0], data.band_size[1]], data.block_size, meta.subbands,
            (data.first_subband, data.subband_count), meta.tier1_style, (policy.0, policy.1),
            (component, resolution, precinct, before.precincts.len() as usize), before.placements, before.planned_code_blocks,
            resolution <= meta.output_resolution, limits,
        ) {
            Err(error) => Err(error),
            Ok(planned) => Ok(Part2ComponentPlanBuffers {
                precincts: before.precincts.push(planned.precinct), placements: planned.placements,
                planned_code_blocks: planned.planned_code_blocks,
            }),
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_component_plan_precincts(
    component: u16, resolution: u8, meta: Part2ComponentPlanMetadata, data: Part2ResolutionPlanMetadata,
    policy: (bool, u8, bool), limits: &crate::ResourceLimits, precinct: nat, before: Part2ComponentPlanBuffers,
) -> Result<Part2ComponentPlanBuffers, crate::DecodeError>
    decreases if precinct < data.precincts_in_resolution { (data.precincts_in_resolution as int - precinct) as nat } else { 0nat },
{
    if precinct >= data.precincts_in_resolution { Ok(before) } else {
        match part2_component_plan_precinct(component, resolution, meta, data, policy, limits, precinct as u32, before) {
            Err(error) => Err(error),
            Ok(next) => part2_component_plan_precincts(component, resolution, meta, data, policy, limits, precinct + 1, next),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_component_plan_resolutions(
    size: &crate::codestream::ImageSize, component: u16, tile: u16, meta: Part2ComponentPlanMetadata,
    policy: (bool, u8, bool), limits: &crate::ResourceLimits, resolution: nat, before: Part2ComponentPlanBuffers,
) -> Result<Part2PlannedComponent, crate::DecodeError>
    decreases if resolution <= meta.coding_style.decomposition_levels { (meta.coding_style.decomposition_levels as int + 1 - resolution) as nat } else { 0nat },
{
    if resolution > meta.coding_style.decomposition_levels {
        Ok(Part2PlannedComponent {
            component: Part1PreparePlan {
                component, x: meta.x, y: meta.y, width: meta.width, height: meta.height,
                resolution: meta.output_resolution, subbands: meta.subbands, placements: before.placements,
            },
            precincts: before.precincts, planned_code_blocks: before.planned_code_blocks,
        })
    } else {
        match part2_resolution_plan_metadata(size, meta.coding_style, component, (tile, resolution as u8), [meta.bounds.x0, meta.bounds.y0]) {
            Err(error) => Err(error),
            Ok(data) => match part2_component_plan_precincts(component, resolution as u8, meta, data, policy, limits, 0, before) {
                Err(error) => Err(error),
                Ok(after) => if resolution == u8::MAX { Err(part1_block_placement_error(true)) }
                    else { part2_component_plan_resolutions(size, component, tile, meta, policy, limits, resolution + 1, after) },
            },
        }
    }
}

pub open spec fn part2_planned_component(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    quantizations: &crate::codestream::ComponentQuantizations, roi: &crate::codestream::RoiShifts,
    component: u16, selection: (u16, u8), policy: (bool, u8, bool), precincts: Seq<Part1PacketPrecinctState>,
    total: u64, limits: &crate::ResourceLimits,
) -> Result<Part2PlannedComponent, crate::DecodeError> {
    part2_planned_component_owned(size, styles, crate::codestream::quantization_owner_view(quantizations), roi,
        component, selection, policy, precincts, total, limits)
}

pub open spec fn part2_planned_component_owned(
    size: &crate::codestream::ImageSize, styles: &crate::codestream::ComponentCodingStyles,
    quantizations: (u16, Seq<crate::codestream::Quantization>), roi: &crate::codestream::RoiShifts,
    component: u16, selection: (u16, u8), policy: (bool, u8, bool), precincts: Seq<Part1PacketPrecinctState>,
    total: u64, limits: &crate::ResourceLimits,
) -> Result<Part2PlannedComponent, crate::DecodeError> {
    match part2_component_plan_metadata_owned(size, styles, quantizations, roi, component, selection, policy.2) {
        Err(error) => Err(error),
        Ok(meta) => part2_component_plan_resolutions(size, component, selection.0, meta, policy, limits, 0,
            Part2ComponentPlanBuffers { precincts, placements: Seq::empty(), planned_code_blocks: total }),
    }
}

pub struct Part2ResolutionPlanMetadata {
    pub geometry: crate::decode::ComponentResolutionGeometry,
    pub first_subband: usize,
    pub subband_count: usize,
    pub precincts_in_resolution: u32,
    pub first_precinct: [u32; 2],
    pub band_size: [u32; 2],
    pub block_size: [u32; 2],
}

pub open spec fn part2_planned_precinct_origin(first: [u32; 2], across: u32, precinct: u32, band_size: [u32; 2])
    -> Result<[u32; 2], crate::DecodeError>
{
    if across == 0 { Err(part1_block_placement_error(true)) } else {
        let x = first[0] as nat + precinct as nat % across as nat;
        let y = first[1] as nat + precinct as nat / across as nat;
        let bx = x * band_size[0] as nat;
        let by = y * band_size[1] as nat;
        if x > u32::MAX || y > u32::MAX || bx > u32::MAX || by > u32::MAX {
            Err(part1_block_placement_error(true))
        } else { Ok([bx as u32, by as u32]) }
    }
}

pub open spec fn part2_resolution_plan_finish(
    style: crate::codestream::CodingStyle, geometry: crate::decode::ComponentResolutionGeometry,
    origin: [u32; 2], resolution: u8, first: usize, count: usize, precincts: u32,
) -> Result<Part2ResolutionPlanMetadata, crate::DecodeError> {
    let selector = crate::codestream::decomposition_selector_view(style);
    let pselector = crate::codestream::precinct_selector_view(style);
    match part2_precinct_exponents(pselector.0, pselector.1, resolution) {
        Err(error) => Err(error),
        Ok(p) => if p.0 > 31 || p.1 > 31 { Err(part1_block_placement_error(false)) } else {
            match part2_resolution_downsampling(selector.0, selector.1, resolution) {
                Err(error) => Err(error),
                Ok(scale) => match part2_selection_ceil(origin[0], scale.0) {
                    Err(error) => Err(error),
                    Ok(x0) => match part2_selection_ceil(origin[1], scale.1) {
                        Err(error) => Err(error),
                        Ok(y0) => {
                            let pw = 1u32 << (p.0 as u32);
                            let ph = 1u32 << (p.1 as u32);
                            match part2_selection_floor(x0, pw) {
                                Err(error) => Err(error),
                                Ok(fx) => match part2_selection_floor(y0, ph) {
                                    Err(error) => Err(error),
                                    Ok(fy) => {
                                        let direction = if resolution == 0 { Ok(crate::codestream::DecompositionDirection::None) }
                                            else { part1_direction_for_resolution(selector.0, selector.1, resolution) };
                                        match direction {
                                            Err(error) => Err(error),
                                            Ok(direction) => {
                                                let split_x = matches!(direction, crate::codestream::DecompositionDirection::Horizontal | crate::codestream::DecompositionDirection::TwoDimensional);
                                                let split_y = matches!(direction, crate::codestream::DecompositionDirection::Vertical | crate::codestream::DecompositionDirection::TwoDimensional);
                                                if (split_x && p.0 == 0) || (split_y && p.1 == 0) { Err(part1_block_placement_error(false)) }
                                                else {
                                                    let bx = if split_x { (p.0 - 1) as u8 } else { p.0 };
                                                    let by = if split_y { (p.1 - 1) as u8 } else { p.1 };
                                                    if bx > 31 || by > 31 { Err(part1_block_placement_error(false)) } else {
                                                        let bw = 1u32 << (bx as u32);
                                                        let bh = 1u32 << (by as u32);
                                                        let cw = if bw <= style.code_block_width as u32 { bw } else { style.code_block_width as u32 };
                                                        let ch = if bh <= style.code_block_height as u32 { bh } else { style.code_block_height as u32 };
                                                        if pw == 0 || ph == 0 || cw == 0 || ch == 0 { Err(part1_block_placement_error(false)) }
                                                        else { Ok(Part2ResolutionPlanMetadata {
                                                            geometry, first_subband: first, subband_count: count, precincts_in_resolution: precincts,
                                                            first_precinct: [fx, fy], band_size: [bw, bh], block_size: [cw, ch],
                                                        }) }
                                                    }
                                                }
                                            },
                                        }
                                    },
                                },
                            }
                        },
                    },
                },
            }
        },
    }
}

pub open spec fn part2_resolution_plan_metadata(
    size: &crate::codestream::ImageSize, style: crate::codestream::CodingStyle,
    component: u16, selection: (u16, u8), origin: [u32; 2],
) -> Result<Part2ResolutionPlanMetadata, crate::DecodeError> {
    let selector = crate::codestream::decomposition_selector_view(style);
    match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),
        crate::codestream::image_size_component_count(size), crate::codestream::image_size_component_infos(size),
        crate::decode::resolution_geometry_style(style), component, selection.1, Some(selection.0)) {
        Err(error) => Err(error),
        Ok(geometry) => {
            let first = if selection.1 == 0 { Ok(0usize) } else {
                part1_subband_count_through_resolution(selector.0, selector.1, (selection.1 - 1) as u8)
            };
            match first {
                Err(error) => Err(error),
                Ok(first) => match part1_subband_count_through_resolution(selector.0, selector.1, selection.1) {
                    Err(error) => Err(error),
                    Ok(last) => if last < first { Err(part1_block_placement_error(true)) } else {
                        let count = (last - first) as usize;
                        if count != 0 && geometry.precincts > u32::MAX as u64 { Err(part1_block_placement_error(true)) }
                        else {
                            part2_resolution_plan_finish(style, geometry, origin, selection.1, first, count,
                                if count == 0 { 0u32 } else { geometry.precincts as u32 })
                        }
                    },
                },
            }
        },
    }
}

pub struct Part2PrecinctPlanBuilder {
    pub executions: Seq<Part2PacketSubbandExecution>,
    pub placements: Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub decoder_index: usize,
    pub planned_code_blocks: u64,
}

pub struct Part2PlannedPrecinct {
    pub precinct: Part1PacketPrecinctState,
    pub placements: Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub planned_code_blocks: u64,
}

pub open spec fn part2_planned_precinct_subband(
    band: [u32; 4], block_size: [u32; 2], subbands: Seq<crate::decode::SubbandGeometry>,
    first: usize, local: usize, style: crate::tier1::Tier1CodingStyle, policy: (bool, u8),
    precinct_index: usize, selected: bool, limits: &crate::ResourceLimits, before: Part2PrecinctPlanBuilder,
) -> Result<Part2PrecinctPlanBuilder, crate::DecodeError> {
    let index = first as nat + local as nat;
    if index > usize::MAX { Err(part1_block_placement_error(true)) }
    else if index >= subbands.len() { Err(part1_block_placement_error(false)) }
    else {
        match part2_planned_subband_execution(band, block_size, subbands[index as int], style, policy,
            (precinct_index, index as usize, before.decoder_index), before.placements, before.planned_code_blocks, selected, limits) {
            Err(error) => Err(error),
            Ok(planned) => Ok(Part2PrecinctPlanBuilder {
                executions: match planned.execution { None => before.executions, Some(execution) => before.executions.push(execution) },
                placements: planned.placements, decoder_index: planned.decoder_index, planned_code_blocks: planned.planned_code_blocks,
            }),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_planned_precinct_rows(
    band: [u32; 4], block_size: [u32; 2], subbands: Seq<crate::decode::SubbandGeometry>, range: (usize, usize),
    style: crate::tier1::Tier1CodingStyle, policy: (bool, u8), location: (u16, u8, u32, usize),
    selected: bool, limits: &crate::ResourceLimits, local: nat, builder: Part2PrecinctPlanBuilder,
) -> Result<Part2PlannedPrecinct, crate::DecodeError>
    decreases if local < range.1 { (range.1 as int - local) as nat } else { 0nat },
{
    if local >= range.1 {
        match part2_precinct_from_executions(location.0, location.1, location.2, style, builder.executions, limits) {
            Err(error) => Err(error),
            Ok(precinct) => Ok(Part2PlannedPrecinct { precinct, placements: builder.placements, planned_code_blocks: builder.planned_code_blocks }),
        }
    } else {
        match part2_planned_precinct_subband(band, block_size, subbands, range.0, local as usize,
            style, policy, location.3, selected, limits, builder) {
            Err(error) => Err(error),
            Ok(next) => part2_planned_precinct_rows(band, block_size, subbands, range, style, policy, location, selected, limits, local + 1, next),
        }
    }
}

pub open spec fn part2_planned_precinct(
    band: [u32; 4], block_size: [u32; 2], subbands: Seq<crate::decode::SubbandGeometry>, range: (usize, usize),
    style: crate::tier1::Tier1CodingStyle, policy: (bool, u8), location: (u16, u8, u32, usize),
    placements: Seq<crate::decode::ProgressionCodeBlockPlacement>, total: u64, selected: bool, limits: &crate::ResourceLimits,
) -> Result<Part2PlannedPrecinct, crate::DecodeError> {
    part2_planned_precinct_rows(band, block_size, subbands, range, style, policy, location, selected, limits, 0,
        Part2PrecinctPlanBuilder { executions: Seq::empty(), placements, decoder_index: 0, planned_code_blocks: total })
}

pub struct Part2PlannedSubbandLattice {
    pub grid: [u32; 4],
    pub clip: [u32; 4],
    pub blocks: [u32; 2],
}

pub open spec fn part2_planned_subband_lattice(
    band: [u32; 4], block_size: [u32; 2], subband: crate::decode::SubbandGeometry,
) -> Result<Option<Part2PlannedSubbandLattice>, crate::DecodeError> {
    let start_x = if band[0] >= subband.x0 { band[0] } else { subband.x0 };
    let start_y = if band[1] >= subband.y0 { band[1] } else { subband.y0 };
    match part1_image_checked_u32(subband.x0 as int + subband.width as int) {
        Err(error) => Err(error),
        Ok(sx1) => match part1_image_checked_u32(subband.y0 as int + subband.height as int) {
            Err(error) => Err(error),
            Ok(sy1) => if start_x >= sx1 || start_y >= sy1 { Ok(None) } else {
                match part1_image_checked_u32(band[0] as int + band[2] as int) {
                    Err(error) => Err(error),
                    Ok(bx1) => match part1_image_checked_u32(band[1] as int + band[3] as int) {
                        Err(error) => Err(error),
                        Ok(by1) => {
                            let ex = if bx1 <= sx1 { bx1 } else { sx1 };
                            let ey = if by1 <= sy1 { by1 } else { sy1 };
                            match part2_selection_floor(start_x, block_size[0]) {
                                Err(error) => Err(error),
                                Ok(fx) => match part2_selection_floor(start_y, block_size[1]) {
                                    Err(error) => Err(error),
                                    Ok(fy) => match part2_selection_ceil(ex, block_size[0]) {
                                        Err(error) => Err(error),
                                        Ok(cx) => match part1_image_checked_u32(cx as int - fx as int) {
                                            Err(error) => Err(error),
                                            Ok(across) => match part2_selection_ceil(ey, block_size[1]) {
                                                Err(error) => Err(error),
                                                Ok(cy) => match part1_image_checked_u32(cy as int - fy as int) {
                                                    Err(error) => Err(error),
                                                    Ok(down) => Ok(Some(Part2PlannedSubbandLattice {
                                                        grid: [fx, fy, block_size[0], block_size[1]],
                                                        clip: [start_x, start_y, ex, ey], blocks: [across, down],
                                                    })),
                                                },
                                            },
                                        },
                                    },
                                },
                            }
                        },
                    },
                }
            },
        },
    }
}

pub struct Part2PlannedSubbandExecution {
    pub execution: Option<Part2PacketSubbandExecution>,
    pub placements: Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub decoder_index: usize,
    pub planned_code_blocks: u64,
}

pub open spec fn part2_planned_subband_execution(
    band: [u32; 4], block_size: [u32; 2], subband: crate::decode::SubbandGeometry,
    style: crate::tier1::Tier1CodingStyle, policy: (bool, u8), indices: (usize, usize, usize),
    placements: Seq<crate::decode::ProgressionCodeBlockPlacement>, total: u64, selected: bool, limits: &crate::ResourceLimits,
) -> Result<Part2PlannedSubbandExecution, crate::DecodeError> {
    match part2_planned_subband_lattice(band, block_size, subband) {
        Err(error) => Err(error),
        Ok(None) => Ok(Part2PlannedSubbandExecution { execution: None, placements, decoder_index: indices.2, planned_code_blocks: total }),
        Ok(Some(lattice)) => match part2_planned_codeblocks(
            lattice.grid, lattice.clip, lattice.blocks, subband, style, policy, indices, placements, total, selected, limits,
        ) {
            Err(error) => Err(error),
            Ok(planned) => Ok(Part2PlannedSubbandExecution {
                execution: Some(Part2PacketSubbandExecution {
                    orientation: subband.orientation, across: lattice.blocks[0], down: lattice.blocks[1],
                    maximum_zero: subband.significant_bitplanes, decoders: planned.decoders,
                }),
                placements: planned.placements, decoder_index: planned.decoder_index,
                planned_code_blocks: planned.planned_code_blocks,
            }),
        },
    }
}

pub struct Part2PlannedCodeBlocks {
    pub decoders: Seq<Tier1DecoderState>,
    pub placements: Seq<crate::decode::ProgressionCodeBlockPlacement>,
    pub decoder_index: usize,
    pub planned_code_blocks: u64,
}

pub open spec fn part2_planned_codeblock_cell(
    grid: [u32; 4], clip: [u32; 4], block: [u32; 2],
    subband: crate::decode::SubbandGeometry, style: crate::tier1::Tier1CodingStyle,
    policy: (bool, u8), indices: (usize, usize), before: Part2PlannedCodeBlocks,
) -> Result<Part2PlannedCodeBlocks, crate::DecodeError> {
    match part2_planned_codeblock_geometry(grid, clip, block) {
        Err(error) => Err(error),
        Ok(geometry) => match part2_tier1_configured_decoder(
            geometry.2, geometry.3, subband.significant_bitplanes, subband.orientation, style, policy.0, policy.1,
        ) {
            Err(error) => Err(error),
            Ok(decoder) => {
                let x = geometry.0 as int - subband.x0 as int;
                let y = geometry.1 as int - subband.y0 as int;
                if x < 0 || y < 0 || before.decoder_index == usize::MAX {
                    Err(part1_block_placement_error(true))
                } else {
                    Ok(Part2PlannedCodeBlocks {
                        decoders: before.decoders.push(decoder),
                        placements: before.placements.push(crate::decode::ProgressionCodeBlockPlacement {
                            precinct_index: indices.0, decoder_index: before.decoder_index, subband_index: indices.1,
                            x: x as u32, y: y as u32,
                        }),
                        decoder_index: (before.decoder_index + 1) as usize,
                        planned_code_blocks: before.planned_code_blocks,
                    })
                }
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_planned_codeblock_columns(
    grid: [u32; 4], clip: [u32; 4], across: u32,
    subband: crate::decode::SubbandGeometry, style: crate::tier1::Tier1CodingStyle,
    policy: (bool, u8), indices: (usize, usize), row: u32, column: nat, state: Part2PlannedCodeBlocks,
) -> Result<Part2PlannedCodeBlocks, crate::DecodeError>
    decreases if column < across { (across as int - column) as nat } else { 0nat },
{
    if column >= across { Ok(state) } else {
        match part2_planned_codeblock_cell(grid, clip, [column as u32, row], subband, style, policy, indices, state) {
            Err(error) => Err(error),
            Ok(next) => part2_planned_codeblock_columns(
                grid, clip, across, subband, style, policy, indices, row, column + 1, next),
        }
    }
}

#[verifier::opaque]
pub open spec fn part2_planned_codeblock_rows(
    grid: [u32; 4], clip: [u32; 4], blocks: [u32; 2],
    subband: crate::decode::SubbandGeometry, style: crate::tier1::Tier1CodingStyle,
    policy: (bool, u8), indices: (usize, usize), row: nat, state: Part2PlannedCodeBlocks,
) -> Result<Part2PlannedCodeBlocks, crate::DecodeError>
    decreases if row < blocks[1] { (blocks[1] as int - row) as nat } else { 0nat },
{
    if row >= blocks[1] { Ok(state) } else {
        match part2_planned_codeblock_columns(
            grid, clip, blocks[0], subband, style, policy, indices, row as u32, 0, state,
        ) {
            Err(error) => Err(error),
            Ok(next) => part2_planned_codeblock_rows(grid, clip, blocks, subband, style, policy, indices, row + 1, next),
        }
    }
}

pub open spec fn part2_planned_codeblocks(
    grid: [u32; 4], clip: [u32; 4], blocks: [u32; 2],
    subband: crate::decode::SubbandGeometry, style: crate::tier1::Tier1CodingStyle,
    policy: (bool, u8), indices: (usize, usize, usize),
    placements: Seq<crate::decode::ProgressionCodeBlockPlacement>, total: u64,
    selected: bool, limits: &crate::ResourceLimits,
) -> Result<Part2PlannedCodeBlocks, crate::DecodeError> {
    let count = blocks[0] as nat * blocks[1] as nat;
    let next = if selected { total as nat + count } else { total as nat };
    if count > u64::MAX || next > u64::MAX { Err(part1_block_placement_error(true)) }
    else if selected && next > crate::limits::resource_code_block_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlocks,
            limit: crate::limits::resource_code_block_limit(limits), actual: next as u64 })
    } else if selected && next > crate::limits::resource_work_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
            limit: crate::limits::resource_work_limit(limits), actual: next as u64 })
    } else if count > usize::MAX { Err(part1_block_placement_error(true)) }
    else {
        part2_planned_codeblock_rows(grid, clip, blocks, subband, style, policy, (indices.0, indices.1), 0,
            Part2PlannedCodeBlocks { decoders: Seq::empty(), placements, decoder_index: indices.2,
                planned_code_blocks: next as u64 })
    }
}

pub open spec fn part2_tier1_magnitude_bound(before: Tier1DecoderState, bound: u8)
    -> (Result<(), crate::DecodeError>, Tier1DecoderState)
{
    if bound == 0 || bound > crate::tier1::tier1_max_ht_magnitude_bits() {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), before)
    } else {
        (Ok(()), Tier1DecoderState { ht_magnitude_bound: bound, ..before })
    }
}

pub struct Tier1DecoderState {
    pub plane: Tier1RawPlane,
    pub orientation: crate::tier1::SubbandOrientation,
    pub style: crate::tier1::Tier1CodingStyle,
    pub maximum_passes: u32,
    pub next_pass: u32,
    pub bitplane: u16,
    pub zero_bitplanes: Option<u16>,
    pub bitplane_state: Option<Part1LegacyBitplane>,
    pub mq_context_state: Option<Seq<Part1MqContext>>,
    pub reset_contexts_before_mq: bool,
    pub decoded_segments: u32,
    pub decoded_bytes: u64,
    pub legacy_segment: Option<Tier1LegacyFrame>,
    pub legacy_decode_work: u64,
    pub ht_cleanup_plane: Option<Tier1RawPlane>,
    pub ht_refinement_data: Seq<u8>,
    pub ht_refinement_passes: u8,
    pub ht_decoded_bitplanes: u16,
    pub ht_current_set_has_cleanup: bool,
    pub ht_sets_seen: u16,
    pub allow_multiple_ht_sets: bool,
    pub ht_magnitude_bound: u8,
}

pub open spec fn tier1_duplicate_plane(plane: Tier1RawPlane) -> Result<Tier1RawPlane, crate::DecodeError> {
    match tier1_empty_plane(plane.width, plane.height) {
        Err(error) => Err(error),
        Ok(blank) => if blank.coefficients.len() != plane.coefficients.len() {
            Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
        } else { Ok(plane) },
    }
}

pub open spec fn ht_cleanup_prepare(
    plane: Tier1RawPlane, cleanup: HtCleanupSegmentState, maximum_passes: u32,
    maximum_u: u8, skipped_bitplanes: u16, maximum_work: u64,
) -> Result<(Tier1RawPlane, Tier1RawPlane, crate::tier1::Tier1PassStatistics, u16), crate::DecodeError> {
    match ht_cleanup_segment_metadata(cleanup, plane.width, plane.height, maximum_u, maximum_work) {
        Err(error) => Err(error),
        Ok(metadata) => {
            let significant = (maximum_passes as nat + 2) / 3;
            if maximum_passes as nat + 2 > u32::MAX || significant > u16::MAX
                || significant < skipped_bitplanes {
                Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
            } else {
                let bitplanes = (significant - skipped_bitplanes) as u16;
                match ht_cleanup_plane(plane, cleanup, metadata, maximum_u, bitplanes, maximum_work) {
                    Err(error) => Err(error),
                    Ok((output, statistics)) => match tier1_duplicate_plane(output) {
                        Err(error) => Err(error),
                        Ok(duplicate) => Ok((output, duplicate, statistics, bitplanes)),
                    },
                }
            }
        },
    }
}

pub type HtDecoderResult = (Result<crate::tier1::Tier1SegmentDecode, crate::DecodeError>, Tier1DecoderState);

pub open spec fn ht_store_coefficient_symbols(
    state: Tier1DecoderState, output: Tier1RawPlane, cleanup: Tier1RawPlane,
    statistics: crate::tier1::Tier1PassStatistics, bitplanes: u16,
    passes: u32, bytes: u32, has_refinement: bool,
) -> HtDecoderResult {
    let state = Tier1DecoderState {
        plane: output, ht_cleanup_plane: Some(cleanup),
        ht_current_set_has_cleanup: true, ht_decoded_bitplanes: bitplanes, ..state
    };
    if state.ht_sets_seen == u16::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else {
        let state = Tier1DecoderState { ht_sets_seen: (state.ht_sets_seen + 1) as u16, ..state };
        if state.next_pass as nat + passes as nat > u32::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let state = Tier1DecoderState { next_pass: (state.next_pass + passes) as u32, ..state };
            let segments = if has_refinement { 2nat } else { 1nat };
            if state.decoded_segments as nat + segments > u32::MAX {
                (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
            } else {
                let state = Tier1DecoderState { decoded_segments: (state.decoded_segments + segments) as u32, ..state };
                if state.decoded_bytes as nat + bytes as nat > u64::MAX {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
                } else {
                    let state = Tier1DecoderState { decoded_bytes: (state.decoded_bytes + bytes) as u64, ..state };
                    (Ok(crate::tier1::Tier1SegmentDecode { passes, bytes, statistics }), state)
                }
            }
        }
    }
}

pub open spec fn ht_cleanup_symbols_only(
    state: Tier1DecoderState, segments: HtBlockSegmentsState, passes: u32,
    maximum_u: u8, skipped_bitplanes: u16, maximum_work: u64,
) -> HtDecoderResult {
    match ht_cleanup_prepare(state.plane, segments.cleanup, state.maximum_passes, maximum_u, skipped_bitplanes, maximum_work) {
        Err(error) => (Err(error), state),
        Ok((output, cleanup, statistics, bitplanes)) => ht_store_coefficient_symbols(
            ht_clear_refinement_state(state),
            output, cleanup, statistics, bitplanes, passes, segments.bytes, false),
    }
}

pub open spec fn ht_coefficient_symbols(
    state: Tier1DecoderState, segments: HtBlockSegmentsState, passes: u32,
    maximum_u: u8, skipped_bitplanes: u16, maximum_work: u64,
) -> HtDecoderResult {
    match ht_cleanup_prepare(state.plane, segments.cleanup, state.maximum_passes, maximum_u, skipped_bitplanes, maximum_work) {
        Err(error) => (Err(error), state),
        Ok((output, cleanup, statistics, bitplanes)) => {
            let state = ht_clear_refinement_state(state);
            match segments.refinement {
                None => ht_store_coefficient_symbols(state, output, cleanup, statistics, bitplanes, passes, segments.bytes, false),
                Some(segment) => {
                    let refinement_passes = if passes == 0 { 0nat } else { (passes - 1) as nat };
                    if refinement_passes > u8::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
                    else {
                        match ht_refinement_plane(cleanup, segment, refinement_passes as u8, bitplanes,
                            state.style.vertical_causal_context, maximum_work) {
                            Err(error) => (Err(error), state),
                            Ok((refined, refinement_statistics)) => {
                                let merged = tier1_statistics_merge(statistics, refinement_statistics);
                                match merged.0 {
                                    Err(error) => (Err(error), state),
                                    Ok(()) => match ht_copy_refinement_bytes(segment.encoded) {
                                        Err(error) => (Err(error), state),
                                        Ok(data) => ht_store_coefficient_symbols(Tier1DecoderState {
                                            ht_refinement_data: data, ht_refinement_passes: refinement_passes as u8, ..state },
                                            refined, cleanup, merged.1, bitplanes, passes, segments.bytes, true),
                                    },
                                }
                            },
                        }
                    }
                },
            }
        },
    }
}

pub open spec fn ht_clear_refinement_state(state: Tier1DecoderState) -> Tier1DecoderState {
    Tier1DecoderState { ht_refinement_data: Seq::empty(), ht_refinement_passes: 0, ..state }
}

pub open spec fn ht_significant_bitplanes(maximum_passes: u32) -> Result<u16, crate::DecodeError> {
    let planes = (maximum_passes as nat + 2) / 3;
    if maximum_passes as nat + 2 > u32::MAX || planes > u16::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else { Ok(planes as u16) }
}

pub open spec fn ht_block_coding_enabled(coding: crate::tier1::Tier1BlockCoding) -> bool {
    !matches!(coding, crate::tier1::Tier1BlockCoding::Legacy)
}

pub open spec fn ht_segments_after_parse(
    state: Tier1DecoderState, segments: HtBlockSegmentsState, passes: u32, refinement_passes: u8,
    maximum_bytes: u64, maximum_work: u64,
) -> HtDecoderResult {
    let next_bytes = state.decoded_bytes as nat + segments.bytes as nat;
    let coefficient_work = (state.plane.coefficients.len() as u64) as nat * (refinement_passes as nat + 1);
    let work = coefficient_work + segments.bytes as nat + passes as nat;
    if next_bytes > u64::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else if next_bytes > maximum_bytes {
        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlockBytes,
            limit: maximum_bytes, actual: next_bytes as u64 }), state)
    } else if work > u64::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else if work > maximum_work {
        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
            limit: maximum_work, actual: work as u64 }), state)
    } else {
        let skipped = state.next_pass / 3;
        if skipped > u16::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
        else {
            let missing = match state.zero_bitplanes { None => 0nat, Some(value) => value as nat };
            let maximum_u = part15_cleanup_u_bound(missing, skipped as nat, state.ht_magnitude_bound as nat) as u8;
            ht_coefficient_symbols(state, segments, passes, maximum_u, skipped as u16, maximum_work)
        }
    }
}

pub open spec fn ht_decode_segments(
    state: Tier1DecoderState, cleanup: Seq<u8>, cleanup_passes: u8, refinement: Option<Seq<u8>>,
    refinement_passes: u8, maximum_passes: u32, maximum_bytes: u64, maximum_work: u64,
) -> HtDecoderResult {
    if !ht_block_coding_enabled(state.style.block_coding) || state.next_pass % 3 != 0
        || cleanup_passes != 1 || refinement_passes > 2 || (refinement_passes == 0) != refinement.is_none() {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else if state.ht_sets_seen > 0 && !state.allow_multiple_ht_sets {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else {
        let passes = cleanup_passes as nat + refinement_passes as nat;
        let next = state.next_pass as nat + passes;
        if next > u32::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
        else if next > state.maximum_passes { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
        else if next > maximum_passes {
            (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlockPasses,
                limit: maximum_passes as u64, actual: next as u64 }), state)
        } else {
            match ht_significant_bitplanes(state.maximum_passes) {
                Err(error) => (Err(error), state),
                Ok(bitplanes) => if refinement_passes > 0 && bitplanes < 2 {
                    (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
                } else {
                    match ht_parse_block_segments(cleanup, refinement, maximum_bytes) {
                        Err(error) => (Err(error), state),
                        Ok(segments) => ht_segments_after_parse(state, segments, passes as u32,
                            refinement_passes, maximum_bytes, maximum_work),
                    }
                },
            }
        }
    }
}

pub open spec fn ht_finish_refinement_contribution(
    state: Tier1DecoderState, passes: u8, bytes: nat, next_bytes: u64,
    statistics: crate::tier1::Tier1PassStatistics, replayed: bool,
) -> HtDecoderResult {
    let next = state.next_pass as nat + passes as nat;
    if next > u32::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else {
        let state = Tier1DecoderState { next_pass: next as u32, ..state };
        if state.decoded_segments == u32::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let state = Tier1DecoderState { decoded_segments: (state.decoded_segments + 1) as u32, ..state };
            let state = if replayed { Tier1DecoderState { decoded_bytes: next_bytes, ..state } } else { state };
            if bytes > u32::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
            else { (Ok(crate::tier1::Tier1SegmentDecode { passes: passes as u32, bytes: bytes as u32, statistics }), state) }
        }
    }
}

pub open spec fn ht_decode_refinement_contribution(
    state: Tier1DecoderState, input: Seq<u8>, passes: u8, maximum_bytes: u64, maximum_work: u64,
) -> HtDecoderResult {
    let total = state.ht_refinement_passes as nat + passes as nat;
    if !ht_block_coding_enabled(state.style.block_coding) || state.next_pass == 0
        || !state.ht_current_set_has_cleanup || state.next_pass % 3 == 0 || passes == 0 || total > 2 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else {
        match state.ht_cleanup_plane {
            None => (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
            Some(cleanup) => {
                let next_bytes = state.decoded_bytes as nat + (input.len() as u64) as nat;
                if next_bytes > u64::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
                else if next_bytes > maximum_bytes {
                    (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlockBytes,
                        limit: maximum_bytes, actual: next_bytes as u64 }), state)
                } else {
                    let data = state.ht_refinement_data + input;
                    if data.len() > 2046 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
                    else if data.len() == 0 {
                        ht_finish_refinement_contribution(Tier1DecoderState { ht_refinement_passes: total as u8, ..state },
                            passes, 0, next_bytes as u64, tier1_statistics_zero(), false)
                    } else {
                        let segment = HtRefinementSegmentState {
                            encoded: data,
                            significance_propagation: HtSubstreamState { bytes: data, offset: 0, forward: true },
                            magnitude_refinement: HtSubstreamState { bytes: data, offset: 0, forward: false },
                        };
                        match ht_refinement_plane(cleanup, segment, total as u8, state.ht_decoded_bitplanes,
                            state.style.vertical_causal_context, maximum_work) {
                            Err(error) => (Err(error), state),
                            Ok((plane, statistics)) => ht_finish_refinement_contribution(Tier1DecoderState {
                                plane, ht_refinement_data: data, ht_refinement_passes: total as u8, ..state },
                                passes, input.len(), next_bytes as u64, statistics, true),
                        }
                    }
                }
            },
        }
    }
}

pub open spec fn ht_skip_segment(state: Tier1DecoderState, passes: u8, maximum_passes: u32) -> HtDecoderResult {
    let phase = state.next_pass % 3;
    let next = state.next_pass as nat + passes as nat;
    if !ht_block_coding_enabled(state.style.block_coding) || passes == 0 || passes > 2
        || (phase == 0 && passes != 1) || (phase != 0 && passes as nat > 3 - phase as nat) {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else if next > u32::MAX { (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state) }
    else if next > state.maximum_passes { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else if next > maximum_passes {
        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::CodeBlockPasses,
            limit: maximum_passes as u64, actual: next as u64 }), state)
    } else if phase == 0 {
        if !ht_replacement_allowed(phase as nat, state.ht_current_set_has_cleanup, true)
            || (state.ht_sets_seen > 0 && !ht_multiple_set_allowed(state.ht_sets_seen as nat, state.allow_multiple_ht_sets)) {
            (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
        } else if state.ht_sets_seen == u16::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let state = Tier1DecoderState {
                ht_sets_seen: if state.ht_sets_seen > 0 { (state.ht_sets_seen + 1) as u16 } else { state.ht_sets_seen },
                ht_current_set_has_cleanup: false, ht_refinement_data: Seq::empty(), ht_refinement_passes: 0,
                next_pass: next as u32, ..state
            };
            if state.decoded_segments == u32::MAX {
                (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
            } else {
                let state = Tier1DecoderState { decoded_segments: (state.decoded_segments + 1) as u32, ..state };
                (Ok(crate::tier1::Tier1SegmentDecode { passes: passes as u32, bytes: 0, statistics: tier1_statistics_zero() }), state)
            }
        }
    } else if state.ht_current_set_has_cleanup {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else {
        let state = Tier1DecoderState { next_pass: next as u32, ..state };
        if state.decoded_segments == u32::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let state = Tier1DecoderState { decoded_segments: (state.decoded_segments + 1) as u32, ..state };
            (Ok(crate::tier1::Tier1SegmentDecode { passes: passes as u32, bytes: 0, statistics: tier1_statistics_zero() }), state)
        }
    }
}

pub type HtPlaceholderRunResult = (Result<(), crate::DecodeError>, Tier1DecoderState);

#[verifier::opaque]
pub open spec fn ht_placeholder_group_run(
    state: Tier1DecoderState, remaining: nat, maximum_passes: u32,
) -> HtPlaceholderRunResult
    decreases remaining,
{
    if remaining == 0 { (Ok(()), state) } else {
        let cleanup = ht_skip_segment(state, 1, maximum_passes);
        match cleanup.0 {
            Err(error) => (Err(error), cleanup.1),
            Ok(_) => {
                let refinement = ht_skip_segment(cleanup.1, 2, maximum_passes);
                match refinement.0 {
                    Err(error) => (Err(error), refinement.1),
                    Ok(_) => if remaining < 3 {
                        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), refinement.1)
                    } else { ht_placeholder_group_run(refinement.1, (remaining - 3) as nat, maximum_passes) },
                }
            },
        }
    }
}

pub open spec fn ht_group_route(state: Tier1DecoderState) -> bool {
    matches!(state.style.block_coding, crate::tier1::Tier1BlockCoding::HighThroughput)
        || (matches!(state.style.block_coding, crate::tier1::Tier1BlockCoding::Mixed)
            && state.ht_cleanup_plane.is_some())
}

pub open spec fn ht_decode_staged_group(
    state: Tier1DecoderState, input: Seq<u8>, passes: u8,
    maximum_passes: u32, maximum_bytes: u64, maximum_work: u64,
) -> HtDecoderResult {
    if passes == 0 || input.len() == 0 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else {
        match ht_packet_pass_group(passes) {
            Err(error) => (Err(error), state),
            Ok(group) => if group.refinement_passes != 0 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
            } else {
                let skipped = ht_placeholder_group_run(state, group.placeholder_passes as nat, maximum_passes);
                match skipped.0 {
                    Err(error) => (Err(error), state),
                    Ok(()) => {
                        let decoded = ht_decode_segments(skipped.1, input, 1, None, 0,
                            maximum_passes, maximum_bytes, maximum_work);
                        match decoded.0 {
                            Err(error) => (Err(error), state),
                            Ok(result) => (Ok(crate::tier1::Tier1SegmentDecode { passes: passes as u32, ..result }), decoded.1),
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn part1_tier1_segment(
    state: Tier1DecoderState, input: Seq<u8>, passes: u8,
    pass_limit: u32, byte_limit: u64, input_limit: u64, work_limit: u64,
) -> HtDecoderResult {
    if passes == 0 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else if ht_group_route(state) {
        ht_decode_staged_group(state, input, passes, pass_limit, byte_limit, work_limit)
    } else {
        part1_legacy_segment(state, input, passes as u32, pass_limit, byte_limit, input_limit, work_limit)
    }
}

pub open spec fn ht_has_current_cleanup(state: Tier1DecoderState) -> bool { state.ht_current_set_has_cleanup }

pub open spec fn ht_packet_segment_route(
    state: Tier1DecoderState, body: Seq<u8>, passes: u8,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
) -> HtPlaceholderRunResult {
    let result = if state.next_pass % 3 == 0 {
        if passes != 1 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
        else if body.len() == 0 { ht_skip_segment(state, 1, pass_limit) }
        else { ht_decode_segments(state, body, 1, None, 0, pass_limit, byte_limit, work_limit) }
    } else if state.ht_current_set_has_cleanup {
        ht_decode_refinement_contribution(state, body, passes, byte_limit, work_limit)
    } else if body.len() > 0 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else { ht_skip_segment(state, passes, pass_limit) };
    (match result.0 { Err(error) => Err(error), Ok(_) => Ok(()) }, result.1)
}

pub type HtPacketSegmentResult = (Result<(), crate::DecodeError>, Tier1DecoderState, usize, u32);

pub open spec fn ht_packet_segment_body(
    state: Tier1DecoderState, segment: crate::packet::CodeBlockSegmentContribution, body: Seq<u8>,
    offset: usize, decoded_passes: u32, pass_limit: u32, byte_limit: u64, work_limit: u64,
) -> HtPacketSegmentResult {
    let length = segment.data_length as nat;
    let end = offset as nat + length;
    if segment.passes == 0 || segment.passes > 2 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state, offset, decoded_passes)
    } else if length > usize::MAX || end > usize::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state, offset, decoded_passes)
    } else if offset > body.len() || end > body.len() {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state, offset, decoded_passes)
    } else {
        let result = ht_packet_segment_route(state, body.subrange(offset as int, end as int), segment.passes,
            pass_limit, byte_limit, work_limit);
        match result.0 {
            Err(error) => (Err(error), result.1, offset, decoded_passes),
            Ok(()) => if decoded_passes as nat + segment.passes as nat > u32::MAX {
                (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), result.1, offset, decoded_passes)
            } else {
                (Ok(()), result.1, end as usize, (decoded_passes + segment.passes) as u32)
            },
        }
    }
}

pub struct HtPacketBodyProgress {
    pub segment_index: u8,
    pub offset: usize,
    pub decoded_passes: u32,
}

pub type HtPacketBodyRunResult = (Result<(), crate::DecodeError>, Tier1DecoderState, HtPacketBodyProgress);

#[verifier::opaque]
pub open spec fn ht_packet_body_run(
    state: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>, progress: HtPacketBodyProgress,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
) -> HtPacketBodyRunResult
    decreases header.segment_count as nat - progress.segment_index as nat,
{
    if progress.segment_index >= header.segment_count { (Ok(()), state, progress) }
    else {
        match part1_code_block_segment(header, progress.segment_index) {
            Err(error) => (Err(error), state, progress),
            Ok(segment) => {
                let step = ht_packet_segment_body(state, segment, body, progress.offset, progress.decoded_passes,
                    pass_limit, byte_limit, work_limit);
                let progress = HtPacketBodyProgress {
                    offset: step.2, decoded_passes: step.3, ..progress
                };
                match step.0 {
                    Err(error) => (Err(error), step.1, progress),
                    Ok(()) => if progress.segment_index == u8::MAX {
                        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), step.1, progress)
                    } else {
                        ht_packet_body_run(step.1, header, body, HtPacketBodyProgress {
                            segment_index: (progress.segment_index + 1) as u8, ..progress
                        }, pass_limit, byte_limit, work_limit)
                    },
                }
            },
        }
    }
}

pub type HtCodeBlockBodyResult = (Result<crate::packet::CodeBlockBodyDecode, crate::DecodeError>, Tier1DecoderState);

pub open spec fn ht_packet_body_segments(
    state: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
) -> HtCodeBlockBodyResult {
    if header.segment_count == 0 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else {
        let result = ht_packet_body_run(state, header, body, HtPacketBodyProgress {
            segment_index: 0, offset: 0, decoded_passes: 0,
        }, pass_limit, byte_limit, work_limit);
        match result.0 {
            Err(error) => (Err(error), result.1),
            Ok(()) => if result.2.offset != body.len() || result.2.decoded_passes != header.new_passes {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), result.1)
            } else {
                (Ok(crate::packet::CodeBlockBodyDecode { segments: header.segment_count,
                    passes: result.2.decoded_passes, bytes: header.data_length }), result.1)
            },
        }
    }
}

pub open spec fn ht_packet_body_staged(
    state: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
) -> HtCodeBlockBodyResult {
    let admitted = part1_code_block_body_prepare(state, header, body);
    match admitted.0 { Err(error) => (Err(error), admitted.1), Ok(()) =>
        ht_packet_body_segments(admitted.1, header, body, pass_limit, byte_limit, work_limit) }
}

pub open spec fn ht_packet_body(
    state: Tier1DecoderState, header: Part1CodeBlockContribution, body: Seq<u8>,
    pass_limit: u32, byte_limit: u64, work_limit: u64,
) -> HtCodeBlockBodyResult {
    let result = ht_packet_body_staged(state, header, body, pass_limit, byte_limit, work_limit);
    match result.0 { Err(error) => (Err(error), state), Ok(_) => result }
}

pub type HtPlaneResult = (Result<(), crate::DecodeError>, HtPlaneState);

pub open spec fn ht_plane_sample_store(
    state: HtPlaneState, x: u16, y: u16, sample: u8, column: nat,
    value: nat, negative: bool, exponent: u8,
) -> HtPlaneResult
    recommends column + 1 < state.current.len(),
{
    let store = tier1_mark_coefficient(state.output, x, y, tier1_value_limbs(value), value, negative);
    let state = HtPlaneState { output: store.1, ..state };
    match store.0 {
        Err(error) => (Err(error), state),
        Ok(()) => {
            let count = tier1_statistics_increment(state.statistics, 1, 1);
            let state = HtPlaneState { statistics: count.1, ..state };
            match count.0 {
                Err(error) => (Err(error), state),
                Ok(()) => {
                    let count = tier1_statistics_increment(state.statistics, 2, 1);
                    let state = HtPlaneState { statistics: count.1, ..state };
                    match count.0 {
                        Err(error) => (Err(error), state),
                        Ok(()) => (Ok(()), HtPlaneState {
                            current: if sample == 1 {
                                state.current.update(column as int,
                                    if state.current[column as int] > exponent { state.current[column as int] } else { exponent })
                            } else if sample == 3 { state.current.update((column + 1) as int, exponent) }
                            else { state.current }, ..state
                        }),
                    }
                },
            }
        },
    }
}

pub open spec fn ht_plane_sample(
    state: HtPlaneState, quad: crate::tier1::HtQuadMetadata, width: u16, height: u16,
    column: nat, completed_u: u8, bitplanes: u16, sample: u8,
) -> HtPlaneResult
    recommends sample < 4, column + 1 < state.current.len(),
{
    let x = quad.x as nat + (sample >> 1) as nat;
    let y = quad.y as nat + (sample & 1u8) as nat;
    if x > u16::MAX || y > u16::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else if x >= width || y >= height { (Ok(()), state) }
    else {
        let scanned = tier1_statistics_increment(state.statistics, 0, 1);
        let state = HtPlaneState { statistics: scanned.1, ..state };
        match scanned.0 {
            Err(error) => (Err(error), state),
            Ok(()) => if quad.significance & (1u8 << sample) == 0 { (Ok(()), state) } else {
                let decoded = ht_reconstruct_numeric_magnitude(state.reader, completed_u,
                    quad.embedded_bit_mask & (1u8 << sample) != 0,
                    quad.embedded_magnitude & (1u8 << sample) != 0, bitplanes);
                let state = HtPlaneState { reader: decoded.1, ..state };
                match decoded.0 {
                    Err(error) => (Err(error), state),
                    Ok((value, negative, exponent)) =>
                        ht_plane_sample_store(state, x as u16, y as u16, sample, column, value, negative, exponent),
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn ht_plane_samples(
    state: HtPlaneState, quad: crate::tier1::HtQuadMetadata, width: u16, height: u16,
    column: nat, completed_u: u8, bitplanes: u16, count: nat,
) -> HtPlaneResult
    recommends count <= 4, column + 1 < state.current.len(),
    decreases count,
{
    if count == 0 { (Ok(()), state) } else {
        let prefix = ht_plane_samples(state, quad, width, height, column, completed_u, bitplanes, (count - 1) as nat);
        match prefix.0 { Err(_) => prefix, Ok(()) =>
            ht_plane_sample(prefix.1, quad, width, height, column, completed_u, bitplanes, (count - 1) as u8) }
    }
}

pub open spec fn ht_plane_quad_finish(result: HtPlaneResult, quads_per_row: nat, column: nat) -> HtPlaneResult {
    match result.0 {
        Err(_) => result,
        Ok(()) => (Ok(()), if column + 1 == quads_per_row {
            HtPlaneState { previous: result.1.current, current: result.1.previous, ..result.1 }
        } else { result.1 }),
    }
}

pub open spec fn ht_plane_quad(
    state: HtPlaneState, quad: crate::tier1::HtQuadMetadata, width: u16, height: u16,
    maximum_u: u8, bitplanes: u16, quads_per_row: nat, index: nat,
) -> HtPlaneResult
    recommends 0 < quads_per_row <= 32768, state.current.len() == quads_per_row + 1,
        state.previous.len() == quads_per_row + 1,
{
    let column = index % quads_per_row;
    let state = HtPlaneState { current: if column == 0 { Seq::new(state.current.len(), |i: int| 0u8) }
        else { state.current }, ..state };
    let completed = if quad.initial_row {
        if quad.u_base > maximum_u { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) } else { Ok(quad.u_base) }
    } else { ht_complete_kappa(quad.u_base, quad.significance, state.previous[column as int],
        state.previous[(column + 1) as int], maximum_u) };
    match completed {
        Err(error) => (Err(error), state),
        Ok(value) => {
            let result = ht_plane_samples(state, quad, width, height, column, value, bitplanes, 4);
            ht_plane_quad_finish(result, quads_per_row, column)
        },
    }
}

#[verifier::opaque]
pub open spec fn ht_plane_quads(
    state: HtPlaneState, quads: Seq<crate::tier1::HtQuadMetadata>, width: u16, height: u16,
    maximum_u: u8, bitplanes: u16, quads_per_row: nat, count: nat,
) -> HtPlaneResult
    recommends count <= quads.len(), 0 < quads_per_row <= 32768,
        state.current.len() == quads_per_row + 1, state.previous.len() == quads_per_row + 1,
    decreases count,
{
    if count == 0 { (Ok(()), state) } else {
        let prefix = ht_plane_quads(state, quads, width, height, maximum_u, bitplanes, quads_per_row, (count - 1) as nat);
        match prefix.0 { Err(_) => prefix, Ok(()) =>
            ht_plane_quad(prefix.1, quads[(count - 1) as int], width, height, maximum_u, bitplanes, quads_per_row, (count - 1) as nat) }
    }
}

pub open spec fn ht_plane_finish(state: HtPlaneState) -> HtPlaneResult {
    let finished = ht_magsgn_finish(state.reader);
    (finished.0, HtPlaneState { reader: finished.1, ..state })
}

pub open spec fn ht_plane_output(decoded: HtPlaneResult)
    -> Result<(Tier1RawPlane, crate::tier1::Tier1PassStatistics), crate::DecodeError> {
    match decoded.0 {
        Err(error) => Err(error),
        Ok(()) => {
            let finished = ht_plane_finish(decoded.1);
            match finished.0 { Err(error) => Err(error),
                Ok(()) => Ok((finished.1.output, finished.1.statistics)) }
        },
    }
}

pub open spec fn ht_cleanup_plane(
    plane: Tier1RawPlane, cleanup: HtCleanupSegmentState, metadata: HtMetadataOutput,
    maximum_u: u8, bitplanes: u16, maximum_work: u64,
) -> Result<(Tier1RawPlane, crate::tier1::Tier1PassStatistics), crate::DecodeError> {
    if metadata.width == 0 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else {
        match tier1_empty_plane(plane.width, plane.height) {
            Err(error) => Err(error),
            Ok(output) => match ht_magsgn_initial(cleanup.mag_sgn.bytes, maximum_work) {
                Err(error) => Err(error),
                Ok(reader) => {
                    let quads_per_row = (metadata.width as nat + 1) / 2;
                    if metadata.width as nat + 1 > usize::MAX || quads_per_row + 1 > usize::MAX {
                        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                    } else if quads_per_row == 0 {
                        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
                    } else {
                    let state = HtPlaneState { output, reader,
                        previous: Seq::new(quads_per_row + 1, |i: int| 0u8),
                        current: Seq::new(quads_per_row + 1, |i: int| 0u8),
                        statistics: tier1_statistics_zero(),
                    };
                    let decoded = ht_plane_quads(state, metadata.quads, metadata.width, metadata.height,
                        maximum_u, bitplanes, quads_per_row, metadata.quads.len());
                    ht_plane_output(decoded)
                    }
                },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn ht_numeric_payload(
    reader: HtMagSgnState, remaining: nat, index: nat, value: nat, negative: bool, exponent: u8,
) -> HtNumericMagnitudeResult
    recommends index + remaining <= 75, value < part1_magnitude_capacity(),
    decreases remaining,
{
    if remaining == 0 { (Ok((value, negative, exponent)), reader) } else {
        let read = ht_magsgn_read(reader);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(bit) => if bit {
                let changed = value + pow2(index);
                if changed >= part1_magnitude_capacity() {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), read.1)
                } else {
                    ht_numeric_payload(read.1, (remaining - 1) as nat, index + 1, changed,
                        negative || index == 0, (index + 1) as u8)
                }
            } else {
                ht_numeric_payload(read.1, (remaining - 1) as nat, index + 1, value, negative, exponent)
            },
        }
    }
}

pub open spec fn ht_numeric_center(
    base: nat, negative: bool, exponent: u8, magnitude_bits: u8, embedded_value: bool, decoded_bitplanes: u16,
) -> Result<(nat, bool, u8), crate::DecodeError>
    recommends magnitude_bits <= 75, 1 <= decoded_bitplanes <= 292,
{
    let embedded = if embedded_value { base + pow2(magnitude_bits as nat) } else { base };
    let exp = if embedded_value { (magnitude_bits + 1) as u8 } else { exponent };
    if embedded >= part1_magnitude_capacity() {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else {
        let odd = if embedded % 2 == 0 { embedded + 1 } else { embedded };
        let exp = if embedded % 2 == 0 && exp < 1 { 1u8 } else { exp };
        let centered = odd + 2;
        let scaled = centered * pow2((decoded_bitplanes - 1) as nat);
        if odd >= part1_magnitude_capacity() || centered >= part1_magnitude_capacity()
            || scaled >= part1_magnitude_capacity() {
            Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
        } else if scaled / 2 == 0 {
            Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
        } else { Ok(((scaled / 2) as nat, negative, exp)) }
    }
}

pub open spec fn ht_numeric_finish(
    payload: HtNumericMagnitudeResult, magnitude_bits: u8, embedded_value: bool, decoded_bitplanes: u16,
) -> HtNumericMagnitudeResult
    recommends magnitude_bits <= 75, 1 <= decoded_bitplanes <= 292,
{
    (match payload.0 {
        Err(error) => Err(error),
        Ok((base, negative, exponent)) => ht_numeric_center(base, negative, exponent, magnitude_bits, embedded_value, decoded_bitplanes),
    }, payload.1)
}

pub open spec fn ht_reconstruct_numeric_magnitude(
    reader: HtMagSgnState, completed_u: u8, embedded_bit: bool, embedded_value: bool, decoded_bitplanes: u16,
) -> HtNumericMagnitudeResult {
    if completed_u == 0 || completed_u > 75 || decoded_bitplanes == 0 || decoded_bitplanes > 292 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), reader)
    } else {
        let bits = ht_magnitude_payload_bits(completed_u as nat, embedded_bit) as u8;
        ht_numeric_finish(ht_numeric_payload(reader, bits as nat, 0, 0, false, 0),
            bits, embedded_value, decoded_bitplanes)
    }
}

pub struct HtMetadataWordsState {
    pub readers: HtCleanupReaderState,
    pub current: Seq<u8>,
    pub left: u8,
    pub words: Seq<u16>,
    pub contexts: Seq<u8>,
}

pub type HtMetadataWordsResult = (
    Result<(Seq<u16>, Seq<u8>), crate::DecodeError>, HtCleanupReaderState, Seq<u8>, u8,
);

pub open spec fn ht_metadata_context(previous: Seq<u8>, left: u8, index: nat, initial: bool) -> u8
    recommends index < previous.len(),
{
    if initial { left } else {
        ht_noninitial_vlc_context(left,
            if index > 0 { previous[(index - 1) as int] } else { 0 },
            previous[index as int],
            if index + 1 < previous.len() { previous[(index + 1) as int] } else { 0 })
    }
}

pub open spec fn ht_metadata_left(significance: u8, initial: bool) -> u8 {
    if initial { (significance & 1u8) | ((significance & 0x0eu8) >> 1u8) }
    else if significance & 0x0cu8 != 0 { 2 } else { 0 }
}

#[verifier::opaque]
pub open spec fn ht_metadata_words_run(
    state: HtMetadataWordsState, previous: Seq<u8>, pair: nat, initial: bool, member: nat,
) -> (Result<(), crate::DecodeError>, HtMetadataWordsState)
    recommends member <= 2, state.words.len() == 2, state.contexts.len() == 2,
        state.current.len() == previous.len(),
    decreases 2nat - member,
{
    if member >= 2 || pair + member >= previous.len() { (Ok(()), state) } else {
        let index = pair + member;
        let context = ht_metadata_context(previous, state.left, index, initial);
        let read = ht_cleanup_quad_word(state.readers, crate::tier1::ht_vlc_table_view(initial), context);
        let consumed = HtMetadataWordsState { readers: read.1, ..state };
        match read.0 {
            Err(error) => (Err(error), consumed),
            Ok(word) => {
                let significance = ((word >> 4u16) & 0x0fu16) as u8;
                ht_metadata_words_run(HtMetadataWordsState {
                    current: state.current.update(index as int, significance),
                    left: ht_metadata_left(significance, initial),
                    words: state.words.update(member as int, word),
                    contexts: state.contexts.update(member as int, context), ..consumed
                }, previous, pair, initial, member + 1)
            },
        }
    }
}

pub open spec fn ht_metadata_words_finish(result: (Result<(), crate::DecodeError>, HtMetadataWordsState))
    -> HtMetadataWordsResult
{
    (match result.0 { Err(error) => Err(error), Ok(()) => Ok((result.1.words, result.1.contexts)) },
        result.1.readers, result.1.current, result.1.left)
}

pub open spec fn ht_metadata_words(
    readers: HtCleanupReaderState, current: Seq<u8>, left: u8,
    previous: Seq<u8>, pair: nat, initial: bool,
) -> HtMetadataWordsResult
    recommends current.len() == previous.len(),
{
    ht_metadata_words_finish(ht_metadata_words_run(HtMetadataWordsState {
        readers, current, left, words: Seq::new(2, |i: int| 0u16), contexts: Seq::new(2, |i: int| 0u8),
    }, previous, pair, initial, 0))
}

pub struct HtMetadataQuadInput {
    pub index: usize,
    pub row: usize,
    pub width: u16,
    pub height: u16,
    pub maximum_u: u8,
    pub word: u16,
    pub context: u8,
    pub significance: u8,
    pub u_value: u8,
    pub initial: bool,
}

#[verifier::opaque]
pub open spec fn ht_metadata_samples(
    significant: u16, significance: u8, x: u16, y: u16, width: u16, height: u16, sample: u8,
) -> (Result<(), crate::DecodeError>, u16)
    recommends sample <= 4, x <= 65534, y <= 65534,
    decreases 4nat - sample,
{
    if sample >= 4 { (Ok(()), significant) }
    else if significance & (1u8 << sample) == 0 {
        ht_metadata_samples(significant, significance, x, y, width, height, (sample + 1) as u8)
    } else if x as nat + (sample >> 1u8) as nat >= width
        || y as nat + (sample & 1u8) as nat >= height {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), significant)
    } else if significant == u16::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), significant)
    } else {
        ht_metadata_samples((significant + 1) as u16, significance, x, y, width, height, (sample + 1) as u8)
    }
}

pub type HtMetadataEmitResult = (
    Result<(), crate::DecodeError>, HtCleanupReaderState, Seq<crate::tier1::HtQuadMetadata>, u16,
);

pub open spec fn ht_metadata_emit_after_samples(
    result: (Result<(), crate::DecodeError>, u16),
    readers: HtCleanupReaderState, quads: Seq<crate::tier1::HtQuadMetadata>, input: HtMetadataQuadInput,
) -> HtMetadataEmitResult {
    match result.0 {
        Err(error) => (Err(error), readers, quads, result.1),
        Ok(()) => {
            let quad = crate::tier1::HtQuadMetadata {
                x: (input.index * 2) as u16, y: (input.row * 2) as u16,
                context: input.context, initial_row: input.initial,
                significance: input.significance,
                embedded_magnitude: ((input.word >> 8u16) & 0x0fu16) as u8,
                embedded_bit_mask: ((input.word >> 12u16) & 0x0fu16) as u8,
                u_offset: input.word & 8u16 != 0, u_base: input.u_value,
                codeword_bits: (input.word & 7u16) as u8,
            };
            let tick = ht_cleanup_reader_tick(readers);
            (tick.0, tick.1, quads.push(quad), result.1)
        },
    }
}

pub open spec fn ht_metadata_emit(
    readers: HtCleanupReaderState, quads: Seq<crate::tier1::HtQuadMetadata>,
    significant: u16, input: HtMetadataQuadInput,
) -> HtMetadataEmitResult
    recommends input.index < 32768, input.row < 32768,
{
    let x = (input.index * 2) as u16;
    let y = (input.row * 2) as u16;
    if input.u_value > input.maximum_u
        || !ht_quad_origin_valid(x as nat, y as nat, input.width as nat, input.height as nat) {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), readers, quads, significant)
    } else {
        ht_metadata_emit_after_samples(ht_metadata_samples(significant, input.significance, x, y,
            input.width, input.height, 0), readers, quads, input)
    }
}

pub struct HtMetadataPairState {
    pub readers: HtCleanupReaderState,
    pub quads: Seq<crate::tier1::HtQuadMetadata>,
    pub current: Seq<u8>,
    pub significant: u16,
    pub left: u8,
}

pub open spec fn ht_metadata_u_values(readers: HtCleanupReaderState, words: Seq<u16>, initial: bool)
    -> (Result<[u8; 2], crate::DecodeError>, HtCleanupReaderState)
    recommends words.len() == 2,
{
    let mode = (if words[0] & 8u16 != 0 { 1u8 } else { 0u8 })
        | (if words[1] & 8u16 != 0 { 2u8 } else { 0u8 });
    let event = if initial && mode == 3 { ht_cleanup_mel_event(readers) } else { (Ok(false), readers) };
    match event.0 {
        Err(error) => (Err(error), event.1),
        Ok(four) => {
            let selected = if four { 4u8 } else { mode };
            if initial { ht_uvlc_initial(event.1, selected) } else { ht_uvlc_non_initial(event.1, selected) }
        },
    }
}

#[verifier::opaque]
pub open spec fn ht_metadata_emits_run(
    state: HtMetadataPairState, words: Seq<u16>, contexts: Seq<u8>, values: [u8; 2],
    pair: nat, row: nat, width: u16, height: u16, maximum_u: u8, initial: bool, member: nat,
) -> (Result<(), crate::DecodeError>, HtMetadataPairState)
    recommends member <= 2, words.len() == 2, contexts.len() == 2, pair < 32768, row < 32768,
        state.current.len() <= 32768,
    decreases 2nat - member,
{
    if member >= 2 || pair + member >= state.current.len() { (Ok(()), state) } else {
        let index = pair + member;
        let emit = ht_metadata_emit(state.readers, state.quads, state.significant, HtMetadataQuadInput {
            index: index as usize, row: row as usize, width, height, maximum_u,
            word: words[member as int], context: contexts[member as int],
            significance: state.current[index as int], u_value: values[member as int], initial,
        });
        let changed = HtMetadataPairState {
            readers: emit.1, quads: emit.2, significant: emit.3, ..state
        };
        match emit.0 {
            Err(error) => (Err(error), changed),
            Ok(()) => ht_metadata_emits_run(changed, words, contexts, values,
                pair, row, width, height, maximum_u, initial, member + 1),
        }
    }
}

pub open spec fn ht_metadata_pair_after_words(
    words: HtMetadataWordsResult, quads: Seq<crate::tier1::HtQuadMetadata>, significant: u16,
    pair: nat, row: nat, width: u16, height: u16, maximum_u: u8, initial: bool,
) -> (Result<(), crate::DecodeError>, HtMetadataPairState)
    recommends pair < 32768, row < 32768, words.2.len() <= 32768,
{
    let changed = HtMetadataPairState { readers: words.1, quads, significant, current: words.2, left: words.3 };
    match words.0 {
        Err(error) => (Err(error), changed),
        Ok((cache, contexts)) => {
            let values = ht_metadata_u_values(changed.readers, cache, initial);
            let consumed = HtMetadataPairState { readers: values.1, ..changed };
            match values.0 {
                Err(error) => (Err(error), consumed),
                Ok(values) => ht_metadata_emits_run(consumed, cache, contexts, values,
                    pair, row, width, height, maximum_u, initial, 0),
            }
        },
    }
}

pub open spec fn ht_metadata_pair(
    state: HtMetadataPairState, previous: Seq<u8>,
    pair: nat, row: nat, width: u16, height: u16, maximum_u: u8, initial: bool,
) -> (Result<(), crate::DecodeError>, HtMetadataPairState)
    recommends pair < 32768, row < 32768, state.current.len() == previous.len() <= 32768,
{
    ht_metadata_pair_after_words(
        ht_metadata_words(state.readers, state.current, state.left, previous, pair, initial),
        state.quads, state.significant, pair, row, width, height, maximum_u, initial)
}

pub struct HtMetadataRowState {
    pub readers: HtCleanupReaderState,
    pub quads: Seq<crate::tier1::HtQuadMetadata>,
    pub previous: Seq<u8>,
    pub significant: u16,
}

#[verifier::opaque]
pub open spec fn ht_metadata_pairs(
    state: HtMetadataPairState, previous: Seq<u8>, row: nat,
    width: u16, height: u16, maximum_u: u8, count: nat,
) -> (Result<(), crate::DecodeError>, HtMetadataPairState)
    recommends 0 < previous.len() <= 32768, state.current.len() == previous.len(),
        row < 32768, count <= (previous.len() + 1) / 2,
    decreases count,
{
    if count == 0 { (Ok(()), state) } else {
        let prefix = ht_metadata_pairs(state, previous, row, width, height, maximum_u, (count - 1) as nat);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(()) => ht_metadata_pair(prefix.1, previous, 2 * ((count - 1) as nat), row, width, height, maximum_u, row == 0),
        }
    }
}

pub open spec fn ht_metadata_row_initial(state: HtMetadataRowState) -> HtMetadataPairState {
    HtMetadataPairState {
        readers: state.readers, quads: state.quads, significant: state.significant,
        current: Seq::new(state.previous.len(), |i: int| 0u8), left: 0,
    }
}

pub open spec fn ht_metadata_row_finish(
    result: (Result<(), crate::DecodeError>, HtMetadataPairState), previous: Seq<u8>,
) -> (Result<(), crate::DecodeError>, HtMetadataRowState) {
    (result.0, HtMetadataRowState {
        readers: result.1.readers, quads: result.1.quads, significant: result.1.significant,
        previous: if result.0.is_ok() { result.1.current } else { previous },
    })
}

pub open spec fn ht_metadata_row(
    state: HtMetadataRowState, row: nat, width: u16, height: u16, maximum_u: u8,
) -> (Result<(), crate::DecodeError>, HtMetadataRowState)
    recommends 0 < state.previous.len() <= 32768, row < 32768,
{
    ht_metadata_row_finish(ht_metadata_pairs(ht_metadata_row_initial(state), state.previous, row,
        width, height, maximum_u, (state.previous.len() + 1) / 2), state.previous)
}

#[verifier::opaque]
pub open spec fn ht_metadata_rows(
    state: HtMetadataRowState, width: u16, height: u16, maximum_u: u8, count: nat,
) -> (Result<(), crate::DecodeError>, HtMetadataRowState)
    recommends 0 < state.previous.len() <= 32768, count <= 32768,
    decreases count,
{
    if count == 0 { (Ok(()), state) } else {
        let prefix = ht_metadata_rows(state, width, height, maximum_u, (count - 1) as nat);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(()) => ht_metadata_row(prefix.1, (count - 1) as nat, width, height, maximum_u),
        }
    }
}

pub struct HtMetadataOutput {
    pub width: u16,
    pub height: u16,
    pub quads: Seq<crate::tier1::HtQuadMetadata>,
    pub significant_samples: u16,
    pub mel_bits: u32,
    pub vlc_bits: u32,
    pub mel_events: u32,
}

pub open spec fn ht_metadata_finish(
    result: (Result<(), crate::DecodeError>, HtMetadataRowState), width: u16, height: u16,
) -> Result<HtMetadataOutput, crate::DecodeError> {
    match result.0 {
        Err(error) => Err(error),
        Ok(()) => {
            let state = result.1;
            match ht_cleanup_readers_finish(state.readers) {
                Err(error) => Err(error),
                Ok(()) => if state.readers.mel.bits_read > u32::MAX || state.readers.vlc.bits_read > u32::MAX {
                    Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
                } else {
                    Ok(HtMetadataOutput {
                        width, height, quads: state.quads, significant_samples: state.significant,
                        mel_bits: state.readers.mel.bits_read as u32, vlc_bits: state.readers.vlc.bits_read as u32,
                        mel_events: state.readers.mel_events,
                    })
                },
            }
        },
    }
}

pub open spec fn ht_cleanup_segment_metadata(
    cleanup: HtCleanupSegmentState, width: u16, height: u16, maximum_u: u8, maximum_work: u64,
) -> Result<HtMetadataOutput, crate::DecodeError> {
    if width == 0 || height == 0 || maximum_u == 0 || maximum_u > 75 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else if width as nat * height as nat > u32::MAX {
        Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))
    } else if width as nat * height as nat > 4096 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        match ht_cleanup_readers_initial(cleanup.mel.bytes, cleanup.vlc.bytes, maximum_work) {
            Err(error) => Err(error),
            Ok(readers) => ht_metadata_finish(ht_metadata_rows(HtMetadataRowState {
                readers, quads: Seq::empty(), significant: 0,
                previous: Seq::new((width as nat + 1) / 2, |i: int| 0u8),
            }, width, height, maximum_u, (height as nat + 1) / 2), width, height),
        }
    }
}

pub open spec fn ht_decode_cleanup_metadata(
    cleanup: Seq<u8>, width: u16, height: u16, maximum_u: u8, maximum_bytes: u64, maximum_work: u64,
) -> Result<HtMetadataOutput, crate::DecodeError> {
    match ht_parse_block_segments(cleanup, None, maximum_bytes) {
        Err(error) => Err(error),
        Ok(segments) => ht_cleanup_segment_metadata(segments.cleanup, width, height, maximum_u, maximum_work),
    }
}

pub struct HtSubstreamState {
    pub bytes: Seq<u8>,
    pub offset: u32,
    pub forward: bool,
}

pub struct HtCleanupSegmentState {
    pub encoded: Seq<u8>,
    pub scup: u16,
    pub mag_sgn: HtSubstreamState,
    pub mel_vlc: HtSubstreamState,
    pub mel: HtSubstreamState,
    pub vlc: HtSubstreamState,
}

pub struct HtRefinementSegmentState {
    pub encoded: Seq<u8>,
    pub significance_propagation: HtSubstreamState,
    pub magnitude_refinement: HtSubstreamState,
}

pub struct HtBlockSegmentsState {
    pub cleanup: HtCleanupSegmentState,
    pub refinement: Option<HtRefinementSegmentState>,
    pub bytes: u32,
}

pub open spec fn ht_parse_block_segments(
    cleanup: Seq<u8>, refinement: Option<Seq<u8>>, maximum_bytes: u64,
) -> Result<HtBlockSegmentsState, crate::DecodeError> {
    let refinement_length = match refinement { None => 0nat, Some(bytes) => bytes.len() };
    if cleanup.len() < 2 || cleanup.len() > 65534 || refinement_length > 2046 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        let total = cleanup.len() + refinement_length;
        if total > maximum_bytes {
            Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::CodeBlockBytes, limit: maximum_bytes, actual: total as u64,
            })
        } else {
            let scup = ht_scup(cleanup[(cleanup.len() - 2) as int], cleanup[(cleanup.len() - 1) as int]);
            if scup < 2 || scup > 4079 || scup > cleanup.len() {
                Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
            } else {
                let start = (cleanup.len() - scup) as int;
                let offset = start as u32;
                let suffix = cleanup.subrange(start, cleanup.len() as int);
                Ok(HtBlockSegmentsState {
                    cleanup: HtCleanupSegmentState {
                        encoded: cleanup, scup: scup as u16,
                        mag_sgn: HtSubstreamState { bytes: cleanup.subrange(0, start), offset: 0, forward: true },
                        mel_vlc: HtSubstreamState { bytes: suffix, offset, forward: true },
                        mel: HtSubstreamState { bytes: cleanup.subrange(start, (cleanup.len() - 1) as int), offset, forward: true },
                        vlc: HtSubstreamState { bytes: suffix, offset, forward: false },
                    },
                    refinement: match refinement {
                        None => None,
                        Some(bytes) => Some(HtRefinementSegmentState {
                            encoded: bytes,
                            significance_propagation: HtSubstreamState { bytes, offset: cleanup.len() as u32, forward: true },
                            magnitude_refinement: HtSubstreamState { bytes, offset: cleanup.len() as u32, forward: false },
                        }),
                    },
                    bytes: total as u32,
                })
            }
        }
    }
}

pub open spec fn ht_packet_pass_group(passes: u8) -> Result<crate::tier1::HtPassGroup, crate::DecodeError> {
    if passes == 0 || passes > 164 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        let placeholders = ht_placeholder_passes(passes as nat);
        Ok(crate::tier1::HtPassGroup {
            cleanup_passes: (placeholders + 1) as u8,
            refinement_passes: (ht_substantive_passes(passes as nat) - 1) as u8,
            placeholder_passes: placeholders as u8,
            skipped_bitplanes: (placeholders / 3) as u8,
        })
    }
}

pub struct HtMagSgnState {
    pub input: Seq<u8>,
    pub next_byte: usize,
    pub value: u8,
    pub next_bit: u8,
    pub last_bit: u8,
    pub has_byte: bool,
    pub current_is_physical: bool,
    pub previous_was_ff: bool,
    pub physical_bits_read: u64,
    pub fill_bits_read: u64,
    pub work_units: u64,
    pub maximum_work_units: u64,
}

pub open spec fn ht_magsgn_initial(input: Seq<u8>, maximum_work_units: u64)
    -> Result<HtMagSgnState, crate::DecodeError>
{
    if input.len() > 65534 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        Ok(HtMagSgnState {
            input, next_byte: 0, value: 0, next_bit: 0, last_bit: 0, has_byte: false,
            current_is_physical: false, previous_was_ff: false,
            physical_bits_read: 0, fill_bits_read: 0, work_units: 0, maximum_work_units,
        })
    }
}

pub open spec fn ht_magsgn_load(state: HtMagSgnState)
    -> (Result<(), crate::DecodeError>, HtMagSgnState)
{
    let physical = state.next_byte < state.input.len();
    let value = if physical { state.input[state.next_byte as int] } else { 0xffu8 };
    if physical && !ht_forward_stuffing_valid(state.previous_was_ff, value) {
        (Err(crate::DecodeError::MalformedInput {
            offset: state.next_byte as u64, kind: crate::MalformedKind::InvalidBitStuffing,
        }), state)
    } else {
        let changed = HtMagSgnState { value, current_is_physical: physical, ..state };
        if physical && state.next_byte == usize::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), changed)
        } else {
            (Ok(()), HtMagSgnState {
                next_byte: if physical { (state.next_byte + 1) as usize } else { state.next_byte },
                next_bit: 0, last_bit: (ht_forward_data_bits(state.previous_was_ff) - 1) as u8,
                has_byte: true, previous_was_ff: value == 0xff, ..changed
            })
        }
    }
}

pub open spec fn ht_magsgn_read(state: HtMagSgnState)
    -> (Result<bool, crate::DecodeError>, HtMagSgnState)
{
    let loaded = if !state.has_byte || state.next_bit > state.last_bit {
        ht_magsgn_load(state)
    } else { (Ok(()), state) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => {
            let ready = loaded.1;
            if !ready.has_byte || ready.next_bit > ready.last_bit || ready.next_bit >= 8 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), ready)
            } else {
                let advanced = HtMagSgnState { next_bit: (ready.next_bit + 1) as u8, ..ready };
                let counter = if ready.current_is_physical { ready.physical_bits_read } else { ready.fill_bits_read };
                if counter == u64::MAX {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), advanced)
                } else {
                    let consumed = HtMagSgnState {
                        physical_bits_read: if ready.current_is_physical { (counter + 1) as u64 } else { ready.physical_bits_read },
                        fill_bits_read: if ready.current_is_physical { ready.fill_bits_read } else { (counter + 1) as u64 },
                        ..advanced
                    };
                    if ready.work_units == u64::MAX {
                        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), consumed)
                    } else {
                        let charged = HtMagSgnState { work_units: (ready.work_units + 1) as u64, ..consumed };
                        if charged.work_units > ready.maximum_work_units {
                            (Err(ht_reader_work_error(ready.maximum_work_units, charged.work_units)), charged)
                        } else {
                            (Ok(ht_reader_bit(ready.value, ready.next_bit)), charged)
                        }
                    }
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn ht_magsgn_word_run(state: HtMagSgnState, remaining: nat, index: nat, value: u64)
    -> (Result<u64, crate::DecodeError>, HtMagSgnState)
    recommends index + remaining <= 39,
    decreases remaining,
{
    if remaining == 0 { (Ok(value), state) } else {
        let read = ht_magsgn_read(state);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(bit) => ht_magsgn_word_run(read.1, (remaining - 1) as nat, index + 1,
                if bit { value | (1u64 << index as u8) } else { value }),
        }
    }
}

pub open spec fn ht_magsgn_read_bits(state: HtMagSgnState, count: u8)
    -> (Result<u64, crate::DecodeError>, HtMagSgnState)
{
    if count > 39 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else { ht_magsgn_word_run(state, count as nat, 0, 0) }
}

pub open spec fn ht_magsgn_pending(state: HtMagSgnState) -> bool {
    (state.has_byte && state.current_is_physical && state.next_bit <= state.last_bit)
        || state.next_byte < state.input.len()
}

#[verifier::opaque]
pub open spec fn ht_magsgn_finish_run(state: HtMagSgnState, remaining: nat)
    -> (Result<(), crate::DecodeError>, HtMagSgnState)
    decreases remaining,
{
    if !ht_magsgn_pending(state) { (Ok(()), state) }
    else if remaining == 0 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else {
        let read = ht_magsgn_read(state);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(false) => (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), read.1),
            Ok(true) => ht_magsgn_finish_run(read.1, (remaining - 1) as nat),
        }
    }
}

pub open spec fn ht_magsgn_finish(state: HtMagSgnState)
    -> (Result<(), crate::DecodeError>, HtMagSgnState)
{
    if state.input.len() * 8 > usize::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else { ht_magsgn_finish_run(state, state.input.len() * 8) }
}

pub struct HtForwardRefinementState {
    pub input: Seq<u8>,
    pub next_byte: usize,
    pub current_byte: usize,
    pub value: u8,
    pub next_bit: u8,
    pub last_bit: u8,
    pub has_byte: bool,
    pub previous_was_ff: bool,
    pub physical_bits_read: u64,
    pub fill_bits_read: u64,
    pub maximum_work_units: u64,
}

pub struct HtReverseRefinementState {
    pub input: Seq<u8>,
    pub current_byte: usize,
    pub value: u8,
    pub next_bit: u8,
    pub last_bit: u8,
    pub has_byte: bool,
    pub later_requires_unstuffing: bool,
    pub physical_bits_read: u64,
    pub fill_bits_read: u64,
    pub maximum_work_units: u64,
}

pub type HtPositionedRead = Result<(bool, Option<crate::tier1::HtBitPosition>), crate::DecodeError>;

pub open spec fn ht_refinement_work(physical: u64, fill: u64, maximum: u64) -> Result<(), crate::DecodeError> {
    if physical + fill > u64::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else if physical + fill > maximum { Err(ht_reader_work_error(maximum, (physical + fill) as u64)) }
    else { Ok(()) }
}

pub open spec fn ht_forward_refinement_initial(input: Seq<u8>, maximum_work_units: u64)
    -> Result<HtForwardRefinementState, crate::DecodeError>
{
    if input.len() > 2046 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else { Ok(HtForwardRefinementState {
        input, next_byte: 0, current_byte: 0, value: 0, next_bit: 0, last_bit: 0,
        has_byte: false, previous_was_ff: false, physical_bits_read: 0, fill_bits_read: 0, maximum_work_units,
    }) }
}

pub open spec fn ht_forward_refinement_load(state: HtForwardRefinementState)
    -> (Result<(), crate::DecodeError>, HtForwardRefinementState)
{
    let physical = state.next_byte < state.input.len();
    let value = if physical { state.input[state.next_byte as int] } else { 0u8 };
    if physical && state.previous_was_ff && value & 0x80u8 != 0 {
        (Err(crate::DecodeError::MalformedInput {
            offset: state.next_byte as u64, kind: crate::MalformedKind::InvalidBitStuffing,
        }), state)
    } else {
        let changed = HtForwardRefinementState {
            current_byte: if physical { state.next_byte } else { state.input.len() as usize },
            value, ..state
        };
        if physical && state.next_byte == usize::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), changed)
        } else {
            (Ok(()), HtForwardRefinementState {
                next_byte: if physical { (state.next_byte + 1) as usize } else { state.next_byte },
                next_bit: 0, last_bit: if state.previous_was_ff { 6 } else { 7 },
                has_byte: true, previous_was_ff: value == 0xff, ..changed
            })
        }
    }
}

pub open spec fn ht_forward_refinement_positioned(state: HtForwardRefinementState)
    -> (HtPositionedRead, HtForwardRefinementState)
{
    let loaded = if !state.has_byte || state.next_bit > state.last_bit {
        ht_forward_refinement_load(state)
    } else { (Ok(()), state) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => {
            let ready = loaded.1;
            if !ready.has_byte || ready.next_bit > ready.last_bit || ready.next_bit >= 8 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), ready)
            } else {
                let physical = ready.current_byte < ready.input.len();
                let position = if physical {
                    Some(crate::tier1::HtBitPosition { byte: ready.current_byte as u16, bit: ready.next_bit })
                } else { None };
                let advanced = HtForwardRefinementState { next_bit: (ready.next_bit + 1) as u8, ..ready };
                let counter = if physical { ready.physical_bits_read } else { ready.fill_bits_read };
                if counter == u64::MAX {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), advanced)
                } else {
                    let consumed = HtForwardRefinementState {
                        physical_bits_read: if physical { (counter + 1) as u64 } else { ready.physical_bits_read },
                        fill_bits_read: if physical { ready.fill_bits_read } else { (counter + 1) as u64 }, ..advanced
                    };
                    match ht_refinement_work(consumed.physical_bits_read, consumed.fill_bits_read, consumed.maximum_work_units) {
                        Err(error) => (Err(error), consumed),
                        Ok(()) => (Ok((ht_reader_bit(ready.value, ready.next_bit), position)), consumed),
                    }
                }
            }
        },
    }
}

pub open spec fn ht_forward_refinement_read(state: HtForwardRefinementState)
    -> (Result<bool, crate::DecodeError>, HtForwardRefinementState)
{
    let read = ht_forward_refinement_positioned(state);
    (match read.0 { Err(error) => Err(error), Ok((bit, _)) => Ok(bit) }, read.1)
}

pub open spec fn ht_reverse_refinement_load(state: HtReverseRefinementState)
    -> (Result<(), crate::DecodeError>, HtReverseRefinementState)
{
    if state.current_byte == 0 {
        (Ok(()), HtReverseRefinementState { has_byte: false, value: 0, next_bit: 0, last_bit: 7, ..state })
    } else {
        let index = (state.current_byte - 1) as usize;
        let moved = HtReverseRefinementState { current_byte: index, ..state };
        if index >= state.input.len() {
            (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), moved)
        } else {
            let value = state.input[index as int];
            (Ok(()), HtReverseRefinementState {
                value, next_bit: 0,
                last_bit: if state.later_requires_unstuffing && value & 0x7fu8 == 0x7f { 6 } else { 7 },
                later_requires_unstuffing: value > 0x8f, has_byte: true, ..moved
            })
        }
    }
}

pub open spec fn ht_reverse_refinement_initial(input: Seq<u8>, maximum_work_units: u64)
    -> Result<HtReverseRefinementState, crate::DecodeError>
{
    if input.len() > 2046 { Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)) }
    else {
        let loaded = ht_reverse_refinement_load(HtReverseRefinementState {
            current_byte: input.len() as usize, input, value: 0, next_bit: 0, last_bit: 7,
            has_byte: false, later_requires_unstuffing: true, physical_bits_read: 0, fill_bits_read: 0, maximum_work_units,
        });
        match loaded.0 { Err(error) => Err(error), Ok(()) => Ok(loaded.1) }
    }
}

pub open spec fn ht_reverse_refinement_positioned(state: HtReverseRefinementState)
    -> (HtPositionedRead, HtReverseRefinementState)
{
    let loaded = if !state.has_byte || state.next_bit > state.last_bit {
        ht_reverse_refinement_load(state)
    } else { (Ok(()), state) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => {
            let ready = loaded.1;
            if ready.has_byte && ready.next_bit >= 8 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), ready)
            } else {
                let position = if ready.has_byte {
                    Some(crate::tier1::HtBitPosition { byte: ready.current_byte as u16, bit: ready.next_bit })
                } else { None };
                let advanced = HtReverseRefinementState {
                    next_bit: if ready.has_byte { (ready.next_bit + 1) as u8 } else { ready.next_bit }, ..ready
                };
                let counter = if ready.has_byte { ready.physical_bits_read } else { ready.fill_bits_read };
                if counter == u64::MAX {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), advanced)
                } else {
                    let consumed = HtReverseRefinementState {
                        physical_bits_read: if ready.has_byte { (counter + 1) as u64 } else { ready.physical_bits_read },
                        fill_bits_read: if ready.has_byte { ready.fill_bits_read } else { (counter + 1) as u64 }, ..advanced
                    };
                    match ht_refinement_work(consumed.physical_bits_read, consumed.fill_bits_read, consumed.maximum_work_units) {
                        Err(error) => (Err(error), consumed),
                        Ok(()) => (Ok((if ready.has_byte { ht_reader_bit(ready.value, ready.next_bit) } else { false }, position)), consumed),
                    }
                }
            }
        },
    }
}

pub open spec fn ht_reverse_refinement_read(state: HtReverseRefinementState)
    -> (Result<bool, crate::DecodeError>, HtReverseRefinementState)
{
    let read = ht_reverse_refinement_positioned(state);
    (match read.0 { Err(error) => Err(error), Ok((bit, _)) => Ok(bit) }, read.1)
}

pub struct HtRefinementReadersState {
    pub forward: HtForwardRefinementState,
    pub reverse: Option<HtReverseRefinementState>,
    pub claimed: Seq<u8>,
    pub stuffed: Seq<u8>,
}

pub open spec fn ht_refinement_readers_initial(
    forward_input: Seq<u8>, reverse_input: Seq<u8>, bytes: usize, has_reverse: bool, maximum_work_units: u64,
) -> Result<HtRefinementReadersState, crate::DecodeError> {
    match ht_forward_refinement_initial(forward_input, maximum_work_units) {
        Err(error) => Err(error),
        Ok(forward) => {
            let reverse = if has_reverse {
                match ht_reverse_refinement_initial(reverse_input, maximum_work_units) {
                    Err(error) => Err(error), Ok(reverse) => Ok(Some(reverse)),
                }
            } else { Ok(None) };
            match reverse {
                Err(error) => Err(error),
                Ok(reverse) => Ok(HtRefinementReadersState {
                    forward, reverse, claimed: Seq::new(bytes as nat, |i: int| 0u8), stuffed: Seq::new(bytes as nat, |i: int| 0u8),
                }),
            }
        },
    }
}

pub open spec fn ht_refinement_claim(state: HtRefinementReadersState, position: Option<crate::tier1::HtBitPosition>)
    -> (Result<(), crate::DecodeError>, HtRefinementReadersState)
{
    match position {
        None => (Ok(()), state),
        Some(position) => if position.bit >= 8 || position.byte >= state.claimed.len() {
            (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
        } else {
            let mask = 1u8 << position.bit;
            let value = state.claimed[position.byte as int];
            if value & mask != 0 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
            } else {
                (Ok(()), HtRefinementReadersState { claimed: state.claimed.update(position.byte as int, value | mask), ..state })
            }
        },
    }
}

pub open spec fn ht_refinement_read_forward(state: HtRefinementReadersState)
    -> (Result<bool, crate::DecodeError>, HtRefinementReadersState)
{
    let read = ht_forward_refinement_positioned(state.forward);
    let consumed = HtRefinementReadersState { forward: read.1, ..state };
    match read.0 {
        Err(error) => (Err(error), consumed),
        Ok((bit, position)) => {
            let claim = ht_refinement_claim(consumed, position);
            (match claim.0 { Err(error) => Err(error), Ok(()) => Ok(bit) }, claim.1)
        },
    }
}

pub open spec fn ht_refinement_read_reverse(state: HtRefinementReadersState)
    -> (Result<bool, crate::DecodeError>, HtRefinementReadersState)
{
    match state.reverse {
        None => (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
        Some(reverse) => {
            let read = ht_reverse_refinement_positioned(reverse);
            let consumed = HtRefinementReadersState { reverse: Some(read.1), ..state };
            match read.0 {
                Err(error) => (Err(error), consumed),
                Ok((bit, position)) => {
                    if read.1.has_byte && read.1.last_bit == 6 && read.1.current_byte >= consumed.stuffed.len() {
                        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), consumed)
                    } else {
                        let marked = if read.1.has_byte && read.1.last_bit == 6 {
                            HtRefinementReadersState { stuffed: consumed.stuffed.update(
                                read.1.current_byte as int, consumed.stuffed[read.1.current_byte as int] | 0x80u8), ..consumed }
                        } else { consumed };
                        let claim = ht_refinement_claim(marked, position);
                        (match claim.0 { Err(error) => Err(error), Ok(()) => Ok(bit) }, claim.1)
                    }
                },
            }
        },
    }
}

pub open spec fn ht_refinement_finish(state: HtRefinementReadersState, encoded: Seq<u8>) -> Result<(), crate::DecodeError> {
    if state.claimed.len() != encoded.len() || state.stuffed.len() != encoded.len()
        || !(forall |i: int| 0 <= i < encoded.len() ==> encoded[i] & !(state.claimed[i] | state.stuffed[i]) == 0) {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else { Ok(()) }
}

pub struct HtReverseVlcState {
    pub input: Seq<u8>,
    pub current_byte: usize,
    pub value: u8,
    pub next_bit: u8,
    pub last_bit: u8,
    pub has_byte: bool,
    pub later_byte_requires_unstuffing: bool,
    pub bits_read: u64,
    pub maximum_work_units: u64,
}

pub struct HtMelState {
    pub input: Seq<u8>,
    pub next_byte: usize,
    pub current_byte: usize,
    pub value: u8,
    pub next_bit: i8,
    pub previous_was_ff: bool,
    pub bits_read: u64,
    pub maximum_work_units: u64,
}

pub open spec fn ht_reader_error(kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: 0, kind }
}

pub open spec fn ht_reader_work_error(limit: u64, actual: u64) -> crate::DecodeError {
    crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits, limit, actual }
}

pub open spec fn ht_reader_bit(value: u8, index: u8) -> bool
    recommends index < 8,
{
    (value >> index) & 1 != 0
}

pub open spec fn ht_reverse_vlc_initial(input: Seq<u8>, maximum_work_units: u64)
    -> Result<HtReverseVlcState, crate::DecodeError>
{
    if input.len() < 2 || input.len() > 4079 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        let index = (input.len() - 2) as usize;
        let value = input[index as int];
        Ok(HtReverseVlcState {
            input, current_byte: index, value, next_bit: 4,
            last_bit: if (value >> 4) & 7 == 7 { 6 } else { 7 },
            has_byte: true, later_byte_requires_unstuffing: value | 0x0fu8 > 0x8f,
            bits_read: 0, maximum_work_units,
        })
    }
}

pub open spec fn ht_reverse_vlc_load(state: HtReverseVlcState)
    -> (Result<(), crate::DecodeError>, HtReverseVlcState)
{
    if state.current_byte == 0 {
        (Ok(()), HtReverseVlcState { has_byte: false, ..state })
    } else {
        let index = (state.current_byte - 1) as usize;
        let moved = HtReverseVlcState { current_byte: index, ..state };
        if index >= state.input.len() {
            (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), moved)
        } else {
            let value = state.input[index as int];
            (Ok(()), HtReverseVlcState {
                value, next_bit: 0,
                last_bit: (ht_reverse_data_bits(state.later_byte_requires_unstuffing, value) - 1) as u8,
                later_byte_requires_unstuffing: value > 0x8f, ..moved
            })
        }
    }
}

pub open spec fn ht_reverse_vlc_read(state: HtReverseVlcState)
    -> (Result<bool, crate::DecodeError>, HtReverseVlcState)
{
    if !state.has_byte || state.next_bit >= 8 {
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
    } else {
        let advanced = HtReverseVlcState { next_bit: (state.next_bit + 1) as u8, ..state };
        if state.bits_read == u64::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), advanced)
        } else {
            let charged = HtReverseVlcState { bits_read: (state.bits_read + 1) as u64, ..advanced };
            if charged.bits_read > state.maximum_work_units {
                (Err(ht_reader_work_error(state.maximum_work_units, charged.bits_read)), charged)
            } else {
                let loaded = if charged.next_bit > state.last_bit {
                    ht_reverse_vlc_load(charged)
                } else { (Ok(()), charged) };
                match loaded.0 {
                    Err(error) => (Err(error), loaded.1),
                    Ok(()) => (Ok(ht_reader_bit(state.value, state.next_bit)), loaded.1),
                }
            }
        }
    }
}

pub open spec fn ht_reverse_vlc_position(state: HtReverseVlcState) -> Option<(u16, u8)> {
    if !state.has_byte || state.current_byte > u16::MAX { None }
    else { Some((state.current_byte as u16, state.next_bit)) }
}

pub open spec fn ht_mel_load(state: HtMelState)
    -> (Result<(), crate::DecodeError>, HtMelState)
{
    if state.next_byte >= state.input.len() {
        (Ok(()), HtMelState { next_bit: -1i8, ..state })
    } else {
        let index = state.next_byte;
        let value = if index + 1 == state.input.len() {
            state.input[index as int] | 0x0fu8
        } else { state.input[index as int] };
        if !ht_mel_stuffing_valid(state.previous_was_ff, value as nat) {
            (Err(crate::DecodeError::MalformedInput {
                offset: index as u64, kind: crate::MalformedKind::InvalidBitStuffing,
            }), state)
        } else {
            (Ok(()), HtMelState {
                next_byte: (index + 1) as usize, current_byte: index, value,
                next_bit: if state.previous_was_ff { 6 } else { 7 },
                previous_was_ff: value == 0xff, ..state
            })
        }
    }
}

pub open spec fn ht_mel_initial(input: Seq<u8>, maximum_work_units: u64)
    -> Result<HtMelState, crate::DecodeError>
{
    if input.len() == 0 || input.len() > 4078 {
        Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
    } else {
        let loaded = ht_mel_load(HtMelState {
            input, next_byte: 0, current_byte: 0, value: 0, next_bit: -1i8,
            previous_was_ff: false, bits_read: 0, maximum_work_units,
        });
        match loaded.0 { Err(error) => Err(error), Ok(()) => Ok(loaded.1) }
    }
}

pub open spec fn ht_mel_read(state: HtMelState)
    -> (Result<bool, crate::DecodeError>, HtMelState)
{
    let loaded = if state.next_bit < 0 { ht_mel_load(state) } else { (Ok(()), state) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => {
            let ready = loaded.1;
            if ready.next_bit < 0 || ready.next_bit >= 8 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), ready)
            } else {
                let advanced = HtMelState { next_bit: (ready.next_bit - 1) as i8, ..ready };
                if ready.bits_read == u64::MAX {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), advanced)
                } else {
                    let charged = HtMelState { bits_read: (ready.bits_read + 1) as u64, ..advanced };
                    if charged.bits_read > ready.maximum_work_units {
                        (Err(ht_reader_work_error(ready.maximum_work_units, charged.bits_read)), charged)
                    } else {
                        (Ok(ht_reader_bit(ready.value, ready.next_bit as u8)), charged)
                    }
                }
            }
        },
    }
}

pub open spec fn ht_mel_position(state: HtMelState) -> Option<(u16, u8)> {
    if state.next_bit < 0 || state.current_byte > u16::MAX { None }
    else { Some((state.current_byte as u16, state.next_bit as u8)) }
}

pub open spec fn ht_reverse_vlc_prefix(state: HtReverseVlcState, count: nat)
    -> (Result<Seq<bool>, crate::DecodeError>, HtReverseVlcState)
    decreases count,
{
    if count == 0 { (Ok(Seq::empty()), state) }
    else {
        let prefix = ht_reverse_vlc_prefix(state, (count - 1) as nat);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(bits) => {
                let step = ht_reverse_vlc_read(prefix.1);
                match step.0 {
                    Err(error) => (Err(error), step.1),
                    Ok(bit) => (Ok(bits.push(bit)), step.1),
                }
            },
        }
    }
}

pub open spec fn ht_mel_prefix(state: HtMelState, count: nat)
    -> (Result<Seq<bool>, crate::DecodeError>, HtMelState)
    decreases count,
{
    if count == 0 { (Ok(Seq::empty()), state) }
    else {
        let prefix = ht_mel_prefix(state, (count - 1) as nat);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(bits) => {
                let step = ht_mel_read(prefix.1);
                match step.0 {
                    Err(error) => (Err(error), step.1),
                    Ok(bit) => (Ok(bits.push(bit)), step.1),
                }
            },
        }
    }
}

pub struct HtCleanupReaderState {
    pub mel: HtMelState,
    pub vlc: HtReverseVlcState,
    pub mel_last_byte: Option<u16>,
    pub vlc_last_byte: Option<u16>,
    pub terminal_byte: u16,
    pub mel_state: u8,
    pub mel_zero_events: u8,
    pub mel_terminating_one: bool,
    pub mel_events: u32,
    pub work_units: u64,
    pub maximum_work_units: u64,
}

pub open spec fn ht_cleanup_readers_initial(mel_input: Seq<u8>, vlc_input: Seq<u8>, maximum_work_units: u64)
    -> Result<HtCleanupReaderState, crate::DecodeError>
{
    match ht_mel_initial(mel_input, maximum_work_units) {
        Err(error) => Err(error),
        Ok(mel) => match ht_reverse_vlc_initial(vlc_input, maximum_work_units) {
            Err(error) => Err(error),
            Ok(vlc) => Ok(HtCleanupReaderState {
                mel, vlc, mel_last_byte: None, vlc_last_byte: None,
                terminal_byte: (vlc_input.len() - 2) as u16,
                mel_state: 0, mel_zero_events: 0, mel_terminating_one: false,
                mel_events: 0, work_units: 0, maximum_work_units,
            }),
        },
    }
}

pub open spec fn ht_cleanup_reader_tick(state: HtCleanupReaderState)
    -> (Result<(), crate::DecodeError>, HtCleanupReaderState)
{
    if state.work_units == u64::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let changed = HtCleanupReaderState { work_units: (state.work_units + 1) as u64, ..state };
        if changed.work_units > state.maximum_work_units {
            (Err(ht_reader_work_error(state.maximum_work_units, changed.work_units)), changed)
        } else { (Ok(()), changed) }
    }
}

pub open spec fn ht_cleanup_reader_can_claim(state: HtCleanupReaderState, forward: bool, byte: u16) -> bool {
    if byte >= state.vlc.input.len() { false } else {
        let value = state.vlc.input[byte as int];
        let opposite = if forward { state.vlc_last_byte } else { state.mel_last_byte };
        match opposite {
            None => byte <= state.terminal_byte,
            Some(other) => if forward {
                ht_cleanup_byte_claims_valid(byte as nat, other as nat, state.terminal_byte as nat, value)
            } else {
                ht_cleanup_byte_claims_valid(other as nat, byte as nat, state.terminal_byte as nat, value)
            },
        }
    }
}

pub open spec fn ht_cleanup_reader_read_mel(state: HtCleanupReaderState)
    -> (Result<bool, crate::DecodeError>, HtCleanupReaderState)
{
    let loaded = if ht_mel_position(state.mel).is_none() { ht_mel_load(state.mel) }
        else { (Ok(()), state.mel) };
    let ready = HtCleanupReaderState { mel: loaded.1, ..state };
    match loaded.0 {
        Err(error) => (Err(error), ready),
        Ok(()) => match ht_mel_position(ready.mel) {
            None => (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), ready),
            Some(position) => if !ht_cleanup_reader_can_claim(ready, true, position.0) {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), ready)
            } else {
                let read = ht_mel_read(ready.mel);
                let consumed = HtCleanupReaderState { mel: read.1, ..ready };
                match read.0 {
                    Err(error) => (Err(error), consumed),
                    Ok(bit) => {
                        let claimed = HtCleanupReaderState { mel_last_byte: Some(position.0), ..consumed };
                        let charged = ht_cleanup_reader_tick(claimed);
                        match charged.0 { Err(error) => (Err(error), charged.1), Ok(()) => (Ok(bit), charged.1) }
                    },
                }
            },
        },
    }
}

pub open spec fn ht_cleanup_reader_read_vlc(state: HtCleanupReaderState)
    -> (Result<bool, crate::DecodeError>, HtCleanupReaderState)
{
    match ht_reverse_vlc_position(state.vlc) {
        None => (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state),
        Some(position) => if !ht_cleanup_reader_can_claim(state, false, position.0) {
            (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state)
        } else {
            let read = ht_reverse_vlc_read(state.vlc);
            let consumed = HtCleanupReaderState { vlc: read.1, ..state };
            match read.0 {
                Err(error) => (Err(error), consumed),
                Ok(bit) => {
                    let claimed = HtCleanupReaderState { vlc_last_byte: Some(position.0), ..consumed };
                    let charged = ht_cleanup_reader_tick(claimed);
                    match charged.0 { Err(error) => (Err(error), charged.1), Ok(()) => (Ok(bit), charged.1) }
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn ht_cleanup_peek_run(
    owner: HtCleanupReaderState, copy: HtReverseVlcState, remaining: nat, index: nat, value: u16,
) -> u16
    recommends index + remaining <= 255,
    decreases remaining,
{
    if remaining == 0 { value } else {
        let available = match ht_reverse_vlc_position(copy) {
            None => false, Some(position) => ht_cleanup_reader_can_claim(owner, false, position.0),
        };
        if !available { value } else {
            let read = ht_reverse_vlc_read(copy);
            match read.0 {
                Err(_) => value,
                Ok(bit) => if bit && index >= 16 { value } else {
                    ht_cleanup_peek_run(owner, read.1, (remaining - 1) as nat, index + 1,
                        if bit { value | (1u16 << index as u8) } else { value })
                },
            }
        }
    }
}

pub open spec fn ht_cleanup_peek_vlc(state: HtCleanupReaderState, count: u8) -> u16 {
    ht_cleanup_peek_run(state, state.vlc, count as nat, 0, 0)
}

pub open spec fn ht_cleanup_readers_finish(state: HtCleanupReaderState) -> Result<(), crate::DecodeError> {
    match (state.mel_last_byte, state.vlc_last_byte) {
        (Some(mel), Some(vlc)) => {
            if mel >= state.vlc.input.len()
                || !ht_cleanup_byte_claims_valid(mel as nat, vlc as nat, state.terminal_byte as nat, state.vlc.input[mel as int]) {
                Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))
            } else { Ok(()) }
        },
        _ => Ok(()),
    }
}

#[verifier::opaque]
pub open spec fn ht_cleanup_advance_vlc(state: HtCleanupReaderState, count: nat)
    -> (Result<(), crate::DecodeError>, HtCleanupReaderState)
    decreases count,
{
    if count == 0 { (Ok(()), state) } else {
        let read = ht_cleanup_reader_read_vlc(state);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(_) => ht_cleanup_advance_vlc(read.1, (count - 1) as nat),
        }
    }
}

pub open spec fn ht_cleanup_mel_emit(state: HtCleanupReaderState)
    -> (Result<bool, crate::DecodeError>, HtCleanupReaderState)
{
    let changed = if state.mel_zero_events > 0 {
        HtCleanupReaderState { mel_zero_events: (state.mel_zero_events - 1) as u8, ..state }
    } else { HtCleanupReaderState { mel_terminating_one: false, ..state } };
    if state.mel_events == u32::MAX {
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), changed)
    } else {
        (Ok(state.mel_zero_events == 0), HtCleanupReaderState { mel_events: (state.mel_events + 1) as u32, ..changed })
    }
}

#[verifier::opaque]
pub open spec fn ht_cleanup_mel_suffix(state: HtCleanupReaderState, remaining: nat, suffix: u8)
    -> (Result<u8, crate::DecodeError>, HtCleanupReaderState)
    recommends remaining <= 5,
    decreases remaining,
{
    if remaining == 0 { (Ok(suffix), state) } else {
        let shifted = suffix << 1u8;
        let read = ht_cleanup_reader_read_mel(state);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(bit) => ht_cleanup_mel_suffix(read.1, (remaining - 1) as nat,
                if bit { shifted | 1u8 } else { shifted }),
        }
    }
}

pub open spec fn ht_cleanup_mel_complete_suffix(result: (Result<u8, crate::DecodeError>, HtCleanupReaderState))
    -> (Result<bool, crate::DecodeError>, HtCleanupReaderState)
{
    match result.0 {
        Err(error) => (Err(error), result.1),
        Ok(suffix) => ht_cleanup_mel_emit(HtCleanupReaderState {
            mel_zero_events: suffix, mel_terminating_one: true,
            mel_state: ht_mel_next_state(result.1.mel_state as nat, false) as u8, ..result.1
        }),
    }
}

pub open spec fn ht_cleanup_mel_event(state: HtCleanupReaderState)
    -> (Result<bool, crate::DecodeError>, HtCleanupReaderState)
{
    if state.mel_zero_events > 0 || state.mel_terminating_one { ht_cleanup_mel_emit(state) }
    else if state.mel_state > 12 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else {
        let read = ht_cleanup_reader_read_mel(state);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(true) => ht_cleanup_mel_emit(HtCleanupReaderState {
                mel_zero_events: 1u8 << ht_mel_exponent(state.mel_state as nat) as u8,
                mel_state: ht_mel_next_state(state.mel_state as nat, true) as u8, ..read.1
            }),
            Ok(false) => ht_cleanup_mel_complete_suffix(
                ht_cleanup_mel_suffix(read.1, ht_mel_exponent(state.mel_state as nat), 0)),
        }
    }
}

#[verifier::opaque]
pub open spec fn ht_uvlc_prefix(state: HtCleanupReaderState)
    -> (Result<(u8, u8, u8), crate::DecodeError>, HtCleanupReaderState)
{
    let first = ht_cleanup_reader_read_vlc(state);
    match first.0 {
        Err(error) => (Err(error), first.1),
        Ok(true) => (Ok((1, 0, 1)), first.1),
        Ok(false) => {
            let second = ht_cleanup_reader_read_vlc(first.1);
            match second.0 {
                Err(error) => (Err(error), second.1),
                Ok(true) => (Ok((2, 0, 2)), second.1),
                Ok(false) => {
                    let third = ht_cleanup_reader_read_vlc(second.1);
                    match third.0 {
                        Err(error) => (Err(error), third.1),
                        Ok(true) => (Ok((3, 1, 3)), third.1),
                        Ok(false) => (Ok((5, 5, 3)), third.1),
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn ht_uvlc_suffix_run(state: HtCleanupReaderState, remaining: nat, index: nat, value: u8)
    -> (Result<u8, crate::DecodeError>, HtCleanupReaderState)
    recommends index + remaining <= 255,
    decreases remaining,
{
    if remaining == 0 { (Ok(value), state) } else {
        let read = ht_cleanup_reader_read_vlc(state);
        match read.0 {
            Err(error) => (Err(error), read.1),
            Ok(bit) => if bit && index >= 8 {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), read.1)
            } else {
                ht_uvlc_suffix_run(read.1, (remaining - 1) as nat, index + 1,
                    if bit { value | (1u8 << index as u8) } else { value })
            },
        }
    }
}

pub open spec fn ht_uvlc_suffix(state: HtCleanupReaderState, length: u8)
    -> (Result<u8, crate::DecodeError>, HtCleanupReaderState)
{
    ht_uvlc_suffix_run(state, length as nat, 0, 0)
}

#[verifier::opaque]
pub open spec fn ht_uvlc_prefix_value(state: HtCleanupReaderState)
    -> (Result<(u8, u8), crate::DecodeError>, HtCleanupReaderState)
{
    let prefix = ht_uvlc_prefix(state);
    match prefix.0 {
        Err(error) => (Err(error), prefix.1),
        Ok((base, length, prefix_length)) => {
            let suffix = ht_uvlc_suffix(prefix.1, length);
            match suffix.0 {
                Err(error) => (Err(error), suffix.1),
                Ok(value) => if base + value > u8::MAX {
                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), suffix.1)
                } else { (Ok(((base + value) as u8, prefix_length)), suffix.1) },
            }
        },
    }
}

pub type HtUvlcPairResult = (Result<[u8; 2], crate::DecodeError>, HtCleanupReaderState);

pub open spec fn ht_uvlc_byte(base: u8, suffix: u8, bias: u8) -> Result<u8, crate::DecodeError> {
    let value = base + suffix + bias;
    if value > u8::MAX { Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)) }
    else { Ok(value as u8) }
}

pub open spec fn ht_uvlc_single(state: HtCleanupReaderState, first: bool) -> HtUvlcPairResult {
    let prefix = ht_uvlc_prefix_value(state);
    match prefix.0 {
        Err(error) => (Err(error), prefix.1),
        Ok((value, _)) => if value == u8::MAX {
            (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), prefix.1)
        } else {
            (Ok(if first { [(value + 1) as u8, 1u8] } else { [1u8, (value + 1) as u8] }), prefix.1)
        },
    }
}

pub open spec fn ht_uvlc_pair_after_first(
    state: HtCleanupReaderState, first: (u8, u8, u8), bias: u8,
) -> HtUvlcPairResult {
    let second = ht_uvlc_prefix(state);
    match second.0 {
        Err(error) => (Err(error), second.1),
        Ok(second_prefix) => {
            let first_suffix = ht_uvlc_suffix(second.1, first.1);
            match first_suffix.0 {
                Err(error) => (Err(error), first_suffix.1),
                Ok(value) => {
                    let first_value = first.0 + value + bias;
                    if first_value > u8::MAX {
                        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), first_suffix.1)
                    } else {
                        let second_suffix = ht_uvlc_suffix(first_suffix.1, second_prefix.1);
                        match second_suffix.0 {
                            Err(error) => (Err(error), second_suffix.1),
                            Ok(value) => {
                                let second_value = second_prefix.0 + value + bias;
                                if second_value > u8::MAX {
                                    (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), second_suffix.1)
                                } else { (Ok([first_value as u8, second_value as u8]), second_suffix.1) }
                            },
                        }
                    }
                },
            }
        },
    }
}

pub open spec fn ht_uvlc_initial(state: HtCleanupReaderState, mode: u8) -> HtUvlcPairResult {
    if mode == 0 { (Ok([1u8, 1u8]), state) }
    else if mode == 1 || mode == 2 { ht_uvlc_single(state, mode == 1) }
    else if mode == 3 || mode == 4 {
        let prefix = ht_uvlc_prefix(state);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(first) => if mode == 4 || first.2 <= 2 {
                ht_uvlc_pair_after_first(prefix.1, first, if mode == 4 { 3 } else { 1 })
            } else {
                let bit = ht_cleanup_reader_read_vlc(prefix.1);
                match bit.0 {
                    Err(error) => (Err(error), bit.1),
                    Ok(bit_value) => {
                        let suffix = ht_uvlc_suffix(bit.1, first.1);
                        match suffix.0 {
                            Err(error) => (Err(error), suffix.1),
                            Ok(value) => if first.0 + value + 1 > u8::MAX {
                                (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)), suffix.1)
                            } else {
                                (Ok([(first.0 + value + 1) as u8, if bit_value { 3u8 } else { 2u8 }]), suffix.1)
                            },
                        }
                    },
                }
            },
        }
    } else { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
}

pub open spec fn ht_uvlc_non_initial(state: HtCleanupReaderState, mode: u8) -> HtUvlcPairResult {
    if mode == 0 { (Ok([1u8, 1u8]), state) }
    else if mode == 1 || mode == 2 { ht_uvlc_single(state, mode == 1) }
    else if mode == 3 {
        let prefix = ht_uvlc_prefix(state);
        match prefix.0 {
            Err(error) => (Err(error), prefix.1),
            Ok(first) => ht_uvlc_pair_after_first(prefix.1, first, 1),
        }
    } else { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
}

pub open spec fn ht_cleanup_quad_word(state: HtCleanupReaderState, table: Seq<u16>, context: u8)
    -> (Result<u16, crate::DecodeError>, HtCleanupReaderState)
{
    if context > 7 { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
    else {
        let index = context as nat * 128 + (ht_cleanup_peek_vlc(state, 7) & 0x7fu16) as nat;
        if index >= table.len() { (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), state) }
        else {
            let event = if context == 0 { ht_cleanup_mel_event(state) } else { (Ok(true), state) };
            match event.0 {
                Err(error) => (Err(error), event.1),
                Ok(keep) => {
                    let word = if keep { table[index as int] } else { 0u16 };
                    let length = (word & 7u16) as u8;
                    if !ht_vlc_word_valid(word as nat, length as nat) {
                        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)), event.1)
                    } else {
                        let advanced = ht_cleanup_advance_vlc(event.1, length as nat);
                        match advanced.0 {
                            Err(error) => (Err(error), advanced.1),
                            Ok(()) => {
                                let charged = ht_cleanup_reader_tick(advanced.1);
                                (match charged.0 { Err(error) => Err(error), Ok(()) => Ok(word) }, charged.1)
                            },
                        }
                    }
                },
            }
        }
    }
}

pub struct Part1RawReaderState {
    pub input: Seq<u8>,
    pub next_index: usize,
    pub current_byte: u8,
    pub bits_remaining: u8,
    pub marker_padding_count: u64,
    pub work_units: u64,
    pub maximum_work_units: u64,
}

pub open spec fn part1_raw_reader_error(offset: usize, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: offset as u64, kind }
}

pub open spec fn part1_raw_reader_initial(
    input: Seq<u8>, maximum_input_bytes: u64, maximum_work_units: u64,
) -> Result<Part1RawReaderState, crate::DecodeError>
    recommends input.len() <= usize::MAX,
{
    if input.len() as u64 > maximum_input_bytes {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::InputBytes, limit: maximum_input_bytes, actual: input.len() as u64,
        })
    } else {
        Ok(Part1RawReaderState {
            input, next_index: 0, current_byte: 0, bits_remaining: 0,
            marker_padding_count: 0, work_units: 0, maximum_work_units,
        })
    }
}

pub open spec fn part1_raw_reader_load(state: Part1RawReaderState)
    -> (Result<(), crate::DecodeError>, Part1RawReaderState)
{
    let next = if state.next_index < state.input.len() { state.input[state.next_index as int] } else { 0xffu8 };
    let stuffed = state.current_byte == 0xff;
    if stuffed && next > 0x8f {
        let changed = Part1RawReaderState { current_byte: 0xff, bits_remaining: 8, ..state };
        if state.marker_padding_count == u64::MAX {
            (Err(part1_raw_reader_error(state.next_index, crate::MalformedKind::ArithmeticOverflow)), changed)
        } else {
            (Ok(()), Part1RawReaderState { marker_padding_count: (state.marker_padding_count + 1) as u64, ..changed })
        }
    } else if state.next_index < state.input.len() && state.next_index == usize::MAX {
        (Err(part1_raw_reader_error(state.next_index, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        (Ok(()), Part1RawReaderState {
            next_index: if state.next_index < state.input.len() { (state.next_index + 1) as usize } else { state.next_index },
            current_byte: next,
            bits_remaining: if stuffed { 7 } else { 8 },
            ..state
        })
    }
}

pub open spec fn part1_raw_reader_read(state: Part1RawReaderState)
    -> (Result<bool, crate::DecodeError>, Part1RawReaderState)
{
    let loaded = if state.bits_remaining == 0 { part1_raw_reader_load(state) } else { (Ok(()), state) };
    match loaded.0 {
        Err(error) => (Err(error), loaded.1),
        Ok(()) => {
            let ready = loaded.1;
            if ready.bits_remaining == 0 || ready.bits_remaining > 8 {
                (Err(part1_raw_reader_error(ready.next_index, crate::MalformedKind::InvalidBitStuffing)), ready)
            } else {
                let consumed = Part1RawReaderState { bits_remaining: (ready.bits_remaining - 1) as u8, ..ready };
                if ready.work_units == u64::MAX {
                    (Err(part1_raw_reader_error(ready.next_index, crate::MalformedKind::ArithmeticOverflow)), consumed)
                } else {
                    let charged = Part1RawReaderState { work_units: (ready.work_units + 1) as u64, ..consumed };
                    if charged.work_units > charged.maximum_work_units {
                        (Err(crate::DecodeError::LimitExceeded {
                            resource: crate::Resource::WorkUnits,
                            limit: charged.maximum_work_units,
                            actual: charged.work_units,
                        }), charged)
                    } else {
                        (Ok(part1_packet_bit(charged.current_byte, charged.bits_remaining)), charged)
                    }
                }
            }
        },
    }
}

pub open spec fn part1_raw_reader_termination(state: Part1RawReaderState) -> Result<(), crate::DecodeError> {
    let valid = if state.next_index == 0 {
        (state.input.len() == 0 && state.work_units == 0)
            || (state.input.len() == 1 && state.input[0] == 0x55)
    } else if state.bits_remaining == 0 && state.current_byte == 0xff
        && state.next_index < state.input.len()
        && state.next_index + 1 == state.input.len()
        && state.input[state.next_index as int] == 0x2a {
        true
    } else if state.next_index != state.input.len() || state.bits_remaining > 8 {
        false
    } else if state.bits_remaining == 0 {
        true
    } else {
        let shift = (8 - state.bits_remaining) as u8;
        state.current_byte & (0xffu8 >> shift) == 0x55u8 >> shift
    };
    if valid { Ok(()) } else {
        Err(part1_raw_reader_error(0, crate::MalformedKind::InvalidCodeBlock))
    }
}

pub open spec fn part1_tag_inherited_low(low: nat, inherited: nat) -> nat {
    if low < inherited { inherited } else { low }
}

pub open spec fn part1_tag_step_low(low: nat, bit: bool) -> nat {
    if bit { low } else { low + 1 }
}

pub open spec fn part1_tag_step_value(low: nat, value: nat, bit: bool) -> nat {
    if bit { low } else { value }
}

pub open spec fn part1_progression_digit(index: nat, dimension: nat) -> nat
    recommends dimension > 0,
{
    (index % dimension) as nat
}

pub open spec fn part1_progression_advance(index: nat, dimension: nat) -> nat
    recommends dimension > 0,
{
    (index / dimension) as nat
}

pub open spec fn part1_progression_emit_allowed(already_seen: bool) -> bool {
    !already_seen
}

pub open spec fn part1_mq_decision(mps: bool, lps: bool) -> bool {
    if lps { !mps } else { mps }
}

pub open spec fn part1_mq_next_mps(mps: bool, switch_mps: bool) -> bool {
    if switch_mps { !mps } else { mps }
}

pub open spec fn part1_tier1_pass_code(pass_index: nat) -> nat {
    if pass_index == 0 { 2 } else { ((pass_index - 1) % 3) as nat }
}

pub open spec fn part1_tier1_refinement_context(refined: bool, neighbors: nat) -> nat {
    if refined { 16 } else if neighbors > 0 { 15 } else { 14 }
}

pub open spec fn part1_tier1_refined_magnitude(
    magnitude: nat,
    delta: nat,
    refinement_bit: bool,
) -> nat {
    if refinement_bit { magnitude + delta } else { magnitude }
}

pub open spec fn part1_maxshift_restore(magnitude: u64, shift: u8) -> u64 {
    if shift >= 64 {
        magnitude
    } else {
        let threshold = 1_u64 << shift;
        if magnitude < threshold { magnitude } else { magnitude >> shift }
    }
}

pub open spec fn part1_tier1_midpoint_delta(bitplane: u16) -> u64 {
    if bitplane == 0 || bitplane > 64 { 0 } else { 1_u64 << (bitplane - 1) }
}

pub open spec fn part1_reversible_inverse_quantize(coefficient: int) -> int {
    coefficient
}

pub open spec fn part1_five_three_predict(sum: i64) -> i64 {
    sum >> 1
}

pub open spec fn part1_five_three_update(biased_sum: i64) -> i64 {
    biased_sum >> 2
}

pub open spec fn part1_rct_green(y: i64, chroma_sum: i64) -> i64 {
    ((y as int) - ((chroma_sum >> 2) as int)) as i64
}

pub open spec fn part1_rct_red(green: int, cr: int) -> int {
    green + cr
}

pub open spec fn part1_rct_blue(green: int, cb: int) -> int {
    green + cb
}

pub open spec fn part1_level_shift(precision: u8, signed: bool) -> i64
    recommends precision > 0 && precision <= 63,
{
    if signed { 0 } else { 1_i64 << (precision - 1) }
}

pub open spec fn part1_clip_sample(value: i64, minimum: i64, maximum: i64) -> i64 {
    if value < minimum { minimum } else if value > maximum { maximum } else { value }
}

pub open spec fn part1_marker_value(high: u8, low: u8) -> u16 {
    ((high as u16) << 8) | (low as u16)
}

pub open spec fn part1_parser_progress(previous: usize, current: usize, limit: usize) -> bool {
    previous < current && current <= limit
}

pub struct Part1CodestreamReader<'a> {
    pub input: Seq<u8>,
    pub limits: &'a crate::ResourceLimits,
    pub position: usize,
    pub work_units: u64,
    pub packet_length_bytes: u64,
    pub packet_lengths: u64,
}

pub struct Part1CodestreamSegment {
    pub marker: u16,
    pub offset: usize,
    pub payload: Seq<u8>,
}

pub open spec fn part1_codestream_offset(value: usize) -> u64 { value as u64 }

pub open spec fn part1_codestream_malformed(value: usize, kind: crate::MalformedKind) -> crate::DecodeError {
    crate::DecodeError::MalformedInput { offset: part1_codestream_offset(value), kind }
}

pub open spec fn part1_codestream_reader_new<'a>(input: Seq<u8>, limits: &'a crate::ResourceLimits)
    -> Result<Part1CodestreamReader<'a>, crate::DecodeError>
{
    let length = input.len() as u64;
    let maximum = crate::limits::resource_input_byte_limit(limits);
    if length > maximum { Err(crate::DecodeError::LimitExceeded {
        resource: crate::Resource::InputBytes, limit: maximum, actual: length,
    }) } else { Ok(Part1CodestreamReader {
        input, limits, position: 0, work_units: 0, packet_length_bytes: 0, packet_lengths: 0,
    }) }
}

pub open spec fn part1_codestream_position<'a>(state: Part1CodestreamReader<'a>, position: usize)
    -> Part1CodestreamReader<'a>
{
    Part1CodestreamReader { input: state.input, limits: state.limits, position,
        work_units: state.work_units, packet_length_bytes: state.packet_length_bytes, packet_lengths: state.packet_lengths }
}

pub open spec fn part1_codestream_work<'a>(state: Part1CodestreamReader<'a>, work_units: u64)
    -> Part1CodestreamReader<'a>
{
    Part1CodestreamReader { input: state.input, limits: state.limits, position: state.position,
        work_units, packet_length_bytes: state.packet_length_bytes, packet_lengths: state.packet_lengths }
}

pub open spec fn part1_codestream_charge_work<'a>(state: Part1CodestreamReader<'a>, amount: u64)
    -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>)
{
    if state.work_units as int + amount as int > u64::MAX {
        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let next = (state.work_units + amount) as u64;
        let updated = part1_codestream_work(state, next);
        let maximum = crate::limits::resource_work_limit(state.limits);
        (if next > maximum { Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::WorkUnits, limit: maximum, actual: next,
        }) } else { Ok(()) }, updated)
    }
}

pub open spec fn part1_codestream_packet_bytes<'a>(state: Part1CodestreamReader<'a>, bytes: u64)
    -> Part1CodestreamReader<'a>
{
    Part1CodestreamReader { input: state.input, limits: state.limits, position: state.position,
        work_units: state.work_units, packet_length_bytes: bytes, packet_lengths: state.packet_lengths }
}

pub open spec fn part1_codestream_packet_count<'a>(state: Part1CodestreamReader<'a>, count: u64)
    -> Part1CodestreamReader<'a>
{
    Part1CodestreamReader { input: state.input, limits: state.limits, position: state.position,
        work_units: state.work_units, packet_length_bytes: state.packet_length_bytes, packet_lengths: count }
}

#[verifier::opaque]
pub open spec fn part1_packet_length_admission_from<'a>(
    state: Part1CodestreamReader<'a>, encoded: Seq<u8>, marker_offset: usize,
    position: usize, count: u64, total: u64,
) -> (Result<(u64, u64), crate::DecodeError>, Part1CodestreamReader<'a>)
    decreases encoded.len() - position,
{
    if position >= encoded.len() {
        if state.packet_lengths as int + count as int > u64::MAX {
            (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            let count_sum = (state.packet_lengths + count) as u64;
            let updated = part1_codestream_packet_count(state, count_sum);
            let maximum = crate::limits::resource_packet_limit(state.limits);
            (if count_sum > maximum { Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::Packets, limit: maximum, actual: count_sum,
            }) } else { Ok((count, total)) }, updated)
        }
    } else {
        match part1_packet_length_decode(encoded, position, encoded.len() as usize) {
            Err(_) => (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::InvalidPacketLength)), state),
            Ok((length, next)) => {
                if next <= position || next > encoded.len() {
                    (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::InvalidPacketLength)), state)
                } else if count == u64::MAX || total as int + length as int > u64::MAX {
                    (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::ArithmeticOverflow)), state)
                } else {
                    part1_packet_length_admission_from(state, encoded, marker_offset, next,
                        (count + 1) as u64, (total + length) as u64)
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_validate_packet_lengths<'a>(
    state: Part1CodestreamReader<'a>, encoded: Seq<u8>, marker_offset: usize,
) -> (Result<(u64, u64), crate::DecodeError>, Part1CodestreamReader<'a>) {
    if state.packet_length_bytes as int + encoded.len() > u64::MAX {
        (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let bytes = (state.packet_length_bytes as int + encoded.len()) as u64;
        let updated = part1_codestream_packet_bytes(state, bytes);
        let maximum = crate::limits::resource_packet_header_byte_limit(state.limits);
        if bytes > maximum {
            (Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::PacketHeaderBytes, limit: maximum, actual: bytes,
            }), updated)
        } else {
            let charged = part1_codestream_charge_work(updated, encoded.len() as u64);
            match charged.0 {
                Err(error) => (Err(error), charged.1),
                Ok(()) => part1_packet_length_admission_from(charged.1, encoded, marker_offset, 0, 0, 0),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_plm_groups_from<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, next_index: u16,
    position: nat, groups: Seq<Part1PacketLengths>,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u16, Seq<Part1PacketLengths>)
    decreases segment.payload.len() - position,
{
    if position >= segment.payload.len() {
        (Ok(()), state, next_index, groups)
    } else if segment.payload.len() - position < 4 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), state, next_index, groups)
    } else {
        let length = part1_siz_word(segment.payload, position as int) as nat;
        let start = position + 4;
        let end = start + length;
        if length > usize::MAX || start > usize::MAX || end > usize::MAX {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow)), state, next_index, groups)
        } else if end > segment.payload.len() {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), state, next_index, groups)
        } else {
            let encoded = segment.payload.subrange(start as int, end as int);
            let admitted = part1_validate_packet_lengths(state, encoded, segment.offset);
            match admitted.0 {
                Err(error) => (Err(error), admitted.1, next_index, groups),
                Ok((count, _)) => {
                    let appended = groups.push(Part1PacketLengths {
                        source: Part1PacketLengthSource::Plm(encoded), packet_count: count, encoded_bytes: encoded.len() as u64,
                    });
                    let maximum = crate::limits::resource_tile_part_limit(admitted.1.limits) as u64;
                    if appended.len() > maximum {
                        (Err(crate::DecodeError::LimitExceeded {
                            resource: crate::Resource::TileParts, limit: maximum, actual: appended.len() as u64,
                        }), admitted.1, next_index, appended)
                    } else {
                        part1_plm_groups_from(admitted.1, segment, next_index, end, appended)
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_plm<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment,
    next_index: u16, groups: Seq<Part1PacketLengths>,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u16, Seq<Part1PacketLengths>) {
    if segment.payload.len() < 5 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), state, next_index, groups)
    } else if segment.payload[0] as u16 != next_index {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), state, next_index, groups)
    } else {
        part1_plm_groups_from(state, segment, (next_index + 1) as u16, 1, groups)
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_packed_fragment<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, expected_marker: u16,
    next_index: u16, fragments: u16, bytes: Seq<u8>,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u16, u16, Seq<u8>) {
    if segment.marker != expected_marker || segment.payload.len() == 0 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)),
            state, next_index, fragments, bytes)
    } else if segment.payload[0] as u16 != next_index {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)),
            state, next_index, fragments, bytes)
    } else {
        let next = (next_index as int + 1) as u16;
        if fragments == u16::MAX {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow)),
                state, next, fragments, bytes)
        } else {
            let count = (fragments as int + 1) as u16;
            let fragment = segment.payload.subrange(1, segment.payload.len() as int);
            let total = state.packet_length_bytes as int + fragment.len();
            if bytes.len() + fragment.len() > usize::MAX || total > u64::MAX {
                (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow)),
                    state, next, count, bytes)
            } else if total > crate::limits::resource_packet_header_byte_limit(state.limits) {
                (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::PacketHeaderBytes,
                    limit: crate::limits::resource_packet_header_byte_limit(state.limits), actual: total as u64 }),
                    state, next, count, bytes)
            } else {
                let charged = part1_codestream_charge_work(part1_codestream_packet_bytes(state, total as u64), fragment.len() as u64);
                match charged.0 {
                    Err(error) => (Err(error), charged.1, next, count, bytes),
                    Ok(()) => (Ok(()), charged.1, next, count, bytes + fragment),
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_ppm_frames_from(
    bytes: Seq<u8>, maximum: u32, position: nat, frames: Seq<(usize, usize)>,
) -> Result<Seq<(usize, usize)>, crate::DecodeError>
    decreases bytes.len() - position,
{
    if position >= bytes.len() { Ok(frames) }
    else if bytes.len() - position < 4 {
        Err(part1_codestream_malformed(position as usize, crate::MalformedKind::InvalidPackedPacketHeader))
    } else {
        let length = part1_codestream_u32(bytes[position as int], bytes[position as int + 1],
            bytes[position as int + 2], bytes[position as int + 3]) as nat;
        if length > usize::MAX {
            Err(part1_codestream_malformed(position as usize, crate::MalformedKind::ArithmeticOverflow))
        } else {
            let start = position + 4;
            let end = start + length;
            if start > usize::MAX {
                Err(part1_codestream_malformed(position as usize, crate::MalformedKind::ArithmeticOverflow))
            } else if end > usize::MAX {
                Err(part1_codestream_malformed(start as usize, crate::MalformedKind::ArithmeticOverflow))
            } else if end > bytes.len() {
                Err(part1_codestream_malformed(start as usize, crate::MalformedKind::InvalidPackedPacketHeader))
            } else {
                let next = frames.push((start as usize, length as usize));
                if next.len() > maximum {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TileParts,
                        limit: maximum as u64, actual: next.len() as u64 })
                } else { part1_ppm_frames_from(bytes, maximum, end, next) }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_ppm_frames(bytes: Seq<u8>, fragments: u16, limits: &crate::ResourceLimits)
    -> Result<Seq<(usize, usize)>, crate::DecodeError>
{
    if fragments == 0 { Ok(Seq::empty()) }
    else { part1_ppm_frames_from(bytes, crate::limits::resource_tile_part_limit(limits), 0, Seq::empty()) }
}

pub open spec fn part1_codestream_peek_marker(state: Part1CodestreamReader<'_>)
    -> Result<u16, crate::DecodeError>
{
    if state.position as int + 2 > state.input.len() {
        Err(part1_codestream_malformed(state.position, crate::MalformedKind::Truncated))
    } else {
        let high = state.input[state.position as int];
        let low = state.input[state.position as int + 1];
        if high != 255 || low == 0 || low == 255 {
            Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidMarker))
        } else { Ok(part1_marker_value(high, low)) }
    }
}

pub open spec fn part1_codestream_standalone(marker: u16) -> bool {
    marker == 0xff4f || marker == 0xff93 || marker == 0xffd9 || marker == 0xff92
}

pub open spec fn part1_known_segment_marker(marker: u16) -> bool {
    matches!(marker, 0xff50..=0xff53 | 0xff55..=0xff59 | 0xff5c..=0xff61 |
        0xff63..=0xff64 | 0xff72..=0xff79 | 0xff90)
}

pub open spec fn part1_allowed_main_header(marker: u16) -> bool {
    part1_known_segment_marker(marker) && !matches!(marker, 0xff51 | 0xff58 | 0xff61 | 0xff90)
}

pub open spec fn part1_allowed_tile_header(marker: u16) -> bool {
    matches!(marker, 0xff52..=0xff53 | 0xff58 | 0xff5c..=0xff5f | 0xff61 |
        0xff64 | 0xff72..=0xff79)
}

#[verifier::opaque]
pub open spec fn part1_codestream_read_sot<'a>(state: Part1CodestreamReader<'a>, tile_count: u64)
    -> (Result<(usize, u32, u16, u8, u8), crate::DecodeError>, Part1CodestreamReader<'a>)
{
    let read = part1_codestream_read_segment(state);
    match read.0 {
        Err(error) => (Err(error), read.1),
        Ok(segment) => {
            if segment.marker != 0xff90 || segment.payload.len() != 8 {
                (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTilePart)), read.1)
            } else {
                let index = part1_marker_value(segment.payload[0], segment.payload[1]);
                let length = part1_siz_word(segment.payload, 2);
                let part = segment.payload[6];
                let count = segment.payload[7];
                if index as u64 >= tile_count || (count != 0 && part >= count) || (length != 0 && length < 14) {
                    (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTilePart)), read.1)
                } else { (Ok((segment.offset, length, index, part, count)), read.1) }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_codestream_expect_standalone<'a>(state: Part1CodestreamReader<'a>, expected: u16)
    -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>)
{
    match part1_codestream_peek_marker(state) {
        Err(error) => (Err(error), state),
        Ok(marker) => if marker != expected {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidMarkerOrder)), state)
        } else if state.position as int + 2 > usize::MAX {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
        } else {
            part1_codestream_charge_work(part1_codestream_position(state, (state.position + 2) as usize), 1)
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_codestream_read_segment<'a>(state: Part1CodestreamReader<'a>)
    -> (Result<Part1CodestreamSegment, crate::DecodeError>, Part1CodestreamReader<'a>)
{
    match part1_codestream_peek_marker(state) {
        Err(error) => (Err(error), state),
        Ok(marker) => {
            let charged = part1_codestream_charge_work(state, 1);
            match charged.0 {
                Err(error) => (Err(error), charged.1),
                Ok(()) => {
                    let state = charged.1;
                    if part1_codestream_standalone(marker) && marker != 0xff90 {
                        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidMarkerOrder)), state)
                    } else if state.position as int + 2 > usize::MAX {
                        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
                    } else {
                        let length_offset = state.position as int + 2;
                        if length_offset + 2 > state.input.len() {
                            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::Truncated)), state)
                        } else {
                            let length = part1_marker_value(state.input[length_offset], state.input[length_offset + 1]) as int;
                            let end = length_offset + length;
                            if length < 2 {
                                (Err(part1_codestream_malformed(state.position, crate::MalformedKind::InvalidMarkerLength)), state)
                            } else if end > usize::MAX {
                                (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
                            } else if end > state.input.len() {
                                (Err(part1_codestream_malformed(state.position, crate::MalformedKind::Truncated)), state)
                            } else if length_offset + 2 > end {
                                (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
                            } else {
                                (Ok(Part1CodestreamSegment { marker, offset: state.position,
                                    payload: state.input.subrange(length_offset + 2, end) }),
                                    part1_codestream_position(state, end as usize))
                            }
                        }
                    }
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_codestream_find_eoc<'a>(state: Part1CodestreamReader<'a>)
    -> (Result<usize, crate::DecodeError>, Part1CodestreamReader<'a>)
    decreases state.input.len() - state.position,
{
    if state.position >= state.input.len() || state.input.len() - state.position < 2 {
        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::Truncated)), state)
    } else if state.position as int + 1 > usize::MAX {
        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state)
    } else {
        let next = (state.position + 1) as usize;
        if state.position >= state.input.len() || next >= state.input.len() {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::Truncated)), state)
        } else {
            let found = state.input[state.position as int] == 255 && state.input[next as int] == 217;
            let charged = part1_codestream_charge_work(state, 1);
            match charged.0 {
                Err(error) => (Err(error), charged.1),
                Ok(()) => if found { (Ok(state.position), charged.1) }
                else if next <= state.position || next > state.input.len() {
                    (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), charged.1)
                } else { part1_codestream_find_eoc(part1_codestream_position(charged.1, next)) },
            }
        }
    }
}

pub open spec fn part1_codestream_u32(a: u8, b: u8, c: u8, d: u8) -> u32 {
    ((a as u32) << 24) | ((b as u32) << 16) | ((c as u32) << 8) | d as u32
}

pub open spec fn part1_siz_word(payload: Seq<u8>, offset: int) -> u32
    recommends 0 <= offset && offset + 4 <= payload.len(),
{
    part1_codestream_u32(payload[offset], payload[offset + 1], payload[offset + 2], payload[offset + 3])
}

pub struct Part1SizHeader {
    pub xsiz: u32, pub ysiz: u32, pub xosiz: u32, pub yosiz: u32,
    pub xtsiz: u32, pub ytsiz: u32, pub xtosiz: u32, pub ytosiz: u32,
    pub components: u16, pub r_siz: u16,
}

pub struct Part1ParsedImageSize {
    pub geometry: Part2SelectionGeometry,
    pub components: u16,
    pub uniform_bit_depth: Option<u8>,
    pub uniform_signed: Option<bool>,
    pub infos: Seq<crate::codestream::ComponentInfo>,
}

#[verifier::opaque]
pub open spec fn part1_component_depths_uniform_from(
    size: Part1ParsedImageSize, first: crate::codestream::ComponentInfo, component: nat,
) -> bool
    decreases size.components as nat - component,
{
    if component >= size.components {
        true
    } else {
        match part1_image_size_component(size.components, size.infos, component as u16) {
            Err(_) => false,
            Ok(info) => info.precision == first.precision && info.signed == first.signed
                && part1_component_depths_uniform_from(size, first, component + 1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_component_depths_uniform(size: Part1ParsedImageSize, first: crate::codestream::ComponentInfo) -> bool {
    part1_component_depths_uniform_from(size, first, 1)
}

#[verifier::opaque]
pub open spec fn part1_apply_component_depths_from(
    size: Part1ParsedImageSize, depths: Seq<crate::codestream::ComponentBitDepth>,
    offset: usize, component: nat,
) -> (Result<(), crate::DecodeError>, Part1ParsedImageSize)
    decreases size.components as nat - component,
{
    if component >= size.components {
        match part1_image_size_component(size.components, size.infos, 0) {
            Err(error) => (Err(error), size),
            Ok(first) => {
                let uniform = part1_component_depths_uniform(size, first);
                (Ok(()), Part1ParsedImageSize {
                    uniform_bit_depth: if uniform { Some(first.precision) } else { None },
                    uniform_signed: if uniform { Some(first.signed) } else { None }, ..size
                })
            },
        }
    } else if component >= depths.len() {
        (Err(part1_codestream_malformed(offset, crate::MalformedKind::MissingRequiredStructure)), size)
    } else if component >= size.infos.len() {
        (Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidImageGeometry)), size)
    } else {
        let depth = depths[component as int];
        let info = crate::codestream::ComponentInfo {
            precision: depth.precision, signed: depth.signed, ..size.infos[component as int]
        };
        part1_apply_component_depths_from(Part1ParsedImageSize {
            infos: size.infos.update(component as int, info), ..size
        }, depths, offset, component + 1)
    }
}

#[verifier::opaque]
pub open spec fn part1_apply_component_depths(
    size: Part1ParsedImageSize, depths: Seq<crate::codestream::ComponentBitDepth>, offset: usize,
) -> (Result<(), crate::DecodeError>, Part1ParsedImageSize) {
    if depths.len() == 0 { (Ok(()), size) }
    else { part1_apply_component_depths_from(size, depths, offset, 0) }
}

#[verifier::opaque]
pub open spec fn part1_apply_component_registrations_from(
    size: Part1ParsedImageSize, registrations: Seq<crate::codestream::ComponentRegistration>,
    offset: usize, component: nat,
) -> (Result<(), crate::DecodeError>, Part1ParsedImageSize)
    decreases size.components as nat - component,
{
    if component >= size.components {
        (Ok(()), size)
    } else if component >= registrations.len() {
        (Err(part1_codestream_malformed(offset, crate::MalformedKind::MissingRequiredStructure)), size)
    } else if component >= size.infos.len() {
        (Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidImageGeometry)), size)
    } else {
        let registration = registrations[component as int];
        let info = crate::codestream::ComponentInfo {
            x_registration: registration.horizontal, y_registration: registration.vertical,
            ..size.infos[component as int]
        };
        part1_apply_component_registrations_from(Part1ParsedImageSize {
            infos: size.infos.update(component as int, info), ..size
        }, registrations, offset, component + 1)
    }
}

#[verifier::opaque]
pub open spec fn part1_apply_component_registrations(
    size: Part1ParsedImageSize, registrations: Seq<crate::codestream::ComponentRegistration>, offset: usize,
) -> (Result<(), crate::DecodeError>, Part1ParsedImageSize) {
    if registrations.len() == 0 { (Ok(()), size) }
    else { part1_apply_component_registrations_from(size, registrations, offset, 0) }
}

pub struct Part1SizComponents {
    pub offset: usize, pub component: u16,
    pub infos: Seq<crate::codestream::ComponentInfo>,
    pub first_precision: u8, pub first_signed: bool, pub uniform: bool,
}

pub open spec fn part1_empty_component_info() -> crate::codestream::ComponentInfo {
    crate::codestream::ComponentInfo { precision: 0, signed: false, x_subsampling: 0, y_subsampling: 0,
        x_registration: 0, y_registration: 0 }
}

pub(crate) open spec fn part1_siz_components_initial() -> Part1SizComponents {
    Part1SizComponents { offset: 36, component: 0,
        infos: Seq::new(crate::codestream::MAX_COMPONENTS as nat, |i: int| part1_empty_component_info()),
        first_precision: 0, first_signed: false, uniform: true }
}

#[verifier::opaque]
pub open spec fn part1_siz_header(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    -> Result<Part1SizHeader, crate::DecodeError>
{
    let payload = segment.payload;
    if payload.len() < 36 { Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)) }
    else {
        let h = Part1SizHeader {
            xsiz: part1_siz_word(payload, 2), ysiz: part1_siz_word(payload, 6),
            xosiz: part1_siz_word(payload, 10), yosiz: part1_siz_word(payload, 14),
            xtsiz: part1_siz_word(payload, 18), ytsiz: part1_siz_word(payload, 22),
            xtosiz: part1_siz_word(payload, 26), ytosiz: part1_siz_word(payload, 30),
            components: part1_marker_value(payload[34], payload[35]), r_siz: part1_marker_value(payload[0], payload[1]),
        };
        let first_x = h.xtosiz as int + h.xtsiz as int;
        let first_y = h.ytosiz as int + h.ytsiz as int;
        let bytes = h.components as int * 3;
        if first_x > u32::MAX || first_y > u32::MAX || bytes > usize::MAX || 36 + bytes > usize::MAX {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow))
        } else if payload.len() != 36 + bytes || h.xsiz <= h.xosiz || h.ysiz <= h.yosiz
            || h.xtsiz == 0 || h.ytsiz == 0 || h.xtosiz > h.xosiz || h.ytosiz > h.yosiz
            || first_x <= h.xosiz || first_y <= h.yosiz || h.components == 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidImageGeometry))
        } else if h.components > crate::limits::resource_component_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Components,
                limit: crate::limits::resource_component_limit(limits) as u64, actual: h.components as u64 })
        } else { Ok(h) }
    }
}

#[verifier::opaque]
pub open spec fn part1_siz_components(
    payload: Seq<u8>, offset: usize, state: Part1SizComponents,
) -> Result<Part1SizComponents, crate::DecodeError>
    decreases payload.len() - state.offset,
{
    if state.offset >= payload.len() { Ok(state) }
    else if payload.len() - state.offset < 3 {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let precision = (payload[state.offset as int] & 127) as u16 + 1;
        let signed = payload[state.offset as int] & 128 != 0;
        if precision > 38 || payload[state.offset as int + 1] == 0 || payload[state.offset as int + 2] == 0 {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidImageGeometry))
        } else if state.component as nat >= state.infos.len() {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidImageGeometry))
        } else {
            let info = crate::codestream::ComponentInfo { precision: precision as u8, signed,
                x_subsampling: payload[state.offset as int + 1], y_subsampling: payload[state.offset as int + 2],
                x_registration: 0, y_registration: 0 };
            if state.component == u16::MAX || state.offset as int + 3 > usize::MAX {
                Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
            } else {
                part1_siz_components(payload, offset, Part1SizComponents {
                    offset: (state.offset + 3) as usize, component: (state.component + 1) as u16,
                    infos: state.infos.update(state.component as int, info),
                    first_precision: if state.component == 0 { precision as u8 } else { state.first_precision },
                    first_signed: if state.component == 0 { signed } else { state.first_signed },
                    uniform: if state.component > 0 && (precision != state.first_precision || signed != state.first_signed) {
                        false
                    } else { state.uniform },
                })
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_siz_finish(
    h: Part1SizHeader, components: Part1SizComponents, offset: usize, limits: &crate::ResourceLimits,
) -> Result<(Part1ParsedImageSize, u16), crate::DecodeError>
    recommends h.xsiz > h.xosiz, h.ysiz > h.yosiz, h.xsiz > h.xtosiz, h.ysiz > h.ytosiz,
{
    let width = (h.xsiz - h.xosiz) as u32;
    let height = (h.ysiz - h.yosiz) as u32;
    if width > crate::limits::resource_width_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Width,
            limit: crate::limits::resource_width_limit(limits) as u64, actual: width as u64 })
    } else if height > crate::limits::resource_height_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Height,
            limit: crate::limits::resource_height_limit(limits) as u64, actual: height as u64 })
    } else if width as int * height as int > u64::MAX {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
    } else if width as int * height as int > crate::limits::resource_pixel_limit(limits) {
        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Pixels,
            limit: crate::limits::resource_pixel_limit(limits), actual: (width * height) as u64 })
    } else {
        match part1_image_ceil_div((h.xsiz - h.xtosiz) as u32, h.xtsiz) {
            Err(error) => Err(error),
            Ok(across) => match part1_image_ceil_div((h.ysiz - h.ytosiz) as u32, h.ytsiz) {
                Err(error) => Err(error),
                Ok(down) => if across as int * down as int > u64::MAX {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
                } else if across as int * down as int > crate::limits::resource_tile_limit(limits) {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Tiles,
                        limit: crate::limits::resource_tile_limit(limits) as u64, actual: (across * down) as u64 })
                } else {
                    Ok((Part1ParsedImageSize {
                        geometry: (width, height, h.xosiz, h.yosiz, h.xtsiz, h.ytsiz, h.xtosiz, h.ytosiz, across, down),
                        components: h.components,
                        uniform_bit_depth: if components.uniform { Some(components.first_precision) } else { None },
                        uniform_signed: if components.uniform { Some(components.first_signed) } else { None },
                        infos: components.infos,
                    }, h.r_siz))
                },
            },
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn part1_parse_siz(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    -> Result<(Part1ParsedImageSize, u16), crate::DecodeError>
{
    match part1_siz_header(segment, limits) {
        Err(error) => Err(error),
        Ok(h) => match part1_siz_components(segment.payload, segment.offset, part1_siz_components_initial()) {
            Err(error) => Err(error),
            Ok(components) => part1_siz_finish(h, components, segment.offset, limits),
        },
    }
}

pub struct Part1ParsedCodingStyle {
    pub progression_order: crate::codestream::ProgressionOrder,
    pub layers: u16, pub multiple_component_transform: bool,
    pub decomposition_levels: u8, pub decomposition_structure: Option<u8>,
    pub decomposition_directions: Seq<crate::codestream::DecompositionDirection>,
    pub code_block_width: u16, pub code_block_height: u16, pub code_block_style: u8,
    pub transform: crate::codestream::WaveletTransform,
    pub precincts_defined: bool, pub sop_markers: bool, pub eph_markers: bool,
    pub precinct_exponents: Seq<(u8, u8)>,
}

#[verifier::opaque]
pub open spec fn part1_dfs_lookup(rows: Seq<(u8, Seq<crate::codestream::DecompositionDirection>)>, index: u8, position: nat)
    -> Option<(u8, Seq<crate::codestream::DecompositionDirection>)>
    decreases rows.len() - position,
{
    if position >= rows.len() { None }
    else if rows[position as int].0 == index { Some(rows[position as int]) }
    else { part1_dfs_lookup(rows, index, position + 1) }
}

#[verifier::opaque]
pub open spec fn part1_ads_lookup(
    rows: Seq<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)>, index: u8, position: nat,
) -> Option<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)>
    decreases rows.len() - position,
{
    if position >= rows.len() { None }
    else if rows[position as int].0 == index { Some(rows[position as int]) }
    else { part1_ads_lookup(rows, index, position + 1) }
}

#[verifier::opaque]
pub open spec fn part1_ads_depths_valid(depths: Seq<u8>, position: nat) -> bool
    decreases depths.len() - position,
{
    position >= depths.len() || (1 <= depths[position as int] <= 3 && part1_ads_depths_valid(depths, position + 1))
}

#[verifier::opaque]
pub open spec fn part1_decomposition_directions_from(
    style: Part1ParsedCodingStyle, directions: Seq<crate::codestream::DecompositionDirection>, stage: nat,
) -> Result<Part1ParsedCodingStyle, crate::DecodeError>
    decreases style.decomposition_levels as nat - stage,
{
    if stage >= style.decomposition_levels { Ok(style) }
    else if directions.len() == 0 || stage >= style.decomposition_directions.len() {
        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle))
    } else {
        let index = if stage < directions.len() { stage } else { (directions.len() - 1) as nat };
        part1_decomposition_directions_from(Part1ParsedCodingStyle {
            decomposition_directions: style.decomposition_directions.update(stage as int, directions[index as int]), ..style
        }, directions, stage + 1)
    }
}

#[verifier::opaque]
pub open spec fn part1_resolve_decomposition_style(style: Part1ParsedCodingStyle, extensions: Part2OwnedExtensions)
    -> Result<Part1ParsedCodingStyle, crate::DecodeError>
{
    match style.decomposition_structure {
        None => Ok(style),
        Some(index) => match part1_dfs_lookup(extensions.decompositions, index, 0) {
            Some(structure) => {
                if structure.1.len() == 0 {
                    Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle))
                } else { part1_decomposition_directions_from(style, structure.1, 0) }
            },
            None => match part1_ads_lookup(extensions.arbitrary, index, 0) {
                None => Err(part1_codestream_malformed(0, crate::MalformedKind::MissingRequiredStructure)),
                Some(decomposition) => {
                    if part1_ads_depths_valid(decomposition.1, 0) { Ok(style) }
                    else { Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle)) }
                },
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_set_component_style(
    owner: (u16, Seq<Part1ParsedCodingStyle>), component: u16, style: Part1ParsedCodingStyle,
) -> (Result<(), crate::DecodeError>, (u16, Seq<Part1ParsedCodingStyle>)) {
    if component >= owner.0 || component >= owner.1.len() {
        (Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle)), owner)
    } else { (Ok(()), (owner.0, owner.1.update(component as int, style))) }
}

#[verifier::opaque]
pub open spec fn part1_resolve_decompositions_from(
    owner: (u16, Seq<Part1ParsedCodingStyle>), extensions: Part2OwnedExtensions, component: nat,
) -> (Result<(), crate::DecodeError>, (u16, Seq<Part1ParsedCodingStyle>))
    decreases owner.0 as nat - component,
{
    if component >= owner.0 { (Ok(()), owner) }
    else if component >= owner.1.len() {
        (Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle)), owner)
    } else {
        let style = owner.1[component as int];
        match part1_resolve_decomposition_style(style, extensions) {
            Err(error) => (Err(error), owner),
            Ok(resolved) => {
                let updated = if style.decomposition_structure.is_some() {
                    (owner.0, owner.1.update(component as int, resolved))
                } else { owner };
                part1_resolve_decompositions_from(updated, extensions, component + 1)
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_resolve_decompositions(owner: (u16, Seq<Part1ParsedCodingStyle>), extensions: Part2OwnedExtensions)
    -> (Result<(), crate::DecodeError>, (u16, Seq<Part1ParsedCodingStyle>))
{
    part1_resolve_decompositions_from(owner, extensions, 0)
}

#[verifier::opaque]
pub open spec fn part1_component_styles_new(components: u16, default: Part1ParsedCodingStyle)
    -> Result<(u16, Seq<Part1ParsedCodingStyle>), crate::DecodeError>
{
    if components == 0 || components > 64 {
        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidImageGeometry))
    } else { Ok((components, Seq::new(64, |i: int| default))) }
}

#[verifier::opaque]
pub open spec fn part1_component_quantizations_new(components: u16, default: Part2Quantization)
    -> Result<(u16, Seq<Part2Quantization>), crate::DecodeError>
{
    if components == 0 || components > 64 {
        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidImageGeometry))
    } else { Ok((components, Seq::new(components as nat, |i: int| default))) }
}

#[verifier::opaque]
pub open spec fn part1_style_owner_lookup(owner: (u16, Seq<Part1ParsedCodingStyle>), component: u16)
    -> Result<Part1ParsedCodingStyle, crate::DecodeError>
{
    if component >= owner.0 || component >= owner.1.len() {
        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidCodingStyle))
    } else { Ok(owner.1[component as int]) }
}

#[verifier::opaque]
pub open spec fn part1_quantization_owner_lookup(owner: (u16, Seq<Part2Quantization>), component: u16)
    -> Result<Part2Quantization, crate::DecodeError>
{
    if component >= owner.0 || component >= owner.1.len() {
        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidQuantization))
    } else { Ok(owner.1[component as int]) }
}

#[verifier::opaque]
pub open spec fn part1_set_component_quantization(
    owner: (u16, Seq<Part2Quantization>), component: u16, value: Part2Quantization,
) -> (Result<(), crate::DecodeError>, (u16, Seq<Part2Quantization>)) {
    if component >= owner.0 || component >= owner.1.len() {
        (Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidQuantization)), owner)
    } else { (Ok(()), (owner.0, owner.1.update(component as int, value))) }
}

#[verifier::opaque]
pub open spec fn part1_quantization_compatible(
    value: Part2Quantization, style: (u8, Seq<crate::codestream::DecompositionDirection>),
) -> bool {
    match value.0 {
        crate::codestream::QuantizationStyle::None | crate::codestream::QuantizationStyle::ScalarExpounded =>
            value.2 == part2_subband_count(style.0, style.1),
        crate::codestream::QuantizationStyle::ScalarDerived => value.2 == 1,
    }
}

#[verifier::opaque]
pub open spec fn part1_style_overrides_from(
    components: u16, default: Part1ParsedCodingStyle, segments: Seq<Option<Part1CodestreamSegment>>,
    limits: &crate::ResourceLimits, owner: (u16, Seq<Part1ParsedCodingStyle>), component: nat,
) -> (Result<(), crate::DecodeError>, (u16, Seq<Part1ParsedCodingStyle>))
    decreases components as nat - component,
{
    if component >= components { (Ok(()), owner) }
    else {
        let step = if component >= segments.len() || segments[component as int].is_none() {
            (Ok(()), owner)
        } else {
            let segment = segments[component as int].unwrap();
            match part1_parse_coc(segment.offset, segment.payload, components, default, limits) {
                Err(error) => (Err(error), owner),
                Ok((_, style)) => part1_set_component_style(owner, component as u16, style),
            }
        };
        match step.0 {
            Err(error) => (Err(error), step.1),
            Ok(()) => part1_style_overrides_from(
                components, default, segments, limits, step.1, component + 1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_main_styles_from(
    components: u16, default: Part1ParsedCodingStyle, segments: Seq<Option<Part1CodestreamSegment>>,
    limits: &crate::ResourceLimits, owner: (u16, Seq<Part1ParsedCodingStyle>), component: nat,
) -> Result<(u16, Seq<Part1ParsedCodingStyle>), crate::DecodeError>
    decreases components as nat - component,
{
    if component >= components { Ok(owner) }
    else {
        let updated = if component >= segments.len() || segments[component as int].is_none() { Ok(owner) }
        else {
            let segment = segments[component as int].unwrap();
            match part1_parse_coc(segment.offset, segment.payload, components, default, limits) {
                Err(error) => Err(error),
                Ok((_, style)) => {
                    let set = part1_set_component_style(owner, component as u16, style);
                    match set.0 { Err(error) => Err(error), Ok(()) => Ok(set.1) }
                },
            }
        };
        match updated {
            Err(error) => Err(error),
            Ok(next) => part1_main_styles_from(components, default, segments, limits, next, component + 1),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_finish_main_styles(
    components: u16, default: Part1ParsedCodingStyle, segments: Seq<Option<Part1CodestreamSegment>>,
    limits: &crate::ResourceLimits, extensions: Part2OwnedExtensions,
) -> Result<(u16, Seq<Part1ParsedCodingStyle>), crate::DecodeError> {
    match part1_component_styles_new(components, default) {
        Err(error) => Err(error),
        Ok(owner) => match part1_main_styles_from(components, default, segments, limits, owner, 0) {
            Err(error) => Err(error),
            Ok(styles) => {
                let resolved = part1_resolve_decompositions(styles, extensions);
                match resolved.0 { Err(error) => Err(error), Ok(()) => Ok(resolved.1) }
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_quantization_overrides_from(
    components: u16, styles: (u16, Seq<Part1ParsedCodingStyle>), segments: Seq<Option<Part1CodestreamSegment>>,
    owner: (u16, Seq<Part2Quantization>), component: nat,
) -> (Result<(), crate::DecodeError>, (u16, Seq<Part2Quantization>))
    decreases components as nat - component,
{
    if component >= components { (Ok(()), owner) }
    else {
        let updated = if component >= segments.len() || segments[component as int].is_none() { (Ok(()), owner) }
        else {
            let segment = segments[component as int].unwrap();
            match part1_style_owner_lookup(styles, component as u16) {
                Err(error) => (Err(error), owner),
                Ok(style) => match part1_parse_qcc(segment.offset, segment.payload, components, style) {
                    Err(error) => (Err(error), owner),
                    Ok((_, value)) => part1_set_component_quantization(owner, component as u16, value),
                },
            }
        };
        match updated.0 {
            Err(error) => (Err(error), updated.1),
            Ok(()) => match part1_quantization_owner_lookup(updated.1, component as u16) {
                Err(error) => (Err(error), updated.1),
                Ok(value) => match part1_style_owner_lookup(styles, component as u16) {
                    Err(error) => (Err(error), updated.1),
                    Ok(style) => if !part1_quantization_compatible(value, (style.decomposition_levels, style.decomposition_directions)) {
                        (Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidQuantization)), updated.1)
                    } else { part1_quantization_overrides_from(components, styles, segments, updated.1, component + 1) },
                },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_main_quantizations_from(
    components: u16, styles: (u16, Seq<Part1ParsedCodingStyle>), segments: Seq<Option<Part1CodestreamSegment>>,
    owner: (u16, Seq<Part2Quantization>), component: nat,
) -> Result<(u16, Seq<Part2Quantization>), crate::DecodeError>
    decreases components as nat - component,
{
    if component >= components { Ok(owner) }
    else {
        let updated = if component >= segments.len() || segments[component as int].is_none() { Ok(owner) }
        else {
            let segment = segments[component as int].unwrap();
            match part1_style_owner_lookup(styles, component as u16) {
                Err(error) => Err(error),
                Ok(style) => match part1_parse_qcc(segment.offset, segment.payload, components, style) {
                    Err(error) => Err(error),
                    Ok((_, value)) => {
                        let set = part1_set_component_quantization(owner, component as u16, value);
                        match set.0 { Err(error) => Err(error), Ok(()) => Ok(set.1) }
                    },
                },
            }
        };
        match updated {
            Err(error) => Err(error),
            Ok(next) => match part1_quantization_owner_lookup(next, component as u16) {
                Err(error) => Err(error),
                Ok(value) => match part1_style_owner_lookup(styles, component as u16) {
                    Err(error) => Err(error),
                    Ok(style) => if !part1_quantization_compatible(value, (style.decomposition_levels, style.decomposition_directions)) {
                        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidQuantization))
                    } else { part1_main_quantizations_from(components, styles, segments, next, component + 1) },
                },
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_finish_main_quantizations(
    components: u16, default: Part2Quantization, styles: (u16, Seq<Part1ParsedCodingStyle>),
    segments: Seq<Option<Part1CodestreamSegment>>,
) -> Result<(u16, Seq<Part2Quantization>), crate::DecodeError> {
    match part1_component_quantizations_new(components, default) {
        Err(error) => Err(error),
        Ok(owner) => part1_main_quantizations_from(components, styles, segments, owner, 0),
    }
}

#[verifier::opaque]
pub open spec fn part1_finish_tile_components(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc_segments: Seq<Option<Part1CodestreamSegment>>, qcd_segment: Option<Part1CodestreamSegment>,
    default_quantization: Part2Quantization, qcc_segments: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited_quantizations: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
) -> Result<((u16, Seq<Part1ParsedCodingStyle>), Part2Quantization, (u16, Seq<Part2Quantization>)), crate::DecodeError> {
    let initial = if cod_seen { part1_component_styles_new(components, coding_style) } else { Ok(inherited_styles) };
    match initial {
        Err(error) => Err(error),
        Ok(styles) => {
            let overrides = part1_style_overrides_from(components, coding_style, coc_segments, limits, styles, 0);
            match overrides.0 {
                Err(error) => Err(error),
                Ok(()) => {
                    let resolved = part1_resolve_decompositions(overrides.1, extensions);
                    match resolved.0 {
                        Err(error) => Err(error),
                        Ok(()) => {
                            let default = match qcd_segment {
                                None => Ok(default_quantization),
                                Some(segment) => part1_parse_qcd_payload(segment.offset, segment.payload, coding_style),
                            };
                            match default {
                                Err(error) => Err(error),
                                Ok(quantization) => {
                                    let initial_quantizations = if qcd_segment.is_some() {
                                        part1_component_quantizations_new(components, quantization)
                                    } else { Ok(inherited_quantizations) };
                                    match initial_quantizations {
                                        Err(error) => Err(error),
                                        Ok(owner) => {
                                            let applied = part1_quantization_overrides_from(
                                                components, resolved.1, qcc_segments, owner, 0);
                                            match applied.0 {
                                                Err(error) => Err(error),
                                                Ok(()) => Ok((resolved.1, quantization, applied.1)),
                                            }
                                        },
                                    }
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

pub struct Part1CodHeader {
    pub flags: u8, pub progression_order: crate::codestream::ProgressionOrder,
    pub layers: u16, pub multiple_component_transform: bool, pub decomposition_levels: u8,
    pub code_block_width: u16, pub code_block_height: u16, pub code_block_style: u8,
    pub transform: crate::codestream::WaveletTransform, pub precinct_count: usize,
}

pub open spec fn part1_cod_progression(value: u8) -> Option<crate::codestream::ProgressionOrder> {
    match value {
        0 => Some(crate::codestream::ProgressionOrder::Lrcp),
        1 => Some(crate::codestream::ProgressionOrder::Rlcp),
        2 => Some(crate::codestream::ProgressionOrder::Rpcl),
        3 => Some(crate::codestream::ProgressionOrder::Pcrl),
        4 => Some(crate::codestream::ProgressionOrder::Cprl),
        _ => None,
    }
}

#[verifier::opaque]
pub open spec fn part1_cod_header(offset: usize, payload: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part1CodHeader, crate::DecodeError>
{
    if payload.len() < 10 { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength)) }
    else if payload[0] & 248 != 0 { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle)) }
    else {
        match part1_cod_progression(payload[1]) {
            None => Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle)),
            Some(progression_order) => {
                let layers = part1_marker_value(payload[2], payload[3]);
                if layers > crate::limits::resource_layer_limit(limits) {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Layers,
                        limit: crate::limits::resource_layer_limit(limits) as u64, actual: layers as u64 })
                } else if layers == 0 || payload[4] > 1 {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle))
                } else if payload[5] == u8::MAX {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    let resolutions = (payload[5] + 1) as u8;
                    if resolutions > crate::limits::resource_resolution_limit(limits) {
                        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::Resolutions,
                            limit: crate::limits::resource_resolution_limit(limits) as u64, actual: resolutions as u64 })
                    } else if payload[6] > 8 || payload[7] > 8 {
                        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle))
                    } else {
                        let width = 1u16 << ((payload[6] as u32) + 2);
                        let height = 1u16 << ((payload[7] as u32) + 2);
                        if width as int * height as int > u32::MAX {
                            Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
                        } else if width as int * height as int > 4096 || part1_tier1_block_coding_byte(payload[8]).is_err() {
                            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle))
                        } else {
                            let count = resolutions as usize;
                            let expected = if payload[0] & 1 != 0 { 10int + count as int } else { 10int };
                            if expected > usize::MAX { Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow)) }
                            else if payload.len() != expected { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength)) }
                            else {
                                Ok(Part1CodHeader {
                                    flags: payload[0], progression_order, layers,
                                    multiple_component_transform: payload[4] == 1, decomposition_levels: payload[5],
                                    code_block_width: width, code_block_height: height, code_block_style: payload[8],
                                    transform: match payload[9] { 0 => crate::codestream::WaveletTransform::Irreversible9x7,
                                        1 => crate::codestream::WaveletTransform::Reversible5x3,
                                        index => crate::codestream::WaveletTransform::Arbitrary(index) },
                                    precinct_count: count,
                                })
                            }
                        }
                    }
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_cod_precincts(
    offset: usize, payload: Seq<u8>, count: usize, resolution: usize, precincts: Seq<(u8, u8)>,
) -> Result<Seq<(u8, u8)>, crate::DecodeError>
    decreases count - resolution,
{
    if resolution >= count { Ok(precincts) }
    else if 10int + resolution as int > usize::MAX {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
    } else {
        let index = 10int + resolution as int;
        if index >= payload.len() || resolution as nat >= precincts.len() {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle))
        } else if resolution == usize::MAX {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
        } else {
            part1_cod_precincts(offset, payload, count, (resolution + 1) as usize,
                precincts.update(resolution as int, (payload[index] & 15, payload[index] >> 4)))
        }
    }
}

pub open spec fn part1_cod_from_header(h: Part1CodHeader, precincts: Seq<(u8, u8)>) -> Part1ParsedCodingStyle {
    Part1ParsedCodingStyle {
        progression_order: h.progression_order, layers: h.layers,
        multiple_component_transform: h.multiple_component_transform,
        decomposition_levels: h.decomposition_levels, decomposition_structure: None,
        decomposition_directions: Seq::new(32, |i: int| crate::codestream::DecompositionDirection::TwoDimensional),
        code_block_width: h.code_block_width, code_block_height: h.code_block_height, code_block_style: h.code_block_style,
        transform: h.transform, precincts_defined: h.flags & 1 != 0, sop_markers: h.flags & 2 != 0,
        eph_markers: h.flags & 4 != 0, precinct_exponents: precincts,
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_cod_payload(offset: usize, payload: Seq<u8>, limits: &crate::ResourceLimits)
    -> Result<Part1ParsedCodingStyle, crate::DecodeError>
{
    match part1_cod_header(offset, payload, limits) {
        Err(error) => Err(error),
        Ok(h) => {
            let initial = Seq::new(33, |i: int| (15u8, 15u8));
            match if h.flags & 1 != 0 { part1_cod_precincts(offset, payload, h.precinct_count, 0, initial) } else { Ok(initial) } {
                Err(error) => Err(error),
                Ok(precincts) => Ok(part1_cod_from_header(h, precincts)),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_component_index(
    offset: usize, payload: Seq<u8>, components: u16, invalid_kind: crate::MalformedKind,
) -> Result<(u16, usize), crate::DecodeError> {
    let bytes = if components < 257 { 1usize } else { 2usize };
    if payload.len() < bytes {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let component = if bytes == 1 { payload[0] as u16 } else { part1_marker_value(payload[0], payload[1]) };
        if component >= components { Err(part1_codestream_malformed(offset, invalid_kind)) }
        else { Ok((component, bytes)) }
    }
}

pub struct Part1CocPrepared {
    pub component: u16,
    pub payload: Seq<u8>,
    pub decomposition_structure: Option<u8>,
}

pub open spec fn part1_cod_progression_byte(order: crate::codestream::ProgressionOrder) -> u8 {
    match order {
        crate::codestream::ProgressionOrder::Lrcp => 0,
        crate::codestream::ProgressionOrder::Rlcp => 1,
        crate::codestream::ProgressionOrder::Rpcl => 2,
        crate::codestream::ProgressionOrder::Pcrl => 3,
        crate::codestream::ProgressionOrder::Cprl => 4,
    }
}

pub open spec fn part1_coc_cod_payload(
    parameters: Seq<u8>, scoc: u8, default: Part1ParsedCodingStyle, structure: Option<u8>,
) -> Seq<u8>
    recommends parameters.len() >= 5,
{
    let prefix = seq![
        (scoc & 1) | (if default.sop_markers { 2u8 } else { 0u8 }) | (if default.eph_markers { 4u8 } else { 0u8 }),
        part1_cod_progression_byte(default.progression_order),
        (default.layers >> 8) as u8,
        (default.layers & 255) as u8,
        if default.multiple_component_transform { 1u8 } else { 0u8 },
    ];
    let payload = prefix + parameters;
    if structure.is_some() { payload.update(5, default.decomposition_levels) } else { payload }
}

#[verifier::opaque]
pub open spec fn part1_coc_prepare(
    offset: usize, payload: Seq<u8>, components: u16, default: Part1ParsedCodingStyle,
) -> Result<Part1CocPrepared, crate::DecodeError> {
    match part1_parse_component_index(offset, payload, components, crate::MalformedKind::InvalidCodingStyle) {
        Err(error) => Err(error),
        Ok((component, bytes)) => {
            if payload.len() < bytes as int + 6 {
                Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
            } else if payload[bytes as int] & 254 != 0 {
                Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle))
            } else {
                let parameters = payload.subrange(bytes as int + 1, payload.len() as int);
                let structure = if parameters[0] & 128 != 0 { Some(parameters[0] & 127) } else { None };
                if structure == Some(0u8) {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidCodingStyle))
                } else if parameters.len() + 5 > usize::MAX {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
                } else if parameters.len() + 5 > 43 {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
                } else {
                    Ok(Part1CocPrepared { component,
                        payload: part1_coc_cod_payload(parameters, payload[bytes as int], default, structure),
                        decomposition_structure: structure })
                }
            }
        },
    }
}

pub open spec fn part1_coc_style(style: Part1ParsedCodingStyle, structure: Option<u8>) -> Part1ParsedCodingStyle {
    Part1ParsedCodingStyle {
        progression_order: style.progression_order, layers: style.layers,
        multiple_component_transform: style.multiple_component_transform,
        decomposition_levels: style.decomposition_levels, decomposition_structure: structure,
        decomposition_directions: style.decomposition_directions,
        code_block_width: style.code_block_width, code_block_height: style.code_block_height,
        code_block_style: style.code_block_style, transform: style.transform,
        precincts_defined: style.precincts_defined, sop_markers: style.sop_markers, eph_markers: style.eph_markers,
        precinct_exponents: style.precinct_exponents,
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_coc(
    offset: usize, payload: Seq<u8>, components: u16, default: Part1ParsedCodingStyle,
    limits: &crate::ResourceLimits,
) -> Result<(u16, Part1ParsedCodingStyle), crate::DecodeError> {
    match part1_coc_prepare(offset, payload, components, default) {
        Err(error) => Err(error),
        Ok(prepared) => match part1_parse_cod_payload(offset, prepared.payload, limits) {
            Err(error) => Err(error),
            Ok(style) => Ok((prepared.component, part1_coc_style(style, prepared.decomposition_structure))),
        },
    }
}

pub struct Part1QcdHeader {
    pub style: crate::codestream::QuantizationStyle,
    pub guard_bits: u8,
    pub subband_count: u16,
}

#[verifier::opaque]
pub open spec fn part1_qcd_header(offset: usize, payload: Seq<u8>, coding: Part1ParsedCodingStyle)
    -> Result<Part1QcdHeader, crate::DecodeError>
{
    if payload.len() == 0 {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let style = match payload[0] & 31 {
            0 => Some(crate::codestream::QuantizationStyle::None),
            1 => Some(crate::codestream::QuantizationStyle::ScalarDerived),
            2 => Some(crate::codestream::QuantizationStyle::ScalarExpounded),
            _ => None,
        };
        match style {
            None => Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidQuantization)),
            Some(style) => {
                let count = part2_subband_count(coding.decomposition_levels, coding.decomposition_directions);
                let expected = match style {
                    crate::codestream::QuantizationStyle::None => count as int,
                    crate::codestream::QuantizationStyle::ScalarDerived => 2int,
                    crate::codestream::QuantizationStyle::ScalarExpounded => count as int * 2,
                };
                if expected > usize::MAX {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
                } else if payload.len() - 1 != expected {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
                } else {
                    Ok(Part1QcdHeader { style, guard_bits: payload[0] >> 5, subband_count: count })
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_qcd_validate_unscaled(offset: usize, payload: Seq<u8>, position: usize)
    -> Result<(), crate::DecodeError>
    decreases payload.len() - position,
{
    if position as nat >= payload.len() { Ok(()) }
    else if payload[position as int] & 7 != 0 {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidQuantization))
    } else if position == usize::MAX {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
    } else { part1_qcd_validate_unscaled(offset, payload, (position + 1) as usize) }
}

#[verifier::opaque]
pub open spec fn part1_qcd_step(
    offset: usize, payload: Seq<u8>, style: crate::codestream::QuantizationStyle, position: usize,
) -> Result<crate::transform::QuantizationStep, crate::DecodeError> {
    let index = if style == crate::codestream::QuantizationStyle::None { position as int + 1 } else { position as int * 2 + 1 };
    if index > usize::MAX {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
    } else if style == crate::codestream::QuantizationStyle::None {
        if index >= payload.len() {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidQuantization))
        } else { Ok(crate::transform::QuantizationStep { exponent: payload[index] >> 3, mantissa: 0 }) }
    } else if index + 1 > usize::MAX {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
    } else if index + 1 >= payload.len() {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidQuantization))
    } else {
        let word = part1_marker_value(payload[index], payload[index + 1]);
        Ok(crate::transform::QuantizationStep { exponent: (word >> 11) as u8, mantissa: word & 2047 })
    }
}

#[verifier::opaque]
pub open spec fn part1_qcd_steps(
    offset: usize, payload: Seq<u8>, style: crate::codestream::QuantizationStyle,
    total: usize, position: usize, steps: Seq<crate::transform::QuantizationStep>,
) -> Result<Seq<crate::transform::QuantizationStep>, crate::DecodeError>
    decreases total - position,
{
    if position >= total { Ok(steps) }
    else {
        match part1_qcd_step(offset, payload, style, position) {
            Err(error) => Err(error),
            Ok(step) => if position as nat >= steps.len() {
                Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidQuantization))
            } else if position == usize::MAX {
                Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
            } else {
                part1_qcd_steps(offset, payload, style, total, (position + 1) as usize, steps.update(position as int, step))
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_qcd_after_validation(offset: usize, payload: Seq<u8>, h: Part1QcdHeader)
    -> Result<Part2Quantization, crate::DecodeError>
{
    let count = if h.style == crate::codestream::QuantizationStyle::ScalarDerived { 1u16 } else { h.subband_count };
    if count > 97 {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidQuantization))
    } else {
        let initial = Seq::new(97, |i: int| crate::transform::QuantizationStep { exponent: 0, mantissa: 0 });
        match part1_qcd_steps(offset, payload, h.style, count as usize, 0, initial) {
            Err(error) => Err(error),
            Ok(steps) => Ok((h.style, h.guard_bits, count, steps)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_qcd_payload(offset: usize, payload: Seq<u8>, coding: Part1ParsedCodingStyle)
    -> Result<Part2Quantization, crate::DecodeError>
{
    match part1_qcd_header(offset, payload, coding) {
        Err(error) => Err(error),
        Ok(h) => {
            let validation = if h.style == crate::codestream::QuantizationStyle::None {
                part1_qcd_validate_unscaled(offset, payload, 1)
            } else { Ok(()) };
            match validation {
                Err(error) => Err(error),
                Ok(()) => part1_qcd_after_validation(offset, payload, h),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_qcc(
    offset: usize, payload: Seq<u8>, components: u16, coding: Part1ParsedCodingStyle,
) -> Result<(u16, Part2Quantization), crate::DecodeError> {
    match part1_parse_component_index(offset, payload, components, crate::MalformedKind::InvalidQuantization) {
        Err(error) => Err(error),
        Ok((component, bytes)) => match part1_parse_qcd_payload(offset, payload.subrange(bytes as int, payload.len() as int), coding) {
            Err(error) => Err(error),
            Ok(quantization) => Ok((component, quantization)),
        },
    }
}

pub open spec fn part1_metadata_byte_limit(limits: &crate::ResourceLimits) -> u64 {
    crate::limits::resource_metadata_byte_limit(limits)
}

pub open spec fn part1_extension_components(
    extensions: Part2OwnedExtensions, metadata_bytes: u64,
    registrations: Seq<crate::codestream::ComponentRegistration>,
) -> Part2OwnedExtensions {
    Part2OwnedExtensions {
        decompositions: extensions.decompositions, arbitrary: extensions.arbitrary,
        nonlinear: extensions.nonlinear, depths: extensions.depths, kernels: extensions.kernels,
        registrations, lengths: extensions.lengths, metadata_bytes,
    }
}

#[verifier::opaque]
pub open spec fn part1_charge_extension_metadata<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let length = segment.payload.len() as u64;
    if length as int + 4 > u64::MAX {
        (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state, extensions)
    } else {
        let bytes = (length + 4) as u64;
        if extensions.metadata_bytes as int + bytes as int > u64::MAX {
            (Err(part1_codestream_malformed(state.position, crate::MalformedKind::ArithmeticOverflow)), state, extensions)
        } else {
            let next = (extensions.metadata_bytes + bytes) as u64;
            let updated = part1_extension_components(extensions, next, extensions.registrations);
            let maximum = part1_metadata_byte_limit(state.limits);
            if next > maximum {
                (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::MetadataBytes,
                    limit: maximum, actual: next }), state, updated)
            } else {
                let charged = part1_codestream_charge_work(state, bytes);
                (charged.0, charged.1, updated)
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_segment_byte(
    parser_position: usize, segment: Part1CodestreamSegment, position: usize, relative: usize,
) -> Result<u8, crate::DecodeError> {
    let index = position as int + relative as int;
    if index > usize::MAX {
        Err(part1_codestream_malformed(parser_position, crate::MalformedKind::ArithmeticOverflow))
    } else if index >= segment.payload.len() {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else { Ok(segment.payload[index]) }
}

pub open spec fn part1_crg_registrations(payload: Seq<u8>) -> Seq<crate::codestream::ComponentRegistration> {
    Seq::new(payload.len() / 4, |index: int| crate::codestream::ComponentRegistration {
        horizontal: part1_marker_value(payload[4 * index], payload[4 * index + 1]),
        vertical: part1_marker_value(payload[4 * index + 2], payload[4 * index + 3]),
    })
}

#[verifier::opaque]
pub open spec fn part1_parse_crg<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, components: u16,
    extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { charged }
    else if segment.payload.len() != part2_crg_payload_bytes(components) {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), charged.1, charged.2)
    } else if charged.2.registrations.len() != 0 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)), charged.1, charged.2)
    } else {
        (Ok(()), charged.1, part1_extension_components(charged.2, charged.2.metadata_bytes,
            part1_crg_registrations(segment.payload)))
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_rgn(offset: usize, payload: Seq<u8>, components: u16)
    -> Result<(u16, u8), crate::DecodeError>
{
    let bytes = if components < 257 { 1usize } else { 2usize };
    if payload.len() != bytes as int + 2 {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let component = if bytes == 1 { payload[0] as u16 } else { part1_marker_value(payload[0], payload[1]) };
        if component >= components || payload[bytes as int] != 0 {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidRegionOfInterest))
        } else { Ok((component, payload[bytes as int + 1])) }
    }
}

pub open spec fn part1_decomposition_code(value: u8) -> crate::codestream::DecompositionDirection {
    match value {
        0 => crate::codestream::DecompositionDirection::None,
        1 => crate::codestream::DecompositionDirection::TwoDimensional,
        2 => crate::codestream::DecompositionDirection::Horizontal,
        _ => crate::codestream::DecompositionDirection::Vertical,
    }
}

pub open spec fn part1_two_bit_padding_mask(count: usize) -> u8 {
    if count % 4 == 0 { 0 } else { ((1u16 << ((2 * (4 - count % 4)) as u32)) - 1) as u8 }
}

#[verifier::opaque]
pub open spec fn part1_unpack_two_bit_run(
    parser_position: usize, segment: Part1CodestreamSegment, start: usize, count: usize,
    allow_terminal: bool, position: usize, values: Seq<u8>,
) -> Result<Seq<u8>, crate::DecodeError>
    decreases count - position,
{
    if position < count {
        match part1_segment_byte(parser_position, segment, start, position / 4) {
            Err(error) => Err(error),
            Ok(byte) => {
                let value = part2_dfs_direction_code(byte, (position % 4) as u8);
                if !allow_terminal && value == 0 {
                    Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidCodingStyle))
                } else if position == usize::MAX {
                    Err(part1_codestream_malformed(parser_position, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    part1_unpack_two_bit_run(parser_position, segment, start, count, allow_terminal,
                        (position + 1) as usize, values.push(value))
                }
            },
        }
    } else if count % 4 != 0 {
        match part1_segment_byte(parser_position, segment, start, count / 4) {
            Err(error) => Err(error),
            Ok(last) => if last & part1_two_bit_padding_mask(count) != 0 {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidCodingStyle))
            } else { Ok(values) },
        }
    } else { Ok(values) }
}

pub open spec fn part1_unpack_two_bit_values(
    parser_position: usize, segment: Part1CodestreamSegment, start: usize, count: usize, allow_terminal: bool,
) -> Result<Seq<u8>, crate::DecodeError> {
    part1_unpack_two_bit_run(parser_position, segment, start, count, allow_terminal, 0, Seq::empty())
}

#[verifier::opaque]
pub open spec fn part1_dfs_payload(segment: Part1CodestreamSegment)
    -> Result<(u8, Seq<crate::codestream::DecompositionDirection>), crate::DecodeError>
{
    if segment.payload.len() < 3 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let descriptor = part1_marker_value(segment.payload[0], segment.payload[1]);
        let index = (descriptor & 15) as u8;
        let levels = segment.payload[2];
        let expected = 3int + (levels as int + 3) / 4;
        if descriptor & 65520 != 0 || index == 0 || levels == 0 || levels > 32 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidCodingStyle))
        } else if segment.payload.len() != expected {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
        } else {
            Ok((index, Seq::new(levels as nat, |level: int| part1_decomposition_code(
                part2_dfs_direction_code(segment.payload[3 + level / 4], (level % 4) as u8)))))
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_ads_payload(parser_position: usize, segment: Part1CodestreamSegment)
    -> Result<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>), crate::DecodeError>
{
    if segment.payload.len() < 3 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let index = segment.payload[0];
        if index == 0 || index > 127 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidCodingStyle))
        } else {
            let depth_count = segment.payload[1] as usize;
            let split_position = 2int + part2_packed_two_bit_bytes(depth_count) as int;
            if split_position >= segment.payload.len() {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
            } else {
                let split_count = segment.payload[split_position] as usize;
                let expected = split_position + 1 + part2_packed_two_bit_bytes(split_count) as int;
                if segment.payload.len() != expected {
                    Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
                } else {
                    match part1_unpack_two_bit_values(parser_position, segment, 2, depth_count, false) {
                        Err(error) => Err(error),
                        Ok(depths) => match part1_unpack_two_bit_values(parser_position, segment,
                            (split_position + 1) as usize, split_count, true) {
                            Err(error) => Err(error),
                            Ok(splits) => Ok((index, depths, splits.map_values(|code: u8| part1_decomposition_code(code)))),
                        },
                    }
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_dfs_replace(
    entries: Seq<(u8, Seq<crate::codestream::DecompositionDirection>)>,
    replacement: (u8, Seq<crate::codestream::DecompositionDirection>), position: nat,
) -> Seq<(u8, Seq<crate::codestream::DecompositionDirection>)>
    decreases entries.len() - position,
{
    if position as nat >= entries.len() { entries.push(replacement) }
    else if entries[position as int].0 == replacement.0 { entries.update(position as int, replacement) }
    else { part1_dfs_replace(entries, replacement, position + 1) }
}

#[verifier::opaque]
pub open spec fn part1_ads_replace(
    entries: Seq<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)>,
    replacement: (u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>), position: nat,
) -> Seq<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)>
    decreases entries.len() - position,
{
    if position as nat >= entries.len() { entries.push(replacement) }
    else if entries[position as int].0 == replacement.0 { entries.update(position as int, replacement) }
    else { part1_ads_replace(entries, replacement, position + 1) }
}

pub open spec fn part1_extension_decompositions(
    extensions: Part2OwnedExtensions,
    decompositions: Seq<(u8, Seq<crate::codestream::DecompositionDirection>)>,
    arbitrary: Seq<(u8, Seq<u8>, Seq<crate::codestream::DecompositionDirection>)>,
) -> Part2OwnedExtensions {
    Part2OwnedExtensions {
        decompositions, arbitrary, nonlinear: extensions.nonlinear, depths: extensions.depths,
        kernels: extensions.kernels, registrations: extensions.registrations,
        lengths: extensions.lengths, metadata_bytes: extensions.metadata_bytes,
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_dfs<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { charged }
    else {
        match part1_dfs_payload(segment) {
            Err(error) => (Err(error), charged.1, charged.2),
            Ok(replacement) => (Ok(()), charged.1, part1_extension_decompositions(charged.2,
                part1_dfs_replace(charged.2.decompositions, replacement, 0), charged.2.arbitrary)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_ads<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { charged }
    else {
        match part1_ads_payload(charged.1.position, segment) {
            Err(error) => (Err(error), charged.1, charged.2),
            Ok(replacement) => (Ok(()), charged.1, part1_extension_decompositions(charged.2,
                charged.2.decompositions, part1_ads_replace(charged.2.arbitrary, replacement, 0))),
        }
    }
}

pub open spec fn part1_extension_depths(
    extensions: Part2OwnedExtensions, depths: Seq<crate::codestream::ComponentBitDepth>,
) -> Part2OwnedExtensions {
    Part2OwnedExtensions {
        decompositions: extensions.decompositions, arbitrary: extensions.arbitrary,
        nonlinear: extensions.nonlinear, depths, kernels: extensions.kernels,
        registrations: extensions.registrations, lengths: extensions.lengths,
        metadata_bytes: extensions.metadata_bytes,
    }
}

pub open spec fn part1_cbd_expand(
    depths: Seq<crate::codestream::ComponentBitDepth>, repeated: bool, components: u16,
) -> Seq<crate::codestream::ComponentBitDepth> {
    if repeated && depths.len() > 0 {
        Seq::new(if components == 0 { 1 } else { components as nat }, |index: int| depths[0])
    } else { depths }
}

#[verifier::opaque]
pub open spec fn part1_cbd_run(
    segment: Part1CodestreamSegment, position: nat,
    depths: Seq<crate::codestream::ComponentBitDepth>, repeated: bool, components: u16,
) -> (Result<(), crate::DecodeError>, Seq<crate::codestream::ComponentBitDepth>)
    decreases segment.payload.len() - position,
{
    if position >= segment.payload.len() {
        (Ok(()), part1_cbd_expand(depths, repeated, components))
    } else {
        let packed = segment.payload[position as int];
        let precision = part2_cbd_precision(packed);
        if precision > 38 {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), depths)
        } else {
            part1_cbd_run(segment, position + 1, depths.push(crate::codestream::ComponentBitDepth {
                precision, signed: part2_cbd_signed(packed),
            }), repeated, components)
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_cbd<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, components: u16,
    extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { charged }
    else if segment.payload.len() < 2 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), charged.1, charged.2)
    } else {
        let descriptor = part1_marker_value(segment.payload[0], segment.payload[1]);
        let repeated = descriptor & 32768 != 0;
        let count = descriptor & 32767;
        let expected = 2 + if repeated { 1int } else { count as int };
        if count != components || segment.payload.len() != expected {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), charged.1, charged.2)
        } else {
            let decoded = part1_cbd_run(segment, 2, Seq::empty(), repeated, components);
            (decoded.0, charged.1, part1_extension_depths(charged.2, decoded.1))
        }
    }
}

pub open spec fn part1_set_bits_prefix(value: u32, bits: nat) -> nat
    recommends bits <= 32,
    decreases bits,
{
    if bits == 0 { 0 } else {
        part1_set_bits_prefix(value, (bits - 1) as nat)
            + if value & (1u32 << ((bits - 1) as u32)) != 0 { 1nat } else { 0nat }
    }
}

pub open spec fn part1_marker_word_sequence(payload: Seq<u8>) -> Seq<u16> {
    Seq::new(payload.len() / 2, |index: int| part1_marker_value(payload[2 * index], payload[2 * index + 1]))
}

#[verifier::opaque]
pub open spec fn part1_marker_words(segment: Part1CodestreamSegment, start: usize)
    -> Result<Seq<u16>, crate::DecodeError>
{
    if start > segment.payload.len() || (segment.payload.len() - start as int) % 2 != 0 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else { Ok(part1_marker_word_sequence(segment.payload.subrange(start as int, segment.payload.len() as int))) }
}

#[verifier::opaque]
pub open spec fn part1_parse_cap(segment: Part1CodestreamSegment)
    -> Result<(u32, Seq<u16>), crate::DecodeError>
{
    if segment.payload.len() < 4 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let p_cap = part1_siz_word(segment.payload, 0);
        if p_cap == 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidProfile))
        } else if segment.payload.len() != part15_cap_payload_length(part1_set_bits_prefix(p_cap, 32) as u8) {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
        } else {
            match part1_marker_words(segment, 4) {
                Err(error) => Err(error),
                Ok(words) => Ok((p_cap, words)),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_profile_number(segment: Part1CodestreamSegment)
    -> Result<Seq<u16>, crate::DecodeError>
{
    if segment.payload.len() < 2 || segment.payload.len() % 2 != 0 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        match part1_marker_words(segment, 0) {
            Err(error) => Err(error),
            Ok(words) => if words[words.len() as int - 1] == 0 {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidProfile))
            } else { Ok(words) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_copy_segment_tail(segment: Part1CodestreamSegment, start: usize)
    -> Result<Seq<u8>, crate::DecodeError>
{
    if start > segment.payload.len() {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else { Ok(segment.payload.subrange(start as int, segment.payload.len() as int)) }
}

pub open spec fn part1_maximum_u32_for_bits(bits: u8) -> Result<u32, crate::DecodeError> {
    if bits == 0 || bits > 31 {
        Err(part1_codestream_malformed(0, crate::MalformedKind::ArithmeticOverflow))
    } else { Ok(((1u64 << bits) - 1) as u32) }
}

pub open spec fn part1_nlt_gamma_word(payload: Seq<u8>, index: int) -> u32
    recommends 0 <= index < 5, payload.len() == 19,
{
    ((payload[4 + 3 * index] as u32) << 16)
        | ((payload[5 + 3 * index] as u32) << 8) | payload[6 + 3 * index] as u32
}

#[verifier::opaque]
pub open spec fn part1_nlt_gamma(segment: Part1CodestreamSegment) -> Result<[u32; 5], crate::DecodeError> {
    if segment.payload.len() != 19 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let parameters = [
            part1_nlt_gamma_word(segment.payload, 0), part1_nlt_gamma_word(segment.payload, 1),
            part1_nlt_gamma_word(segment.payload, 2), part1_nlt_gamma_word(segment.payload, 3),
            part1_nlt_gamma_word(segment.payload, 4),
        ];
        if parameters[0] == 0 || parameters[1] == 0 || parameters[3] == 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else { Ok(parameters) }
    }
}

pub open spec fn part1_nlt_point_width(bits: u8) -> usize {
    if bits <= 8 { 1 } else if bits <= 16 { 2 } else { 4 }
}

pub open spec fn part1_nlt_point_value(payload: Seq<u8>, width: usize, index: int) -> u32
    recommends 0 <= index, width == 1 || width == 2 || width == 4,
        15 + width as int * (index + 1) <= payload.len(),
{
    let position = 15 + width as int * index;
    if width == 1 { payload[position] as u32 }
    else if width == 2 { part1_marker_value(payload[position], payload[position + 1]) as u32 }
    else { part1_siz_word(payload, position) }
}

#[verifier::opaque]
pub open spec fn part1_nlt_points_header(segment: Part1CodestreamSegment)
    -> Result<(u16, u32, u32, u8, usize), crate::DecodeError>
{
    if segment.payload.len() < 15 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let stored = part1_marker_value(segment.payload[4], segment.payload[5]);
        if stored == 0 || stored > 8191 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else {
            let minimum = part1_siz_word(segment.payload, 6);
            let maximum = part1_siz_word(segment.payload, 10);
            let bits = segment.payload[14];
            let width = part1_nlt_point_width(bits);
            if minimum >= maximum || bits == 0 || bits > 32 {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
            } else if segment.payload.len() != 15 + (stored as int + 1) * width as int {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
            } else { Ok(((stored + 1) as u16, minimum, maximum, bits, width)) }
        }
    }
}

pub open spec fn part1_nlt_point_maximum(bits: u8) -> u32 {
    if bits == 32 { u32::MAX } else { ((1u64 << bits) - 1) as u32 }
}

#[verifier::opaque]
pub open spec fn part1_nlt_points(segment: Part1CodestreamSegment)
    -> Result<(u32, u32, u8, Seq<u32>), crate::DecodeError>
{
    match part1_nlt_points_header(segment) {
        Err(error) => Err(error),
        Ok(header) => {
            let values = Seq::new(header.0 as nat, |index: int| part1_nlt_point_value(segment.payload, header.4, index));
            if forall|index: int| 0 <= index < values.len() ==> values[index] <= part1_nlt_point_maximum(header.3) {
                Ok((header.1, header.2, header.3, values))
            } else { Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)) }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_nlt_header(segment: Part1CodestreamSegment, components: u16)
    -> Result<(Option<u16>, u8, bool, u8), crate::DecodeError>
{
    if segment.payload.len() < 4 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let raw = part1_marker_value(segment.payload[0], segment.payload[1]);
        if raw != u16::MAX && raw >= components {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else {
            let precision = part2_cbd_precision(segment.payload[2]);
            let kind = segment.payload[3];
            if precision > 38 || kind > 4 {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
            } else if (kind == 0 || kind == 3) && segment.payload.len() != 4 {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
            } else {
                Ok((if raw == u16::MAX { None } else { Some(raw) }, precision,
                    part2_cbd_signed(segment.payload[2]), kind))
            }
        }
    }
}

pub open spec fn part1_nlt_record(
    segment: Part1CodestreamSegment, header: (Option<u16>, u8, bool, u8),
    points: Option<(u32, u32, u8, Seq<u32>)>, gamma: Option<[u32; 5]>,
) -> Part2OwnedNonlinear {
    Part2OwnedNonlinear {
        component: header.0, precision: header.1, signed: header.2, transform_type: header.3,
        parameters: segment.payload.subrange(4, segment.payload.len() as int),
        d_min: match points { None => None, Some(value) => Some(value.0) },
        d_max: match points { None => None, Some(value) => Some(value.1) },
        point_bits: match points { None => None, Some(value) => Some(value.2) },
        points: match points { None => Seq::empty(), Some(value) => value.3 },
        gamma,
    }
}

#[verifier::opaque]
pub open spec fn part1_nlt_payload(segment: Part1CodestreamSegment, components: u16)
    -> Result<Part2OwnedNonlinear, crate::DecodeError>
{
    match part1_nlt_header(segment, components) {
        Err(error) => Err(error),
        Ok(header) => if header.3 == 1 {
            match part1_nlt_gamma(segment) {
                Err(error) => Err(error),
                Ok(gamma) => Ok(part1_nlt_record(segment, header, None, Some(gamma))),
            }
        } else if header.3 == 2 || header.3 == 4 {
            match part1_nlt_points(segment) {
                Err(error) => Err(error),
                Ok(points) => Ok(part1_nlt_record(segment, header, Some(points), None)),
            }
        } else { Ok(part1_nlt_record(segment, header, None, None)) },
    }
}

#[verifier::opaque]
pub open spec fn part1_nlt_replace(entries: Seq<Part2OwnedNonlinear>, replacement: Part2OwnedNonlinear, position: nat)
    -> Seq<Part2OwnedNonlinear>
    decreases entries.len() - position,
{
    if position >= entries.len() { entries.push(replacement) }
    else if entries[position as int].component == replacement.component { entries.update(position as int, replacement) }
    else { part1_nlt_replace(entries, replacement, position + 1) }
}

pub open spec fn part1_extension_nonlinear(extensions: Part2OwnedExtensions, nonlinear: Seq<Part2OwnedNonlinear>)
    -> Part2OwnedExtensions
{
    Part2OwnedExtensions {
        decompositions: extensions.decompositions, arbitrary: extensions.arbitrary, nonlinear,
        depths: extensions.depths, kernels: extensions.kernels, registrations: extensions.registrations,
        lengths: extensions.lengths, metadata_bytes: extensions.metadata_bytes,
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_nlt<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, components: u16,
    extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { charged } else {
        match part1_nlt_payload(segment, components) {
            Err(error) => (Err(error), charged.1, charged.2),
            Ok(replacement) => (Ok(()), charged.1, part1_extension_nonlinear(charged.2,
                part1_nlt_replace(charged.2.nonlinear, replacement, 0))),
        }
    }
}

pub open spec fn part1_extension_lengths(
    extensions: Part2OwnedExtensions, lengths: Seq<crate::codestream::TilePartLength>,
) -> Part2OwnedExtensions {
    Part2OwnedExtensions {
        decompositions: extensions.decompositions, arbitrary: extensions.arbitrary,
        nonlinear: extensions.nonlinear, depths: extensions.depths, kernels: extensions.kernels,
        registrations: extensions.registrations, lengths, metadata_bytes: extensions.metadata_bytes,
    }
}

pub open spec fn part1_tlm_tile_index(payload: Seq<u8>, position: int, tile_bytes: usize) -> Option<u16> {
    if tile_bytes == 0 { None } else if tile_bytes == 1 { Some(payload[position] as u16) }
    else { Some(part1_marker_value(payload[position], payload[position + 1])) }
}

pub open spec fn part1_tlm_length(payload: Seq<u8>, position: int, length_bytes: usize) -> u32 {
    if length_bytes == 2 { part1_marker_value(payload[position], payload[position + 1]) as u32 }
    else { part1_siz_word(payload, position) }
}

#[verifier::opaque]
pub open spec fn part1_tlm_records(
    segment: Part1CodestreamSegment, tile_count: u64, tile_bytes: usize, length_bytes: usize,
    position: nat, lengths: Seq<crate::codestream::TilePartLength>,
) -> (Result<(), crate::DecodeError>, Seq<crate::codestream::TilePartLength>)
    decreases segment.payload.len() - position,
{
    if position >= segment.payload.len() { (Ok(()), lengths) }
    else if tile_bytes > 2 || (length_bytes != 2 && length_bytes != 4) {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTilePart)), lengths)
    } else if position + tile_bytes as nat + length_bytes as nat > segment.payload.len() {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)), lengths)
    } else {
        let tile_index = part1_tlm_tile_index(segment.payload, position as int, tile_bytes);
        if match tile_index { None => false, Some(value) => value as u64 >= tile_count } {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTilePart)), lengths)
        } else {
            let length = part1_tlm_length(segment.payload, position as int + tile_bytes as int, length_bytes);
            if length < 14 {
                (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTilePart)), lengths)
            } else {
                part1_tlm_records(segment, tile_count, tile_bytes, length_bytes,
                    position + tile_bytes as nat + length_bytes as nat,
                    lengths.push(crate::codestream::TilePartLength { tile_index, length }))
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_tlm<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, next_index: u16,
    tile_count: u64, extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, u16, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { (charged.0, charged.1, next_index, charged.2) }
    else if segment.payload.len() < 2 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)),
            charged.1, next_index, charged.2)
    } else if segment.payload[0] as u16 != next_index {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerOrder)),
            charged.1, next_index, charged.2)
    } else {
        let index = (next_index as int + 1) as u16;
        let style = segment.payload[1];
        let tile_bytes = part2_tlm_tile_index_bytes(style);
        let length_bytes = part2_tlm_length_bytes(style);
        let record_bytes = (tile_bytes + length_bytes) as usize;
        if style & 0x8f != 0 || tile_bytes == 3 {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTilePart)),
                charged.1, index, charged.2)
        } else if record_bytes == 0 || (segment.payload.len() - 2) % record_bytes as int != 0 {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength)),
                charged.1, index, charged.2)
        } else {
            let records = part1_tlm_records(segment, tile_count, tile_bytes, length_bytes, 2, charged.2.lengths);
            (records.0, charged.1, index, part1_extension_lengths(charged.2, records.1))
        }
    }
}

pub open spec fn part1_kernel_advance(cursor: usize, position: usize, amount: usize)
    -> Result<usize, crate::DecodeError>
{
    if position as int + amount as int > usize::MAX {
        Err(part1_codestream_malformed(cursor, crate::MalformedKind::ArithmeticOverflow))
    } else { Ok((position + amount) as usize) }
}

pub open spec fn part1_kernel_coefficient_bytes(
    payload: Seq<u8>, position: usize, width: usize, coefficient_type: u8,
) -> Seq<u8>
    recommends 0 < width <= 16, position as int + width as int <= payload.len(),
{
    let start = 16 - width as int;
    let negative = coefficient_type <= 1 && payload[position as int] & 0x80 != 0;
    Seq::new(16, |index: int| if index < start { if negative { 255u8 } else { 0u8 } }
        else { payload[position as int + index - start] })
}

#[verifier::opaque]
pub open spec fn part1_kernel_coefficient(
    cursor: usize, segment: Part1CodestreamSegment, position: usize, width: usize, coefficient_type: u8,
) -> Result<Part2RawKernelCoefficient, crate::DecodeError> {
    if width == 0 || width > 16 {
        Err(part1_codestream_malformed(cursor, crate::MalformedKind::InvalidTransform))
    } else {
        match part1_kernel_advance(cursor, position, width) {
            Err(error) => Err(error),
            Ok(end) => if end > segment.payload.len() {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
            } else { Ok((part1_kernel_coefficient_bytes(segment.payload, position, width, coefficient_type), width as u8)) },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_atk_coefficients(
    cursor: usize, segment: Part1CodestreamSegment, position: usize, width: usize, coefficient_type: u8,
    remaining: nat, coefficients: Seq<Part2RawKernelCoefficient>,
) -> Result<(Seq<Part2RawKernelCoefficient>, usize), crate::DecodeError>
    decreases remaining,
{
    if remaining == 0 { Ok((coefficients, position)) } else {
        match part1_kernel_coefficient(cursor, segment, position, width, coefficient_type) {
            Err(error) => Err(error),
            Ok(value) => match part1_kernel_advance(cursor, position, width) {
                Err(error) => Err(error),
                Ok(next) => part1_atk_coefficients(cursor, segment, next, width, coefficient_type,
                    (remaining - 1) as nat, coefficients.push(value)),
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_atk_step_header(
    cursor: usize, segment: Part1CodestreamSegment, start: usize, width: usize,
    coefficient_type: u8, reversible: bool, whole_sample_filter: bool,
) -> Result<(i8, u8, Option<Part2RawKernelCoefficient>, usize, usize), crate::DecodeError> {
    let offset = if whole_sample_filter { Ok((0i8, start)) } else {
        match part1_segment_byte(cursor, segment, start, 0) {
            Err(error) => Err(error),
            Ok(value) => match part1_kernel_advance(cursor, start, 1) {
                Err(error) => Err(error), Ok(next) => Ok((value as i8, next)),
            },
        }
    };
    match offset {
        Err(error) => Err(error),
        Ok((offset, position)) => {
            let parameters = if !reversible { Ok((0u8, None, position)) } else {
                match part1_segment_byte(cursor, segment, position, 0) {
                    Err(error) => Err(error),
                    Ok(exponent) => match part1_kernel_advance(cursor, position, 1) {
                        Err(error) => Err(error),
                        Ok(position) => match part1_kernel_coefficient(cursor, segment, position, width, coefficient_type) {
                            Err(error) => Err(error),
                            Ok(residue) => match part1_kernel_advance(cursor, position, width) {
                                Err(error) => Err(error), Ok(next) => Ok((exponent, Some(residue), next)),
                            },
                        },
                    },
                }
            };
            match parameters {
                Err(error) => Err(error),
                Ok((exponent, residue, position)) => match part1_segment_byte(cursor, segment, position, 0) {
                    Err(error) => Err(error),
                    Ok(count) => match part1_kernel_advance(cursor, position, 1) {
                        Err(error) => Err(error),
                        Ok(next) => if count == 0 {
                            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
                        } else { Ok((offset, exponent, residue, count as usize, next)) },
                    },
                },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_atk_step(
    cursor: usize, segment: Part1CodestreamSegment, start: usize, width: usize,
    coefficient_type: u8, reversible: bool, whole_sample_filter: bool,
) -> Result<(Part2RawKernelStep, usize), crate::DecodeError> {
    match part1_atk_step_header(cursor, segment, start, width, coefficient_type, reversible, whole_sample_filter) {
        Err(error) => Err(error),
        Ok(header) => match part1_atk_coefficients(cursor, segment, header.4, width, coefficient_type,
            header.3 as nat, Seq::empty()) {
            Err(error) => Err(error),
            Ok((coefficients, next)) => Ok(((header.0, header.1, header.2, coefficients), next)),
        },
    }
}

pub struct Part1AtkHeader {
    pub index: u8, pub descriptor: u16, pub coefficient_type: u8, pub width: usize,
    pub whole_sample_filter: bool, pub reversible: bool, pub initial_odd: bool, pub whole_sample_extension: bool,
    pub scaling: Option<Part2RawKernelCoefficient>, pub step_count: usize, pub position: usize,
}

#[verifier::opaque]
pub open spec fn part1_atk_header(cursor: usize, segment: Part1CodestreamSegment)
    -> Result<Part1AtkHeader, crate::DecodeError>
{
    if segment.payload.len() < 7 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        let descriptor = part1_marker_value(segment.payload[0], segment.payload[1]);
        let index = (descriptor & 255) as u8;
        let coefficient_type = ((descriptor >> 8) & 7) as u8;
        let width = if coefficient_type == 0 { 1usize } else if coefficient_type == 1 { 2 }
            else if coefficient_type == 2 { 4 } else if coefficient_type == 3 { 8 } else { 16 };
        let reversible = descriptor & 0x1000 != 0;
        if index < 2 || coefficient_type > 4 || descriptor & 0x8000 != 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else {
            let scaling = if reversible { Ok((None, 2usize)) } else {
                match part1_kernel_coefficient(cursor, segment, 2, width, coefficient_type) {
                    Err(error) => Err(error),
                    Ok(coefficient) => match part1_kernel_advance(cursor, 2, width) {
                        Err(error) => Err(error), Ok(next) => Ok((Some(coefficient), next)),
                    },
                }
            };
            match scaling {
                Err(error) => Err(error),
                Ok((scaling, position)) => match part1_segment_byte(cursor, segment, position, 0) {
                    Err(error) => Err(error),
                    Ok(count) => match part1_kernel_advance(cursor, position, 1) {
                        Err(error) => Err(error),
                        Ok(next) => Ok(Part1AtkHeader {
                            index, descriptor, coefficient_type, width, reversible, scaling,
                            whole_sample_filter: descriptor & 0x0800 != 0,
                            initial_odd: descriptor & 0x2000 != 0,
                            whole_sample_extension: descriptor & 0x4000 != 0,
                            step_count: count as usize, position: next,
                        }),
                    },
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_atk_steps(
    cursor: usize, segment: Part1CodestreamSegment, position: usize, width: usize,
    coefficient_type: u8, reversible: bool, whole_sample_filter: bool,
    remaining: nat, steps: Seq<Part2RawKernelStep>,
) -> Result<(Seq<Part2RawKernelStep>, usize), crate::DecodeError>
    decreases remaining,
{
    if remaining == 0 { Ok((steps, position)) } else {
        match part1_atk_step(cursor, segment, position, width, coefficient_type, reversible, whole_sample_filter) {
            Err(error) => Err(error),
            Ok((step, next)) => part1_atk_steps(cursor, segment, next, width, coefficient_type,
                reversible, whole_sample_filter, (remaining - 1) as nat, steps.push(step)),
        }
    }
}

pub open spec fn part1_atk_kernel(header: Part1AtkHeader, steps: Seq<Part2RawKernelStep>) -> (u8, u16, Part2RawKernel) {
    (header.index, header.descriptor, (header.reversible, header.coefficient_type,
        header.whole_sample_filter, header.initial_odd, header.whole_sample_extension, header.scaling, steps))
}

#[verifier::opaque]
pub open spec fn part1_atk_payload(cursor: usize, segment: Part1CodestreamSegment)
    -> Result<(u8, u16, Part2RawKernel), crate::DecodeError>
{
    match part1_atk_header(cursor, segment) {
        Err(error) => Err(error),
        Ok(header) => match part1_atk_steps(cursor, segment, header.position, header.width,
            header.coefficient_type, header.reversible, header.whole_sample_filter, header.step_count as nat, Seq::empty()) {
            Err(error) => Err(error),
            Ok((steps, next)) => if next != segment.payload.len() {
                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
            } else { Ok(part1_atk_kernel(header, steps)) },
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_atk_replace(
    entries: Seq<(u8, u16, Part2RawKernel)>, replacement: (u8, u16, Part2RawKernel), position: nat,
) -> Seq<(u8, u16, Part2RawKernel)>
    decreases entries.len() - position,
{
    if position >= entries.len() { entries.push(replacement) }
    else if entries[position as int].0 == replacement.0 { entries.update(position as int, replacement) }
    else { part1_atk_replace(entries, replacement, position + 1) }
}

pub open spec fn part1_extension_kernels(extensions: Part2OwnedExtensions, kernels: Seq<(u8, u16, Part2RawKernel)>)
    -> Part2OwnedExtensions
{
    Part2OwnedExtensions {
        decompositions: extensions.decompositions, arbitrary: extensions.arbitrary,
        nonlinear: extensions.nonlinear, depths: extensions.depths, kernels,
        registrations: extensions.registrations, lengths: extensions.lengths, metadata_bytes: extensions.metadata_bytes,
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_atk<'a>(
    state: Part1CodestreamReader<'a>, segment: Part1CodestreamSegment, extensions: Part2OwnedExtensions,
) -> (Result<(), crate::DecodeError>, Part1CodestreamReader<'a>, Part2OwnedExtensions) {
    let charged = part1_charge_extension_metadata(state, segment, extensions);
    if charged.0.is_err() { charged } else {
        match part1_atk_payload(charged.1.position, segment) {
            Err(error) => (Err(error), charged.1, charged.2),
            Ok(replacement) => (Ok(()), charged.1, part1_extension_kernels(charged.2,
                part1_atk_replace(charged.2.kernels, replacement, 0))),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_poc_byte(segment: Part1CodestreamSegment, position: usize) -> Result<u8, crate::DecodeError> {
    if position >= segment.payload.len() {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else { Ok(segment.payload[position as int]) }
}

pub open spec fn part1_poc_component_value(payload: Seq<u8>, position: int, width: usize) -> u16 {
    if width == 1 { payload[position] as u16 } else { part1_marker_value(payload[position], payload[position + 1]) }
}

#[verifier::opaque]
pub open spec fn part1_poc_component(segment: Part1CodestreamSegment, position: usize, width: usize)
    -> Result<u16, crate::DecodeError>
{
    if width != 1 && position as int + 2 > usize::MAX {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow))
    } else if position as int + if width == 1 { 1int } else { 2int } > segment.payload.len() {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else { Ok(part1_poc_component_value(segment.payload, position as int, width)) }
}

pub open spec fn part1_poc_record(segment: Part1CodestreamSegment, components: u16, position: int)
    -> Result<crate::codestream::ProgressionChange, crate::DecodeError>
{
    let width = if components < 257 { 1usize } else { 2usize };
    let component_end = part1_poc_component_value(segment.payload, position + 4 + width as int, width);
    match part1_cod_progression(segment.payload[position + 4 + 2 * width as int]) {
        None => Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidProgressionOrderChange)),
        Some(progression_order) => Ok(crate::codestream::ProgressionChange {
            resolution_start: segment.payload[position],
            component_start: part1_poc_component_value(segment.payload, position + 1, width),
            layer_end: part1_marker_value(segment.payload[position + 1 + width as int], segment.payload[position + 2 + width as int]),
            resolution_end: segment.payload[position + 3 + width as int],
            component_end: if width == 1 && component_end == 0 && components == 256 { 256 } else { component_end },
            progression_order,
        }),
    }
}

#[verifier::opaque]
pub open spec fn part1_poc_records(
    segment: Part1CodestreamSegment, components: u16, position: nat, records: Seq<crate::codestream::ProgressionChange>,
) -> Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>
    decreases segment.payload.len() - position,
{
    let width = if components < 257 { 7nat } else { 9nat };
    if position >= segment.payload.len() { Ok(records) }
    else if position + width > segment.payload.len() {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else {
        match part1_poc_record(segment, components, position as int) {
            Err(error) => Err(error),
            Ok(record) => part1_poc_records(segment, components, position + width, records.push(record)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_poc(segment: Part1CodestreamSegment, components: u16)
    -> Result<Seq<crate::codestream::ProgressionChange>, crate::DecodeError>
{
    let width = if components < 257 { 7int } else { 9int };
    if segment.payload.len() == 0 || (segment.payload.len() as int) % width != 0 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidMarkerLength))
    } else { part1_poc_records(segment, components, 0, Seq::empty()) }
}

#[verifier::opaque]
pub open spec fn part1_poc_validation_shape(
    offset: usize, layers: u16, styles: &crate::codestream::ComponentCodingStyles,
    component: u16, active: usize, maximum: u8,
) -> Result<(usize, u8), crate::DecodeError>
    decreases crate::codestream::component_coding_style_count(styles) - component,
{
    if component >= crate::codestream::component_coding_style_count(styles) { Ok((active, maximum)) }
    else {
        match crate::codestream::component_coding_style_result(styles, component) {
            Err(error) => Err(error),
            Ok(style) => if style.decomposition_levels == u8::MAX {
                Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
            } else {
                let resolutions = (style.decomposition_levels + 1) as u8;
                let amount = layers as int * resolutions as int;
                if amount > usize::MAX || active as int + amount > usize::MAX {
                    Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow))
                } else {
                    part1_poc_validation_shape(offset, layers, styles, (component + 1) as u16,
                        (active as int + amount) as usize, if resolutions > maximum { resolutions } else { maximum })
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_poc_mark_resolutions(
    offset: usize, record: crate::codestream::ProgressionChange, coordinate: (u16, u16, u8),
    resolution: u8, owners: Seq<bool>, progress: (usize, bool),
) -> (Result<(usize, bool), crate::DecodeError>, Seq<bool>)
    decreases coordinate.2 - resolution,
{
    if resolution >= coordinate.2 { (Ok(progress), owners) } else {
        let contained = crate::codestream::progression_change_contains(record, coordinate.1, resolution, coordinate.0);
        if contained && progress.0 as nat >= owners.len() {
            (Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow)), owners)
        } else {
            let fresh = contained && !owners[progress.0 as int];
            let updated = if fresh { owners.update(progress.0 as int, true) } else { owners };
            if progress.0 == usize::MAX {
                (Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow)), updated)
            } else {
                part1_poc_mark_resolutions(offset, record, coordinate, (resolution + 1) as u8, updated,
                    ((progress.0 + 1) as usize, progress.1 || fresh))
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_poc_mark_layers(
    offset: usize, record: crate::codestream::ProgressionChange, coordinate: (u16, u8),
    layers: u16, layer: u16, owners: Seq<bool>, progress: (usize, bool),
) -> (Result<(usize, bool), crate::DecodeError>, Seq<bool>)
    decreases layers - layer,
{
    if layer >= layers { (Ok(progress), owners) } else {
        let marked = part1_poc_mark_resolutions(offset, record, (coordinate.0, layer, coordinate.1), 0, owners, progress);
        match marked.0 {
            Err(error) => marked,
            Ok(progress) => part1_poc_mark_layers(offset, record, coordinate, layers, (layer + 1) as u16, marked.1, progress),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_poc_mark_components(
    offset: usize, record: crate::codestream::ProgressionChange, layers: u16,
    styles: &crate::codestream::ComponentCodingStyles, component: u16, owners: Seq<bool>, progress: (usize, bool),
) -> (Result<(usize, bool), crate::DecodeError>, Seq<bool>)
    decreases crate::codestream::component_coding_style_count(styles) - component,
{
    if component >= crate::codestream::component_coding_style_count(styles) { (Ok(progress), owners) }
    else {
        match crate::codestream::component_coding_style_result(styles, component) {
            Err(error) => (Err(error), owners),
            Ok(style) => if style.decomposition_levels == u8::MAX {
                (Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow)), owners)
            } else {
                let marked = part1_poc_mark_layers(offset, record, (component, (style.decomposition_levels + 1) as u8),
                    layers, 0, owners, progress);
                match marked.0 {
                    Err(error) => marked,
                    Ok(progress) => part1_poc_mark_components(offset, record, layers, styles, (component + 1) as u16, marked.1, progress),
                }
            },
        }
    }
}

pub open spec fn part1_poc_mark_record(
    offset: usize, record: crate::codestream::ProgressionChange, layers: u16,
    styles: &crate::codestream::ComponentCodingStyles, owners: Seq<bool>,
) -> (Result<bool, crate::DecodeError>, Seq<bool>) {
    let marked = part1_poc_mark_components(offset, record, layers, styles, 0, owners, (0, false));
    (match marked.0 { Err(error) => Err(error), Ok(progress) => Ok(progress.1) }, marked.1)
}

pub open spec fn part1_progression_owners_complete(owners: Seq<bool>) -> bool {
    forall|index: int| 0 <= index < owners.len() ==> owners[index]
}

#[verifier::opaque]
pub open spec fn part1_poc_admit_records(
    offset: usize, records: Seq<crate::codestream::ProgressionChange>, layers: u16,
    styles: &crate::codestream::ComponentCodingStyles, maximum: u8, index: nat, owners: Seq<bool>,
) -> Result<(), crate::DecodeError>
    decreases records.len() - index,
{
    if index >= records.len() {
        if part1_progression_owners_complete(owners) { Ok(()) }
        else { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidProgressionOrderChange)) }
    } else {
        let record = records[index as int];
        if !valid_poc_record(record.resolution_start as nat, record.resolution_end as nat,
            record.component_start as nat, record.component_end as nat, record.layer_end as nat,
            crate::codestream::component_coding_style_count(styles) as nat, layers as nat, maximum as nat,
            part1_cod_progression_byte(record.progression_order) as nat) {
            Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidProgressionOrderChange))
        } else {
            let marked = part1_poc_mark_record(offset, record, layers, styles, owners);
            match marked.0 {
                Err(error) => Err(error),
                Ok(false) => Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidProgressionOrderChange)),
                Ok(true) => part1_poc_admit_records(offset, records, layers, styles, maximum, index + 1, marked.1),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_validate_progression_changes(
    offset: usize, records: Seq<crate::codestream::ProgressionChange>, layers: u16,
    styles: &crate::codestream::ComponentCodingStyles, limits: &crate::ResourceLimits,
) -> Result<(), crate::DecodeError> {
    if records.len() == 0 { Ok(()) } else {
        match part1_poc_validation_shape(offset, layers, styles, 0, 0, 0) {
            Err(error) => Err(error),
            Ok(shape) => {
                let count = records.len() as u64;
                let active = shape.0 as u64;
                let cost = count as int * active as int;
                if cost > u64::MAX { Err(part1_codestream_malformed(offset, crate::MalformedKind::ArithmeticOverflow)) }
                else if cost > crate::limits::resource_work_limit(limits) {
                    Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::WorkUnits,
                        limit: crate::limits::resource_work_limit(limits), actual: cost as u64 })
                } else {
                    part1_poc_admit_records(offset, records, layers, styles, shape.1, 0,
                        Seq::new(shape.0 as nat, |index: int| false))
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_mco_run(segment: Part1CodestreamSegment, index: nat, order: Seq<u8>)
    -> Result<Seq<u8>, crate::DecodeError>
    decreases segment.payload.len() - index,
{
    if index + 1 >= segment.payload.len() { Ok(order) } else {
        let stage = segment.payload[index as int + 1];
        if order.contains(stage) || stage == 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else { part1_mco_run(segment, index + 1, order.push(stage)) }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_mco(segment: Part1CodestreamSegment) -> Result<Seq<u8>, crate::DecodeError> {
    if segment.payload.len() == 0 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
    } else if segment.payload.len() != segment.payload[0] as int + 1 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
    } else { part1_mco_run(segment, 0, Seq::empty()) }
}

pub open spec fn part1_mcc_reference_present(values: Seq<u16>, value: u16) -> bool {
    values.contains(value)
}

pub open spec fn part1_mcc_reference_value(payload: Seq<u8>, position: int, width: usize) -> u16 {
    if width == 1 { payload[position] as u16 } else { part1_marker_value(payload[position], payload[position + 1]) }
}

#[verifier::opaque]
pub open spec fn part1_mcc_reference_run(
    payload: Seq<u8>, components: u16, marker_offset: usize, position: usize, width: usize,
    remaining: nat, references: Seq<u16>,
) -> (Result<Seq<u16>, crate::DecodeError>, usize)
    decreases remaining,
{
    if remaining == 0 { (Ok(references), position) }
    else if (width != 1 && width != 2) || position as int + width as int > payload.len() {
        (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::InvalidTransform)), position)
    } else {
        let reference = part1_mcc_reference_value(payload, position as int, width);
        if reference >= components || part1_mcc_reference_present(references, reference) {
            (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::InvalidTransform)), position)
        } else {
            part1_mcc_reference_run(payload, components, marker_offset, (position + width) as usize,
                width, (remaining - 1) as nat, references.push(reference))
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_mcc_component_list(
    payload: Seq<u8>, start: usize, components: u16, marker_offset: usize,
) -> (Result<Seq<u16>, crate::DecodeError>, usize) {
    if start as int + 2 > payload.len() {
        (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::InvalidTransform)), start)
    } else {
        let encoded = part1_marker_value(payload[start as int], payload[start as int + 1]);
        let position = (start + 2) as usize;
        let width = if encoded & 0x8000 == 0 { 1usize } else { 2usize };
        let count = encoded & 0x7fff;
        if count == 0 || count > components || position as int + count as int * width as int > payload.len() {
            (Err(part1_codestream_malformed(marker_offset, crate::MalformedKind::InvalidTransform)), position)
        } else { part1_mcc_reference_run(payload, components, marker_offset, position, width, count as nat, Seq::empty()) }
    }
}

pub enum Part1MccTransformReference {
    Array { kind: crate::codestream::MctArrayKind, reversible: bool, transform_index: u8, offset_index: u8 },
    Wavelet(Part2MctWavelet),
}

pub struct Part1MccCollectionReference {
    pub inputs: Seq<u16>,
    pub outputs: Seq<u16>,
    pub transform: Part1MccTransformReference,
}

pub open spec fn part1_signed_u32(value: u32) -> i64 {
    if value < 2147483648 { value as i64 } else { (value as int - 4294967296) as i64 }
}

pub open spec fn part1_mcc_transform_word(payload: Seq<u8>, position: int) -> u32 {
    ((payload[position] as u32) << 16) | ((payload[position + 1] as u32) << 8) | payload[position + 2] as u32
}

#[verifier::opaque]
pub open spec fn part1_mcc_collection(
    segment: Part1CodestreamSegment, components: u16, start: usize,
) -> Result<(Part1MccCollectionReference, usize), crate::DecodeError> {
    if start >= segment.payload.len() {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
    } else {
        let kind = segment.payload[start as int];
        if kind & 0xfc != 0 || kind & 3 == 2 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else {
            let inputs = part1_parse_mcc_component_list(segment.payload, (start + 1) as usize, components, segment.offset);
            match inputs.0 {
                Err(error) => Err(error),
                Ok(input) => {
                    let outputs = part1_parse_mcc_component_list(segment.payload, inputs.1, components, segment.offset);
                    match outputs.0 {
                        Err(error) => Err(error),
                        Ok(output) => if input.len() == 0 || outputs.1 as int + 3 > segment.payload.len() {
                            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
                        } else {
                            let word = part1_mcc_transform_word(segment.payload, outputs.1 as int);
                            let position = (outputs.1 + 3) as usize;
                            if kind == 0 || kind == 1 {
                                if word & 0xfe0000 != 0 || input.len() != output.len() || (kind == 0 && input != output) {
                                    Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
                                } else {
                                    Ok((Part1MccCollectionReference { inputs: input, outputs: output,
                                        transform: Part1MccTransformReference::Array {
                                            kind: if kind == 0 { crate::codestream::MctArrayKind::Dependency }
                                                else { crate::codestream::MctArrayKind::Decorrelation },
                                            reversible: word & 0x010000 != 0,
                                            transform_index: (word & 255) as u8,
                                            offset_index: ((word >> 8) & 255) as u8,
                                        } }, position))
                                }
                            } else if word & 0xc0ff00 != 0 || input.len() != output.len()
                                || position as int + 4 > segment.payload.len() {
                                Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
                            } else {
                                let transform = match (word & 255) as u8 {
                                    0 => Some(crate::codestream::MctWaveletType::Irreversible9x7),
                                    1 => Some(crate::codestream::MctWaveletType::Reversible5x3),
                                    _ => None,
                                };
                                let levels = ((word >> 16) & 63) as u8;
                                match transform {
                                    None => Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)),
                                    Some(transform) => if levels > 32 {
                                        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
                                    } else {
                                        Ok((Part1MccCollectionReference { inputs: input, outputs: output,
                                            transform: Part1MccTransformReference::Wavelet(
                                                (transform, levels, part1_signed_u32(part1_siz_word(segment.payload, position as int)) as i32)),
                                        }, (position + 4) as usize))
                                    },
                                }
                            }
                        },
                    }
                },
            }
        }
    }
}

pub open spec fn part1_mcc_lists_overlap(left: Seq<u16>, right: Seq<u16>) -> bool {
    exists|i: int, j: int| 0 <= i < left.len() && 0 <= j < right.len() && left[i] == right[j]
}

pub open spec fn part1_mcc_parallel_conflict(left: Part1MccCollectionReference, right: Part1MccCollectionReference) -> bool {
    part1_mcc_lists_overlap(left.inputs, right.inputs) || part1_mcc_lists_overlap(left.inputs, right.outputs)
        || part1_mcc_lists_overlap(right.inputs, left.outputs) || part1_mcc_lists_overlap(right.outputs, left.outputs)
}

pub open spec fn part1_mcc_parallel_collections(collections: Seq<Part1MccCollectionReference>, offset: usize)
    -> Result<(), crate::DecodeError>
{
    if forall|index: int, previous: int| 0 <= previous < index < collections.len() ==>
        !part1_mcc_parallel_conflict(collections[index], collections[previous]) {
        Ok(())
    } else { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform)) }
}

#[verifier::opaque]
pub open spec fn part1_mcc_records(
    segment: Part1CodestreamSegment, components: u16, position: usize, remaining: nat,
    collections: Seq<Part1MccCollectionReference>,
) -> Result<(u8, Seq<Part1MccCollectionReference>), crate::DecodeError>
    decreases remaining,
{
    if remaining == 0 {
        if position != segment.payload.len() {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else {
            match part1_mcc_parallel_collections(collections, segment.offset) {
                Err(error) => Err(error), Ok(()) => Ok((segment.payload[2], collections)),
            }
        }
    } else {
        match part1_mcc_collection(segment, components, position) {
            Err(error) => Err(error),
            Ok((collection, next)) => part1_mcc_records(segment, components, next,
                (remaining - 1) as nat, collections.push(collection)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_mcc(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
) -> Result<(u8, Seq<Part1MccCollectionReference>), crate::DecodeError> {
    if segment.payload.len() < 7 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
    } else if part1_marker_value(segment.payload[0], segment.payload[1]) != 0
        || part1_marker_value(segment.payload[3], segment.payload[4]) != 0 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
    } else {
        let index = segment.payload[2];
        let count = part1_marker_value(segment.payload[5], segment.payload[6]);
        if index == 0 || count == 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else if count > crate::limits::resource_component_limit(limits) {
            Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                limit: crate::limits::resource_component_limit(limits) as u64, actual: count as u64 })
        } else { part1_mcc_records(segment, components, 7, count as nat, Seq::empty()) }
    }
}

pub struct Part1MccFragment {
    pub record_index: u8, pub next_index: u16, pub final_index: u16,
    pub collection_count: u16, pub offset: usize, pub data: Seq<u8>,
}

pub open spec fn part1_mcc_fragment_maximum_bytes(components: u16) -> u64 {
    (components as int * (components as int * 4 + 12)) as u64
}

#[verifier::opaque]
pub open spec fn part1_mcc_fragment_find(pending: Seq<Part1MccFragment>, index: u8, position: nat) -> Option<usize>
    decreases pending.len() - position,
{
    if position >= pending.len() { None }
    else if pending[position as int].record_index == index { Some(position as usize) }
    else { part1_mcc_fragment_find(pending, index, position + 1) }
}

pub open spec fn part1_byte_list_contains(values: Seq<u8>, value: u8) -> bool { values.contains(value) }

pub open spec fn part1_mcc_fragment_updated(state: Part1MccFragment, data: Seq<u8>, next_index: u16) -> Part1MccFragment {
    Part1MccFragment { record_index: state.record_index, next_index, final_index: state.final_index,
        collection_count: state.collection_count, offset: state.offset, data }
}

#[verifier::opaque]
pub open spec fn part1_prepare_mcc_fragment(
    segment: Part1CodestreamSegment, components: u16, pending: Seq<Part1MccFragment>, completed: Seq<u8>,
) -> (Result<(usize, u64), crate::DecodeError>, Seq<Part1MccFragment>) {
    if segment.payload.len() < 3 || segment.payload[2] == 0 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
    } else {
        let fragment = part1_marker_value(segment.payload[0], segment.payload[1]);
        let index = segment.payload[2];
        let maximum = part1_mcc_fragment_maximum_bytes(components);
        let found = part1_mcc_fragment_find(pending, index, 0);
        if fragment == 0 {
            if segment.payload.len() < 7 || found.is_some() || completed.contains(index) {
                (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
            } else {
                let final_index = part1_marker_value(segment.payload[3], segment.payload[4]);
                let data = segment.payload.subrange(7, segment.payload.len() as int);
                if final_index as u64 + 1 > maximum {
                    (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                        limit: maximum, actual: (final_index as u64 + 1) as u64 }), pending)
                } else if data.len() as u64 > maximum {
                    (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                        limit: maximum, actual: data.len() as u64 }), pending)
                } else {
                    (Ok((pending.len() as usize, maximum)), pending.push(Part1MccFragment {
                        record_index: index, next_index: 1, final_index,
                        collection_count: part1_marker_value(segment.payload[5], segment.payload[6]),
                        offset: segment.offset, data,
                    }))
                }
            }
        } else {
            match found {
                None => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending),
                Some(position) => {
                    let state = pending[position as int];
                    if fragment != state.next_index || fragment > state.final_index {
                        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
                    } else {
                        let data = state.data + segment.payload.subrange(3, segment.payload.len() as int);
                        let appended = pending.update(position as int, part1_mcc_fragment_updated(state, data, state.next_index));
                        if data.len() as u64 > maximum {
                            (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                                limit: maximum, actual: data.len() as u64 }), appended)
                        } else if state.next_index == u16::MAX {
                            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow)), appended)
                        } else {
                            (Ok((position, maximum)), pending.update(position as int,
                                part1_mcc_fragment_updated(state, data, part2_fragment_next(state.next_index))))
                        }
                    }
                },
            }
        }
    }
}

pub open spec fn part1_mcc_fragment_swap_remove(pending: Seq<Part1MccFragment>, index: usize) -> Seq<Part1MccFragment>
    recommends index < pending.len(),
{
    pending.update(index as int, pending.last()).drop_last()
}

pub open spec fn part1_mcc_fragment_payload(state: Part1MccFragment) -> Seq<u8> {
    seq![0u8, 0u8, state.record_index, 0u8, 0u8,
        (state.collection_count >> 8) as u8, (state.collection_count & 255) as u8] + state.data
}

#[verifier::opaque]
pub open spec fn part1_consume_mcc_fragment(
    segment: Part1CodestreamSegment, components: u16, limits: &crate::ResourceLimits,
    pending: Seq<Part1MccFragment>, completed: Seq<u8>,
) -> (Result<Option<(u8, Seq<Part1MccCollectionReference>)>, crate::DecodeError>, Seq<Part1MccFragment>, Seq<u8>) {
    let prepared = part1_prepare_mcc_fragment(segment, components, pending, completed);
    match prepared.0 {
        Err(error) => (Err(error), prepared.1, completed),
        Ok((index, maximum)) => {
            let state = prepared.1[index as int];
            if !part2_fragment_complete(state.next_index, state.final_index) {
                (Ok(None), prepared.1, completed)
            } else {
                let removed = part1_mcc_fragment_swap_remove(prepared.1, index);
                if state.data.len() as u64 > maximum {
                    (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                        limit: maximum, actual: state.data.len() as u64 }), removed, completed)
                } else {
                    let raw = Part1CodestreamSegment { marker: 0xff75, offset: state.offset, payload: part1_mcc_fragment_payload(state) };
                    match part1_parse_mcc(raw, components, limits) {
                        Err(error) => (Err(error), removed, completed),
                        Ok(record) => (Ok(Some(record)), removed, completed.push(segment.payload[2])),
                    }
                }
            }
        },
    }
}

pub struct Part1MctParameters {
    pub arrays: Seq<Part2MctArray>,
    pub records: Seq<Part1MctRecord>,
    pub order: Seq<u8>,
}

pub open spec fn part1_mct_parameters_copy(
    value: (Seq<Part2MctArray>, Seq<Part1MctRecord>, Seq<u8>),
) -> (Seq<Part2MctArray>, Seq<Part1MctRecord>, Seq<u8>) {
    value
}

pub open spec fn part1_mct_record_copy(value: Part1MctRecord) -> Part1MctRecord {
    value
}

pub open spec fn part1_mcc_collection_reference_copy(
    value: Part1MccCollectionReference,
) -> Part1MccCollectionReference {
    value
}

pub open spec fn part1_mct_graph_element_count(
    rows: usize, columns: usize, kind: crate::codestream::MctArrayKind, reversible: bool,
) -> Result<usize, crate::DecodeError> {
    let maximum = usize::MAX as int;
    let error = part1_codestream_malformed(0, crate::MalformedKind::ArithmeticOverflow);
    if kind == crate::codestream::MctArrayKind::Decorrelation {
        let product = rows as int * columns as int;
        if product > maximum { Err(error) } else { Ok(product as usize) }
    } else if reversible {
        if rows == usize::MAX { Err(error) }
        else {
            let product = rows as int * (rows as int + 1);
            if product > maximum || product / 2 == 0 { Err(error) }
            else { Ok((product / 2 - 1) as usize) }
        }
    } else {
        let partner = if rows == 0 { 0int } else { rows as int - 1 };
        let product = rows as int * partner;
        if product > maximum { Err(error) } else { Ok((product / 2) as usize) }
    }
}

#[verifier::opaque]
pub open spec fn part1_mct_graph_collection(
    reference: Part1MccCollectionReference, arrays: Seq<Part2MctArray>,
) -> Result<Part2MctCollection, crate::DecodeError> {
    let rows = reference.inputs.len();
    let columns = reference.outputs.len();
    if rows == 0 || rows != columns {
        Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidTransform))
    } else {
        match reference.transform {
            Part1MccTransformReference::Wavelet(wavelet) => Ok((
                wavelet.0 == crate::codestream::MctWaveletType::Reversible5x3,
                reference.inputs, reference.outputs, crate::codestream::MctCollectionKind::Wavelet,
                None, None, Some(wavelet))),
            Part1MccTransformReference::Array { kind, reversible, transform_index, offset_index } => {
                let offsets: Result<Option<Part2MctArray>, crate::DecodeError> = if offset_index == 0 { Ok(None) }
                    else { match part1_mct_registry_reference(arrays, offset_index, crate::codestream::MctArrayKind::Offset) {
                        Err(error) => Err(error), Ok(array) => Ok(Some(array)),
                    } };
                match offsets {
                    Err(error) => Err(error),
                    Ok(offsets) => {
                        let matrix: Result<Option<Part2MctArray>, crate::DecodeError> = if transform_index == 0 { Ok(None) }
                            else { match part1_mct_registry_reference(arrays, transform_index, kind) {
                                Err(error) => Err(error), Ok(array) => Ok(Some(array)),
                            } };
                        match matrix {
                            Err(error) => Err(error),
                            Ok(matrix) => {
                                match part1_mct_graph_element_count(rows as usize, columns as usize, kind, reversible) {
                                    Err(error) => Err(error),
                                    Ok(expected) => {
                                        let invalid_offsets = match offsets { None => false, Some(array) => array.4.len() != rows };
                                        let floating_offsets = match offsets { None => false, Some(array) => array.3 != 0 };
                                        let invalid_matrix = match matrix { None => false, Some(array) => array.4.len() != expected };
                                        let floating_matrix = match matrix { None => false, Some(array) => array.3 != 0 };
                                        if invalid_offsets || invalid_matrix || (reversible && (floating_matrix || floating_offsets)) {
                                            Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidTransform))
                                        } else {
                                            Ok((reversible, reference.inputs, reference.outputs,
                                                if kind == crate::codestream::MctArrayKind::Dependency {
                                                    crate::codestream::MctCollectionKind::Dependency
                                                } else { crate::codestream::MctCollectionKind::Decorrelation },
                                                matrix, offsets, None))
                                        }
                                    },
                                }
                            },
                        }
                    },
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_mct_graph_stage_from(
    record: Part1MctRecord, arrays: Seq<Part2MctArray>, position: nat, collections: Seq<Part2MctCollection>,
) -> Result<Part2MctStage, crate::DecodeError>
    decreases record.1.len() - position,
{
    if position >= record.1.len() { Ok((record.0, collections)) }
    else {
        match part1_mct_graph_collection(record.1[position as int], arrays) {
            Err(error) => Err(error),
            Ok(collection) => part1_mct_graph_stage_from(record, arrays, position + 1, collections.push(collection)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_mct_graph_stage(record: Part1MctRecord, arrays: Seq<Part2MctArray>) -> Result<Part2MctStage, crate::DecodeError> {
    part1_mct_graph_stage_from(record, arrays, 0, Seq::empty())
}

#[verifier::opaque]
pub open spec fn part1_mct_graph_from(
    parameters: Part1MctParameters, position: nat, stages: Seq<Part2MctStage>,
) -> Result<Option<Seq<Part2MctStage>>, crate::DecodeError>
    decreases parameters.order.len() - position,
{
    if position >= parameters.order.len() { Ok(Some(stages)) }
    else {
        match part1_mct_registry_record_find(parameters.records, parameters.order[position as int], 0) {
            None => Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidTransform)),
            Some(index) => {
                match part1_mct_graph_stage(parameters.records[index as int], parameters.arrays) {
                    Err(error) => Err(error),
                    Ok(stage) => part1_mct_graph_from(parameters, position + 1, stages.push(stage)),
                }
            },
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_mct_graph(parameters: Part1MctParameters) -> Result<Option<Seq<Part2MctStage>>, crate::DecodeError> {
    if parameters.order.len() == 0 { Ok(None) }
    else { part1_mct_graph_from(parameters, 0, Seq::empty()) }
}

pub type Part1MctRecord = (u8, Seq<Part1MccCollectionReference>);

#[verifier::opaque]
pub open spec fn part1_mct_registry_array_find(arrays: Seq<Part2MctArray>, index: u8, position: nat) -> Option<usize>
    decreases arrays.len() - position,
{
    if position >= arrays.len() { None }
    else if arrays[position as int].0 == index { Some(position as usize) }
    else { part1_mct_registry_array_find(arrays, index, position + 1) }
}

#[verifier::opaque]
pub open spec fn part1_mct_registry_record_find(records: Seq<Part1MctRecord>, index: u8, position: nat) -> Option<usize>
    decreases records.len() - position,
{
    if position >= records.len() { None }
    else if records[position as int].0 == index { Some(position as usize) }
    else { part1_mct_registry_record_find(records, index, position + 1) }
}

pub open spec fn part1_mct_registry_unique_array(arrays: Seq<Part2MctArray>, offset: usize) -> Result<(), crate::DecodeError> {
    if arrays.len() == 0 || part1_mct_registry_array_find(arrays.drop_last(), arrays.last().0, 0).is_none() {
        Ok(())
    } else { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform)) }
}

pub open spec fn part1_mct_registry_unique_record(records: Seq<Part1MctRecord>, offset: usize) -> Result<(), crate::DecodeError> {
    if records.len() == 0 || part1_mct_registry_record_find(records.drop_last(), records.last().0, 0).is_none() {
        Ok(())
    } else { Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform)) }
}

pub open spec fn part1_mct_registry_replace_array(arrays: Seq<Part2MctArray>, replacement: Part2MctArray)
    -> ((), Seq<Part2MctArray>)
{
    ((), match part1_mct_registry_array_find(arrays, replacement.0, 0) {
        None => arrays.push(replacement),
        Some(index) => arrays.update(index as int, replacement),
    })
}

pub open spec fn part1_mct_registry_replace_record(records: Seq<Part1MctRecord>, replacement: Part1MctRecord)
    -> ((), Seq<Part1MctRecord>)
{
    ((), match part1_mct_registry_record_find(records, replacement.0, 0) {
        None => records.push(replacement),
        Some(index) => records.update(index as int, replacement),
    })
}

#[verifier::opaque]
pub open spec fn part1_mct_registry_reference_from(
    arrays: Seq<Part2MctArray>, index: u8, kind: crate::codestream::MctArrayKind,
    position: nat, found: Option<usize>,
) -> Result<Part2MctArray, crate::DecodeError>
    decreases arrays.len() - position,
{
    if position >= arrays.len() {
        match found {
            Some(candidate) if candidate < arrays.len() => Ok(arrays[candidate as int]),
            _ => Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidTransform)),
        }
    } else if arrays[position as int].0 == index && arrays[position as int].1 == kind {
        if found.is_some() {
            Err(part1_codestream_malformed(0, crate::MalformedKind::InvalidTransform))
        } else { part1_mct_registry_reference_from(arrays, index, kind, position + 1, Some(position as usize)) }
    } else { part1_mct_registry_reference_from(arrays, index, kind, position + 1, found) }
}

#[verifier::opaque]
pub open spec fn part1_mct_registry_reference(
    arrays: Seq<Part2MctArray>, index: u8, kind: crate::codestream::MctArrayKind,
) -> Result<Part2MctArray, crate::DecodeError> {
    part1_mct_registry_reference_from(arrays, index, kind, 0, None)
}

pub struct Part1MctFragment {
    pub descriptor: u16, pub next_index: u16, pub final_index: u16,
    pub offset: usize, pub data: Seq<u8>,
}

pub open spec fn part1_mct_fragment_maximum_bytes(limits: &crate::ResourceLimits) -> u64 {
    let components = crate::limits::resource_component_limit(limits) as int;
    (components * components * 8) as u64
}

#[verifier::opaque]
pub open spec fn part1_mct_fragment_find(pending: Seq<Part1MctFragment>, index: u8, position: nat) -> Option<usize>
    decreases pending.len() - position,
{
    if position >= pending.len() { None }
    else if (pending[position as int].descriptor & 255) as u8 == index { Some(position as usize) }
    else { part1_mct_fragment_find(pending, index, position + 1) }
}

pub open spec fn part1_mct_fragment_updated(state: Part1MctFragment, data: Seq<u8>, next_index: u16) -> Part1MctFragment {
    Part1MctFragment { descriptor: state.descriptor, next_index, final_index: state.final_index,
        offset: state.offset, data }
}

#[verifier::opaque]
pub open spec fn part1_prepare_mct_fragment(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits,
    pending: Seq<Part1MctFragment>, completed: Seq<u8>,
) -> (Result<(usize, u64), crate::DecodeError>, Seq<Part1MctFragment>) {
    if segment.payload.len() < 4 {
        (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
    } else {
        let fragment = part1_marker_value(segment.payload[0], segment.payload[1]);
        let descriptor = part1_marker_value(segment.payload[2], segment.payload[3]);
        let index = (descriptor & 255) as u8;
        if index == 0 {
            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
        } else {
            let maximum = part1_mct_fragment_maximum_bytes(limits);
            let found = part1_mct_fragment_find(pending, index, 0);
            if fragment == 0 {
                if segment.payload.len() < 6 || found.is_some() || completed.contains(index) {
                    (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
                } else {
                    let final_index = part1_marker_value(segment.payload[4], segment.payload[5]);
                    let data = segment.payload.subrange(6, segment.payload.len() as int);
                    if final_index as u64 + 1 > maximum {
                        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                            limit: maximum, actual: (final_index as u64 + 1) as u64 }), pending)
                    } else if data.len() as u64 > maximum {
                        (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                            limit: maximum, actual: data.len() as u64 }), pending)
                    } else {
                        (Ok((pending.len() as usize, maximum)), pending.push(Part1MctFragment {
                            descriptor, next_index: 1, final_index, offset: segment.offset, data,
                        }))
                    }
                }
            } else {
                match found {
                    None => (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending),
                    Some(position) => {
                        let state = pending[position as int];
                        if state.descriptor != descriptor || fragment != state.next_index || fragment > state.final_index {
                            (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)), pending)
                        } else {
                            let data = state.data + segment.payload.subrange(4, segment.payload.len() as int);
                            let appended = pending.update(position as int, part1_mct_fragment_updated(state, data, state.next_index));
                            if data.len() as u64 > maximum {
                                (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                                    limit: maximum, actual: data.len() as u64 }), appended)
                            } else if state.next_index == u16::MAX {
                                (Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::ArithmeticOverflow)), appended)
                            } else {
                                (Ok((position, maximum)), pending.update(position as int,
                                    part1_mct_fragment_updated(state, data, part2_fragment_next(state.next_index))))
                            }
                        }
                    },
                }
            }
        }
    }
}

pub open spec fn part1_mct_fragment_swap_remove(pending: Seq<Part1MctFragment>, index: usize) -> Seq<Part1MctFragment>
    recommends index < pending.len(),
{
    pending.update(index as int, pending.last()).drop_last()
}

pub open spec fn part1_mct_fragment_payload(state: Part1MctFragment) -> Seq<u8> {
    seq![0u8, 0u8, (state.descriptor >> 8) as u8, (state.descriptor & 255) as u8, 0u8, 0u8] + state.data
}

#[verifier::opaque]
pub open spec fn part1_consume_mct_fragment(
    segment: Part1CodestreamSegment, limits: &crate::ResourceLimits,
    pending: Seq<Part1MctFragment>, completed: Seq<u8>,
) -> (Result<Option<Part2MctArray>, crate::DecodeError>, Seq<Part1MctFragment>, Seq<u8>) {
    let prepared = part1_prepare_mct_fragment(segment, limits, pending, completed);
    match prepared.0 {
        Err(error) => (Err(error), prepared.1, completed),
        Ok((index, maximum)) => {
            let state = prepared.1[index as int];
            if !part2_fragment_complete(state.next_index, state.final_index) {
                (Ok(None), prepared.1, completed)
            } else {
                let removed = part1_mct_fragment_swap_remove(prepared.1, index);
                if state.data.len() as u64 > maximum {
                    (Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                        limit: maximum, actual: state.data.len() as u64 }), removed, completed)
                } else {
                    let raw = Part1CodestreamSegment { marker: 0xff74, offset: state.offset,
                        payload: part1_mct_fragment_payload(state) };
                    match part1_parse_mct(raw, limits) {
                        Err(error) => (Err(error), removed, completed),
                        Ok(array) => (Ok(Some(array)), removed, completed.push(segment.payload[3])),
                    }
                }
            }
        },
    }
}

pub open spec fn part1_numeric_unit_outcome(value: Result<i64, crate::DecodeError>) -> Result<i64, ()> {
    match value { Err(error) => Err(()), Ok(value) => Ok(value) }
}

pub open spec fn part1_fixed_from_binary(negative: bool, significand: u128, binary_exponent: i32) -> Result<i64, ()> {
    if binary_exponent < i32::MIN + 32 || binary_exponent > i32::MAX - 32 { Err(()) }
    else { part1_numeric_unit_outcome(part2_atk_binary_q32(negative, significand, binary_exponent)) }
}

pub open spec fn part1_float32_to_fixed(bits: u32) -> Result<i64, ()> {
    part1_numeric_unit_outcome(part2_atk_binary_format(bits as u128, 32, 8, 23, 127))
}

pub open spec fn part1_float64_to_fixed(bits: u64) -> Result<i64, ()> {
    part1_numeric_unit_outcome(part2_atk_binary_format(bits as u128, 64, 11, 52, 1023))
}

pub open spec fn part1_codestream_u64(bytes: Seq<u8>) -> u64
    recommends bytes.len() == 8,
{
    ((bytes[0] as u64) << 56) | ((bytes[1] as u64) << 48) | ((bytes[2] as u64) << 40)
        | ((bytes[3] as u64) << 32) | ((bytes[4] as u64) << 24) | ((bytes[5] as u64) << 16)
        | ((bytes[6] as u64) << 8) | bytes[7] as u64
}

pub open spec fn part1_signed_u16(value: u16) -> i64 {
    if value < 32768 { value as i64 } else { (value as int - 65536) as i64 }
}

pub open spec fn part1_mct_element_width(format: crate::codestream::MctNumericFormat) -> usize {
    match format {
        crate::codestream::MctNumericFormat::Int16 => 2,
        crate::codestream::MctNumericFormat::Int32 | crate::codestream::MctNumericFormat::Float32 => 4,
        crate::codestream::MctNumericFormat::Float64 => 8,
    }
}

#[verifier::opaque]
pub open spec fn part1_mct_element(offset: usize, data: Seq<u8>, position: usize, format: crate::codestream::MctNumericFormat)
    -> Result<i64, crate::DecodeError>
{
    let width = part1_mct_element_width(format);
    if position as int + width as int > data.len() {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform))
    } else {
        match format {
            crate::codestream::MctNumericFormat::Int16 =>
                Ok(part1_signed_u16(part1_marker_value(data[position as int], data[position as int + 1]))),
            crate::codestream::MctNumericFormat::Int32 => Ok(part1_signed_u32(part1_siz_word(data, position as int))),
            crate::codestream::MctNumericFormat::Float32 => match part1_float32_to_fixed(part1_siz_word(data, position as int)) {
                Err(error) => Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform)), Ok(value) => Ok(value),
            },
            crate::codestream::MctNumericFormat::Float64 => match part1_float64_to_fixed(
                part1_codestream_u64(data.subrange(position as int, position as int + 8))) {
                Err(error) => Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform)), Ok(value) => Ok(value),
            },
        }
    }
}

pub struct Part1MctHeader {
    pub index: u8, pub kind: crate::codestream::MctArrayKind, pub format: crate::codestream::MctNumericFormat,
    pub width: usize, pub count: usize, pub fraction: u8,
}

#[verifier::opaque]
pub open spec fn part1_mct_header(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    -> Result<Part1MctHeader, crate::DecodeError>
{
    if segment.payload.len() < 8 {
        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
    } else {
        let descriptor = part1_marker_value(segment.payload[2], segment.payload[3]);
        let index = (descriptor & 255) as u8;
        if part1_marker_value(segment.payload[0], segment.payload[1]) != 0
            || part1_marker_value(segment.payload[4], segment.payload[5]) != 0
            || descriptor & 0xf000 != 0 || index == 0 {
            Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
        } else {
            let kind = match (descriptor >> 8) & 3 {
                0 => Some(crate::codestream::MctArrayKind::Dependency),
                1 => Some(crate::codestream::MctArrayKind::Decorrelation),
                2 => Some(crate::codestream::MctArrayKind::Offset),
                _ => None,
            };
            match kind {
                None => Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform)),
                Some(kind) => {
                    let format = match (descriptor >> 10) & 3 {
                        0 => crate::codestream::MctNumericFormat::Int16,
                        1 => crate::codestream::MctNumericFormat::Int32,
                        2 => crate::codestream::MctNumericFormat::Float32,
                        _ => crate::codestream::MctNumericFormat::Float64,
                    };
                    let width = part1_mct_element_width(format);
                    let length = segment.payload.len() - 6;
                    let maximum = crate::limits::resource_component_limit(limits) as int
                        * crate::limits::resource_component_limit(limits) as int;
                    if length == 0 || length % (width as int) != 0 {
                        Err(part1_codestream_malformed(segment.offset, crate::MalformedKind::InvalidTransform))
                    } else if (length / width as int) as u64 > maximum {
                        Err(crate::DecodeError::LimitExceeded { resource: crate::Resource::TransformElements,
                            limit: maximum as u64, actual: (length / width as int) as u64 })
                    } else {
                        Ok(Part1MctHeader { index, kind, format, width, count: (length / width as int) as usize,
                            fraction: match format {
                                crate::codestream::MctNumericFormat::Float32 | crate::codestream::MctNumericFormat::Float64 => 32,
                                _ => 0,
                            },
                        })
                    }
                },
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_mct_values(
    offset: usize, data: Seq<u8>, format: crate::codestream::MctNumericFormat, position: nat, values: Seq<i64>,
) -> Result<Seq<i64>, crate::DecodeError>
    decreases data.len() - position,
{
    let stride = match format {
        crate::codestream::MctNumericFormat::Int16 => 2nat,
        crate::codestream::MctNumericFormat::Int32 | crate::codestream::MctNumericFormat::Float32 => 4nat,
        crate::codestream::MctNumericFormat::Float64 => 8nat,
    };
    if position >= data.len() { Ok(values) }
    else if position + stride > data.len() {
        Err(part1_codestream_malformed(offset, crate::MalformedKind::InvalidTransform))
    } else {
        match part1_mct_element(offset, data, position as usize, format) {
            Err(error) => Err(error),
            Ok(value) => part1_mct_values(offset, data, format, position + stride, values.push(value)),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_parse_mct(segment: Part1CodestreamSegment, limits: &crate::ResourceLimits)
    -> Result<Part2MctArray, crate::DecodeError>
{
    match part1_mct_header(segment, limits) {
        Err(error) => Err(error),
        Ok(header) => match part1_mct_values(segment.offset, segment.payload.subrange(6, segment.payload.len() as int), header.format, 0, Seq::empty()) {
            Err(error) => Err(error), Ok(values) => Ok((header.index, header.kind, header.format, header.fraction, values)),
        },
    }
}

pub open spec fn part1_main_header_boundary(marker: u16) -> bool {
    marker == 0xff4f || marker == 0xff93 || marker == 0xffd9
}

pub open spec fn part1_tile_header_boundary(marker: u16) -> bool {
    marker == 0xff4f || marker == 0xff51 || marker == 0xff90 || marker == 0xffd9
}

pub open spec fn part1_packet_next_included(old: bool, contribution_present: bool) -> bool {
    old || contribution_present
}

pub open spec fn part1_packet_next_lblock(lblock: u8) -> u8
    recommends lblock < 31,
{
    ((lblock as int) + 1) as u8
}

pub open spec fn part1_packet_next_passes(old: u32, added: u32) -> u32
    recommends old <= u32::MAX - added,
{
    ((old as int) + (added as int)) as u32
}

pub open spec fn part1_exact_consumption(consumed: usize, expected: usize) -> bool {
    consumed == expected
}

pub open spec fn part1_packet_logical_bytes(tile: usize, packed: usize) -> usize
    recommends tile <= usize::MAX - packed,
{
    ((tile as int) + (packed as int)) as usize
}

pub open spec fn part1_mq_interval_subtract(interval: u32, qe: u16) -> u32
    recommends (qe as u32) <= interval,
{
    ((interval as int) - (qe as int)) as u32
}

pub open spec fn part1_mq_code_subtract(code: u32, qe: u16) -> u32
    recommends (qe as u64) * 65536 <= code as u64,
{
    ((code as int) - (qe as int) * 65536) as u32
}

pub open spec fn part1_mq_byte_class(current: u8, next: u8) -> u8 {
    if current == 0xff && next > 0x8f {
        0
    } else if current == 0xff {
        1
    } else {
        2
    }
}

pub open spec fn part1_mq_byte_addend(current: u8, next: u8) -> u32 {
    if current == 0xff && next > 0x8f {
        0xff00
    } else if current == 0xff {
        (next as u32) << 9
    } else {
        (next as u32) << 8
    }
}

pub open spec fn part1_mq_byte_ct(current: u8, next: u8) -> u8 {
    if current == 0xff && next <= 0x8f { 7 } else { 8 }
}

pub open spec fn part1_mq_byte_advances(current: u8, next: u8) -> bool {
    !(current == 0xff && next > 0x8f)
}

pub open spec fn part1_mq_renorm_double(value: u32) -> u32
    recommends value <= u32::MAX / 2,
{
    ((value as int) * 2) as u32
}

pub open spec fn part1_mq_renorm_ct(ct: u8) -> u8
    recommends ct > 0,
{
    ((ct as int) - 1) as u8
}

pub open spec fn part1_tier1_stripe_rows(height: u16, y: u16) -> u16
    recommends y < height,
{
    if (height as int) - (y as int) < 4 {
        ((height as int) - (y as int)) as u16
    } else {
        4
    }
}

pub open spec fn part1_tier1_sigprop_eligible(significant: bool, neighbors: u16) -> bool {
    !significant && neighbors > 0
}

pub open spec fn part1_tier1_magref_eligible(significant_before: bool) -> bool {
    significant_before
}

pub open spec fn part1_tier1_cleanup_eligible(
    significant: bool,
    visited: bool,
) -> bool {
    !significant && !visited
}

pub open spec fn part1_tier1_pass_complete(kind: u8) -> u8 {
    if kind == 0 { 1 } else if kind == 1 { 2 } else { 4 }
}

pub open spec fn part1_tier1_zero_context(
    horizontal: u16,
    vertical: u16,
    diagonal: u16,
    high_high: bool,
) -> u8 {
    if high_high {
        let direct = (horizontal as int) + (vertical as int);
        if diagonal == 0 {
            if direct == 0 { 0 } else if direct == 1 { 1 } else { 2 }
        } else if diagonal == 1 {
            if direct == 0 { 3 } else if direct == 1 { 4 } else { 5 }
        } else if diagonal == 2 {
            if direct == 0 { 6 } else { 7 }
        } else {
            8
        }
    } else if horizontal == 0 {
        if vertical == 0 {
            if diagonal == 0 { 0 } else if diagonal == 1 { 1 } else { 2 }
        } else if vertical == 1 {
            3
        } else {
            4
        }
    } else if horizontal == 1 {
        if vertical == 0 {
            if diagonal == 0 { 5 } else { 6 }
        } else {
            7
        }
    } else {
        8
    }
}

pub open spec fn part1_tier1_sign_offset(horizontal: i8, vertical: i8) -> u8 {
    if horizontal == 0 {
        if vertical == 0 { 0 } else { 1 }
    } else if vertical < 0 {
        2
    } else if vertical == 0 {
        3
    } else {
        4
    }
}

pub open spec fn part1_tier1_predicted_negative(horizontal: i8, vertical: i8) -> bool {
    horizontal < 0 || (horizontal == 0 && vertical < 0)
}

pub open spec fn part1_tier1_decoded_sign(symbol: bool, predicted: bool, raw: bool) -> bool {
    if raw { symbol } else { symbol != predicted }
}

pub open spec fn part1_irreversible_centered(magnitude: i64) -> i128 {
    ((magnitude as int) * 2 + 1) as i128
}

pub open spec fn part1_irreversible_scale(product: i128) -> i128
    recommends product >= 0,
{
    ((product as int) / 2) as i128
}

pub open spec fn part1_fixed_round_q16(adjusted: i64) -> i64 {
    adjusted >> 16
}

pub open spec fn part1_nine_seven_scale(low: bool) -> i64 {
    if low { 80621 } else { 53274 }
}

pub open spec fn part1_nine_seven_lift(stage: u8) -> i64 {
    if stage == 0 {
        29066
    } else if stage == 1 {
        57862
    } else if stage == 2 {
        (-3472int) as i64
    } else {
        (-103949int) as i64
    }
}

pub open spec fn part1_wavelet_detail_advance(direction: u8) -> usize {
    if direction == 3 { 3 } else if direction == 0 { 0 } else { 1 }
}

pub open spec fn part1_wavelet_next_resolution(resolution: u8) -> u8
    recommends resolution < u8::MAX,
{
    ((resolution as int) + 1) as u8
}

pub open spec fn part1_wavelet_sample_count(
    width: u32,
    height: u32,
    samples: usize,
) -> bool {
    if width == 0 {
        samples == 0
    } else {
        samples % width as usize == 0
            && samples / width as usize == height as usize
    }
}

pub open spec fn part1_sop_sequence(high: u8, low: u8) -> u16 {
    ((high as u16) << 8) | (low as u16)
}

pub open spec fn part1_sop_valid(
    marker0: u8,
    marker1: u8,
    length0: u8,
    length1: u8,
) -> bool {
    marker0 == 0xff && marker1 == 0x91 && length0 == 0 && length1 == 4
}

pub open spec fn part1_eph_valid(marker0: u8, marker1: u8) -> bool {
    marker0 == 0xff && marker1 == 0x92
}

pub open spec fn part1_packet_length_matches(actual: usize, expected: usize) -> bool {
    actual == expected
}

pub open spec fn part1_decode_output_shape_valid(
    input_bytes: usize,
    tile_parts: usize,
    expected_components: u16,
    output_components: usize,
    width: u32,
    height: u32,
) -> bool {
    input_bytes > 0
        && tile_parts > 0
        && expected_components > 0
        && expected_components as usize == output_components
        && width > 0
        && height > 0
}

pub open spec fn part1_component_output_shape_valid(
    width: u32,
    height: u32,
    samples: usize,
) -> bool {
    width > 0 && height > 0 && part1_wavelet_sample_count(width, height, samples)
}

pub open spec fn part1_validate_typed_output_components(
    components: Seq<Part1TypedComponentModel>, component: nat,
) -> Result<(), crate::DecodeError>
    decreases components.len() - component,
{
    if component >= components.len() { Ok(()) }
    else {
        let output = components[component as int];
        let samples = match output.samples {
            Part1TypedSampleSequence::Signed(values) => values.len(),
            Part1TypedSampleSequence::Unsigned(values) => values.len(),
        };
        if !part1_component_output_shape_valid(output.width, output.height, samples as usize) {
            Err(part1_block_placement_error(false))
        } else { part1_validate_typed_output_components(components, component + 1) }
    }
}

pub open spec fn part1_validate_typed_output_shape(
    input_bytes: usize, tile_parts: usize, expected_components: u16,
    image: Part1DecodedTypedImage,
) -> Result<(), crate::DecodeError> {
    if !part1_decode_output_shape_valid(
        input_bytes, tile_parts, expected_components, image.1.len() as usize,
        image.0.0, image.0.1,
    ) { Err(part1_block_placement_error(false)) }
    else { part1_validate_typed_output_components(image.1, 0) }
}

pub open spec fn part1_magnitude_limb(limbs: Seq<u64>, index: usize) -> Option<u64> {
    if index < limbs.len() { Some(limbs[index as int]) } else { None }
}

pub open spec fn part1_magnitude_zero(limbs: Seq<u64>) -> bool {
    forall |i: int| 0 <= i < limbs.len() ==> limbs[i] == 0
}

pub open spec fn part1_magnitude_prefix_value(limbs: Seq<u64>, count: nat) -> nat
    decreases count,
{
    if count == 0 { 0 }
    else {
        part1_magnitude_prefix_value(limbs, (count - 1) as nat)
            + (limbs[count - 1] as nat) * pow2((64 * (count - 1)) as nat)
    }
}

pub open spec fn part1_magnitude_value(limbs: Seq<u64>) -> nat {
    part1_magnitude_prefix_value(limbs, 6)
}

pub open spec fn part1_magnitude_capacity() -> nat {
    pow2(384)
}

pub open spec fn part1_magnitude_low_value(limbs: Seq<u64>) -> nat {
    part1_magnitude_value(limbs) % pow2(64)
}

pub open spec fn part1_magnitude_limb_or_zero(limbs: Seq<u64>, index: int) -> u64 {
    if 0 <= index < 6 { limbs[index] } else { 0 }
}

pub open spec fn part1_magnitude_right_word(low: u64, high: u64, partial: u32) -> u64 {
    if partial == 0 { low } else { (low >> partial) | (high << ((64 - partial) as u32)) }
}

pub open spec fn part1_magnitude_left_word(current: u64, previous: u64, partial: u32) -> u64 {
    if partial == 0 { current } else { (current << partial) | (previous >> ((64 - partial) as u32)) }
}

pub open spec fn part1_magnitude_left_limb(limbs: Seq<u64>, shift: u16, index: int) -> u64 {
    if shift >= 384 { 0 } else {
        let source = index - shift / 64;
        part1_magnitude_left_word(
            part1_magnitude_limb_or_zero(limbs, source),
            part1_magnitude_limb_or_zero(limbs, source - 1),
            (shift % 64) as u32,
        )
    }
}

pub open spec fn part1_magnitude_left(limbs: Seq<u64>, shift: u16) -> Seq<u64> {
    Seq::new(6, |i: int| part1_magnitude_left_limb(limbs, shift, i))
}

pub open spec fn part1_magnitude_left_fits(limbs: Seq<u64>, shift: u16) -> bool {
    if shift >= 384 {
        part1_magnitude_zero(limbs)
    } else {
        forall |i: int| 0 <= i < 6 ==>
            if i + shift / 64 >= 6 { limbs[i] == 0 }
            else if shift % 64 != 0 && i + shift / 64 == 5 {
                limbs[i] >> ((64 - shift % 64) as u32) == 0
            } else { true }
    }
}

pub open spec fn part1_magnitude_u64(limbs: Seq<u64>) -> Option<u64> {
    if forall |i: int| 1 <= i < limbs.len() ==> limbs[i] == 0 {
        Some(limbs[0])
    } else {
        None
    }
}

pub open spec fn part1_magnitude_less(left: Seq<u64>, right: Seq<u64>) -> bool {
    exists |i: int| 0 <= i < left.len() && left[i] < right[i]
        && forall |j: int| i < j < left.len() ==> left[j] == right[j]
}

pub open spec fn part1_magnitude_prefix_less(left: Seq<u64>, right: Seq<u64>, count: nat) -> bool {
    exists |i: int| 0 <= i < count && left[i] < right[i]
        && forall |j: int| i < j < count ==> left[j] == right[j]
}

pub open spec fn part1_magnitude_subtraction(left: nat, right: nat) -> Result<nat, crate::DecodeError> {
    if left < right { Err(part1_transform_error(true)) } else { Ok((left - right) as nat) }
}

pub open spec fn part1_magnitude_bit(bit: u16) -> Seq<u64> {
    Seq::new(6, |i: int| if i == bit / 64 { 1u64 << (bit % 64) } else { 0 })
}

pub open spec fn part1_magnitude_shift_limb(limbs: Seq<u64>, shift: u16, i: int) -> u64 {
    let source = i + shift / 64;
    let partial = (shift % 64) as u32;
    if shift >= 384 || source >= 6 {
        0
    } else if partial == 0 || source + 1 >= 6 {
        limbs[source] >> partial
    } else {
        (limbs[source] >> partial) | (limbs[source + 1] << (64 - partial))
    }
}

pub open spec fn part1_magnitude_shift(limbs: Seq<u64>, shift: u16) -> Seq<u64> {
    Seq::new(6, |i: int| part1_magnitude_shift_limb(limbs, shift, i))
}

pub open spec fn part1_transform_error(arithmetic: bool) -> crate::DecodeError {
    crate::DecodeError::MalformedInput {
        offset: 0,
        kind: if arithmetic { crate::MalformedKind::ArithmeticOverflow }
            else { crate::MalformedKind::InvalidTransform },
    }
}

pub open spec fn part1_checked_sample(value: int) -> Result<i64, crate::DecodeError> {
    if i64::MIN <= value <= i64::MAX {
        Ok(value as i64)
    } else {
        Err(part1_transform_error(true))
    }
}

pub open spec fn part1_roi_coefficient(
    limbs: Seq<u64>, negative: bool, shift: u8,
) -> Result<i64, crate::DecodeError> {
    if part1_magnitude_zero(limbs) {
        Ok(0)
    } else {
        let restored = if shift == 0 || part1_magnitude_less(limbs, part1_magnitude_bit(shift as u16)) {
            limbs
        } else {
            part1_magnitude_shift(limbs, shift as u16)
        };
        match part1_magnitude_u64(restored) {
            Some(value) => if value <= i64::MAX {
                Ok((if negative { -(value as int) } else { value as int }) as i64)
            } else {
                Err(part1_transform_error(true))
            },
            None => Err(part1_transform_error(true)),
        }
    }
}

pub open spec fn part1_quantization_step(
    exponent: u8, mantissa: u16, dynamic_range: u8,
) -> Result<i64, crate::DecodeError> {
    let base = ((2048 + mantissa as int) * 65536 / 2048) as i64;
    if dynamic_range >= exponent {
        let shift = (dynamic_range - exponent) as u8;
        if shift > 38 {
            Err(part1_transform_error(false))
        } else {
            part1_checked_sample((base as int) * ((1i64 << shift) as int))
        }
    } else {
        let shift = (exponent - dynamic_range) as u8;
        if shift > 62 {
            Err(part1_transform_error(false))
        } else {
            Ok((base / (1i64 << shift)) as i64)
        }
    }
}

pub open spec fn part1_dequantized_sample(
    coefficient: i64, step: i64, reversible: bool,
) -> Result<i64, crate::DecodeError> {
    if reversible || coefficient == 0 {
        Ok(part1_reversible_inverse_quantize(coefficient as int) as i64)
    } else {
        let magnitude = if coefficient < 0 { -(coefficient as int) } else { coefficient as int };
        let scaled = (2 * magnitude + 1) * (step as int) / 2;
        if coefficient == i64::MIN || step < 0 || scaled > i64::MAX {
            Err(part1_transform_error(true))
        } else {
            Ok((if coefficient < 0 { -scaled } else { scaled }) as i64)
        }
    }
}

pub type Part1QuantizedCoefficient = (Seq<u64>, bool);
pub type Part1ReconstructedPlane = (u32, u32, u8, Seq<i64>);
pub type Part1ReconstructionResult = Result<Part1ReconstructedPlane, crate::DecodeError>;

pub open spec fn part1_quantized_sample(
    coefficient: Part1QuantizedCoefficient, shift: u8, step: i64, reversible: bool,
) -> Result<i64, crate::DecodeError> {
    match part1_roi_coefficient(coefficient.0, coefficient.1, shift) {
        Err(error) => Err(error),
        Ok(value) => part1_dequantized_sample(value, step, reversible),
    }
}

pub open spec fn part1_quantized_prefix(
    coefficients: Seq<Part1QuantizedCoefficient>, shift: u8, step: i64, reversible: bool, count: nat,
) -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 {
        Ok(Seq::empty())
    } else {
        match part1_quantized_prefix(coefficients, shift, step, reversible, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(prefix) => match part1_quantized_sample(coefficients[count - 1], shift, step, reversible) {
                Err(error) => Err(error),
                Ok(sample) => Ok(prefix.push(sample)),
            },
        }
    }
}

pub open spec fn part1_quantization_budget(count: nat, maximum: u64) -> Result<(), crate::DecodeError> {
    if count * 8 > u64::MAX {
        Err(part1_transform_error(true))
    } else if count * 8 > maximum {
        Err(crate::DecodeError::LimitExceeded {
            resource: crate::Resource::DecodedBytes, limit: maximum, actual: (count * 8) as u64,
        })
    } else {
        Ok(())
    }
}

pub open spec fn part1_inverse_quantization(
    coefficients: Seq<Part1QuantizedCoefficient>, exponent: u8, mantissa: u16,
    dynamic_range: u8, reversible: bool, shift: u8, maximum: u64,
) -> Part1ReconstructionResult {
    if dynamic_range == 0 || dynamic_range > 38 || mantissa > 2047 || exponent > 31 {
        Err(part1_transform_error(false))
    } else {
        match part1_quantization_budget(coefficients.len(), maximum) {
            Err(error) => Err(error),
            Ok(()) => match if reversible { Ok(1i64) }
                else { part1_quantization_step(exponent, mantissa, dynamic_range) } {
                Err(error) => Err(error),
                Ok(step) => match part1_quantized_prefix(coefficients, shift, step, reversible, coefficients.len()) {
                    Err(error) => Err(error),
                    Ok(samples) => if coefficients.len() > u32::MAX {
                        Err(part1_transform_error(true))
                    } else {
                        Ok((coefficients.len() as u32, 1u32, if reversible { 0u8 } else { 16u8 }, samples))
                    },
                },
            },
        }
    }
}

pub open spec fn part1_integer_coefficients(coefficients: Seq<i64>) -> Seq<Part1QuantizedCoefficient> {
    Seq::new(coefficients.len(), |i: int| {
        let value = coefficients[i];
        let magnitude = (if value < 0 { -(value as int) } else { value as int }) as u64;
        (Seq::new(6, |j: int| if j == 0 { magnitude } else { 0u64 }), value < 0)
    })
}

pub open spec fn part1_inverse_integer_quantization(
    coefficients: Seq<i64>, exponent: u8, mantissa: u16,
    dynamic_range: u8, reversible: bool, shift: u8, maximum: u64,
) -> Part1ReconstructionResult {
    if exists |i: int| 0 <= i < coefficients.len() && coefficients[i] == i64::MIN {
        Err(part1_transform_error(true))
    } else {
        part1_inverse_quantization(
            part1_integer_coefficients(coefficients), exponent, mantissa,
            dynamic_range, reversible, shift, maximum,
        )
    }
}

pub open spec fn part1_interleaved(
    low: Seq<i64>, high: Seq<i64>, low_first: bool,
) -> Result<Seq<i64>, crate::DecodeError> {
    let length = low.len() + high.len();
    let expected = if low_first { length / 2 + length % 2 } else { length / 2 };
    if length > usize::MAX {
        Err(part1_transform_error(true))
    } else if low.len() != expected || high.len() != length - expected {
        Err(part1_transform_error(false))
    } else {
        Ok(Seq::new(length, |i: int| if (i % 2 == 0) == low_first { low[i / 2] } else { high[i / 2] }))
    }
}

pub open spec fn part1_fixed_product(value: i64, factor: i64) -> Result<i64, crate::DecodeError> {
    let product = (value as int) * (factor as int);
    if product < i64::MIN || product > i64::MAX
        || product + 32768 < i64::MIN || product + 32768 > i64::MAX {
        Err(part1_transform_error(true))
    } else {
        Ok(((product + 32768) as i64) >> 16)
    }
}

// Kinds 0/1 are the reversible update/predict; kind 2 is the fixed-point lift.
pub open spec fn part1_lifting_sample(
    samples: Seq<i64>, index: nat, target_even: bool, kind: u8, factor: i64,
) -> Result<i64, crate::DecodeError> {
    if (index % 2 == 0) != target_even || samples.len() <= 1 {
        Ok(samples[index as int])
    } else {
        let left = samples[if index == 0 { 1 } else { index - 1 }];
        let right = samples[if index + 1 < samples.len() { index as int + 1 } else { index - 1 }];
        match part1_checked_sample((left as int) + (right as int)) {
            Err(error) => Err(error),
            Ok(sum) => {
                let adjustment = if kind == 2 {
                    part1_fixed_product(sum, factor)
                } else if kind == 0 {
                    match part1_checked_sample((sum as int) + 2) {
                        Err(error) => Err(error),
                        Ok(biased) => Ok(biased >> 2),
                    }
                } else {
                    Ok(sum >> 1)
                };
                match adjustment {
                    Err(error) => Err(error),
                    Ok(delta) => part1_checked_sample(
                        (samples[index as int] as int) + if kind == 1 { delta as int } else { -(delta as int) },
                    ),
                }
            },
        }
    }
}

pub type Part1LiftingState = (Result<(), crate::DecodeError>, Seq<i64>);

pub open spec fn part1_lifting_prefix(
    samples: Seq<i64>, target_even: bool, kind: u8, factor: i64, count: nat,
) -> Part1LiftingState
    decreases count,
{
    if count == 0 {
        (Ok(()), samples)
    } else {
        let previous = part1_lifting_prefix(samples, target_even, kind, factor, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => match part1_lifting_sample(samples, (count - 1) as nat, target_even, kind, factor) {
                Err(error) => (Err(error), previous.1),
                Ok(value) => (Ok(()), previous.1.update(count - 1, value)),
            },
        }
    }
}

pub open spec fn part1_inverse_five_three(
    low: Seq<i64>, high: Seq<i64>, low_first: bool,
) -> Result<Seq<i64>, crate::DecodeError> {
    match part1_interleaved(low, high, low_first) {
        Err(error) => Err(error),
        Ok(samples) => if samples.len() == 1 && !low_first {
            Ok(samples.update(0, samples[0] >> 1))
        } else {
            let update = part1_lifting_prefix(samples, low_first, 0, 0, samples.len());
            match update.0 {
                Err(error) => Err(error),
                Ok(()) => {
                    let predict = part1_lifting_prefix(update.1, !low_first, 1, 0, update.1.len());
                    match predict.0 {
                        Err(error) => Err(error),
                        Ok(()) => Ok(predict.1),
                    }
                },
            }
        },
    }
}

pub open spec fn part1_scaling_prefix(
    samples: Seq<i64>, target_even: bool, factor: i64, count: nat,
) -> Part1LiftingState
    decreases count,
{
    if count == 0 {
        (Ok(()), samples)
    } else {
        let previous = part1_scaling_prefix(samples, target_even, factor, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => {
                let index = count - 1;
                if (index % 2 == 0) != target_even {
                    previous
                } else {
                    match part1_fixed_product(samples[index], factor) {
                        Err(error) => (Err(error), previous.1),
                        Ok(value) => (Ok(()), previous.1.update(index, value)),
                    }
                }
            },
        }
    }
}

pub open spec fn part1_nine_seven_lifting_prefix(
    samples: Seq<i64>, low_first: bool, count: nat,
) -> Part1LiftingState
    decreases count,
{
    if count == 0 {
        (Ok(()), samples)
    } else {
        let previous = part1_nine_seven_lifting_prefix(samples, low_first, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_lifting_prefix(
                previous.1, if count % 2 == 1 { low_first } else { !low_first },
                2, part1_nine_seven_lift((count - 1) as u8), previous.1.len(),
            ),
        }
    }
}

pub open spec fn part1_inverse_nine_seven(
    low: Seq<i64>, high: Seq<i64>, low_first: bool,
) -> Result<Seq<i64>, crate::DecodeError> {
    match part1_interleaved(low, high, low_first) {
        Err(error) => Err(error),
        Ok(samples) => if samples.len() <= 1 {
            Ok(samples)
        } else {
            let low_scaled = part1_scaling_prefix(samples, low_first, part1_nine_seven_scale(true), samples.len());
            match low_scaled.0 {
                Err(error) => Err(error),
                Ok(()) => {
                    let high_scaled = part1_scaling_prefix(
                        low_scaled.1, !low_first, part1_nine_seven_scale(false), low_scaled.1.len(),
                    );
                    match high_scaled.0 {
                        Err(error) => Err(error),
                        Ok(()) => {
                            let lifted = part1_nine_seven_lifting_prefix(high_scaled.1, low_first, 4);
                            match lifted.0 {
                                Err(error) => Err(error),
                                Ok(()) => Ok(lifted.1),
                            }
                        },
                    }
                },
            }
        },
    }
}

pub type Part1WaveletBand = (u32, u32, Seq<i64>);

pub open spec fn part1_transform_dimension(value: u32) -> Result<usize, crate::DecodeError> {
    if value > usize::MAX {
        Err(part1_transform_error(true))
    } else {
        Ok(value as usize)
    }
}

pub open spec fn part1_transform_area(width: u32, height: u32) -> Result<usize, crate::DecodeError> {
    if width > usize::MAX || height > usize::MAX || (width as int) * (height as int) > usize::MAX {
        Err(part1_transform_error(true))
    } else {
        Ok(((width as int) * (height as int)) as usize)
    }
}

pub open spec fn part1_low_count(length: u32, low_first: bool) -> u32 {
    ((length as int) / 2 + if low_first { (length as int) % 2 } else { 0 }) as u32
}

pub open spec fn part1_band_row(band: Part1WaveletBand, y: u32) -> Result<Seq<i64>, crate::DecodeError> {
    let start = (y as int) * (band.0 as int);
    let end = start + band.0;
    if y >= band.1 {
        Err(part1_transform_error(false))
    } else if y > usize::MAX || band.0 > usize::MAX || start > usize::MAX || end > usize::MAX {
        Err(part1_transform_error(true))
    } else if end > band.2.len() {
        Err(part1_transform_error(false))
    } else {
        Ok(band.2.subrange(start, end))
    }
}

pub open spec fn part1_inverse_sequence(
    low: Seq<i64>, high: Seq<i64>, low_first: bool, irreversible: bool,
) -> Result<Seq<i64>, crate::DecodeError> {
    if irreversible {
        part1_inverse_nine_seven(low, high, low_first)
    } else {
        part1_inverse_five_three(low, high, low_first)
    }
}

pub open spec fn part1_horizontal_row(
    low: Part1WaveletBand, high: Part1WaveletBand, y: u32, low_first: bool, irreversible: bool,
) -> Result<Seq<i64>, crate::DecodeError> {
    match part1_band_row(low, y) {
        Err(error) => Err(error),
        Ok(low_row) => match part1_band_row(high, y) {
            Err(error) => Err(error),
            Ok(high_row) => part1_inverse_sequence(low_row, high_row, low_first, irreversible),
        },
    }
}

pub open spec fn part1_horizontal_prefix(
    low: Part1WaveletBand, high: Part1WaveletBand, low_first: bool, irreversible: bool, count: nat,
) -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 {
        Ok(Seq::empty())
    } else {
        match part1_horizontal_prefix(low, high, low_first, irreversible, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_horizontal_row(low, high, (count - 1) as u32, low_first, irreversible) {
                Err(error) => Err(error),
                Ok(row) => Ok(previous + row),
            },
        }
    }
}

pub open spec fn part1_horizontal_geometry(
    low: Part1WaveletBand, high: Part1WaveletBand, width: u32, low_first: bool,
) -> Result<(), crate::DecodeError> {
    if low.1 == 0 || low.1 != high.1 || low.0 != part1_low_count(width, low_first) {
        Err(part1_transform_error(false))
    } else if low.0 > width {
        Err(part1_transform_error(true))
    } else if high.0 != (width - low.0) as u32 {
        Err(part1_transform_error(false))
    } else {
        Ok(())
    }
}

pub open spec fn part1_inverse_horizontal(
    low: Part1WaveletBand, high: Part1WaveletBand, width: u32,
    low_first: bool, irreversible: bool, maximum: u64,
) -> Part1ReconstructionResult {
    match part1_horizontal_geometry(low, high, width, low_first) {
        Err(error) => Err(error),
        Ok(()) => match part1_transform_area(width, low.1) {
            Err(error) => Err(error),
            Ok(length) => match part1_quantization_budget(length as nat, maximum) {
                Err(error) => Err(error),
                Ok(()) => match part1_horizontal_prefix(low, high, low_first, irreversible, low.1 as nat) {
                    Err(error) => Err(error),
                    Ok(samples) => Ok((width, low.1, if irreversible { 16u8 } else { 0u8 }, samples)),
                },
            },
        },
    }
}

pub open spec fn part1_transform_offset(y: u32, width: u32, x: u32) -> Result<usize, crate::DecodeError> {
    let row = (y as int) * (width as int);
    if y > usize::MAX || width > usize::MAX || x > usize::MAX || row > usize::MAX || row + x > usize::MAX {
        Err(part1_transform_error(true))
    } else {
        Ok((row + x) as usize)
    }
}

pub open spec fn part1_column_sample(
    samples: Seq<i64>, width: u32, x: u32, y: u32,
) -> Result<i64, crate::DecodeError> {
    match part1_transform_offset(y, width, x) {
        Err(error) => Err(error),
        Ok(index) => if index >= samples.len() {
            Err(part1_transform_error(false))
        } else {
            Ok(samples[index as int])
        },
    }
}

pub open spec fn part1_column_prefix(
    samples: Seq<i64>, width: u32, x: u32, count: nat,
) -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 {
        Ok(Seq::empty())
    } else {
        match part1_column_prefix(samples, width, x, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_column_sample(samples, width, x, (count - 1) as u32) {
                Err(error) => Err(error),
                Ok(value) => Ok(previous.push(value)),
            },
        }
    }
}

pub open spec fn part1_collect_column(band: Part1WaveletBand, x: u32) -> Result<Seq<i64>, crate::DecodeError> {
    if x >= band.0 {
        Err(part1_transform_error(false))
    } else if band.1 > usize::MAX {
        Err(part1_transform_error(true))
    } else {
        part1_column_prefix(band.2, band.0, x, band.1 as nat)
    }
}

pub open spec fn part1_store_column_sample(
    output: Seq<i64>, width: u32, x: u32, column: Seq<i64>, y: u32,
) -> Part1LiftingState {
    match part1_transform_offset(y, width, x) {
        Err(error) => (Err(error), output),
        Ok(index) => if y >= column.len() || index >= output.len() {
            (Err(part1_transform_error(false)), output)
        } else {
            (Ok(()), output.update(index as int, column[y as int]))
        },
    }
}

pub open spec fn part1_store_column_prefix(
    output: Seq<i64>, width: u32, x: u32, column: Seq<i64>, count: nat,
) -> Part1LiftingState
    decreases count,
{
    if count == 0 {
        (Ok(()), output)
    } else {
        let previous = part1_store_column_prefix(output, width, x, column, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_store_column_sample(previous.1, width, x, column, (count - 1) as u32),
        }
    }
}

pub open spec fn part1_vertical_column(
    low: Part1WaveletBand, high: Part1WaveletBand, x: u32, low_first: bool, irreversible: bool,
) -> Result<Seq<i64>, crate::DecodeError> {
    match part1_collect_column(low, x) {
        Err(error) => Err(error),
        Ok(low_column) => match part1_collect_column(high, x) {
            Err(error) => Err(error),
            Ok(high_column) => part1_inverse_sequence(low_column, high_column, low_first, irreversible),
        },
    }
}

pub open spec fn part1_vertical_prefix(
    low: Part1WaveletBand, high: Part1WaveletBand, height: u32, low_first: bool,
    irreversible: bool, length: usize, count: nat,
) -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 {
        Ok(Seq::new(length as nat, |i: int| 0i64))
    } else {
        match part1_vertical_prefix(low, high, height, low_first, irreversible, length, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_vertical_column(low, high, (count - 1) as u32, low_first, irreversible) {
                Err(error) => Err(error),
                Ok(column) => {
                    let stored = part1_store_column_prefix(previous, low.0, (count - 1) as u32, column, height as nat);
                    match stored.0 {
                        Err(error) => Err(error),
                        Ok(()) => Ok(stored.1),
                    }
                },
            },
        }
    }
}

pub open spec fn part1_vertical_geometry(
    low: Part1WaveletBand, high: Part1WaveletBand, height: u32, low_first: bool,
) -> Result<(), crate::DecodeError> {
    if low.0 == 0 || low.0 != high.0 || low.1 != part1_low_count(height, low_first) {
        Err(part1_transform_error(false))
    } else if low.1 > height {
        Err(part1_transform_error(true))
    } else if high.1 != (height - low.1) as u32 {
        Err(part1_transform_error(false))
    } else {
        Ok(())
    }
}

pub open spec fn part1_inverse_vertical(
    low: Part1WaveletBand, high: Part1WaveletBand, height: u32,
    low_first: bool, irreversible: bool, maximum: u64,
) -> Part1ReconstructionResult {
    match part1_vertical_geometry(low, high, height, low_first) {
        Err(error) => Err(error),
        Ok(()) => match part1_transform_area(low.0, height) {
            Err(error) => Err(error),
            Ok(length) => match part1_quantization_budget(length as nat, maximum) {
                Err(error) => Err(error),
                Ok(()) => match part1_vertical_prefix(low, high, height, low_first, irreversible, length, low.0 as nat) {
                    Err(error) => Err(error),
                    Ok(samples) => Ok((low.0, height, if irreversible { 16u8 } else { 0u8 }, samples)),
                },
            },
        },
    }
}

pub type Part1WaveletLevel = (Part1WaveletBand, Part1WaveletBand, Part1WaveletBand, Part1WaveletBand, u32, u32, bool, bool);

pub open spec fn part1_validate_band(band: Part1WaveletBand, width: u32, height: u32) -> Result<(), crate::DecodeError> {
    if band.0 != width || band.1 != height {
        Err(part1_transform_error(false))
    } else {
        match part1_transform_area(width, height) {
            Err(error) => Err(error),
            Ok(length) => if band.2.len() != length {
                Err(part1_transform_error(false))
            } else {
                Ok(())
            },
        }
    }
}

pub open spec fn part1_validate_level(level: Part1WaveletLevel) -> Result<(), crate::DecodeError> {
    let low_width = part1_low_count(level.4, level.6);
    let high_width = (level.4 - low_width) as u32;
    let low_height = part1_low_count(level.5, level.7);
    let high_height = (level.5 - low_height) as u32;
    if level.4 == 0 || level.5 == 0 {
        Err(part1_transform_error(false))
    } else {
        match part1_validate_band(level.0, low_width, low_height) {
            Err(error) => Err(error),
            Ok(()) => match part1_validate_band(level.1, high_width, low_height) {
                Err(error) => Err(error),
                Ok(()) => match part1_validate_band(level.2, low_width, high_height) {
                    Err(error) => Err(error),
                    Ok(()) => part1_validate_band(level.3, high_width, high_height),
                },
            },
        }
    }
}

pub open spec fn part1_level_rows_and_columns(
    level: Part1WaveletLevel, irreversible: bool, length: usize,
) -> Part1ReconstructionResult {
    match part1_transform_area(level.4, level.0.1) {
        Err(error) => Err(error),
        Ok(_) => match part1_horizontal_prefix(level.0, level.1, level.6, irreversible, level.0.1 as nat) {
            Err(error) => Err(error),
            Ok(low_rows) => match part1_transform_area(level.4, level.2.1) {
                Err(error) => Err(error),
                Ok(_) => match part1_horizontal_prefix(level.2, level.3, level.6, irreversible, level.2.1 as nat) {
                    Err(error) => Err(error),
                    Ok(high_rows) => match part1_vertical_prefix(
                        (level.4, level.0.1, low_rows), (level.4, level.2.1, high_rows),
                        level.5, level.7, irreversible, length, level.4 as nat,
                    ) {
                        Err(error) => Err(error),
                        Ok(samples) => Ok((level.4, level.5, if irreversible { 16u8 } else { 0u8 }, samples)),
                    },
                },
            },
        },
    }
}

pub open spec fn part1_inverse_level(
    level: Part1WaveletLevel, irreversible: bool, maximum: u64,
) -> Part1ReconstructionResult {
    match part1_validate_level(level) {
        Err(error) => Err(error),
        Ok(()) => match part1_transform_area(level.4, level.5) {
            Err(error) => Err(error),
            Ok(length) => if !part1_wavelet_sample_count(level.4, level.5, length) {
                Err(part1_transform_error(false))
            } else {
                match part1_quantization_budget(length as nat, maximum) {
                    Err(error) => Err(error),
                    Ok(()) => part1_level_rows_and_columns(level, irreversible, length),
                }
            },
        },
    }
}

pub open spec fn part1_round_fixed(value: i64, fraction_bits: u8) -> Result<i64, crate::DecodeError> {
    if fraction_bits == 0 {
        Ok(value)
    } else if fraction_bits > 62 {
        Err(part1_transform_error(false))
    } else {
        let half = 1i64 << ((fraction_bits - 1) as u8);
        match part1_checked_sample((value as int) + (half as int)) {
            Err(error) => Err(error),
            Ok(biased) => Ok(biased >> fraction_bits),
        }
    }
}

pub open spec fn part1_convert_sample(
    value: i64, fraction_bits: u8, shift: i64, minimum: i64, maximum: i64,
) -> Result<i64, crate::DecodeError> {
    match part1_round_fixed(value, fraction_bits) {
        Err(error) => Err(error),
        Ok(rounded) => match part1_checked_sample((rounded as int) + (shift as int)) {
            Err(error) => Err(error),
            Ok(shifted) => Ok(part1_clip_sample(shifted, minimum, maximum)),
        },
    }
}

pub open spec fn part1_conversion_prefix(
    samples: Seq<i64>, fraction_bits: u8, shift: i64, minimum: i64, maximum: i64, count: nat,
) -> Result<Seq<i64>, crate::DecodeError>
    decreases count,
{
    if count == 0 {
        Ok(Seq::empty())
    } else {
        match part1_conversion_prefix(samples, fraction_bits, shift, minimum, maximum, (count - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_convert_sample(samples[count - 1], fraction_bits, shift, minimum, maximum) {
                Err(error) => Err(error),
                Ok(value) => Ok(previous.push(value)),
            },
        }
    }
}

pub open spec fn part1_output_maximum(precision: u8, signed: bool) -> i64 {
    (((if signed { 1i64 << ((precision - 1) as u8) } else { 1i64 << precision }) as int) - 1) as i64
}

pub open spec fn part1_output_minimum(precision: u8, signed: bool) -> i64 {
    if signed { (-((1i64 << ((precision - 1) as u8)) as int)) as i64 } else { 0 }
}

pub open spec fn part1_convert_samples(
    plane: Part1ReconstructedPlane, precision: u8, signed: bool, maximum_bytes: u64,
) -> Result<Seq<i64>, crate::DecodeError> {
    if precision == 0 || precision > 38 || plane.2 > 62 {
        Err(part1_transform_error(false))
    } else {
        match part1_quantization_budget(plane.3.len(), maximum_bytes) {
            Err(error) => Err(error),
            Ok(()) => part1_conversion_prefix(
                plane.3, plane.2, part1_level_shift(precision, signed),
                part1_output_minimum(precision, signed), part1_output_maximum(precision, signed), plane.3.len(),
            ),
        }
    }
}

pub open spec fn part1_image_error(arithmetic: bool) -> crate::DecodeError {
    crate::DecodeError::MalformedInput {
        offset: 0,
        kind: if arithmetic { crate::MalformedKind::ArithmeticOverflow }
            else { crate::MalformedKind::InvalidImageGeometry },
    }
}

pub open spec fn part2_registered_component_ceil(value: u32, divisor: u32, registration: u16)
    -> Result<u32, crate::DecodeError>
{
    if divisor == 0 { Err(part1_image_error(false)) } else {
        let numerator = value as int * 65536;
        if numerator > u64::MAX { Err(part1_image_error(true)) }
        else if numerator <= registration as int { Ok(0) }
        else {
            let adjusted = numerator - registration as int;
            let denominator = divisor as int * 65536;
            if adjusted < 0 || denominator > u64::MAX { Err(part1_image_error(true)) } else {
                let rounded = adjusted / denominator + if adjusted % denominator == 0 { 0int } else { 1int };
                if rounded > u64::MAX || rounded > u32::MAX { Err(part1_image_error(true)) }
                else { Ok(rounded as u32) }
            }
        }
    }
}

pub open spec fn part2_tile_component_bounds(
    size: Part2SelectionGeometry, count: u16, infos: Seq<crate::codestream::ComponentInfo>,
    tile_index: u16, component: u16,
) -> Result<crate::codestream::TileComponentBounds, crate::DecodeError> {
    match part2_selection_tile_bounds(size, tile_index) {
        Err(error) => Err(error),
        Ok(tile) => match part1_image_size_component(count, infos, component) {
            Err(error) => Err(error),
            Ok(info) => match (
                part2_registered_component_ceil(size.2, info.x_subsampling as u32, info.x_registration),
                part2_registered_component_ceil(size.3, info.y_subsampling as u32, info.y_registration),
                part2_registered_component_ceil(tile.x0, info.x_subsampling as u32, info.x_registration),
                part2_registered_component_ceil(tile.y0, info.y_subsampling as u32, info.y_registration),
                part2_registered_component_ceil(tile.x1, info.x_subsampling as u32, info.x_registration),
                part2_registered_component_ceil(tile.y1, info.y_subsampling as u32, info.y_registration),
            ) {
                (Err(error), _, _, _, _, _) => Err(error),
                (_, Err(error), _, _, _, _) => Err(error),
                (_, _, Err(error), _, _, _) => Err(error),
                (_, _, _, Err(error), _, _) => Err(error),
                (_, _, _, _, Err(error), _) => Err(error),
                (_, _, _, _, _, Err(error)) => Err(error),
                (Ok(image_x0), Ok(image_y0), Ok(x0), Ok(y0), Ok(x1), Ok(y1)) => {
                    if x0 >= x1 || y0 >= y1 || x0 < image_x0 || y0 < image_y0 {
                        Err(part1_image_error(false))
                    } else {
                        Ok(crate::codestream::TileComponentBounds {
                            tile_index, component, x0, y0, x1, y1,
                            image_x: (x0 - image_x0) as u32,
                            image_y: (y0 - image_y0) as u32,
                        })
                    }
                },
            },
        },
    }
}

pub open spec fn part2_registered_decode_ceil(value: u32, divisor: u32, registration: u16)
    -> Result<u32, crate::DecodeError>
{
    if divisor == 0 { Err(part1_block_placement_error(false)) }
    else { part2_registered_component_ceil(value, divisor, registration) }
}

pub open spec fn part1_image_size_component(
    components: u16, information: Seq<crate::codestream::ComponentInfo>, index: u16,
) -> Result<crate::codestream::ComponentInfo, crate::DecodeError> {
    if index >= components || index >= information.len() {
        Err(part1_image_error(false))
    } else {
        Ok(information[index as int])
    }
}

pub open spec fn part1_image_checked_u32(value: int) -> Result<u32, crate::DecodeError> {
    if value < 0 || value > u32::MAX { Err(part1_image_error(true)) } else { Ok(value as u32) }
}

pub open spec fn part1_image_ceil_div(value: u32, divisor: u32) -> Result<u32, crate::DecodeError> {
    if divisor == 0 { Err(part1_image_error(false)) }
    else { Ok(part1_ceil_div(value as nat, divisor as nat) as u32) }
}

pub open spec fn part1_assembly_registered_ceil(value: u32, divisor: u32, registration: u16)
    -> Result<u32, crate::DecodeError>
{
    if divisor == 0 { Err(part1_image_error(false)) }
    else { color_registered_coordinate(value, divisor, registration, true) }
}

pub open spec fn part1_accumulate_decoded_bytes(samples: nat, before: u64, maximum: u64)
    -> (Result<(), crate::DecodeError>, u64)
{
    let bytes = samples * 8;
    if bytes > u64::MAX || before as nat + bytes > u64::MAX {
        (Err(part1_image_error(true)), before)
    } else {
        let next = (before as nat + bytes) as u64;
        if next > maximum {
            (Err(crate::DecodeError::LimitExceeded {
                resource: crate::Resource::DecodedBytes, limit: maximum, actual: next,
            }), next)
        } else { (Ok(()), next) }
    }
}

pub open spec fn part1_assembly_write_indices(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, destination: usize, source: usize,
) -> Part1AssemblyPlaneState {
    if destination >= plane.3.len() || destination >= plane.4.len()
        || source >= tile.6.len() || plane.4[destination as int] {
        (Err(part1_image_error(false)), plane)
    } else {
        (Ok(()), (plane.0, plane.1, plane.2,
            plane.3.update(destination as int, tile.6[source as int]), plane.4.update(destination as int, true)))
    }
}

pub open spec fn part1_assembly_pixel(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, x: u32, y: u32, crop: Option<(u32, u32)>,
) -> Part1AssemblyPlaneState {
    let destination_x = match crop {
        Some(origin) => part1_image_checked_u32((x as int) - origin.0),
        None => part1_image_checked_u32((tile.1 as int) + x),
    };
    let destination_y = match crop {
        Some(origin) => part1_image_checked_u32((y as int) - origin.1),
        None => part1_image_checked_u32((tile.2 as int) + y),
    };
    match destination_x {
        Err(error) => (Err(error), plane),
        Ok(dx) => match destination_y {
            Err(error) => (Err(error), plane),
            Ok(dy) => match part1_transform_offset(dy, plane.0, dx) {
                Err(error) => (Err(error), plane),
                Ok(destination) => {
                    let source_x = match crop {
                        Some(_) => part1_image_checked_u32((x as int) - tile.1),
                        None => Ok(x),
                    };
                    let source_y = match crop {
                        Some(_) => part1_image_checked_u32((y as int) - tile.2),
                        None => Ok(y),
                    };
                    match source_x {
                        Err(error) => (Err(error), plane),
                        Ok(sx) => match source_y {
                            Err(error) => (Err(error), plane),
                            Ok(sy) => match part1_transform_offset(sy, tile.3, sx) {
                                Err(error) => (Err(error), plane),
                                Ok(source) => part1_assembly_write_indices(plane, tile, destination, source),
                            },
                        },
                    }
                },
            },
        },
    }
}

pub open spec fn part1_assembly_row_prefix(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, x_start: u32, y: u32,
    crop: Option<(u32, u32)>, completed: nat,
) -> Part1AssemblyPlaneState
    decreases completed,
{
    if completed == 0 { (Ok(()), plane) } else {
        let previous = part1_assembly_row_prefix(plane, tile, x_start, y, crop, (completed - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_assembly_pixel(previous.1, tile, (x_start as nat + completed - 1) as u32, y, crop),
        }
    }
}

pub open spec fn part1_assembly_rectangle_prefix(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, rectangle: (u32, u32, u32, u32),
    crop: Option<(u32, u32)>, completed: nat,
) -> Part1AssemblyPlaneState
    decreases completed,
{
    if completed == 0 { (Ok(()), plane) } else {
        let previous = part1_assembly_rectangle_prefix(plane, tile, rectangle, crop, (completed - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_assembly_row_prefix(
                previous.1, tile, rectangle.0, (rectangle.1 as nat + completed - 1) as u32, crop,
                (rectangle.2 as nat - rectangle.0 as nat) as nat,
            ),
        }
    }
}

pub open spec fn part1_assembly_rectangle(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, rectangle: (u32, u32, u32, u32),
    crop: Option<(u32, u32)>,
) -> Part1AssemblyPlaneState {
    if rectangle.0 >= rectangle.2 || rectangle.1 >= rectangle.3 {
        (Ok(()), plane)
    } else {
        part1_assembly_rectangle_prefix(plane, tile, rectangle, crop, (rectangle.3 - rectangle.1) as nat)
    }
}

pub open spec fn part1_validate_assembly_tile(plane: Part1AssemblyPlane, tile: Part1AssemblyTile)
    -> Result<(), crate::DecodeError>
{
    if tile.3 == 0 || tile.4 == 0 { Err(part1_image_error(false)) } else {
        match part1_image_checked_u32((tile.1 as int) + tile.3) {
            Err(error) => Err(error),
            Ok(x1) => if x1 > plane.0 { Err(part1_image_error(false)) } else {
                match part1_image_checked_u32((tile.2 as int) + tile.4) {
                    Err(error) => Err(error),
                    Ok(y1) => if y1 > plane.1 { Err(part1_image_error(false)) } else {
                        match part1_transform_area(tile.3, tile.4) {
                            Err(error) => Err(error),
                            Ok(count) => if tile.6.len() != count { Err(part1_image_error(false)) } else { Ok(()) },
                        }
                    },
                }
            },
        }
    }
}

pub open spec fn part1_place_assembly_tile(plane: Part1AssemblyPlane, tile: Part1AssemblyTile)
    -> Part1AssemblyPlaneState
{
    match part1_validate_assembly_tile(plane, tile) {
        Err(error) => (Err(error), plane),
        Ok(()) => part1_assembly_rectangle_prefix(plane, tile, (0, 0, tile.3, tile.4), None, tile.4 as nat),
    }
}

pub open spec fn part1_place_selected_tile(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, crop: (u32, u32, u32, u32),
) -> Part1AssemblyPlaneState {
    let x0 = if tile.1 > crop.0 { tile.1 } else { crop.0 };
    let y0 = if tile.2 > crop.1 { tile.2 } else { crop.1 };
    match part1_image_checked_u32((tile.1 as int) + tile.3) {
        Err(error) => (Err(error), plane),
        Ok(tile_x1) => match part1_image_checked_u32((tile.2 as int) + tile.4) {
            Err(error) => (Err(error), plane),
            Ok(tile_y1) => {
                let x1 = if tile_x1 < crop.2 { tile_x1 } else { crop.2 };
                let y1 = if tile_y1 < crop.3 { tile_y1 } else { crop.3 };
                if x0 < x1 && y0 < y1 {
                    part1_assembly_rectangle_prefix(
                        plane, tile, (x0, y0, x1, y1), Some((crop.0, crop.1)), (y1 - y0) as nat,
                    )
                } else { (Ok(()), plane) }
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_assembly_tile_step(
    plane: Part1AssemblyPlane, tile: Part1AssemblyTile, component: u16, crop: Option<(u32, u32, u32, u32)>,
) -> Part1AssemblyPlaneState {
    if tile.0 != component {
        (Ok(()), plane)
    } else if plane.2.is_some() && plane.2 != Some(tile.5) {
        (Err(part1_image_error(false)), plane)
    } else {
        let changed = (plane.0, plane.1, Some(tile.5), plane.3, plane.4);
        match crop {
            None => part1_place_assembly_tile(changed, tile),
            Some(region) => part1_place_selected_tile(changed, tile, region),
        }
    }
}

#[verifier::opaque]
pub open spec fn part1_assembly_tiles_prefix(
    plane: Part1AssemblyPlane, tiles: Seq<Part1AssemblyTile>, component: u16,
    crop: Option<(u32, u32, u32, u32)>, completed: nat,
) -> Part1AssemblyPlaneState
    decreases completed,
{
    if completed == 0 { (Ok(()), plane) } else {
        let previous = part1_assembly_tiles_prefix(plane, tiles, component, crop, (completed - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_assembly_tile_step(previous.1, tiles[completed - 1], component, crop),
        }
    }
}

pub open spec fn part1_assembly_coverage_error(selected: bool) -> crate::DecodeError {
    if selected {
        crate::DecodeError::InvalidSelection { reason: crate::SelectionError::RegionOutsideSelectedTiles }
    } else { part1_image_error(false) }
}

pub open spec fn part1_collect_assembly_tiles(
    plane: Part1AssemblyPlane, tiles: Seq<Part1AssemblyTile>, component: u16,
    crop: Option<(u32, u32, u32, u32)>,
) -> Part1AssemblyPlaneState {
    let result = part1_assembly_tiles_prefix(plane, tiles, component, crop, tiles.len());
    match result.0 {
        Err(_) => result,
        Ok(()) => if result.1.2.is_none() || !(forall |i: int| 0 <= i < result.1.4.len() ==> result.1.4[i]) {
            (Err(part1_assembly_coverage_error(crop.is_some())), result.1)
        } else { result },
    }
}

pub open spec fn part1_assembly_base_dimensions(
    size: Part1AssemblySize, info: crate::codestream::ComponentInfo, extent: (u32, u32),
) -> Result<Part1AssemblyDimensions, crate::DecodeError> {
    match part1_assembly_registered_ceil(extent.0, info.x_subsampling as u32, info.x_registration) {
        Err(error) => Err(error),
        Ok(x1) => match part1_assembly_registered_ceil(size.2, info.x_subsampling as u32, info.x_registration) {
            Err(error) => Err(error),
            Ok(x0) => match part1_image_checked_u32((x1 as int) - x0) {
                Err(error) => Err(error),
                Ok(width) => match part1_assembly_registered_ceil(extent.1, info.y_subsampling as u32, info.y_registration) {
                    Err(error) => Err(error),
                    Ok(y1) => match part1_assembly_registered_ceil(size.3, info.y_subsampling as u32, info.y_registration) {
                        Err(error) => Err(error),
                        Ok(y0) => match part1_image_checked_u32((y1 as int) - y0) {
                            Err(error) => Err(error),
                            Ok(height) => Ok((info, width, height, info.x_subsampling as u32, info.y_subsampling as u32, x0, y0)),
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn part1_assembly_selected_dimensions(
    info: crate::codestream::ComponentInfo, region: [u32; 4], scale: u32,
) -> Result<Part1AssemblyDimensions, crate::DecodeError> {
    match part1_image_checked_u32((info.x_subsampling as int) * (scale as int)) {
        Err(error) => Err(error),
        Ok(x_step) => match part1_image_checked_u32((info.y_subsampling as int) * (scale as int)) {
            Err(error) => Err(error),
            Ok(y_step) => match part1_assembly_registered_ceil(region[0], x_step, info.x_registration) {
                Err(error) => Err(error),
                Ok(x0) => match part1_assembly_registered_ceil(region[1], y_step, info.y_registration) {
                    Err(error) => Err(error),
                    Ok(y0) => match part1_assembly_registered_ceil(region[2], x_step, info.x_registration) {
                        Err(error) => Err(error),
                        Ok(x1) => match part1_image_checked_u32((x1 as int) - x0) {
                            Err(error) => Err(error),
                            Ok(width) => match part1_assembly_registered_ceil(region[3], y_step, info.y_registration) {
                                Err(error) => Err(error),
                                Ok(y1) => match part1_image_checked_u32((y1 as int) - y0) {
                                    Err(error) => Err(error),
                                    Ok(height) => if width == 0 || height == 0 {
                                        Err(crate::DecodeError::InvalidSelection { reason: crate::SelectionError::EmptyComponentIntersection })
                                    } else { Ok((info, width, height, x_step, y_step, x0, y0)) },
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn part1_assembly_component_dimensions(
    size: Part1AssemblySize, component: u16, extent: (u32, u32), selection: Part1AssemblySelection,
) -> Result<Part1AssemblyDimensions, crate::DecodeError> {
    match part1_image_size_component(size.4, size.5, component) {
        Err(error) => Err(error),
        Ok(info) => match selection {
            None => part1_assembly_base_dimensions(size, info, extent),
            Some((region, scale)) => part1_assembly_selected_dimensions(info, region, scale),
        },
    }
}

pub open spec fn part1_assembly_component_crop(
    size: Part1AssemblySize, dimensions: Part1AssemblyDimensions, selected: bool,
) -> Result<Option<(u32, u32, u32, u32)>, crate::DecodeError> {
    if !selected { Ok(None) } else {
        match part1_assembly_registered_ceil(size.2, dimensions.3, dimensions.0.x_registration) {
            Err(error) => Err(error),
            Ok(full_x0) => match part1_image_checked_u32((dimensions.5 as int) - full_x0) {
                Err(error) => Err(error),
                Ok(x0) => match part1_assembly_registered_ceil(size.3, dimensions.4, dimensions.0.y_registration) {
                    Err(error) => Err(error),
                    Ok(full_y0) => match part1_image_checked_u32((dimensions.6 as int) - full_y0) {
                        Err(error) => Err(error),
                        Ok(y0) => match part1_image_checked_u32((x0 as int) + dimensions.1) {
                            Err(error) => Err(error),
                            Ok(x1) => match part1_image_checked_u32((y0 as int) + dimensions.2) {
                                Err(error) => Err(error),
                                Ok(y1) => Ok(Some((x0, y0, x1, y1))),
                            },
                        },
                    },
                },
            },
        }
    }
}

pub open spec fn part1_assembly_append_plane(
    image: Part1DecodedImageModel, bytes: u64, size: Part1AssemblySize, tiles: Seq<Part1AssemblyTile>,
    component: u16, extent: (u32, u32), selection: Part1AssemblySelection, maximum: u64,
) -> Part1AssemblyState {
    match part1_assembly_component_dimensions(size, component, extent, selection) {
        Err(error) => (Err(error), image, bytes),
        Ok(dimensions) => match part1_transform_area(dimensions.1, dimensions.2) {
            Err(error) => (Err(error), image, bytes),
            Ok(count) => {
                let charged = part1_accumulate_decoded_bytes(count as nat, bytes, maximum);
                match charged.0 {
                    Err(error) => (Err(error), image, charged.1),
                    Ok(()) => match part1_assembly_component_crop(size, dimensions, selection.is_some()) {
                        Err(error) => (Err(error), image, charged.1),
                        Ok(crop) => {
                            let initial = (dimensions.1, dimensions.2, None,
                                Seq::new(count as nat, |i: int| 0i64), Seq::new(count as nat, |i: int| false));
                            let collected = part1_collect_assembly_tiles(initial, tiles, component, crop);
                            match collected.0 {
                                Err(error) => (Err(error), image, charged.1),
                                Ok(()) => match collected.1.2 {
                                    None => (Err(part1_image_error(false)), image, charged.1),
                                    Some(fraction_bits) => (Ok(()),
                                        (image.0, image.1, image.2, image.3, image.4.push((
                                            dimensions.1, dimensions.2, dimensions.0, fraction_bits, collected.1.3,
                                        ))), charged.1),
                                },
                            }
                        },
                    },
                }
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part1_assembly_components_prefix(
    image: Part1DecodedImageModel, bytes: u64, size: Part1AssemblySize, tiles: Seq<Part1AssemblyTile>,
    extent: (u32, u32), selection: Part1AssemblySelection, maximum: u64, completed: nat,
) -> Part1AssemblyState
    decreases completed,
{
    if completed == 0 { (Ok(()), image, bytes) } else {
        let previous = part1_assembly_components_prefix(image, bytes, size, tiles, extent, selection, maximum, (completed - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_assembly_append_plane(previous.1, previous.2, size, tiles, (completed - 1) as u16, extent, selection, maximum),
        }
    }
}

pub open spec fn part1_assemble_image(size: Part1AssemblySize, tiles: Seq<Part1AssemblyTile>, maximum: u64)
    -> Result<Part1DecodedImageModel, crate::DecodeError>
{
    match part1_image_checked_u32((size.2 as int) + size.0) {
        Err(error) => Err(error),
        Ok(x1) => match part1_image_checked_u32((size.3 as int) + size.1) {
            Err(error) => Err(error),
            Ok(y1) => {
                let initial = (size.0, size.1, size.2, size.3, Seq::empty());
                let result = part1_assembly_components_prefix(initial, 0, size, tiles, (x1, y1), None, maximum, size.4 as nat);
                match result.0 { Err(error) => Err(error), Ok(()) => Ok(result.1) }
            },
        },
    }
}

pub open spec fn part1_assembly_selected_header(region: [u32; 4], discard: u8)
    -> Result<(u32, u32, u32, u32, u32), crate::DecodeError>
{
    if region[0] >= region[2] || region[1] >= region[3] || discard > 31 {
        Err(part1_image_error(false))
    } else {
        let scale = 1u32 << discard;
        match part1_image_ceil_div(region[0], scale) {
            Err(error) => Err(error),
            Ok(x0) => match part1_image_ceil_div(region[1], scale) {
                Err(error) => Err(error),
                Ok(y0) => match part1_image_ceil_div(region[2], scale) {
                    Err(error) => Err(error),
                    Ok(x1) => match part1_image_checked_u32((x1 as int) - x0) {
                        Err(error) => Err(error),
                        Ok(width) => match part1_image_ceil_div(region[3], scale) {
                            Err(error) => Err(error),
                            Ok(y1) => match part1_image_checked_u32((y1 as int) - y0) {
                                Err(error) => Err(error),
                                Ok(height) => if width == 0 || height == 0 { Err(part1_image_error(false)) }
                                    else { Ok((scale, x0, y0, width, height)) },
                            },
                        },
                    },
                },
            },
        }
    }
}

pub open spec fn part1_assemble_selected_image(
    size: Part1AssemblySize, tiles: Seq<Part1AssemblyTile>, region: [u32; 4], discard: u8, maximum: u64,
) -> Result<Part1DecodedImageModel, crate::DecodeError> {
    match part1_assembly_selected_header(region, discard) {
        Err(error) => Err(error),
        Ok(header) => {
            let initial = (header.3, header.4, header.1, header.2, Seq::empty());
            let result = part1_assembly_components_prefix(initial, 0, size, tiles, (0, 0), Some((region, header.0)), maximum, size.4 as nat);
            match result.0 { Err(error) => Err(error), Ok(()) => Ok(result.1) }
        },
    }
}

pub open spec fn part1_selector_error(arithmetic: bool) -> crate::DecodeError {
    crate::DecodeError::MalformedInput {
        offset: 0,
        kind: if arithmetic { crate::MalformedKind::ArithmeticOverflow }
            else { crate::MalformedKind::InvalidCodingStyle },
    }
}

pub open spec fn part1_decomposition_direction(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, stage: u8,
) -> Result<crate::codestream::DecompositionDirection, crate::DecodeError> {
    if stage >= levels || stage >= directions.len() {
        Err(part1_selector_error(false))
    } else {
        Ok(directions[stage as int])
    }
}

pub open spec fn part1_direction_for_resolution(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, resolution: u8,
) -> Result<crate::codestream::DecompositionDirection, crate::DecodeError> {
    if resolution == 0 || resolution > levels {
        Err(part1_selector_error(false))
    } else {
        part1_decomposition_direction(levels, directions, (levels - resolution) as u8)
    }
}

pub open spec fn part1_direction_detail_count(direction: crate::codestream::DecompositionDirection) -> nat {
    match direction {
        crate::codestream::DecompositionDirection::None => 0,
        crate::codestream::DecompositionDirection::Horizontal => 1,
        crate::codestream::DecompositionDirection::Vertical => 1,
        crate::codestream::DecompositionDirection::TwoDimensional => 3,
    }
}

pub open spec fn part2_resolution_scale_step(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, stage: u8,
    before: (u32, u32),
) -> Result<(u32, u32), crate::DecodeError> {
    match part1_decomposition_direction(levels, directions, stage) {
        Err(error) => Err(error),
        Ok(direction) => match direction {
            crate::codestream::DecompositionDirection::None => Ok(before),
            crate::codestream::DecompositionDirection::Horizontal => {
                match part1_image_checked_u32(before.0 as int * 2) {
                    Err(error) => Err(error), Ok(horizontal) => Ok((horizontal, before.1)),
                }
            },
            crate::codestream::DecompositionDirection::Vertical => {
                match part1_image_checked_u32(before.1 as int * 2) {
                    Err(error) => Err(error), Ok(vertical) => Ok((before.0, vertical)),
                }
            },
            crate::codestream::DecompositionDirection::TwoDimensional => {
                match part1_image_checked_u32(before.0 as int * 2) {
                    Err(error) => Err(error),
                    Ok(horizontal) => match part1_image_checked_u32(before.1 as int * 2) {
                        Err(error) => Err(error), Ok(vertical) => Ok((horizontal, vertical)),
                    },
                }
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_resolution_scale_prefix(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, completed: nat,
) -> Result<(u32, u32), crate::DecodeError>
    decreases completed,
{
    if completed == 0 { Ok((1, 1)) } else {
        match part2_resolution_scale_prefix(levels, directions, (completed - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => part2_resolution_scale_step(levels, directions, (completed - 1) as u8, previous),
        }
    }
}

pub open spec fn part2_resolution_downsampling(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, resolution: u8,
) -> Result<(u32, u32), crate::DecodeError> {
    if resolution > levels { Err(part1_selector_error(false)) }
    else { part2_resolution_scale_prefix(levels, directions, (levels - resolution) as nat) }
}

pub open spec fn part2_precinct_exponents(
    levels: u8, exponents: Seq<(u8, u8)>, resolution: u8,
) -> Result<(u8, u8), crate::DecodeError> {
    if resolution > levels || resolution as nat >= exponents.len() {
        Err(part1_selector_error(false))
    } else { Ok(exponents[resolution as int]) }
}

pub open spec fn part1_subband_count_prefix(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, completed: nat,
) -> Result<usize, crate::DecodeError>
    decreases completed,
{
    if completed == 0 {
        Ok(1)
    } else {
        match part1_subband_count_prefix(levels, directions, (completed - 1) as nat) {
            Err(error) => Err(error),
            Ok(previous) => match part1_direction_for_resolution(levels, directions, completed as u8) {
                Err(error) => Err(error),
                Ok(direction) => {
                    let next = previous as nat + part1_direction_detail_count(direction);
                    if next > usize::MAX || completed as u8 == u8::MAX {
                        Err(part1_selector_error(true))
                    } else {
                        Ok(next as usize)
                    }
                },
            },
        }
    }
}

pub open spec fn part1_subband_count_through_resolution(
    levels: u8, directions: Seq<crate::codestream::DecompositionDirection>, resolution: u8,
) -> Result<usize, crate::DecodeError> {
    if resolution > levels {
        Err(part1_selector_error(false))
    } else {
        part1_subband_count_prefix(levels, directions, resolution as nat)
    }
}

pub open spec fn part1_decoded_component_sample(
    image: Part1DecodedImageModel, component: usize, index: usize,
) -> Result<i64, crate::DecodeError> {
    if component >= image.4.len() {
        Err(part1_image_error(false))
    } else if index >= image.4[component as int].4.len() {
        Err(part1_image_error(false))
    } else {
        Ok(image.4[component as int].4[index as int])
    }
}

pub open spec fn part1_set_decoded_component_sample(
    image: Part1DecodedImageModel, component: usize, index: usize, value: i64,
) -> Part1DecodedImageState {
    if component >= image.4.len() {
        (Err(part1_image_error(false)), image)
    } else {
        let original = image.4[component as int];
        if index >= original.4.len() {
            (Err(part1_image_error(false)), image)
        } else {
            let changed = (original.0, original.1, original.2, original.3, original.4.update(index as int, value));
            (Ok(()), (image.0, image.1, image.2, image.3, image.4.update(component as int, changed)))
        }
    }
}

pub open spec fn part1_component_transform_compatible(
    first: Part1DecodedComponentModel, component: Part1DecodedComponentModel, fraction_bits: u8,
) -> bool {
    component.0 == first.0 && component.1 == first.1 && component.3 == fraction_bits
        && component.2.x_subsampling == first.2.x_subsampling
        && component.2.y_subsampling == first.2.y_subsampling
}

pub open spec fn part1_validate_transform_components(
    image: Part1DecodedImageModel, fraction_bits: u8,
) -> Result<(), crate::DecodeError> {
    if image.4.len() >= 3 && forall |i: int| 0 <= i < 3 ==>
        part1_component_transform_compatible(image.4[0], image.4[i], fraction_bits)
    {
        Ok(())
    } else {
        Err(part1_image_error(false))
    }
}

pub open spec fn part1_reversible_component_values(y: i64, cb: i64, cr: i64)
    -> Result<(i64, i64, i64), crate::DecodeError>
{
    match part1_checked_sample((cb as int) + (cr as int)) {
        Err(error) => Err(error),
        Ok(sum) => match part1_checked_sample((y as int) - ((sum >> 2) as int)) {
            Err(error) => Err(error),
            Ok(green) => match part1_checked_sample((green as int) + (cr as int)) {
                Err(error) => Err(error),
                Ok(red) => match part1_checked_sample((green as int) + (cb as int)) {
                    Err(error) => Err(error),
                    Ok(blue) => Ok((red, green, blue)),
                },
            },
        },
    }
}

pub open spec fn part1_irreversible_component_values(y: i64, cb: i64, cr: i64)
    -> Result<(i64, i64, i64), crate::DecodeError>
{
    match part1_fixed_product(cr, 91881) {
        Err(error) => Err(error),
        Ok(red_delta) => match part1_checked_sample((y as int) + (red_delta as int)) {
            Err(error) => Err(error),
            Ok(red) => match part1_fixed_product(cb, 22553) {
                Err(error) => Err(error),
                Ok(green_cb) => match part1_checked_sample((y as int) - (green_cb as int)) {
                    Err(error) => Err(error),
                    Ok(green_first) => match part1_fixed_product(cr, 46797) {
                        Err(error) => Err(error),
                        Ok(green_cr) => match part1_checked_sample((green_first as int) - (green_cr as int)) {
                            Err(error) => Err(error),
                            Ok(green) => match part1_fixed_product(cb, 116130) {
                                Err(error) => Err(error),
                                Ok(blue_delta) => match part1_checked_sample((y as int) + (blue_delta as int)) {
                                    Err(error) => Err(error),
                                    Ok(blue) => Ok((red, green, blue)),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

pub open spec fn part1_component_values(y: i64, cb: i64, cr: i64, irreversible: bool)
    -> Result<(i64, i64, i64), crate::DecodeError>
{
    if irreversible { part1_irreversible_component_values(y, cb, cr) }
    else { part1_reversible_component_values(y, cb, cr) }
}

pub open spec fn part1_component_pixel_state(
    image: Part1DecodedImageModel, index: usize, irreversible: bool,
) -> Part1DecodedImageState {
    match part1_decoded_component_sample(image, 0, index) {
        Err(error) => (Err(error), image),
        Ok(y) => match part1_decoded_component_sample(image, 1, index) {
            Err(error) => (Err(error), image),
            Ok(cb) => match part1_decoded_component_sample(image, 2, index) {
                Err(error) => (Err(error), image),
                Ok(cr) => match part1_component_values(y, cb, cr, irreversible) {
                    Err(error) => (Err(error), image),
                    Ok((red, green, blue)) => {
                        let red_state = part1_set_decoded_component_sample(image, 0, index, red);
                        match red_state.0 {
                            Err(_) => red_state,
                            Ok(()) => {
                                let green_state = part1_set_decoded_component_sample(red_state.1, 1, index, green);
                                match green_state.0 {
                                    Err(_) => green_state,
                                    Ok(()) => part1_set_decoded_component_sample(green_state.1, 2, index, blue),
                                }
                            },
                        }
                    },
                },
            },
        },
    }
}

pub open spec fn part1_component_transform_prefix(
    image: Part1DecodedImageModel, irreversible: bool, count: nat,
) -> Part1DecodedImageState
    decreases count,
{
    if count == 0 {
        (Ok(()), image)
    } else {
        let previous = part1_component_transform_prefix(image, irreversible, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_component_pixel_state(previous.1, (count - 1) as usize, irreversible),
        }
    }
}

pub open spec fn part1_apply_component_transform(
    image: Part1DecodedImageModel, irreversible: bool,
) -> Part1DecodedImageState {
    match part1_validate_transform_components(image, if irreversible { 16u8 } else { 0u8 }) {
        Err(error) => (Err(error), image),
        Ok(()) => if image.4.len() < 3
            || image.4[1].4.len() != image.4[0].4.len()
            || image.4[2].4.len() != image.4[0].4.len()
        {
            (Err(part1_image_error(false)), image)
        } else {
            part1_component_transform_prefix(image, irreversible, image.4[0].4.len())
        },
    }
}

pub open spec fn part1_component_transform_frame(
    before: Part1DecodedImageModel, after: Part1DecodedImageModel,
) -> bool {
    before.0 == after.0 && before.1 == after.1 && before.2 == after.2 && before.3 == after.3
        && before.4.len() == after.4.len()
        && forall |i: int| 0 <= i < before.4.len() ==>
            before.4[i].0 == after.4[i].0
                && before.4[i].1 == after.4[i].1
                && before.4[i].2 == after.4[i].2
                && before.4[i].3 == after.4[i].3
                && before.4[i].4.len() == after.4[i].4.len()
                && (i >= 3 ==> before.4[i] == after.4[i])
}

pub open spec fn part1_block_placement_error(arithmetic: bool) -> crate::DecodeError {
    crate::DecodeError::MalformedInput {
        offset: 0,
        kind: if arithmetic { crate::MalformedKind::ArithmeticOverflow }
            else { crate::MalformedKind::InvalidCodeBlock },
    }
}

pub open spec fn part1_quantized_block_pixel(
    band: Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, x: u32, y: u32,
) -> Part1WorkingSubbandState {
    let destination_x = (placement_x as int) + (x as int);
    let destination_y = (placement_y as int) + (y as int);
    if destination_x > u32::MAX || destination_y > u32::MAX {
        (Err(part1_block_placement_error(true)), band)
    } else {
        match part1_transform_offset(destination_y as u32, band.0, destination_x as u32) {
            Err(error) => (Err(error), band),
            Ok(destination) => match part1_transform_offset(y, block_width, x) {
                Err(error) => (Err(error), band),
                Ok(input) => if destination >= band.3.len() || destination >= band.4.len()
                    || input >= source.len() || band.4[destination as int]
                {
                    (Err(part1_block_placement_error(false)), band)
                } else {
                    (Ok(()), (band.0, band.1, band.2,
                        band.3.update(destination as int, source[input as int]),
                        band.4.update(destination as int, true)))
                },
            },
        }
    }
}

pub open spec fn part1_quantized_block_row(
    band: Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, y: u32, count: nat,
) -> Part1WorkingSubbandState
    decreases count,
{
    if count == 0 {
        (Ok(()), band)
    } else {
        let previous = part1_quantized_block_row(band, source, block_width, placement_x, placement_y, y, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_quantized_block_pixel(previous.1, source, block_width, placement_x, placement_y, (count - 1) as u32, y),
        }
    }
}

pub open spec fn part1_quantized_block_rows(
    band: Part1WorkingSubbandModel, source: Seq<i64>, block_width: u32,
    placement_x: u32, placement_y: u32, count: nat,
) -> Part1WorkingSubbandState
    decreases count,
{
    if count == 0 {
        (Ok(()), band)
    } else {
        let previous = part1_quantized_block_rows(band, source, block_width, placement_x, placement_y, (count - 1) as nat);
        match previous.0 {
            Err(_) => previous,
            Ok(()) => part1_quantized_block_row(previous.1, source, block_width, placement_x, placement_y, (count - 1) as u32, block_width as nat),
        }
    }
}

pub open spec fn part1_working_subband_frame(
    before: Part1WorkingSubbandModel, after: Part1WorkingSubbandModel,
) -> bool {
    before.0 == after.0 && before.1 == after.1 && before.2 == after.2
        && before.3.len() == after.3.len() && before.4.len() == after.4.len()
        && (forall |i: int| 0 <= i < before.4.len() && before.4[i] ==> after.4[i])
        && (forall |i: int| 0 <= i < before.4.len() && i < before.3.len() && before.4[i] ==>
            before.3[i] == after.3[i])
}

}
