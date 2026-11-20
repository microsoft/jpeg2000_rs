//! Geometry count production followed by the actual fallible reference-position owner.
use super::*;
use vstd::prelude::*;

verus! {
pub open spec fn part2_spatial_uniform_grid_value(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>) -> Result<Part1PacketGrid,crate::DecodeError> {
    match part1_uniform_geometry_model(size,style,limits,tile) {
        Err(error)=>Err(error),
        Ok(grid)=>part2_packet_spatial_value(grid,size,
            part2_packet_spatial_uniform_styles(style),tile),
    }
}
pub(crate) open spec fn part2_spatial_uniform_grid_run(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,events:Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1PacketGrid> {
    part2_jpip_snapshot_bind(part2_uniform_geometry_run(size,style,limits,tile,events),
        |grid:Part1PacketGrid,rest|part2_packet_spatial_run(grid,size,
            part2_packet_spatial_uniform_styles(style),tile,rest))
}
pub closed spec fn part2_spatial_uniform_grid_result(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,result:Result<Part1PacketGrid,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_spatial_uniform_grid_run(size,style,limits,tile,events),result)
}
pub(crate) proof fn part2_spatial_uniform_actual(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,base:Result<Part1PacketGrid,crate::DecodeError>,result:Result<Part1PacketGrid,crate::DecodeError>)
    requires part1_uniform_geometry_cold_result(size,style,limits,tile,base),
        match base {
            Err(error)=>result==Err(error),
            Ok(grid)=>part2_packet_spatial_result(grid,size,
                crate::decode::spatial::packet_spatial_styles_view(crate::decode::spatial::PacketSpatialStyles::Uniform(style)),tile,result),
        },
    ensures part2_spatial_uniform_grid_result(size,style,limits,tile,result),
{
    part2_uniform_geometry_result_framed(size,style,limits,tile,base);
    crate::decode::spatial::packet_spatial_styles_known(crate::decode::spatial::PacketSpatialStyles::Uniform(style));
    reveal(part2_spatial_uniform_grid_result);reveal(part2_packet_spatial_result);
    let selectors=crate::decode::spatial::packet_spatial_styles_view(crate::decode::spatial::PacketSpatialStyles::Uniform(style));
    if let Ok(grid)=base {
        part2_decode_eta(|events|part2_packet_spatial_run(grid,size,selectors,tile,events),result);
    }
    part2_cold_bind(|events|part2_uniform_geometry_run(size,style,limits,tile,events),
        |grid:Part1PacketGrid,rest|part2_packet_spatial_run(grid,size,selectors,tile,rest),base,result);
}
pub(crate) proof fn part2_spatial_uniform_grid_normal(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>)
    ensures part2_spatial_uniform_grid_result(size,style,limits,tile,part2_spatial_uniform_grid_value(size,style,limits,tile)),
{
    part2_uniform_geometry_model_known(size,style,limits,tile);
    part2_uniform_geometry_normal(size,style,limits,tile);
    crate::decode::spatial::packet_spatial_styles_known(crate::decode::spatial::PacketSpatialStyles::Uniform(style));
    let base=part1_uniform_geometry_model(size,style,limits,tile);
    if let Ok(grid)=base {
        part2_packet_spatial_normal(grid,size,
            crate::decode::spatial::packet_spatial_styles_view(crate::decode::spatial::PacketSpatialStyles::Uniform(style)),tile);
    }
    part2_spatial_uniform_actual(size,style,limits,tile,base,part2_spatial_uniform_grid_value(size,style,limits,tile));
}

pub open spec fn part2_spatial_packet_grid_from_components(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8)->Result<Part1PacketGrid,crate::DecodeError> {
    match part2_packet_grid_from_components(size,styles,layers,limits,tile,discard) {
        Err(error)=>Err(error),
        Ok(grid)=>part2_packet_spatial_value(grid,size,
            part2_packet_spatial_component_styles(styles),tile),
    }
}
pub(crate) open spec fn part2_spatial_derived_grid_run(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,events:Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<Part1PacketGrid> {
    part2_jpip_snapshot_bind(part2_derived_grid_run(size,styles,layers,limits,tile,discard,events),
        |grid:Part1PacketGrid,rest|part2_packet_spatial_run(grid,size,
            part2_packet_spatial_component_styles(styles),tile,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_spatial_derived_grid_result(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,result:Result<Part1PacketGrid,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_spatial_derived_grid_run(size,styles,layers,limits,tile,discard,events),result)
}
pub(crate) proof fn part2_spatial_derived_actual(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,base:Result<Part1PacketGrid,crate::DecodeError>,result:Result<Part1PacketGrid,crate::DecodeError>)
    requires part2_derived_grid_result(size,styles,layers,limits,tile,discard,base),
        match base {
            Err(error)=>result==Err(error),
            Ok(grid)=>part2_packet_spatial_result(grid,size,
                crate::decode::spatial::packet_spatial_styles_view(crate::decode::spatial::PacketSpatialStyles::Components(styles)),tile,result),
        },
    ensures part2_spatial_derived_grid_result(size,styles,layers,limits,tile,discard,result),
{
    reveal(part2_derived_grid_result);reveal(part2_spatial_derived_grid_result);reveal(part2_packet_spatial_result);
    crate::decode::spatial::packet_spatial_styles_known(crate::decode::spatial::PacketSpatialStyles::Components(styles));
    let selectors=crate::decode::spatial::packet_spatial_styles_view(crate::decode::spatial::PacketSpatialStyles::Components(styles));
    if let Ok(grid)=base {
        part2_decode_eta(|events|part2_packet_spatial_run(grid,size,selectors,tile,events),result);
    }
    part2_cold_bind(|events|part2_derived_grid_run(size,styles,layers,limits,tile,discard,events),
        |grid:Part1PacketGrid,rest|part2_packet_spatial_run(grid,size,selectors,tile,rest),base,result);
}
pub(crate) proof fn part2_spatial_derived_grid_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8)
    ensures part2_spatial_derived_grid_result(size,styles,layers,limits,tile,discard,
        part2_spatial_packet_grid_from_components(size,styles,layers,limits,tile,discard)),
{
    part2_derived_grid_normal(size,styles,layers,limits,tile,discard);
    crate::decode::spatial::packet_spatial_styles_known(crate::decode::spatial::PacketSpatialStyles::Components(styles));
    let base=part2_packet_grid_from_components(size,styles,layers,limits,tile,discard);
    if let Ok(grid)=base {
        part2_packet_spatial_normal(grid,size,
            crate::decode::spatial::packet_spatial_styles_view(crate::decode::spatial::PacketSpatialStyles::Components(styles)),tile);
    }
    part2_spatial_derived_actual(size,styles,layers,limits,tile,discard,base,
        part2_spatial_packet_grid_from_components(size,styles,layers,limits,tile,discard));
}
}
