//! Input-derived uniform geometry count production and its public cold Result.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_uniform_geometry_counts(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,resolutions:u8,
    limits:&crate::ResourceLimits,tile:Option<u16>,component:u16,counts:Seq<u32>,total:u64)->Result<(Seq<u32>,u64),crate::DecodeError>
    decreases if component<size.components {(size.components-component) as nat}else{0nat},1nat,0nat,
{
    if component>=size.components {Ok((counts,total))}else{
        part2_uniform_geometry_resolutions(size,style,resolutions,limits,tile,component,0,counts,total)
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_uniform_geometry_resolutions(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,resolutions:u8,
    limits:&crate::ResourceLimits,tile:Option<u16>,component:u16,resolution:u8,counts:Seq<u32>,total:u64)->Result<(Seq<u32>,u64),crate::DecodeError>
    decreases if component<size.components {(size.components-component) as nat}else{0nat},0nat,if resolution<resolutions{(resolutions-resolution) as nat}else{0nat},
{
    if component>=size.components {Err(part1_block_placement_error(false))}
    else if resolution>=resolutions {part2_uniform_geometry_counts(size,style,resolutions,limits,tile,(component+1) as u16,counts,total)}
    else{
        match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),crate::codestream::image_size_component_count(size),
            crate::codestream::image_size_component_infos(size),crate::decode::resolution_geometry_style(style),component,resolution,tile) {
            Err(error)=>Err(error),
            Ok(geometry)=>match part2_packet_grid_subband_delta(style,resolution) {
                Err(error)=>Err(error),
                Ok(subbands)=>match part2_packet_grid_codeblocks(total,geometry.code_blocks,true,limits) {
                    Err(error)=>Err(error),
                    Ok(next)=>if subbands!=0 && geometry.precincts>u32::MAX || resolution==u8::MAX {Err(part1_block_placement_error(true))}
                    else{part2_uniform_geometry_resolutions(size,style,resolutions,limits,tile,component,(resolution+1) as u8,
                        counts.push(if subbands==0{0u32}else{geometry.precincts as u32}),next)},
                },
            },
        }
    }
}
pub(crate) proof fn part2_uniform_geometry_step(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,resolutions:u8,
    limits:&crate::ResourceLimits,tile:Option<u16>,component:u16,resolution:u8,counts:Seq<u32>,total:u64)
    requires component<size.components,resolution<resolutions,
    ensures part2_uniform_geometry_resolutions(size,style,resolutions,limits,tile,component,resolution,counts,total)
        ==match part2_geometry_counts_step(size,style,limits,tile,component,resolution,resolutions,0,counts,total) {
            Err(error)=>Err(error),Ok((after,next))=>part2_uniform_geometry_resolutions(size,style,resolutions,limits,tile,component,(resolution+1) as u8,after,next),
        },
{
    reveal(part2_geometry_counts_step);
    reveal_with_fuel(part2_uniform_geometry_resolutions,2);reveal_with_fuel(part2_uniform_geometry_counts,1);
}
#[verifier::opaque]
pub(crate) open spec fn part2_uniform_geometry_value(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>)->Result<Part1PacketGrid,crate::DecodeError> {
    if style.decomposition_levels==u8::MAX || size.components as nat*(style.decomposition_levels as nat+1)>usize::MAX {
        Err(part1_block_placement_error(true))
    }else{
        let resolutions=(style.decomposition_levels+1) as u8;
        match part2_uniform_geometry_counts(size,style,resolutions,limits,tile,0,Seq::empty(),0) {
            Err(error)=>Err(error),Ok((counts,_))=>part1_uniform_grid_model(style.layers,size.components,resolutions,counts,limits),
        }
    }
}
pub(crate) open spec fn part2_uniform_geometry_after_capacity(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid> {
    match part2_uniform_geometry_counts(size,style,(style.decomposition_levels+1) as u8,limits,tile,0,Seq::empty(),0) {
        Err(error)=>Some((Err(error),events)),
        Ok((counts,_))=>part2_uniform_grid_run(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits,events),
    }
}
pub(crate) open spec fn part2_uniform_geometry_run(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid> {
    if style.decomposition_levels==u8::MAX || size.components as nat*(style.decomposition_levels as nat+1)>usize::MAX {
        Some((Err(part1_block_placement_error(true)),events))
    }else{
        part2_jpip_snapshot_bind(part2_geometry_capacity_run(Part2GeometryCapacityContext::UniformCounts {size:*size,style,tile},events),
            |_:(),rest|part2_uniform_geometry_after_capacity(size,style,limits,tile,rest))
    }
}
pub closed spec fn part1_uniform_geometry_cold_result(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,result:Result<Part1PacketGrid,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_uniform_geometry_run(size,style,limits,tile,events),result)
}
pub closed spec fn part1_uniform_geometry_model(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>)->Result<Part1PacketGrid,crate::DecodeError> {
    part2_uniform_geometry_value(size,style,limits,tile)
}
pub(crate) proof fn part2_uniform_geometry_result_framed(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,result:Result<Part1PacketGrid,crate::DecodeError>)
    requires part1_uniform_geometry_cold_result(size,style,limits,tile,result),
    ensures part2_cold_framed(|events|part2_uniform_geometry_run(size,style,limits,tile,events),result),
{}
pub(crate) proof fn part2_uniform_geometry_model_known(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>)
    ensures part1_uniform_geometry_model(size,style,limits,tile)==part2_uniform_geometry_value(size,style,limits,tile),
        (style.decomposition_levels==u8::MAX || size.components as nat*(style.decomposition_levels as nat+1)>usize::MAX)
            ==>part2_uniform_geometry_value(size,style,limits,tile)==Err(part1_block_placement_error(true)),
{reveal(part2_uniform_geometry_value);}
pub(crate) proof fn part2_uniform_geometry_value_known(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,resolutions:u8)
    requires style.decomposition_levels<u8::MAX,resolutions as int==style.decomposition_levels as int+1,
        size.components as nat*resolutions as nat<=usize::MAX,
    ensures part2_uniform_geometry_value(size,style,limits,tile)==match part2_uniform_geometry_counts(size,style,resolutions,limits,tile,0,Seq::empty(),0) {
        Err(error)=>Err(error),Ok((counts,_))=>part1_uniform_grid_model(style.layers,size.components,resolutions,counts,limits),
    },
{
    reveal(part2_uniform_geometry_value);
}
pub(crate) proof fn part2_uniform_geometry_normal(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>)
    ensures part1_uniform_geometry_cold_result(size,style,limits,tile,part2_uniform_geometry_value(size,style,limits,tile)),
{
    reveal(part2_geometry_capacity_result);reveal(part2_uniform_geometry_value);
    let result=part2_uniform_geometry_value(size,style,limits,tile);
    if style.decomposition_levels==u8::MAX || size.components as nat*(style.decomposition_levels as nat+1)>usize::MAX {part2_cold_pure::<Part1PacketGrid>(result);}else{
        let context=Part2GeometryCapacityContext::UniformCounts {size:*size,style,tile};
        part2_geometry_capacity_observed(context,Ok(()));
        match part2_uniform_geometry_counts(size,style,(style.decomposition_levels+1) as u8,limits,tile,0,Seq::empty(),0) {
            Err(_)=>{part2_cold_pure::<Part1PacketGrid>(result);},
            Ok((counts,_))=>{
                part2_uniform_grid_normal(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits);
                part2_uniform_grid_frames(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits,result);
                part2_decode_eta(|events|part2_uniform_grid_run(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits,events),result);
            },
        }
        part2_decode_eta(|events|part2_uniform_geometry_after_capacity(size,style,limits,tile,events),result);
        part2_cold_bind(|events|part2_geometry_capacity_run(context,events),|_:(),rest|part2_uniform_geometry_after_capacity(size,style,limits,tile,rest),Ok(()),result);
    }
}
pub(crate) proof fn part2_uniform_geometry_refused(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>)
    requires style.decomposition_levels<u8::MAX,size.components as nat*(style.decomposition_levels as nat+1)<=usize::MAX,
        part2_geometry_capacity_result(Part2GeometryCapacityContext::UniformCounts {size:*size,style,tile},Err(crate::DecodeError::AllocationFailed)),
    ensures part1_uniform_geometry_cold_result(size,style,limits,tile,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_geometry_capacity_result);
    part2_cold_bind(|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::UniformCounts {size:*size,style,tile},events),
        |_:(),rest|part2_uniform_geometry_after_capacity(size,style,limits,tile,rest),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_uniform_geometry_finish(size:&crate::codestream::ImageSize,style:crate::codestream::CodingStyle,
    limits:&crate::ResourceLimits,tile:Option<u16>,counts:Seq<u32>,total:u64,result:Result<Part1PacketGrid,crate::DecodeError>)
    requires style.decomposition_levels<u8::MAX,size.components as nat*(style.decomposition_levels as nat+1)<=usize::MAX,
        part2_uniform_geometry_counts(size,style,(style.decomposition_levels+1) as u8,limits,tile,0,Seq::empty(),0)==Ok((counts,total)),
        part2_geometry_capacity_result(Part2GeometryCapacityContext::UniformCounts {size:*size,style,tile},Ok(())),
        part1_uniform_grid_cold_result(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits,result),
    ensures part1_uniform_geometry_cold_result(size,style,limits,tile,result),
{
    reveal(part2_geometry_capacity_result);
    part2_uniform_grid_frames(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits,result);
    part2_decode_eta(|events|part2_uniform_grid_run(style.layers,size.components,(style.decomposition_levels+1) as u8,counts,limits,events),result);
    part2_cold_bind(|events|part2_geometry_capacity_run(Part2GeometryCapacityContext::UniformCounts {size:*size,style,tile},events),
        |_:(),rest|part2_uniform_geometry_after_capacity(size,style,limits,tile,rest),Ok(()),result);
}
}
