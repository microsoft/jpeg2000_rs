//! Actual geometry-to-grid construction, with the offset request at the final producer.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_grid_components_cold_run(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,
    component:u16,counts:Seq<u32>,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid>
    decreases if component<crate::codestream::image_size_component_count(size){(crate::codestream::image_size_component_count(size) as nat-component as nat) as nat}else{0nat},1nat,0nat,
{
    if component>=crate::codestream::image_size_component_count(size) {
        part2_grid_run(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,if discard==0{None}else{Some(descriptors.2)},limits,events)
    }else{
        match crate::codestream::component_coding_style_result(styles,component) {
            Err(error)=>Some((Err(error),events)),
            Ok(style)=>if style.decomposition_levels==u8::MAX {Some((Err(part1_block_placement_error(true)),events))}
                else{part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,
                    (style.decomposition_levels+1) as u8,0,counts,total,events)},
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_grid_resolutions_cold_run(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,
    component:u16,style:crate::codestream::CodingStyle,resolutions:u8,resolution:u8,counts:Seq<u32>,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid>
    decreases if component<crate::codestream::image_size_component_count(size){(crate::codestream::image_size_component_count(size) as nat-component as nat) as nat}else{0nat},
        0nat,if resolution<descriptors.0{(descriptors.0 as nat-resolution as nat) as nat}else{0nat},
{
    if component>=crate::codestream::image_size_component_count(size){Some((Err(part1_block_placement_error(false)),events))}
    else if resolution>=descriptors.0 {
        part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,(component+1) as u16,counts,total,events)
    }else if resolution>=resolutions {
        part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,counts.push(0),total,events)
    }else{
        match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),crate::codestream::image_size_component_count(size),
            crate::codestream::image_size_component_infos(size),crate::decode::resolution_geometry_style(style),component,resolution,tile) {
            Err(error)=>Some((Err(error),events)),
            Ok(geometry)=>match part2_packet_grid_subband_delta(style,resolution) {
                Err(error)=>Some((Err(error),events)),
                Ok(subbands)=>if discard>resolutions {Some((Err(crate::DecodeError::InvalidSelection {reason:crate::SelectionError::ReductionTooLarge}),events))}
                else{match part2_packet_grid_codeblocks(total,geometry.code_blocks,resolution<resolutions-discard,limits) {
                    Err(error)=>Some((Err(error),events)),
                    Ok(next)=>if subbands!=0 && geometry.precincts>u32::MAX {Some((Err(part1_block_placement_error(true)),events))}
                    else{part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,
                        (resolution+1) as u8,counts.push(if subbands==0{0u32}else{geometry.precincts as u32}),next,events)},
                }},
            },
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_derived_grid_run(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketGrid> {
    part2_jpip_snapshot_bind(part2_geometry_descriptors_run(crate::codestream::image_size_component_count(size),styles,discard,events),
        |descriptors:Part2ComponentResolutionCounts,rest|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,descriptors,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_derived_grid_result(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,result:Result<Part1PacketGrid,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_derived_grid_run(size,styles,layers,limits,tile,discard,events),result)
}
pub(crate) proof fn part2_grid_component_cold_start(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,component:u16,counts:Seq<u32>,total:u64,
    style:crate::codestream::CodingStyle,resolutions:u8,events:Seq<Part2JpipSnapshotEvent>)
    requires component<crate::codestream::image_size_component_count(size),
        crate::codestream::component_coding_style_result(styles,component)==Ok(style),
        style.decomposition_levels<u8::MAX,resolutions as int==style.decomposition_levels as int+1,
    ensures part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,events)
        ==part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,0,counts,total,events),
{
    reveal_with_fuel(part2_grid_components_cold_run,2);
    reveal_with_fuel(part2_grid_resolutions_cold_run,1);
    assert(resolutions==(style.decomposition_levels+1) as u8);
    assert(part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,events)
        ==match crate::codestream::component_coding_style_result(styles,component) {
            Err(error)=>Some((Err(error),events)),
            Ok(actual)=>if actual.decomposition_levels==u8::MAX {Some((Err(part1_block_placement_error(true)),events))}
                else{part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,actual,(actual.decomposition_levels+1) as u8,0,counts,total,events)},
        });
}
pub(crate) proof fn part2_grid_components_cold_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,component:u16,counts:Seq<u32>,total:u64)
    ->(calls:Seq<Part2JpipSnapshotEvent>)
    ensures part2_cold_framed(|events|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,events),
        part2_packet_grid_components_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total)),
        forall|tail| #[trigger] part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,calls+tail)
            ==Some((part2_packet_grid_components_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total),tail)),
    decreases if component<crate::codestream::image_size_component_count(size){(crate::codestream::image_size_component_count(size) as nat-component as nat) as nat}else{0nat},1nat,0nat,
{
    let result=part2_packet_grid_components_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total);
    let calls=if component>=crate::codestream::image_size_component_count(size){
        reveal(part2_grid_result);
        part2_grid_normal(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,if discard==0{None}else{Some(descriptors.2)},limits);
        reveal_with_fuel(part2_packet_grid_components_run,1);
        part2_cold_witness(|events|part2_grid_run(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,if discard==0{None}else{Some(descriptors.2)},limits,events),result)
    }else{
        match crate::codestream::component_coding_style_result(styles,component) {
            Err(error)=>Seq::empty(),
            Ok(style)=>if style.decomposition_levels==u8::MAX {Seq::empty()}
            else{
                part2_grid_resolutions_cold_normal(size,styles,layers,limits,tile,discard,descriptors,component,style,(style.decomposition_levels+1) as u8,0,counts,total)
            },
        }
    };
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,calls+tail)==Some((result,tail)) by {
        reveal_with_fuel(part2_grid_components_cold_run,2);reveal_with_fuel(part2_packet_grid_components_run,2);
        reveal_with_fuel(part2_grid_resolutions_cold_run,1);reveal_with_fuel(part2_packet_grid_resolutions_run,1);
        if component>=crate::codestream::image_size_component_count(size){
            part2_cold_prefix_at(|events|part2_grid_run(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,if discard==0{None}else{Some(descriptors.2)},limits,events),calls,result,tail);
            assert(part2_grid_run(layers,crate::codestream::image_size_component_count(size),descriptors.1,counts,if discard==0{None}else{Some(descriptors.2)},limits,calls+tail)==Some((result,tail)));
        }else if let Ok(style)=crate::codestream::component_coding_style_result(styles,component) {
            if style.decomposition_levels<u8::MAX {
                assert(part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,(style.decomposition_levels+1) as u8,0,counts,total,calls+tail)
                    ==Some((part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,discard,descriptors,component,style,(style.decomposition_levels+1) as u8,0,counts,total),tail)));
            }
        }
    }
    assert(part2_cold_prefix(|events|part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,counts,total,events),calls,result));
    calls
}
pub(crate) proof fn part2_grid_resolutions_cold_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    layers:u16,limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8,descriptors:Part2ComponentResolutionCounts,
    component:u16,style:crate::codestream::CodingStyle,resolutions:u8,resolution:u8,counts:Seq<u32>,total:u64)
    ->(calls:Seq<Part2JpipSnapshotEvent>)
    ensures part2_cold_framed(|events|part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total,events),
        part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total)),
        forall|tail| #[trigger] part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total,calls+tail)
            ==Some((part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total),tail)),
    decreases if component<crate::codestream::image_size_component_count(size){(crate::codestream::image_size_component_count(size) as nat-component as nat) as nat}else{0nat},
        0nat,if resolution<descriptors.0{(descriptors.0 as nat-resolution as nat) as nat}else{0nat},
{
    let result=part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total);
    let calls=if component>=crate::codestream::image_size_component_count(size){Seq::empty()}
    else if resolution>=descriptors.0{
        part2_grid_components_cold_normal(size,styles,layers,limits,tile,discard,descriptors,(component+1) as u16,counts,total)
    }else if resolution>=resolutions{
        part2_grid_resolutions_cold_normal(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,counts.push(0),total)
    }else{
        match part2_resolution_geometry(crate::codestream::selection_geometry_view(size),crate::codestream::image_size_component_count(size),
            crate::codestream::image_size_component_infos(size),crate::decode::resolution_geometry_style(style),component,resolution,tile) {
            Err(error)=>Seq::empty(),
            Ok(geometry)=>match part2_packet_grid_subband_delta(style,resolution) {
                Err(error)=>Seq::empty(),
                Ok(subbands)=>if discard>resolutions {Seq::empty()}
                else{match part2_packet_grid_codeblocks(total,geometry.code_blocks,resolution<resolutions-discard,limits) {
                    Err(error)=>Seq::empty(),
                    Ok(next)=>if subbands!=0 && geometry.precincts>u32::MAX {Seq::empty()}
                    else{
                        let updated=counts.push(if subbands==0{0u32}else{geometry.precincts as u32});
                        part2_grid_resolutions_cold_normal(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,updated,next)
                    },
                }},
            },
        }
    };
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total,calls+tail)==Some((result,tail)) by {
        reveal_with_fuel(part2_grid_resolutions_cold_run,2);reveal_with_fuel(part2_packet_grid_resolutions_run,2);
        reveal_with_fuel(part2_grid_components_cold_run,1);reveal_with_fuel(part2_packet_grid_components_run,1);
        if component<crate::codestream::image_size_component_count(size) && resolution>=descriptors.0 {
            assert(part2_grid_components_cold_run(size,styles,layers,limits,tile,discard,descriptors,(component+1) as u16,counts,total,calls+tail)
                ==Some((part2_packet_grid_components_run(size,styles,layers,limits,tile,discard,descriptors,(component+1) as u16,counts,total),tail)));
        }else if component<crate::codestream::image_size_component_count(size) && resolution>=resolutions {
            assert(part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,counts.push(0),total,calls+tail)
                ==Some((part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,counts.push(0),total),tail)));
        }else if component<crate::codestream::image_size_component_count(size) && resolution<descriptors.0 {
            if let Ok(geometry)=part2_resolution_geometry(crate::codestream::selection_geometry_view(size),crate::codestream::image_size_component_count(size),
                crate::codestream::image_size_component_infos(size),crate::decode::resolution_geometry_style(style),component,resolution,tile) {
                if let Ok(subbands)=part2_packet_grid_subband_delta(style,resolution) {
                    if discard<=resolutions {
                        if let Ok(next)=part2_packet_grid_codeblocks(total,geometry.code_blocks,resolution<resolutions-discard,limits) {
                            if subbands==0 || geometry.precincts<=u32::MAX {
                                let updated=counts.push(if subbands==0{0u32}else{geometry.precincts as u32});
                                assert(part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,updated,next,calls+tail)
                                    ==Some((part2_packet_grid_resolutions_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,(resolution+1) as u8,updated,next),tail)));
                            }
                        }
                    }
                }
            }
        }
    }
    assert(part2_cold_prefix(|events|part2_grid_resolutions_cold_run(size,styles,layers,limits,tile,discard,descriptors,component,style,resolutions,resolution,counts,total,events),calls,result));
    calls
}
pub(crate) proof fn part2_derived_grid_normal(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,layers:u16,
    limits:&crate::ResourceLimits,tile:Option<u16>,discard:u8)
    ensures part2_derived_grid_result(size,styles,layers,limits,tile,discard,part2_packet_grid_from_components(size,styles,layers,limits,tile,discard)),
{
    reveal(part2_derived_grid_result);reveal(part2_geometry_descriptors_result);reveal(part2_derived_grid_run);
    crate::codestream::selection_geometry_known_fields(size);
    part2_geometry_descriptors_normal(size.components,styles,discard);
    let descriptors=part2_component_resolution_counts(size.components,styles,discard);
    let result=part2_packet_grid_from_components(size,styles,layers,limits,tile,discard);
    if let Ok(values)=descriptors {
        part2_derived_geometry_after_normal(size,styles,layers,limits,tile,discard,values);
        part2_decode_eta(|events|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,values,events),result);
    }
    part2_cold_bind(|events|part2_geometry_descriptors_run(size.components,styles,discard,events),
        |values:Part2ComponentResolutionCounts,rest|part2_derived_geometry_after_descriptors(size,styles,layers,limits,tile,discard,values,rest),descriptors,result);
}
}
