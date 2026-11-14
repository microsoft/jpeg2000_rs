//! Ordered real resolution/precinct construction, preserving partial owners.
use super::*;
verus! {
pub(crate) proof fn part2_cold_bind_associative<A,B,C>(run:Part2ColdRun<A>,
    first:spec_fn(A,Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<B>,next:spec_fn(B,Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<C>)
    ensures part2_jpip_snapshot_bind(part2_jpip_snapshot_bind(run,first),next)
        ==part2_jpip_snapshot_bind(run,|value:A,rest|part2_jpip_snapshot_bind(first(value,rest),next)),
{}
pub(crate) open spec fn part2_component_after_precinct(before:Part2ComponentPlanBuffers,planned:Part2PlannedPrecinct)->Part2ComponentPlanBuffers {
    Part2ComponentPlanBuffers {precincts:before.precincts.push(planned.precinct),placements:planned.placements,planned_code_blocks:planned.planned_code_blocks}
}
#[verifier::opaque]
pub(crate) open spec fn part2_resolution_precincts_run(component:u16,resolution:u8,meta:Part2ComponentPlanMetadata,data:Part2ResolutionPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,precinct:nat,before:Part2ComponentPlanBuffers,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Part2ComponentPlanBuffers>
    decreases if precinct<data.precincts_in_resolution{(data.precincts_in_resolution as int-precinct) as nat}else{0nat},
{
    if precinct>=data.precincts_in_resolution{Some((Ok(before),events))}else{
        match part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct as u32,data.band_size) {
            Err(error)=>Some((Err(error),events)),
            Ok(origin)=>part2_jpip_snapshot_bind(part2_precinct_owner_run([origin[0],origin[1],data.band_size[0],data.band_size[1]],data.block_size,
                meta.subbands,(data.first_subband,data.subband_count),meta.tier1_style,(policy.0,policy.1),(component,resolution,precinct as u32,before.precincts.len() as usize),
                before.placements,before.planned_code_blocks,resolution<=meta.output_resolution,limits,events),
                |planned:Part2PlannedPrecinct,rest|part2_resolution_precincts_run(component,resolution,meta,data,policy,limits,precinct+1,part2_component_after_precinct(before,planned),rest)),
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_resolution_plan_run(size:&crate::codestream::ImageSize,component:u16,tile:u16,meta:Part2ComponentPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,resolution:nat,before:Part2ComponentPlanBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedComponent>
    decreases if resolution<=meta.coding_style.decomposition_levels{(meta.coding_style.decomposition_levels as int+1-resolution) as nat}else{0nat},
{
    if resolution>meta.coding_style.decomposition_levels {
        Some((part2_component_plan_resolutions(size,component,tile,meta,policy,limits,resolution,before),events))
    }else{
        match part2_resolution_plan_metadata(size,meta.coding_style,component,(tile,resolution as u8),[meta.bounds.x0,meta.bounds.y0]) {
            Err(error)=>Some((Err(error),events)),
            Ok(data)=>part2_jpip_snapshot_bind(part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,0,before,events),
                |after:Part2ComponentPlanBuffers,rest|if resolution==u8::MAX {Some((Err(part1_block_placement_error(true)),rest))}
                    else{part2_resolution_plan_run(size,component,tile,meta,policy,limits,resolution+1,after,rest)}),
        }
    }
}
pub(crate) proof fn part2_resolution_precincts_normal(component:u16,resolution:u8,meta:Part2ComponentPlanMetadata,data:Part2ResolutionPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,precinct:nat,before:Part2ComponentPlanBuffers)
    ensures part2_cold_framed(|events|part2_resolution_precincts_run(component,resolution,meta,data,policy,limits,precinct,before,events),
        part2_component_plan_precincts(component,resolution,meta,data,policy,limits,precinct,before)),
    decreases if precinct<data.precincts_in_resolution{(data.precincts_in_resolution as int-precinct) as nat}else{0nat},
{
    reveal_with_fuel(part2_resolution_precincts_run,1);reveal_with_fuel(part2_component_plan_precincts,1);reveal(part2_precinct_owner_result);
    let result=part2_component_plan_precincts(component,resolution,meta,data,policy,limits,precinct,before);
    if precinct>=data.precincts_in_resolution {part2_cold_pure::<Part2ComponentPlanBuffers>(result);}else{
        match part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct as u32,data.band_size) {
            Err(_)=>{part2_cold_pure::<Part2ComponentPlanBuffers>(result);},
            Ok(origin)=>{
                let band=[origin[0],origin[1],data.band_size[0],data.band_size[1]];
                let range=(data.first_subband,data.subband_count);
                let location=(component,resolution,precinct as u32,before.precincts.len() as usize);
                let selected=resolution<=meta.output_resolution;
                part2_precinct_owner_normal(band,data.block_size,meta.subbands,range,meta.tier1_style,(policy.0,policy.1),location,before.placements,before.planned_code_blocks,selected,limits);
                let planned=part2_planned_precinct(band,data.block_size,meta.subbands,range,meta.tier1_style,(policy.0,policy.1),location,before.placements,before.planned_code_blocks,selected,limits);
                if let Ok(value)=planned {
                    let after=part2_component_after_precinct(before,value);
                    part2_resolution_precincts_normal(component,resolution,meta,data,policy,limits,precinct+1,after);
                    part2_decode_eta(|events|part2_resolution_precincts_run(component,resolution,meta,data,policy,limits,precinct+1,after,events),
                        part2_component_plan_precincts(component,resolution,meta,data,policy,limits,precinct+1,after));
                }
                part2_cold_bind(|events|part2_precinct_owner_run(band,data.block_size,meta.subbands,range,meta.tier1_style,(policy.0,policy.1),location,before.placements,before.planned_code_blocks,selected,limits,events),
                    |planned:Part2PlannedPrecinct,rest|part2_resolution_precincts_run(component,resolution,meta,data,policy,limits,precinct+1,part2_component_after_precinct(before,planned),rest),planned,result);
            },
        }
    }
}
pub(crate) proof fn part2_resolution_plan_normal(size:&crate::codestream::ImageSize,component:u16,tile:u16,meta:Part2ComponentPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,resolution:nat,before:Part2ComponentPlanBuffers)
    ensures part2_cold_framed(|events|part2_resolution_plan_run(size,component,tile,meta,policy,limits,resolution,before,events),
        part2_component_plan_resolutions(size,component,tile,meta,policy,limits,resolution,before)),
    decreases if resolution<=meta.coding_style.decomposition_levels{(meta.coding_style.decomposition_levels as int+1-resolution) as nat}else{0nat},
{
    reveal_with_fuel(part2_resolution_plan_run,1);reveal_with_fuel(part2_component_plan_resolutions,1);
    let result=part2_component_plan_resolutions(size,component,tile,meta,policy,limits,resolution,before);
    if resolution>meta.coding_style.decomposition_levels {part2_cold_pure::<Part2PlannedComponent>(result);}else{
        match part2_resolution_plan_metadata(size,meta.coding_style,component,(tile,resolution as u8),[meta.bounds.x0,meta.bounds.y0]) {
            Err(_)=>{part2_cold_pure::<Part2PlannedComponent>(result);},
            Ok(data)=>{
                part2_resolution_precincts_normal(component,resolution as u8,meta,data,policy,limits,0,before);
                let after=part2_component_plan_precincts(component,resolution as u8,meta,data,policy,limits,0,before);
                if let Ok(value)=after {
                    if resolution==u8::MAX {part2_cold_pure::<Part2PlannedComponent>(Err(part1_block_placement_error(true)));}else{
                        part2_resolution_plan_normal(size,component,tile,meta,policy,limits,resolution+1,value);
                        part2_decode_eta(|events|part2_resolution_plan_run(size,component,tile,meta,policy,limits,resolution+1,value,events),
                            part2_component_plan_resolutions(size,component,tile,meta,policy,limits,resolution+1,value));
                    }
                }
                part2_cold_bind(|events|part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,0,before,events),
                    |after:Part2ComponentPlanBuffers,rest|if resolution==u8::MAX {Some((Err(part1_block_placement_error(true)),rest))}
                        else{part2_resolution_plan_run(size,component,tile,meta,policy,limits,resolution+1,after,rest)},after,result);
            },
        }
    }
}
pub(crate) proof fn part2_resolution_plan_start(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits,meta:Part2ComponentPlanMetadata)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_component_metadata_result(size,styles,quantizations,roi,component,selection,policy.2,Ok(meta)),
    ensures part2_cold_phase(|events|part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events),prefix,
        |events|part2_resolution_plan_run(size,component,selection.0,meta,policy,limits,0,
            Part2ComponentPlanBuffers {precincts,placements:Seq::empty(),planned_code_blocks:total},events)),
{
    reveal(part2_component_metadata_result);
    let prefix=part2_cold_witness(|events|part2_component_metadata_run(size,styles,quantizations,roi,component,selection,policy.2,events),Ok(meta));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,prefix+tail)
        ==part2_resolution_plan_run(size,component,selection.0,meta,policy,limits,0,
            Part2ComponentPlanBuffers {precincts,placements:Seq::empty(),planned_code_blocks:total},tail) by{
        part2_cold_prefix_at(|events|part2_component_metadata_run(size,styles,quantizations,roi,component,selection,policy.2,events),prefix,Ok(meta),tail);
    }
    prefix
}
pub(crate) open spec fn part2_resolution_next(size:&crate::codestream::ImageSize,component:u16,tile:u16,meta:Part2ComponentPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,resolution:nat,after:Part2ComponentPlanBuffers,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedComponent> {
    if resolution==u8::MAX {Some((Err(part1_block_placement_error(true)),events))}
    else{part2_resolution_plan_run(size,component,tile,meta,policy,limits,resolution+1,after,events)}
}
pub(crate) proof fn part2_resolution_plan_step(size:&crate::codestream::ImageSize,component:u16,tile:u16,meta:Part2ComponentPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,resolution:nat,before:Part2ComponentPlanBuffers,data:Part2ResolutionPlanMetadata)
    requires resolution<=meta.coding_style.decomposition_levels,
        part2_resolution_plan_metadata(size,meta.coding_style,component,(tile,resolution as u8),[meta.bounds.x0,meta.bounds.y0])==Ok(data),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_resolution_plan_run(size,component,tile,meta,policy,limits,resolution,before,events)
        ==part2_jpip_snapshot_bind(part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,0,before,events),
            |after:Part2ComponentPlanBuffers,rest|part2_resolution_next(size,component,tile,meta,policy,limits,resolution,after,rest)),
{reveal_with_fuel(part2_resolution_plan_run,1);}
pub(crate) proof fn part2_resolution_precinct_step(size:&crate::codestream::ImageSize,component:u16,tile:u16,meta:Part2ComponentPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,resolution:nat,data:Part2ResolutionPlanMetadata,precinct:nat,before:Part2ComponentPlanBuffers,origin:[u32;2])
    requires precinct<data.precincts_in_resolution,resolution<=u8::MAX,
        part2_planned_precinct_origin(data.first_precinct,data.geometry.precincts_across,precinct as u32,data.band_size)==Ok(origin),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>|
        part2_jpip_snapshot_bind(#[trigger] part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,precinct,before,events),
            |after:Part2ComponentPlanBuffers,rest|part2_resolution_next(size,component,tile,meta,policy,limits,resolution,after,rest))
        ==part2_jpip_snapshot_bind(part2_precinct_owner_run([origin[0],origin[1],data.band_size[0],data.band_size[1]],data.block_size,meta.subbands,
            (data.first_subband,data.subband_count),meta.tier1_style,(policy.0,policy.1),(component,resolution as u8,precinct as u32,before.precincts.len() as usize),
            before.placements,before.planned_code_blocks,resolution<=meta.output_resolution,limits,events),
            |planned:Part2PlannedPrecinct,rest|part2_jpip_snapshot_bind(
                part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,precinct+1,part2_component_after_precinct(before,planned),rest),
                |after:Part2ComponentPlanBuffers,tail|part2_resolution_next(size,component,tile,meta,policy,limits,resolution,after,tail))),
{
    reveal_with_fuel(part2_resolution_precincts_run,1);
    assert forall|events:Seq<Part2JpipSnapshotEvent>|
        part2_jpip_snapshot_bind(#[trigger] part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,precinct,before,events),
            |after:Part2ComponentPlanBuffers,rest|part2_resolution_next(size,component,tile,meta,policy,limits,resolution,after,rest))
        ==part2_jpip_snapshot_bind(part2_precinct_owner_run([origin[0],origin[1],data.band_size[0],data.band_size[1]],data.block_size,meta.subbands,
            (data.first_subband,data.subband_count),meta.tier1_style,(policy.0,policy.1),(component,resolution as u8,precinct as u32,before.precincts.len() as usize),
            before.placements,before.planned_code_blocks,resolution<=meta.output_resolution,limits,events),
            |planned:Part2PlannedPrecinct,rest|part2_jpip_snapshot_bind(
                part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,precinct+1,part2_component_after_precinct(before,planned),rest),
                |after:Part2ComponentPlanBuffers,tail|part2_resolution_next(size,component,tile,meta,policy,limits,resolution,after,tail))) by{
        part2_cold_bind_associative(part2_precinct_owner_run([origin[0],origin[1],data.band_size[0],data.band_size[1]],data.block_size,meta.subbands,
            (data.first_subband,data.subband_count),meta.tier1_style,(policy.0,policy.1),(component,resolution as u8,precinct as u32,before.precincts.len() as usize),
            before.placements,before.planned_code_blocks,resolution<=meta.output_resolution,limits,events),
            |planned:Part2PlannedPrecinct,rest|part2_resolution_precincts_run(component,resolution as u8,meta,data,policy,limits,precinct+1,part2_component_after_precinct(before,planned),rest),
            |after:Part2ComponentPlanBuffers,rest|part2_resolution_next(size,component,tile,meta,policy,limits,resolution,after,rest));
    }
}
pub(crate) proof fn part2_resolution_precinct_end(component:u16,resolution:u8,meta:Part2ComponentPlanMetadata,data:Part2ResolutionPlanMetadata,
    policy:(bool,u8,bool),limits:&crate::ResourceLimits,precinct:nat,before:Part2ComponentPlanBuffers)
    requires precinct>=data.precincts_in_resolution,
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger]
        part2_resolution_precincts_run(component,resolution,meta,data,policy,limits,precinct,before,events)==Some((Ok(before),events)),
{reveal_with_fuel(part2_resolution_precincts_run,1);}
pub(crate) proof fn part2_component_plan_join(size:&crate::codestream::ImageSize,styles:&crate::codestream::ComponentCodingStyles,
    quantizations:(u16,Seq<crate::codestream::Quantization>),roi:&crate::codestream::RoiShifts,component:u16,selection:(u16,u8),policy:(bool,u8,bool),
    precincts:Seq<Part1PacketPrecinctState>,total:u64,limits:&crate::ResourceLimits,
    root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedComponent>,result:Result<Part2PlannedComponent,crate::DecodeError>)
    requires part2_cold_framed(root,result),
        forall|events| #[trigger] root(events)==part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events),
    ensures part2_planned_component_result(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,result),
{
    reveal(part2_planned_component_result);
    part2_cold_framed_extensional(root,|events|part2_planned_component_run(size,styles,quantizations,roi,component,selection,policy,precincts,total,limits,events),result);
}
}
