//! Source-derived component/tile region collection and checked append replies.
use super::*;
verus! {
pub struct Part2NltRegionStorageContext {
    pub input:Part2DecoderLayoutInput,
    pub image:Part1DecodedTypedImage,
    pub discard:u8,
}
pub struct Part2NltRegionAppendContext {
    pub source:Part2NltRegionStorageContext,
    pub component:u16,
    pub extent:(u32,u32,u32,u32),
    pub scale:u32,
    pub tile:u16,
    pub before:Seq<Part2NonlinearRegion>,
    pub region:Part2NonlinearRegion,
}
pub(crate) open spec fn part2_nlt_region_append_admitted(context:Part2NltRegionAppendContext)->bool {
    part2_nonlinear_tile_region_input(context.source.input,context.component,context.tile,context.extent,context.scale)
        ==Ok(Some(context.region))
}
pub(crate) open spec fn part2_nlt_region_capacity_run(context:Part2NltRegionAppendContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if !part2_nlt_region_append_admitted(context) || events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::NltRegionCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=1 {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_nlt_region_capacity_result(context:Part2NltRegionAppendContext,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_nlt_region_capacity_run(context,events),result)
}
pub(crate) proof fn part2_nlt_region_capacity_observed(context:Part2NltRegionAppendContext,
    result:Result<(),crate::DecodeError>)
    requires part2_nlt_region_append_admitted(context),
        result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures part2_nlt_region_capacity_result(context,result),
{
    let prefix=seq![Part2JpipSnapshotEvent::NltRegionCapacity {context,elements:1,succeeded:result.is_ok()}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_nlt_region_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_nlt_region_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_nlt_region_capacity_frames(context:Part2NltRegionAppendContext,
    result:Result<(),crate::DecodeError>)
    requires part2_nlt_region_capacity_result(context,result),
    ensures part2_cold_framed(|events|part2_nlt_region_capacity_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_nlt_region_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_nlt_region_capacity_run(context,events),result);}
pub(crate) open spec fn part2_nlt_region_step_value(context:Part2NltRegionStorageContext,component:u16,
    extent:(u32,u32,u32,u32),scale:u32,tile:u16,regions:Seq<Part2NonlinearRegion>)
    ->Result<Seq<Part2NonlinearRegion>,crate::DecodeError> {
    match part2_nonlinear_tile_region_input(context.input,component,tile,extent,scale) {
        Err(error)=>Err(error),Ok(None)=>Ok(regions),Ok(Some(region))=>Ok(regions.push(region)),
    }
}
pub(crate) open spec fn part2_nlt_region_step_run(context:Part2NltRegionStorageContext,component:u16,
    extent:(u32,u32,u32,u32),scale:u32,tile:u16,regions:Seq<Part2NonlinearRegion>,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>> {
    match part2_nonlinear_tile_region_input(context.input,component,tile,extent,scale) {
        Err(error)=>Some((Err(error),events)),Ok(None)=>Some((Ok(regions),events)),
        Ok(Some(region))=>part2_jpip_snapshot_bind(part2_nlt_region_capacity_run(
            Part2NltRegionAppendContext {source:context,component,extent,scale,tile,before:regions,region},events),
            |_:(),rest|Some((Ok(regions.push(region)),rest))),
    }
}
pub(crate) proof fn part2_nlt_region_step_normal(context:Part2NltRegionStorageContext,component:u16,
    extent:(u32,u32,u32,u32),scale:u32,tile:u16,regions:Seq<Part2NonlinearRegion>)
    ensures part2_cold_framed(|events|part2_nlt_region_step_run(context,component,extent,scale,tile,regions,events),
            part2_nlt_region_step_value(context,component,extent,scale,tile,regions)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>>|
            (forall|events| #[trigger] other(events)==part2_nlt_region_step_run(context,component,extent,scale,tile,regions,events)) ==>
                #[trigger] part2_cold_framed(other,part2_nlt_region_step_value(context,component,extent,scale,tile,regions)),
{
    let result=part2_nlt_region_step_value(context,component,extent,scale,tile,regions);part2_cold_pure(result);
    if let Ok(Some(region))=part2_nonlinear_tile_region_input(context.input,component,tile,extent,scale) {
        let append=Part2NltRegionAppendContext {source:context,component,extent,scale,tile,before:regions,region};
        part2_nlt_region_capacity_observed(append,Ok(()));part2_nlt_region_capacity_frames(append,Ok(()));
        part2_cold_bind(|events|part2_nlt_region_capacity_run(append,events),
            |_:(),rest|Some((Ok(regions.push(region)),rest)),Ok(()),result);
    }
    part2_decode_eta(|events|part2_nlt_region_step_run(context,component,extent,scale,tile,regions,events),result);
}
#[verifier::opaque]
pub(crate) open spec fn part2_nlt_region_tiles_run(context:Part2NltRegionStorageContext,component:u16,
    extent:(u32,u32,u32,u32),scale:u32,count:u64,tile:nat,regions:Seq<Part2NonlinearRegion>,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>>
    decreases count-tile,
{
    if tile>=count {Some((Ok(regions),events))}
    else if tile>u16::MAX {Some((Err(part1_block_placement_error(true)),events))}
    else{part2_jpip_snapshot_bind(part2_nlt_region_step_run(context,component,extent,scale,tile as u16,regions,events),
        |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_tiles_run(context,component,extent,scale,count,tile+1,updated,rest))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_nlt_region_components_run(context:Part2NltRegionStorageContext,scale:u32,
    component:nat,regions:Seq<Part2NonlinearRegion>,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Seq<Part2NonlinearRegion>>
    decreases context.input.size.components-component,
{
    if component>=context.input.size.components {Some((Ok(regions),events))}
    else{match part2_nonlinear_component_extent(&context.input.size,context.image,component as u16) {
        Err(error)=>Some((Err(error),events)),
        Ok((extent,count))=>part2_jpip_snapshot_bind(part2_nlt_region_tiles_run(context,component as u16,extent,scale,count,0,regions,events),
            |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_components_run(context,scale,component+1,updated,rest)),
    }}
}
pub(crate) proof fn part2_nlt_region_tiles_normal(context:Part2NltRegionStorageContext,component:u16,
    extent:(u32,u32,u32,u32),scale:u32,count:u64,tile:nat,regions:Seq<Part2NonlinearRegion>)
    ensures part2_cold_framed(|events|part2_nlt_region_tiles_run(context,component,extent,scale,count,tile,regions,events),
        part2_nonlinear_tile_regions_input(context.input,component,extent,scale,count,tile,regions)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>>|
            (forall|events| #[trigger] other(events)==part2_nlt_region_tiles_run(context,component,extent,scale,count,tile,regions,events)) ==>
                #[trigger] part2_cold_framed(other,part2_nonlinear_tile_regions_input(context.input,component,extent,scale,count,tile,regions)),
    decreases count-tile,
{
    reveal_with_fuel(part2_nlt_region_tiles_run,1);
    let result=part2_nonlinear_tile_regions_input(context.input,component,extent,scale,count,tile,regions);
    part2_cold_pure(result);
    if tile<count && tile<=u16::MAX {
        let step=part2_nlt_region_step_value(context,component,extent,scale,tile as u16,regions);
        part2_nlt_region_step_normal(context,component,extent,scale,tile as u16,regions);
        if let Ok(updated)=step {part2_nlt_region_tiles_normal(context,component,extent,scale,count,tile+1,updated);}
        part2_cold_bind(|events|part2_nlt_region_step_run(context,component,extent,scale,tile as u16,regions,events),
            |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_tiles_run(context,component,extent,scale,count,tile+1,updated,rest),step,result);
    }
    part2_decode_eta(|events|part2_nlt_region_tiles_run(context,component,extent,scale,count,tile,regions,events),result);
}
pub(crate) proof fn part2_nlt_region_components_normal(context:Part2NltRegionStorageContext,scale:u32,
    component:nat,regions:Seq<Part2NonlinearRegion>)
    ensures part2_cold_framed(|events|part2_nlt_region_components_run(context,scale,component,regions,events),
        part2_nonlinear_component_regions_input(context.input,context.image,scale,component,regions)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>>|
            (forall|events| #[trigger] other(events)==part2_nlt_region_components_run(context,scale,component,regions,events)) ==>
                #[trigger] part2_cold_framed(other,part2_nonlinear_component_regions_input(context.input,context.image,scale,component,regions)),
    decreases context.input.size.components-component,
{
    reveal_with_fuel(part2_nlt_region_components_run,1);
    let result=part2_nonlinear_component_regions_input(context.input,context.image,scale,component,regions);
    part2_cold_pure(result);
    if component<context.input.size.components {
        if let Ok((extent,count))=part2_nonlinear_component_extent(&context.input.size,context.image,component as u16) {
            let tiles=part2_nonlinear_tile_regions_input(context.input,component as u16,extent,scale,count,0,regions);
            part2_nlt_region_tiles_normal(context,component as u16,extent,scale,count,0,regions);
            if let Ok(updated)=tiles {part2_nlt_region_components_normal(context,scale,component+1,updated);}
            part2_cold_bind(|events|part2_nlt_region_tiles_run(context,component as u16,extent,scale,count,0,regions,events),
                |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_components_run(context,scale,component+1,updated,rest),tiles,result);
        }
    }
    part2_decode_eta(|events|part2_nlt_region_components_run(context,scale,component,regions,events),result);
}
pub(crate) open spec fn part2_nlt_regions_storage_run(context:Part2NltRegionStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>> {
    if context.discard>=32 {
        Some((Err(crate::DecodeError::InvalidSelection {reason:crate::SelectionError::ReductionTooLarge}),events))
    }else{part2_nlt_region_components_run(context,1u32<<(context.discard as u32),0,Seq::empty(),events)}
}
pub closed spec fn part2_nlt_regions_storage_result(context:Part2NltRegionStorageContext,
    result:Result<Seq<Part2NonlinearRegion>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_nlt_regions_storage_run(context,events),result)
}
pub(crate) proof fn part2_nlt_regions_storage_normal(context:Part2NltRegionStorageContext)
    ensures part2_nlt_regions_storage_result(context,part2_collect_nonlinear_regions_input(context.input,context.image,context.discard)),
{
    let result=part2_collect_nonlinear_regions_input(context.input,context.image,context.discard);
    part2_cold_pure(result);
    if context.discard<32 {part2_nlt_region_components_normal(context,1u32<<(context.discard as u32),0,Seq::empty());}
}
pub(crate) proof fn part2_nlt_regions_storage_frames(context:Part2NltRegionStorageContext,
    result:Result<Seq<Part2NonlinearRegion>,crate::DecodeError>)
    requires part2_nlt_regions_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_nlt_regions_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>>|
            (forall|events| #[trigger] other(events)==part2_nlt_regions_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_nlt_regions_storage_run(context,events),result);}
pub(crate) open spec fn part2_nlt_region_component_tiles_run(context:Part2NltRegionStorageContext,component:nat,
    extent:(u32,u32,u32,u32),scale:u32,count:u64,tile:nat,regions:Seq<Part2NonlinearRegion>,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2NonlinearRegion>> {
    part2_jpip_snapshot_bind(part2_nlt_region_tiles_run(context,component as u16,extent,scale,count,tile,regions,events),
        |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_components_run(context,scale,component+1,updated,rest))
}
pub(crate) proof fn part2_nlt_regions_begin_tiles(context:Part2NltRegionStorageContext,prefix:Seq<Part2JpipSnapshotEvent>,
    component:nat,extent:(u32,u32,u32,u32),scale:u32,count:u64,regions:Seq<Part2NonlinearRegion>)
    requires component<context.input.size.components,
        part2_nonlinear_component_extent(&context.input.size,context.image,component as u16)==Ok((extent,count)),
        part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),prefix,
            |events|part2_nlt_region_components_run(context,scale,component,regions,events)),
    ensures part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),prefix,
        |events|part2_nlt_region_component_tiles_run(context,component,extent,scale,count,0,regions,events)),
{reveal_with_fuel(part2_nlt_region_components_run,1);}
pub(crate) proof fn part2_nlt_regions_finish_tiles(context:Part2NltRegionStorageContext,prefix:Seq<Part2JpipSnapshotEvent>,
    component:nat,extent:(u32,u32,u32,u32),scale:u32,count:u64,tile:nat,regions:Seq<Part2NonlinearRegion>)
    requires tile>=count,part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),prefix,
        |events|part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile,regions,events)),
    ensures part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),prefix,
        |events|part2_nlt_region_components_run(context,scale,component+1,regions,events)),
{reveal_with_fuel(part2_nlt_region_tiles_run,1);}
pub(crate) proof fn part2_nlt_regions_advance(context:Part2NltRegionStorageContext,prefix:Seq<Part2JpipSnapshotEvent>,
    component:nat,extent:(u32,u32,u32,u32),scale:u32,count:u64,tile:nat,
    regions:Seq<Part2NonlinearRegion>,updated:Seq<Part2NonlinearRegion>)->(extended:Seq<Part2JpipSnapshotEvent>)
    requires tile<count,tile<=u16::MAX,
        part2_nlt_region_step_value(context,component as u16,extent,scale,tile as u16,regions)==Ok(updated),
        part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),prefix,
            |events|part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile,regions,events)),
    ensures part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),extended,
        |events|part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile+1,updated,events)),
{
    part2_nlt_region_step_normal(context,component as u16,extent,scale,tile as u16,regions);
    let calls=part2_cold_witness(|events|part2_nlt_region_step_run(context,component as u16,extent,scale,tile as u16,regions,events),Ok(updated));
    reveal_with_fuel(part2_nlt_region_tiles_run,1);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile,regions,calls+tail)
            ==part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile+1,updated,tail) by {
        part2_cold_prefix_at(|events|part2_nlt_region_step_run(context,component as u16,extent,scale,tile as u16,regions,events),calls,Ok(updated),tail);
    }
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_nlt_regions_storage_run(context,(prefix+calls)+tail)
        ==part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile+1,updated,tail) by {
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
        assert((|events|part2_nlt_regions_storage_run(context,events))(prefix+(calls+tail))
            ==part2_nlt_region_component_tiles_run(context,component,extent,scale,count,tile,regions,calls+tail));
    }
    prefix+calls
}
pub(crate) proof fn part2_nlt_regions_append_error(context:Part2NltRegionAppendContext,prefix:Seq<Part2JpipSnapshotEvent>,
    count:u64,error:crate::DecodeError)
    requires context.tile<count,part2_nlt_region_append_admitted(context),
        part2_nlt_region_capacity_result(context,Err(error)),
        part2_cold_phase(|events|part2_nlt_regions_storage_run(context.source,events),prefix,
            |events|part2_nlt_region_component_tiles_run(context.source,context.component as nat,
                context.extent,context.scale,count,context.tile as nat,context.before,events)),
    ensures part2_nlt_regions_storage_result(context.source,Err(error)),
{
    let source=context.source;let component=context.component;let extent=context.extent;
    let scale=context.scale;let tile=context.tile;let regions=context.before;let region=context.region;
    part2_nlt_region_capacity_frames(context,Err(error));
    part2_cold_bind(|events|part2_nlt_region_capacity_run(context,events),
        |_:(),rest|Some((Ok(regions.push(region)),rest)),Err(error),Err(error));
    part2_decode_eta(|events|part2_nlt_region_step_run(source,component,extent,scale,tile,regions,events),Err(error));
    part2_cold_bind(|events|part2_nlt_region_step_run(source,component,extent,scale,tile,regions,events),
        |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_tiles_run(source,component,extent,scale,count,tile as nat+1,updated,rest),
        Err(error),Err(error));
    reveal_with_fuel(part2_nlt_region_tiles_run,1);
    part2_decode_eta(|events|part2_nlt_region_tiles_run(source,component,extent,scale,count,tile as nat,regions,events),Err(error));
    part2_cold_bind(|events|part2_nlt_region_tiles_run(source,component,extent,scale,count,tile as nat,regions,events),
        |updated:Seq<Part2NonlinearRegion>,rest|part2_nlt_region_components_run(source,scale,component as nat+1,updated,rest),Err(error),Err(error));
    part2_decode_eta(|events|part2_nlt_region_component_tiles_run(source,component as nat,extent,scale,count,tile as nat,regions,events),Err(error));
    part2_cold_prefix_result(|events|part2_nlt_regions_storage_run(source,events),
        |events|part2_nlt_region_component_tiles_run(source,component as nat,extent,scale,count,tile as nat,regions,events),prefix,Err(error));
}
pub(crate) proof fn part2_nlt_regions_finish(context:Part2NltRegionStorageContext,prefix:Seq<Part2JpipSnapshotEvent>,
    scale:u32,component:nat,regions:Seq<Part2NonlinearRegion>)
    requires component>=context.input.size.components,
        part2_cold_phase(|events|part2_nlt_regions_storage_run(context,events),prefix,
            |events|part2_nlt_region_components_run(context,scale,component,regions,events)),
    ensures part2_nlt_regions_storage_result(context,Ok(regions)),
{
    part2_cold_pure(Ok(regions));reveal_with_fuel(part2_nlt_region_components_run,1);
    part2_decode_eta(|events|part2_nlt_region_components_run(context,scale,component,regions,events),Ok(regions));
    part2_cold_prefix_result(|events|part2_nlt_regions_storage_run(context,events),
        |events|part2_nlt_region_components_run(context,scale,component,regions,events),prefix,Ok(regions));
}
}
