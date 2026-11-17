//! Fresh execution/decoder owner requests, not nested decoder storage.
use super::*;
verus! {
pub enum Part2PlanningCapacityContext {
    Executions {band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
        style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),
        placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool},
    Decoders {grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
        style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),
        placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool},
    CodeBlockGrowth {cell:Part2Tier1CallContext,subband:crate::decode::SubbandGeometry,
        geometry:(u32,u32,u16,u16),placements:bool},
}
pub(crate) open spec fn part2_planning_capacity_count(context:Part2PlanningCapacityContext)->usize {
    match context {
        Part2PlanningCapacityContext::Executions {range,..}=>range.1,
        Part2PlanningCapacityContext::Decoders {blocks,..}=>(blocks[0] as nat*blocks[1] as nat) as usize,
        Part2PlanningCapacityContext::CodeBlockGrowth {..}=>1,
    }
}
pub(crate) open spec fn part2_planning_capacity_run(context:Part2PlanningCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_planning_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{
        match events[0] {
            Part2JpipSnapshotEvent::PlanningCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{
                    Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
                },
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_planning_capacity_result(context:Part2PlanningCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_planning_capacity_run(context,events),result)
}
pub(crate) proof fn part2_planning_capacity_observed(context:Part2PlanningCapacityContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_planning_capacity_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_planning_capacity_result(context,result),
{
    reveal(part2_planning_capacity_result);
    let count=part2_planning_capacity_count(context);
    let prefix=if count==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::PlanningCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_planning_capacity_run(context,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_planning_capacity_run(context,events),prefix,result));
}
pub(crate) open spec fn part2_codeblock_owner_admit(blocks:[u32;2],total:u64,selected:bool,limits:&crate::ResourceLimits)->Result<u64,crate::DecodeError> {
    let count=blocks[0] as nat*blocks[1] as nat;
    let next=if selected{total as nat+count}else{total as nat};
    if count>u64::MAX || next>u64::MAX {Err(part1_block_placement_error(true))}
    else if selected && next>crate::limits::resource_code_block_limit(limits) {
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlocks,limit:crate::limits::resource_code_block_limit(limits),actual:next as u64})
    }else if selected && next>crate::limits::resource_work_limit(limits) {
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::WorkUnits,limit:crate::limits::resource_work_limit(limits),actual:next as u64})
    }else if count>usize::MAX {Err(part1_block_placement_error(true))}else{Ok(next as u64)}
}
pub(crate) open spec fn part2_codeblock_owner_context(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool)->Part2PlanningCapacityContext {
    Part2PlanningCapacityContext::Decoders {grid,clip,blocks,subband,style,policy,indices,placements,total,selected}
}
pub(crate) open spec fn part2_codeblock_owner_run(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedCodeBlocks> {
    match part2_codeblock_owner_admit(blocks,total,selected,limits) {
        Err(error)=>Some((Err(error),events)),
        Ok(next)=>part2_jpip_snapshot_bind(part2_planning_capacity_run(part2_codeblock_owner_context(grid,clip,blocks,subband,style,policy,indices,placements,total,selected),events),
            |_:(),rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,
                Part2PlannedCodeBlocks {decoders:Seq::empty(),placements,decoder_index:indices.2,planned_code_blocks:next},rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_codeblock_owner_result(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,result:Result<Part2PlannedCodeBlocks,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_codeblock_owner_run(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,events),result)
}
pub(crate) proof fn part2_codeblock_owner_normal(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits)
    ensures part2_codeblock_owner_result(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,
        part2_planned_codeblocks(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits)),
{
    reveal(part2_codeblock_owner_result);reveal(part2_planning_capacity_result);
    let result=part2_planned_codeblocks(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits);
    match part2_codeblock_owner_admit(blocks,total,selected,limits) {
        Err(_)=>{part2_cold_pure::<Part2PlannedCodeBlocks>(result);},
        Ok(next)=>{
            let context=part2_codeblock_owner_context(grid,clip,blocks,subband,style,policy,indices,placements,total,selected);
            let initial=Part2PlannedCodeBlocks {decoders:Seq::empty(),placements,decoder_index:indices.2,planned_code_blocks:next};
            part2_planning_capacity_observed(context,Ok(()));
            part2_codeblock_rows_normal(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,initial);
            part2_decode_eta(|events|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,initial,events),result);
            part2_cold_bind(|events|part2_planning_capacity_run(context,events),
                |_:(),rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,initial,rest),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_codeblock_owner_refused(grid:[u32;4],clip:[u32;4],blocks:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits)
    requires part2_codeblock_owner_admit(blocks,total,selected,limits).is_ok(),
        part2_planning_capacity_result(part2_codeblock_owner_context(grid,clip,blocks,subband,style,policy,indices,placements,total,selected),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_codeblock_owner_result(grid,clip,blocks,subband,style,policy,indices,placements,total,selected,limits,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_codeblock_owner_result);reveal(part2_planning_capacity_result);
    part2_cold_bind(|events|part2_planning_capacity_run(part2_codeblock_owner_context(grid,clip,blocks,subband,style,policy,indices,placements,total,selected),events),
        |_:(),rest|part2_codeblock_rows_run(grid,clip,blocks,subband,style,policy,(indices.0,indices.1),0,
            Part2PlannedCodeBlocks {decoders:Seq::empty(),placements,decoder_index:indices.2,planned_code_blocks:part2_codeblock_owner_admit(blocks,total,selected,limits).get_Ok_0()},rest),
        Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) open spec fn part2_subband_execution_run(band:[u32;4],block_size:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedSubbandExecution> {
    match part2_planned_subband_lattice(band,block_size,subband) {
        Ok(Some(lattice))=>part2_jpip_snapshot_bind(part2_codeblock_owner_run(lattice.grid,lattice.clip,lattice.blocks,subband,style,policy,indices,placements,total,selected,limits,events),
            |_:Part2PlannedCodeBlocks,rest|Some((part2_planned_subband_execution(band,block_size,subband,style,policy,indices,placements,total,selected,limits),rest))),
        _=>Some((part2_planned_subband_execution(band,block_size,subband,style,policy,indices,placements,total,selected,limits),events)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_subband_execution_result(band:[u32;4],block_size:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,result:Result<Part2PlannedSubbandExecution,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_subband_execution_run(band,block_size,subband,style,policy,indices,placements,total,selected,limits,events),result)
}
pub(crate) proof fn part2_subband_execution_normal(band:[u32;4],block_size:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits)
    ensures part2_subband_execution_result(band,block_size,subband,style,policy,indices,placements,total,selected,limits,
        part2_planned_subband_execution(band,block_size,subband,style,policy,indices,placements,total,selected,limits)),
{
    reveal(part2_subband_execution_result);reveal(part2_codeblock_owner_result);
    let result=part2_planned_subband_execution(band,block_size,subband,style,policy,indices,placements,total,selected,limits);
    if let Ok(Some(lattice))=part2_planned_subband_lattice(band,block_size,subband) {
        part2_codeblock_owner_normal(lattice.grid,lattice.clip,lattice.blocks,subband,style,policy,indices,placements,total,selected,limits);
        let planned=part2_planned_codeblocks(lattice.grid,lattice.clip,lattice.blocks,subband,style,policy,indices,placements,total,selected,limits);
        if planned.is_ok(){part2_cold_pure(result);}
        part2_cold_bind(|events|part2_codeblock_owner_run(lattice.grid,lattice.clip,lattice.blocks,subband,style,policy,indices,placements,total,selected,limits,events),
            |_:Part2PlannedCodeBlocks,rest|Some((result,rest)),planned,result);
    }else{part2_cold_pure(result);}
}
pub(crate) proof fn part2_subband_execution_error(band:[u32;4],block_size:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,lattice:Part2PlannedSubbandLattice,error:crate::DecodeError)
    requires part2_planned_subband_lattice(band,block_size,subband)==Ok(Some(lattice)),
        part2_codeblock_owner_result(lattice.grid,lattice.clip,lattice.blocks,subband,style,policy,indices,placements,total,selected,limits,Err(error)),
    ensures part2_subband_execution_result(band,block_size,subband,style,policy,indices,placements,total,selected,limits,Err(error)),
{
    reveal(part2_subband_execution_result);reveal(part2_codeblock_owner_result);
    part2_cold_bind(|events|part2_codeblock_owner_run(lattice.grid,lattice.clip,lattice.blocks,subband,style,policy,indices,placements,total,selected,limits,events),
        |_:Part2PlannedCodeBlocks,rest|Some((part2_planned_subband_execution(band,block_size,subband,style,policy,indices,placements,total,selected,limits),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_subband_execution_frames(band:[u32;4],block_size:[u32;2],subband:crate::decode::SubbandGeometry,
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),indices:(usize,usize,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,
    total:u64,selected:bool,limits:&crate::ResourceLimits,result:Result<Part2PlannedSubbandExecution,crate::DecodeError>)
    requires part2_subband_execution_result(band,block_size,subband,style,policy,indices,placements,total,selected,limits,result),
    ensures part2_cold_framed(|events|part2_subband_execution_run(band,block_size,subband,style,policy,indices,placements,total,selected,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedSubbandExecution>|
            (forall|events| #[trigger] other(events)==part2_subband_execution_run(band,block_size,subband,style,policy,indices,placements,total,selected,limits,events))
            ==> #[trigger] part2_cold_framed(other,result),
{
    reveal(part2_subband_execution_result);
    part2_decode_eta(|events|part2_subband_execution_run(band,block_size,subband,style,policy,indices,placements,total,selected,limits,events),result);
}
pub(crate) open spec fn part2_precinct_after_subband(before:Part2PrecinctPlanBuilder,planned:Part2PlannedSubbandExecution)->Part2PrecinctPlanBuilder {
    Part2PrecinctPlanBuilder {executions:match planned.execution {None=>before.executions,Some(execution)=>before.executions.push(execution)},
        placements:planned.placements,decoder_index:planned.decoder_index,planned_code_blocks:planned.planned_code_blocks}
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_rows_run(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),selected:bool,limits:&crate::ResourceLimits,
    local:nat,before:Part2PrecinctPlanBuilder,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedPrecinct>
    decreases if local<range.1 {(range.1 as int-local) as nat}else{0nat},
{
    if local>=range.1 {part2_jpip_snapshot_bind(part2_precinct_state_run(location.0,location.1,location.2,style,before.executions,limits,events),
        |precinct:Part1PacketPrecinctState,rest|Some((Ok(part2_precinct_plan_finish(before,precinct)),rest)))}
    else {
        let index=range.0 as nat+local;
        if index>usize::MAX {Some((Err(part1_block_placement_error(true)),events))}
        else if index>=subbands.len(){Some((Err(part1_block_placement_error(false)),events))}
        else{part2_jpip_snapshot_bind(part2_subband_execution_run(band,block_size,subbands[index as int],style,policy,
            (location.3,index as usize,before.decoder_index),before.placements,before.planned_code_blocks,selected,limits,events),
            |planned:Part2PlannedSubbandExecution,rest|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,
                local+1,part2_precinct_after_subband(before,planned),rest))}
    }
}
pub(crate) proof fn part2_precinct_rows_normal(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),selected:bool,limits:&crate::ResourceLimits,
    local:nat,before:Part2PrecinctPlanBuilder)
    ensures part2_cold_framed(|events|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,local,before,events),
        part2_planned_precinct_rows(band,block_size,subbands,range,style,policy,location,selected,limits,local,before)),
    decreases if local<range.1 {(range.1 as int-local) as nat}else{0nat},
{
    reveal_with_fuel(part2_precinct_rows_run,1);reveal_with_fuel(part2_planned_precinct_rows,1);reveal(part2_subband_execution_result);
    let result=part2_planned_precinct_rows(band,block_size,subbands,range,style,policy,location,selected,limits,local,before);
    let index=range.0 as nat+local;
    if local>=range.1 {
        reveal(part2_precinct_state_result);
        part2_precinct_state_normal(location.0,location.1,location.2,style,before.executions,limits);
        let precinct=part2_precinct_from_executions(location.0,location.1,location.2,style,before.executions,limits);
        if precinct.is_ok(){part2_cold_pure::<Part2PlannedPrecinct>(result);}
        part2_cold_bind(|events|part2_precinct_state_run(location.0,location.1,location.2,style,before.executions,limits,events),
            |precinct:Part1PacketPrecinctState,rest|Some((Ok(part2_precinct_plan_finish(before,precinct)),rest)),precinct,result);
    }else if index>usize::MAX || index>=subbands.len(){part2_cold_pure::<Part2PlannedPrecinct>(result);}else{
        let indices=(location.3,index as usize,before.decoder_index);
        part2_subband_execution_normal(band,block_size,subbands[index as int],style,policy,indices,before.placements,before.planned_code_blocks,selected,limits);
        let planned=part2_planned_subband_execution(band,block_size,subbands[index as int],style,policy,indices,before.placements,before.planned_code_blocks,selected,limits);
        if let Ok(value)=planned {
            let after=part2_precinct_after_subband(before,value);
            part2_precinct_rows_normal(band,block_size,subbands,range,style,policy,location,selected,limits,local+1,after);
            part2_decode_eta(|events|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,local+1,after,events),
                part2_planned_precinct_rows(band,block_size,subbands,range,style,policy,location,selected,limits,local+1,after));
        }
        part2_cold_bind(|events|part2_subband_execution_run(band,block_size,subbands[index as int],style,policy,indices,before.placements,before.planned_code_blocks,selected,limits,events),
            |planned:Part2PlannedSubbandExecution,rest|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,local+1,part2_precinct_after_subband(before,planned),rest),planned,result);
    }
}
pub(crate) open spec fn part2_precinct_owner_context(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool)->Part2PlanningCapacityContext {
    Part2PlanningCapacityContext::Executions {band,block_size,subbands,range,style,policy,location,placements,total,selected}
}
pub(crate) open spec fn part2_precinct_owner_run(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,
    limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedPrecinct> {
    part2_jpip_snapshot_bind(part2_planning_capacity_run(part2_precinct_owner_context(band,block_size,subbands,range,style,policy,location,placements,total,selected),events),
        |_:(),rest|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,0,
            Part2PrecinctPlanBuilder {executions:Seq::empty(),placements,decoder_index:0,planned_code_blocks:total},rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_owner_result(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,
    limits:&crate::ResourceLimits,result:Result<Part2PlannedPrecinct,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events),result)
}
pub(crate) proof fn part2_precinct_owner_normal(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,limits:&crate::ResourceLimits)
    ensures part2_precinct_owner_result(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,
        part2_planned_precinct(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits)),
{
    reveal(part2_precinct_owner_result);reveal(part2_planning_capacity_result);
    let initial=Part2PrecinctPlanBuilder {executions:Seq::empty(),placements,decoder_index:0,planned_code_blocks:total};
    let result=part2_planned_precinct(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits);
    let context=part2_precinct_owner_context(band,block_size,subbands,range,style,policy,location,placements,total,selected);
    part2_planning_capacity_observed(context,Ok(()));
    part2_precinct_rows_normal(band,block_size,subbands,range,style,policy,location,selected,limits,0,initial);
    part2_decode_eta(|events|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,0,initial,events),result);
    part2_cold_bind(|events|part2_planning_capacity_run(context,events),
        |_:(),rest|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,0,initial,rest),Ok(()),result);
}
pub(crate) proof fn part2_precinct_owner_refused(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,limits:&crate::ResourceLimits)
    requires part2_planning_capacity_result(part2_precinct_owner_context(band,block_size,subbands,range,style,policy,location,placements,total,selected),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_precinct_owner_result(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_precinct_owner_result);reveal(part2_planning_capacity_result);
    part2_cold_bind(|events|part2_planning_capacity_run(part2_precinct_owner_context(band,block_size,subbands,range,style,policy,location,placements,total,selected),events),
        |_:(),rest|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,0,
            Part2PrecinctPlanBuilder {executions:Seq::empty(),placements,decoder_index:0,planned_code_blocks:total},rest),
        Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) open spec fn part2_cold_phase<R>(root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<R>,prefix:Seq<Part2JpipSnapshotEvent>,
    child:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<R>)->bool {
    forall|tail:Seq<Part2JpipSnapshotEvent>| #[trigger] root(prefix+tail)==child(tail)
}
pub(crate) proof fn part2_precinct_owner_start(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,limits:&crate::ResourceLimits)
    ->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_planning_capacity_result(part2_precinct_owner_context(band,block_size,subbands,range,style,policy,location,placements,total,selected),Ok(())),
    ensures part2_cold_phase(|events|part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events),prefix,
        |events|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,0,
            Part2PrecinctPlanBuilder {executions:Seq::empty(),placements,decoder_index:0,planned_code_blocks:total},events)),
{
    reveal(part2_planning_capacity_result);
    let context=part2_precinct_owner_context(band,block_size,subbands,range,style,policy,location,placements,total,selected);
    let prefix=part2_cold_witness(|events|part2_planning_capacity_run(context,events),Ok(()));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,prefix+tail)
        ==part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,0,
            Part2PrecinctPlanBuilder {executions:Seq::empty(),placements,decoder_index:0,planned_code_blocks:total},tail) by{
        part2_cold_prefix_at(|events|part2_planning_capacity_run(context,events),prefix,Ok(()),tail);
    }
    prefix
}
pub(crate) proof fn part2_precinct_rows_step(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),selected:bool,limits:&crate::ResourceLimits,local:nat,before:Part2PrecinctPlanBuilder)
    requires local<range.1,range.0 as nat+local<=usize::MAX,range.0 as nat+local<subbands.len(),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>|
        #[trigger] part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,local,before,events)
        ==part2_jpip_snapshot_bind(part2_subband_execution_run(band,block_size,subbands[range.0 as int+local as int],style,policy,
            (location.3,(range.0+local) as usize,before.decoder_index),before.placements,before.planned_code_blocks,selected,limits,events),
            |planned:Part2PlannedSubbandExecution,rest|part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,
                local+1,part2_precinct_after_subband(before,planned),rest)),
{reveal_with_fuel(part2_precinct_rows_run,1);}
pub(crate) proof fn part2_precinct_owner_frames(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,
    limits:&crate::ResourceLimits,result:Result<Part2PlannedPrecinct,crate::DecodeError>)
    requires part2_precinct_owner_result(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,result),
    ensures part2_cold_framed(|events|part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedPrecinct>|
            (forall|events| #[trigger] other(events)==part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events))
            ==> #[trigger] part2_cold_framed(other,result),
{reveal(part2_precinct_owner_result);part2_decode_eta(|events|part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events),result);}
pub(crate) proof fn part2_precinct_owner_join(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),placements:Seq<crate::decode::ProgressionCodeBlockPlacement>,total:u64,selected:bool,
    limits:&crate::ResourceLimits,root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PlannedPrecinct>,result:Result<Part2PlannedPrecinct,crate::DecodeError>)
    requires part2_cold_framed(root,result),
        forall|events| #[trigger] root(events)==part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events),
    ensures part2_precinct_owner_result(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,result),
{
    reveal(part2_precinct_owner_result);
    part2_cold_framed_extensional(root,|events|part2_precinct_owner_run(band,block_size,subbands,range,style,policy,location,placements,total,selected,limits,events),result);
}
pub(crate) open spec fn part2_precinct_plan_finish(before:Part2PrecinctPlanBuilder,precinct:Part1PacketPrecinctState)->Part2PlannedPrecinct {
    Part2PlannedPrecinct {precinct,placements:before.placements,planned_code_blocks:before.planned_code_blocks}
}
pub(crate) proof fn part2_precinct_rows_end(band:[u32;4],block_size:[u32;2],subbands:Seq<crate::decode::SubbandGeometry>,range:(usize,usize),
    style:crate::tier1::Tier1CodingStyle,policy:(bool,u8),location:(u16,u8,u32,usize),selected:bool,limits:&crate::ResourceLimits,local:nat,before:Part2PrecinctPlanBuilder)
    requires local>=range.1,
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_precinct_rows_run(band,block_size,subbands,range,style,policy,location,selected,limits,local,before,events)
        ==part2_jpip_snapshot_bind(part2_precinct_state_run(location.0,location.1,location.2,style,before.executions,limits,events),
            |precinct:Part1PacketPrecinctState,rest|Some((Ok(part2_precinct_plan_finish(before,precinct)),rest))),
{reveal_with_fuel(part2_precinct_rows_run,1);}
}
