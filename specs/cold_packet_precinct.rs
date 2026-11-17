//! Real nested precinct state construction and the two ordered TagTree children.
use super::*;
verus! {
pub struct Part2PrecinctCapacityContext {
    pub location:(u16,u8,u32),pub style:crate::tier1::Tier1CodingStyle,pub executions:Seq<Part2PacketSubbandExecution>,
}
pub(crate) open spec fn part2_precinct_capacity_run(context:Part2PrecinctCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=context.executions.len() as usize;
    if count==0{Some((Ok(()),events))}else if events.len()==0{None}else{
        match events[0] {
            Part2JpipSnapshotEvent::PrecinctCapacity {context:actual,elements,succeeded}=>
                if actual!=context || elements!=count {None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_capacity_result(context:Part2PrecinctCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_precinct_capacity_run(context,events),result)
}
pub(crate) proof fn part2_precinct_capacity_observed(context:Part2PrecinctCapacityContext,result:Result<(),crate::DecodeError>)
    requires context.executions.len()<=usize::MAX,
        result==Ok(()) || (context.executions.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_precinct_capacity_result(context,result),
{
    reveal(part2_precinct_capacity_result);
    let prefix=if context.executions.len()==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::PrecinctCapacity {context,elements:context.executions.len() as usize,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_precinct_capacity_run(context,prefix+tail)==Some((result,tail)) by{
        if context.executions.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_precinct_capacity_run(context,events),prefix,result));
}
pub(crate) open spec fn part2_precinct_context_capacity_context(
    states:Seq<Part1CodeBlockPacketState>,contexts:Seq<crate::packet::CodeBlockPacketContext>,
    count:usize,across:u32,maximum_zero:u16,style:crate::tier1::Tier1CodingStyle,contexts_owner:bool,
) -> Part2PlanningCapacityContext {
    Part2PlanningCapacityContext::PrecinctContexts {states,contexts,count,across,maximum_zero,style,contexts_owner}
}
pub(crate) open spec fn part2_precinct_contexts_run(
    states:Seq<Part1CodeBlockPacketState>,contexts:Seq<crate::packet::CodeBlockPacketContext>,
    count:usize,across:u32,maximum_zero:u16,style:crate::tier1::Tier1CodingStyle,events:Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>)> {
    let result=part2_precinct_contexts(states,contexts,count,across,maximum_zero,style);
    match result {
        Err(error)=>Some((Err(error),events)),
        Ok(_)=>part2_jpip_snapshot_bind(
            part2_planning_capacity_run(part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,false),events),
            |_:(),rest|part2_jpip_snapshot_bind(
                part2_planning_capacity_run(part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,true),rest),
                |_:(),tail|Some((result,tail)))),
    }
}
pub(crate) open spec fn part2_precinct_contexts_result(
    states:Seq<Part1CodeBlockPacketState>,contexts:Seq<crate::packet::CodeBlockPacketContext>,
    count:usize,across:u32,maximum_zero:u16,style:crate::tier1::Tier1CodingStyle,
    result:Result<(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events|part2_precinct_contexts_run(states,contexts,count,across,maximum_zero,style,events),result)
}
pub(crate) proof fn part2_precinct_contexts_normal(
    states:Seq<Part1CodeBlockPacketState>,contexts:Seq<crate::packet::CodeBlockPacketContext>,
    count:usize,across:u32,maximum_zero:u16,style:crate::tier1::Tier1CodingStyle,
)
    ensures part2_precinct_contexts_result(states,contexts,count,across,maximum_zero,style,
        part2_precinct_contexts(states,contexts,count,across,maximum_zero,style)),
{
    reveal(part2_planning_capacity_result);
    let result=part2_precinct_contexts(states,contexts,count,across,maximum_zero,style);
    part2_cold_pure(result);
    if result.is_ok() {
        let first=part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,false);
        let last=part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,true);
        part2_planning_capacity_observed(first,Ok(()));
        part2_planning_capacity_observed(last,Ok(()));
        part2_cold_bind(|events|part2_planning_capacity_run(last,events),|_:(),tail|Some((result,tail)),Ok(()),result);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(last,events),|_:(),tail|Some((result,tail))),result);
        part2_cold_bind(|events|part2_planning_capacity_run(first,events),
            |_:(),rest|part2_jpip_snapshot_bind(part2_planning_capacity_run(last,rest),|_:(),tail|Some((result,tail))),Ok(()),result);
    }
}
pub(crate) proof fn part2_precinct_contexts_refused(
    states:Seq<Part1CodeBlockPacketState>,contexts:Seq<crate::packet::CodeBlockPacketContext>,
    count:usize,across:u32,maximum_zero:u16,style:crate::tier1::Tier1CodingStyle,contexts_owner:bool,error:crate::DecodeError,
)
    requires part2_precinct_contexts(states,contexts,count,across,maximum_zero,style).is_ok(),
        part2_planning_capacity_result(part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,contexts_owner),Err(error)),
        contexts_owner ==> part2_planning_capacity_result(
            part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,false),Ok(())),
    ensures part2_precinct_contexts_result(states,contexts,count,across,maximum_zero,style,Err(error)),
{
    reveal(part2_planning_capacity_result);
    let result=part2_precinct_contexts(states,contexts,count,across,maximum_zero,style);
    let first=part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,false);
    let last=part2_precinct_context_capacity_context(states,contexts,count,across,maximum_zero,style,true);
    if contexts_owner {
        part2_cold_bind(|events|part2_planning_capacity_run(last,events),|_:(),tail|Some((result,tail)),Err(error),Err(error));
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(last,events),|_:(),tail|Some((result,tail))),Err(error));
    }
    part2_cold_bind(|events|part2_planning_capacity_run(first,events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_planning_capacity_run(last,rest),|_:(),tail|Some((result,tail))),
        if contexts_owner {Ok(())}else{Err(error)},Err(error));
}
pub(crate) open spec fn part2_precinct_tree_prelude(before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,
    style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits)->Result<(Part1PacketPrecinctState,u64),crate::DecodeError> {
    if row.across==0 || row.down==0 || row.maximum_zero==0 || row.maximum_zero>crate::tier1::MAX_TIER1_BITPLANES {
        Err(part1_packet_header_error())
    }else{
        let count=row.across as nat*row.down as nat;let next=total as nat+count;
        if count>u64::MAX || next>u64::MAX{Err(part1_block_placement_error(true))}
        else if next>crate::limits::resource_code_block_limit(limits){
            Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlocks,limit:crate::limits::resource_code_block_limit(limits),actual:next as u64})
        }else if next>crate::limits::resource_work_limit(limits){
            Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::WorkUnits,limit:crate::limits::resource_work_limit(limits),actual:next as u64})
        }else if count>usize::MAX{Err(part1_block_placement_error(true))}
        else if row.decoders.len()!=count{Err(part1_packet_header_error())}
        else{match part2_precinct_contexts(before.states,before.contexts,count as usize,row.across,row.maximum_zero,style){
            Err(error)=>Err(error),Ok(contexts)=>Ok((Part1PacketPrecinctState {states:contexts.0,contexts:contexts.1,decoders:before.decoders+row.decoders,..before},next as u64)),
        }}
    }
}
pub(crate) open spec fn part2_precinct_decoder_capacity_context(
    before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,style:crate::tier1::Tier1CodingStyle,
) -> Part2PlanningCapacityContext {
    Part2PlanningCapacityContext::PrecinctDecoders {before,total,row,style}
}
pub(crate) open spec fn part2_precinct_prelude_run(
    before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,
    style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>,
) -> Part2ColdRun<(Part1PacketPrecinctState,u64)> {
    let result=part2_precinct_tree_prelude(before,total,row,style,limits);
    match result {
        Err(error)=>Some((Err(error),events)),
        Ok(_)=>part2_jpip_snapshot_bind(
            part2_precinct_contexts_run(before.states,before.contexts,row.decoders.len() as usize,row.across,row.maximum_zero,style,events),
            |_: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
                part2_jpip_snapshot_bind(part2_planning_capacity_run(part2_precinct_decoder_capacity_context(before,total,row,style),rest),
                    |_:(),tail|Some((result,tail)))),
    }
}
pub(crate) open spec fn part2_precinct_prelude_result(
    before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,
    style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    result:Result<(Part1PacketPrecinctState,u64),crate::DecodeError>,
) -> bool {
    part2_cold_framed(|events|part2_precinct_prelude_run(before,total,row,style,limits,events),result)
}
pub(crate) proof fn part2_precinct_prelude_normal(
    before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,
    style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
)
    ensures part2_precinct_prelude_result(before,total,row,style,limits,part2_precinct_tree_prelude(before,total,row,style,limits)),
{
    reveal(part2_planning_capacity_result);
    let result=part2_precinct_tree_prelude(before,total,row,style,limits);
    part2_cold_pure(result);
    if result.is_ok() {
        let count=row.decoders.len() as usize;
        let contexts=part2_precinct_contexts(before.states,before.contexts,count,row.across,row.maximum_zero,style);
        part2_precinct_contexts_normal(before.states,before.contexts,count,row.across,row.maximum_zero,style);
        let capacity=part2_precinct_decoder_capacity_context(before,total,row,style);
        part2_planning_capacity_observed(capacity,Ok(()));
        part2_cold_bind(|events|part2_planning_capacity_run(capacity,events),
            |_:(),tail|Some((result,tail)),Ok(()),result);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(capacity,events),
            |_:(),tail|Some((result,tail))),result);
        part2_cold_bind(|events|part2_precinct_contexts_run(before.states,before.contexts,count,row.across,row.maximum_zero,style,events),
            |_: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
                part2_jpip_snapshot_bind(part2_planning_capacity_run(capacity,rest),|_:(),tail|Some((result,tail))),contexts,result);
    }
}
pub(crate) proof fn part2_precinct_prelude_contexts_refused(
    before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,
    style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,error:crate::DecodeError,
)
    requires part2_precinct_tree_prelude(before,total,row,style,limits).is_ok(),
        part2_precinct_contexts_result(before.states,before.contexts,row.decoders.len() as usize,
            row.across,row.maximum_zero,style,Err(error)),
    ensures part2_precinct_prelude_result(before,total,row,style,limits,Err(error)),
{
    let result=part2_precinct_tree_prelude(before,total,row,style,limits);
    let capacity=part2_precinct_decoder_capacity_context(before,total,row,style);
    part2_cold_bind(|events|part2_precinct_contexts_run(before.states,before.contexts,row.decoders.len() as usize,row.across,row.maximum_zero,style,events),
        |_: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
            part2_jpip_snapshot_bind(part2_planning_capacity_run(capacity,rest),|_:(),tail|Some((result,tail))),
        Err(error),Err(error));
}
pub(crate) proof fn part2_precinct_prelude_decoder_observed(
    before:Part1PacketPrecinctState,total:u64,row:Part2PacketSubbandExecution,
    style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,prepared:(Part1PacketPrecinctState,u64),
    response:Result<(),crate::DecodeError>,
)
    requires part2_precinct_tree_prelude(before,total,row,style,limits)==Ok(prepared),
        part2_precinct_contexts_result(before.states,before.contexts,row.decoders.len() as usize,
            row.across,row.maximum_zero,style,Ok((prepared.0.states,prepared.0.contexts))),
        part2_planning_capacity_result(part2_precinct_decoder_capacity_context(before,total,row,style),response),
    ensures part2_precinct_prelude_result(before,total,row,style,limits,
        match response {Err(error)=>Err(error),Ok(())=>Ok(prepared)}),
{
    reveal(part2_planning_capacity_result);
    let result=match response {Err(error)=>Err(error),Ok(())=>Ok(prepared)};
    let capacity=part2_precinct_decoder_capacity_context(before,total,row,style);
    part2_cold_pure(Ok(prepared));
    part2_cold_bind(|events|part2_planning_capacity_run(capacity,events),
        |_:(),tail|Some((Ok(prepared),tail)),response,result);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_planning_capacity_run(capacity,events),
        |_:(),tail|Some((Ok(prepared),tail))),result);
    part2_cold_bind(|events|part2_precinct_contexts_run(before.states,before.contexts,row.decoders.len() as usize,row.across,row.maximum_zero,style,events),
        |_: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
            part2_jpip_snapshot_bind(part2_planning_capacity_run(capacity,rest),|_:(),tail|Some((Ok(prepared),tail))),
        Ok((prepared.0.states,prepared.0.contexts)),result);
}
pub(crate) open spec fn part2_precinct_tree_context(prepared:(Part1PacketPrecinctState,u64),row:Part2PacketSubbandExecution,index:nat,zero:bool,inclusion:Option<Part1TagTree>,
    limits:&crate::ResourceLimits)->Part2PrecinctTreeContext {
    Part2PrecinctTreeContext {before:prepared.0,total:prepared.1,execution:row,index:index as usize,zero,inclusion,maximum:crate::limits::resource_tag_tree_node_limit(limits)}
}
pub(crate) open spec fn part2_precinct_finish_trees(before:Part1PacketPrecinctState,prepared:Part1PacketPrecinctState,row:Part2PacketSubbandExecution,
    inclusion:Part1TagTree,zero:Part1TagTree)->Part1PacketPrecinctState {
    Part1PacketPrecinctState {subbands:prepared.subbands.push(Part1PacketSubbandState {
        orientation:row.orientation,first_decoder:before.decoders.len() as usize,decoder_count:row.decoders.len() as usize,
        code_blocks_across:row.across,code_blocks_down:row.down,inclusion_tree:inclusion,zero_bitplane_tree:zero,
    }),..prepared}
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_state_rows(executions:Seq<Part2PacketSubbandExecution>,style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    index:nat,before:Part1PacketPrecinctState,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketPrecinctState>
    decreases if index<executions.len(){((executions.len()-index)*2+1) as nat}else{0nat},
{
    if index>=executions.len(){Some((Ok(before),events))}else{
        let row=executions[index as int];
        part2_jpip_snapshot_bind(part2_precinct_prelude_run(before,total,row,style,limits,events),
            |prepared:(Part1PacketPrecinctState,u64),rest|part2_jpip_snapshot_bind(
                part2_precinct_tree_run(part2_precinct_tree_context(prepared,row,index,false,None,limits),rest),
                |inclusion:Part1TagTree,tail|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,tail)))
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_state_after_inclusion(executions:Seq<Part2PacketSubbandExecution>,style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    index:nat,before:Part1PacketPrecinctState,total:u64,prepared:(Part1PacketPrecinctState,u64),inclusion:Part1TagTree,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketPrecinctState>
    decreases if index<executions.len(){((executions.len()-index)*2) as nat}else{0nat},
{
    if index>=executions.len(){Some((Err(part1_packet_header_error()),events))}else{
        let row=executions[index as int];
        part2_jpip_snapshot_bind(part2_precinct_tree_run(part2_precinct_tree_context(prepared,row,index,true,Some(inclusion),limits),events),
            |zero:Part1TagTree,rest|part2_precinct_state_rows(executions,style,limits,index+1,
                part2_precinct_finish_trees(before,prepared.0,row,inclusion,zero),prepared.1,rest))
    }
}
pub(crate) proof fn part2_precinct_state_rows_normal(executions:Seq<Part2PacketSubbandExecution>,style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    index:nat,before:Part1PacketPrecinctState,total:u64)
    ensures part2_cold_framed(|events|part2_precinct_state_rows(executions,style,limits,index,before,total,events),
        part2_precinct_initialization_run(executions,style,limits,index,before,total)),
    decreases if index<executions.len(){((executions.len()-index)*2+1) as nat}else{0nat},
{
    reveal_with_fuel(part2_precinct_state_rows,2);reveal_with_fuel(part2_precinct_state_after_inclusion,1);reveal_with_fuel(part2_precinct_initialization_run,1);
    let result=part2_precinct_initialization_run(executions,style,limits,index,before,total);
    if index>=executions.len(){part2_cold_pure::<Part1PacketPrecinctState>(result);}else{
        let row=executions[index as int];
        let prepared_result=part2_precinct_tree_prelude(before,total,row,style,limits);
        part2_precinct_prelude_normal(before,total,row,style,limits);
        match prepared_result {
            Err(_)=>{part2_cold_pure::<Part1PacketPrecinctState>(result);},
            Ok(prepared)=>{
                let context=part2_precinct_tree_context(prepared,row,index,false,None,limits);
                let inclusion=part1_tag_initial(row.across,row.down,crate::limits::resource_tag_tree_node_limit(limits));
                part2_precinct_tree_normal(context);
                if let Ok(value)=inclusion{
                    part2_precinct_after_inclusion_normal(executions,style,limits,index,before,total,prepared,value);
                    part2_decode_eta(|events|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,value,events),result);
                }
                part2_cold_bind(|events|part2_precinct_tree_run(context,events),
                    |inclusion:Part1TagTree,rest|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,rest),inclusion,result);
                part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_precinct_tree_run(context,events),
                    |inclusion:Part1TagTree,rest|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,rest)),result);
            },
        }
        part2_cold_bind(|events|part2_precinct_prelude_run(before,total,row,style,limits,events),
            |prepared:(Part1PacketPrecinctState,u64),rest|part2_jpip_snapshot_bind(
                part2_precinct_tree_run(part2_precinct_tree_context(prepared,row,index,false,None,limits),rest),
                |inclusion:Part1TagTree,tail|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,tail)),
            prepared_result,result);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_precinct_prelude_run(before,total,row,style,limits,events),
            |prepared:(Part1PacketPrecinctState,u64),rest|part2_jpip_snapshot_bind(
                part2_precinct_tree_run(part2_precinct_tree_context(prepared,row,index,false,None,limits),rest),
                |inclusion:Part1TagTree,tail|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,tail))),result);
    }
}
pub(crate) proof fn part2_precinct_after_inclusion_normal(executions:Seq<Part2PacketSubbandExecution>,style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    index:nat,before:Part1PacketPrecinctState,total:u64,prepared:(Part1PacketPrecinctState,u64),inclusion:Part1TagTree)
    requires index<executions.len(),part2_precinct_tree_prelude(before,total,executions[index as int],style,limits)==Ok(prepared),
        part1_tag_initial(executions[index as int].across,executions[index as int].down,crate::limits::resource_tag_tree_node_limit(limits))==Ok(inclusion),
    ensures part2_cold_framed(|events|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,events),
        part2_precinct_initialization_run(executions,style,limits,index,before,total)),
    decreases ((executions.len()-index)*2) as nat,
{
    reveal_with_fuel(part2_precinct_state_after_inclusion,2);reveal_with_fuel(part2_precinct_state_rows,1);reveal_with_fuel(part2_precinct_initialization_run,1);
    let row=executions[index as int];let context=part2_precinct_tree_context(prepared,row,index,true,Some(inclusion),limits);
    let result=part2_precinct_initialization_run(executions,style,limits,index,before,total);
    let zero=part1_tag_initial(row.across,row.down,crate::limits::resource_tag_tree_node_limit(limits));
    part2_precinct_tree_normal(context);
    if let Ok(value)=zero {
        let after=part2_precinct_finish_trees(before,prepared.0,row,inclusion,value);
        part2_precinct_state_rows_normal(executions,style,limits,index+1,after,prepared.1);
        part2_decode_eta(|events|part2_precinct_state_rows(executions,style,limits,index+1,after,prepared.1,events),result);
    }
    part2_cold_bind(|events|part2_precinct_tree_run(context,events),
        |zero:Part1TagTree,rest|part2_precinct_state_rows(executions,style,limits,index+1,part2_precinct_finish_trees(before,prepared.0,row,inclusion,zero),prepared.1,rest),zero,result);
}
pub(crate) open spec fn part2_precinct_initial(location:(u16,u8,u32))->Part1PacketPrecinctState {
    Part1PacketPrecinctState {component:location.0,resolution:location.1,precinct:location.2,
        states:Seq::empty(),contexts:Seq::empty(),decoders:Seq::empty(),subbands:Seq::empty()}
}
pub(crate) open spec fn part2_precinct_state_run(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketPrecinctState> {
    if executions.len()>3{Some((Err(part1_packet_header_error()),events))}else{
        part2_jpip_snapshot_bind(part2_precinct_capacity_run(Part2PrecinctCapacityContext {location:(component,resolution,precinct),style,executions},events),
            |_:(),rest|part2_precinct_state_rows(executions,style,limits,0,part2_precinct_initial((component,resolution,precinct)),0,rest))
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_state_result(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits,result:Result<Part1PacketPrecinctState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events),result)
}
pub(crate) proof fn part2_precinct_state_normal(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits)
    ensures part2_precinct_state_result(component,resolution,precinct,style,executions,limits,part2_precinct_from_executions(component,resolution,precinct,style,executions,limits)),
{
    reveal(part2_precinct_state_result);reveal(part2_precinct_capacity_result);
    let result=part2_precinct_from_executions(component,resolution,precinct,style,executions,limits);
    if executions.len()>3 {part2_cold_pure::<Part1PacketPrecinctState>(result);}else{
        let context=Part2PrecinctCapacityContext {location:(component,resolution,precinct),style,executions};
        let initial=part2_precinct_initial((component,resolution,precinct));
        part2_precinct_capacity_observed(context,Ok(()));part2_precinct_state_rows_normal(executions,style,limits,0,initial,0);
        part2_decode_eta(|events|part2_precinct_state_rows(executions,style,limits,0,initial,0,events),result);
        part2_cold_bind(|events|part2_precinct_capacity_run(context,events),
            |_:(),rest|part2_precinct_state_rows(executions,style,limits,0,initial,0,rest),Ok(()),result);
    }
}
pub(crate) proof fn part2_precinct_state_refused(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits)
    requires executions.len()<=3,part2_precinct_capacity_result(Part2PrecinctCapacityContext {location:(component,resolution,precinct),style,executions},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_precinct_state_result(component,resolution,precinct,style,executions,limits,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_precinct_state_result);reveal(part2_precinct_capacity_result);
    part2_cold_bind(|events|part2_precinct_capacity_run(Part2PrecinctCapacityContext {location:(component,resolution,precinct),style,executions},events),
        |_:(),rest|part2_precinct_state_rows(executions,style,limits,0,part2_precinct_initial((component,resolution,precinct)),0,rest),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_precinct_state_start(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires executions.len()<=3,part2_precinct_capacity_result(Part2PrecinctCapacityContext {location:(component,resolution,precinct),style,executions},Ok(())),
    ensures part2_cold_phase(|events|part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events),prefix,
        |events|part2_precinct_state_rows(executions,style,limits,0,part2_precinct_initial((component,resolution,precinct)),0,events)),
{
    reveal(part2_precinct_capacity_result);
    let context=Part2PrecinctCapacityContext {location:(component,resolution,precinct),style,executions};
    let prefix=part2_cold_witness(|events|part2_precinct_capacity_run(context,events),Ok(()));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_precinct_state_run(component,resolution,precinct,style,executions,limits,prefix+tail)
        ==part2_precinct_state_rows(executions,style,limits,0,part2_precinct_initial((component,resolution,precinct)),0,tail) by{
        part2_cold_prefix_at(|events|part2_precinct_capacity_run(context,events),prefix,Ok(()),tail);
    }
    prefix
}
pub(crate) proof fn part2_precinct_state_inclusion_step(executions:Seq<Part2PacketSubbandExecution>,style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    index:nat,before:Part1PacketPrecinctState,total:u64)
    requires index<executions.len(),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_precinct_state_rows(executions,style,limits,index,before,total,events)
        ==part2_jpip_snapshot_bind(part2_precinct_prelude_run(before,total,executions[index as int],style,limits,events),
            |prepared:(Part1PacketPrecinctState,u64),rest|part2_jpip_snapshot_bind(
                part2_precinct_tree_run(part2_precinct_tree_context(prepared,executions[index as int],index,false,None,limits),rest),
                |inclusion:Part1TagTree,tail|part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,tail))),
{reveal_with_fuel(part2_precinct_state_rows,2);reveal_with_fuel(part2_precinct_state_after_inclusion,1);}
pub(crate) proof fn part2_precinct_state_zero_step(executions:Seq<Part2PacketSubbandExecution>,style:crate::tier1::Tier1CodingStyle,limits:&crate::ResourceLimits,
    index:nat,before:Part1PacketPrecinctState,total:u64,prepared:(Part1PacketPrecinctState,u64),inclusion:Part1TagTree)
    requires index<executions.len(),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_precinct_state_after_inclusion(executions,style,limits,index,before,total,prepared,inclusion,events)
        ==part2_jpip_snapshot_bind(part2_precinct_tree_run(part2_precinct_tree_context(prepared,executions[index as int],index,true,Some(inclusion),limits),events),
            |zero:Part1TagTree,rest|part2_precinct_state_rows(executions,style,limits,index+1,
                part2_precinct_finish_trees(before,prepared.0,executions[index as int],inclusion,zero),prepared.1,rest)),
{reveal_with_fuel(part2_precinct_state_after_inclusion,2);reveal_with_fuel(part2_precinct_state_rows,1);}
pub(crate) proof fn part2_precinct_state_join(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits,
    root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketPrecinctState>,result:Result<Part1PacketPrecinctState,crate::DecodeError>)
    requires part2_cold_framed(root,result),forall|events| #[trigger] root(events)==part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events),
    ensures part2_precinct_state_result(component,resolution,precinct,style,executions,limits,result),
{
    reveal(part2_precinct_state_result);
    part2_cold_framed_extensional(root,|events|part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events),result);
}
pub(crate) proof fn part2_precinct_state_frames(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits,result:Result<Part1PacketPrecinctState,crate::DecodeError>)
    requires part2_precinct_state_result(component,resolution,precinct,style,executions,limits,result),
    ensures part2_cold_framed(|events|part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketPrecinctState>|
            (forall|events| #[trigger] other(events)==part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events))
            ==> #[trigger] part2_cold_framed(other,result),
{reveal(part2_precinct_state_result);part2_decode_eta(|events|part2_precinct_state_run(component,resolution,precinct,style,executions,limits,events),result);}
}
