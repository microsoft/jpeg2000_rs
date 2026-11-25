use super::*;
verus! {

pub struct PrivateHtExecutionState {
    pub orientation:crate::tier1::SubbandOrientation,
    pub across:u32,pub down:u32,pub maximum_zero:u16,
    pub decoders:Seq<PrivateHtDecoderState>,
}

pub struct PrivateResolutionInitialContext {
    pub component:u16,
    pub resolution:u8,pub precinct:u32,pub style:crate::tier1::Tier1CodingStyle,
    pub executions:Seq<PrivateHtExecutionState>,pub limits:crate::ResourceLimits,
}

pub(crate) open spec fn private_execution_public(row:PrivateHtExecutionState)->Part2PacketSubbandExecution {
    Part2PacketSubbandExecution {
        orientation:row.orientation,across:row.across,down:row.down,maximum_zero:row.maximum_zero,
        decoders:row.decoders.map_values(|decoder:PrivateHtDecoderState|decoder.logical),
    }
}

pub(crate) open spec fn private_executions_public(rows:Seq<PrivateHtExecutionState>)->Seq<Part2PacketSubbandExecution> {
    rows.map_values(|row:PrivateHtExecutionState|private_execution_public(row))
}

pub(crate) open spec fn private_execution_wf(row:PrivateHtExecutionState)->bool {
    forall|i:int|0<=i<row.decoders.len() ==> #[trigger] private_ht_state_wf(row.decoders[i])
}

pub(crate) open spec fn private_precinct_decoder_states(before:PrivateHtPrecinctState)->Seq<PrivateHtDecoderState> {
    Seq::new(before.logical.decoders.len(),|i:int|PrivateHtDecoderState {
        logical:before.logical.decoders[i],packed:before.packed[i],
    })
}

pub(crate) open spec fn private_resolution_initial(context:PrivateResolutionInitialContext)->PrivateHtPrecinctState {
    PrivateHtPrecinctState {
        logical:part2_precinct_initial((context.component,context.resolution,context.precinct)),packed:Seq::empty(),
    }
}

pub(crate) open spec fn private_resolution_capacity(context:PrivateResolutionInitialContext)->Part2PrecinctCapacityContext {
    Part2PrecinctCapacityContext {
        location:(context.component,context.resolution,context.precinct),style:context.style,
        executions:private_executions_public(context.executions),
    }
}

pub(crate) open spec fn private_resolution_decoder_capacity(before:PrivateHtPrecinctState,row:PrivateHtExecutionState)->PrivateOwnerCapacityContext {
    PrivateOwnerCapacityContext::ResolutionDecoders {
        source:private_precinct_decoder_states(before),next:row.decoders,
    }
}

pub(crate) open spec fn private_resolution_decoder_run(before:PrivateHtPrecinctState,row:PrivateHtExecutionState,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if row.decoders.len()==0{Some((Ok(()),events))}
    else{private_owner_capacity_run(private_resolution_decoder_capacity(before,row),events)}
}

pub(crate) proof fn private_resolution_decoder_capacity_observed(before:PrivateHtPrecinctState,row:PrivateHtExecutionState,response:Result<(),crate::DecodeError>)
    requires if row.decoders.len()==0{response==Ok(())}else{private_owner_capacity_result(private_resolution_decoder_capacity(before,row),response)},
    ensures part2_cold_framed(|events|private_resolution_decoder_run(before,row,events),response),
{
    if row.decoders.len()==0{part2_cold_pure(response);}
    else{part2_cold_framed_extensional(|events|private_owner_capacity_run(private_resolution_decoder_capacity(before,row),events),
        |events|private_resolution_decoder_run(before,row,events),response);}
}

pub(crate) open spec fn private_resolution_row_finish(before:PrivateHtPrecinctState,prepared:Part1PacketPrecinctState,
    row:PrivateHtExecutionState,inclusion:Part1TagTree,zero:Part1TagTree)->PrivateHtPrecinctState {
    PrivateHtPrecinctState {
        logical:part2_precinct_finish_trees(before.logical,prepared,private_execution_public(row),inclusion,zero),
        packed:before.packed+row.decoders.map_values(|decoder:PrivateHtDecoderState|decoder.packed),
    }
}

pub(crate) open spec fn private_resolution_row_value(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64)->Result<(PrivateHtPrecinctState,u64),crate::DecodeError> {
    if index>=context.executions.len(){Err(part1_packet_header_error())}
    else{let row=context.executions[index as int];
        match part2_precinct_execution(before.logical,total,private_execution_public(row),context.style,&context.limits){
            Err(error)=>Err(error),
            Ok(after)=>Ok((PrivateHtPrecinctState {
                logical:after.0,packed:before.packed+row.decoders.map_values(|decoder:PrivateHtDecoderState|decoder.packed),
            },after.1)),
        }
    }
}

pub(crate) open spec fn private_resolution_execution_admit(
    across:u32,down:u32,maximum_zero:u16,decoder_count:nat,total:u64,limits:&crate::ResourceLimits,
)->Result<(usize,u64),crate::DecodeError> {
    let count=across as nat*down as nat;
    let next=total as nat+count;
    if across==0 || down==0 || maximum_zero==0 || maximum_zero>crate::tier1::MAX_TIER1_BITPLANES{
        Err(part1_packet_header_error())
    }else if count>u64::MAX || next>u64::MAX{Err(part1_block_placement_error(true))}
    else if next>crate::limits::resource_code_block_limit(limits){
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlocks,
            limit:crate::limits::resource_code_block_limit(limits),actual:next as u64})
    }else if next>crate::limits::resource_work_limit(limits){
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::WorkUnits,
            limit:crate::limits::resource_work_limit(limits),actual:next as u64})
    }else if count>usize::MAX{Err(part1_block_placement_error(true))}
    else if decoder_count!=count{Err(part1_packet_header_error())}
    else{Ok((count as usize,next as u64))}
}

pub(crate) open spec fn private_resolution_prepare(before:PrivateHtPrecinctState,row:PrivateHtExecutionState,
    contexts:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),total:u64)
    ->(Part1PacketPrecinctState,u64) {
    (Part1PacketPrecinctState {
        states:contexts.0,contexts:contexts.1,
        decoders:before.logical.decoders+private_execution_public(row).decoders,..before.logical
    },total)
}

pub(crate) open spec fn private_resolution_after_inclusion(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,prepared:(Part1PacketPrecinctState,u64),inclusion:Part1TagTree,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(PrivateHtPrecinctState,u64)> {
    let row=context.executions[index as int];
    part2_jpip_snapshot_bind(
        part2_precinct_tree_run(part2_precinct_tree_context(prepared,private_execution_public(row),index,true,Some(inclusion),&context.limits),events),
        |zero:Part1TagTree,rest|Some((Ok((private_resolution_row_finish(before,prepared.0,row,inclusion,zero),prepared.1)),rest)))
}

pub(crate) open spec fn private_resolution_after_decoders(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,prepared:(Part1PacketPrecinctState,u64),
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(PrivateHtPrecinctState,u64)> {
    let row=context.executions[index as int];
    part2_jpip_snapshot_bind(
        part2_precinct_tree_run(part2_precinct_tree_context(prepared,private_execution_public(row),index,false,None,&context.limits),events),
        |inclusion:Part1TagTree,rest|private_resolution_after_inclusion(context,index,before,prepared,inclusion,rest))
}

pub(crate) open spec fn private_resolution_after_contexts(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,prepared:(Part1PacketPrecinctState,u64),
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(PrivateHtPrecinctState,u64)> {
    part2_jpip_snapshot_bind(private_resolution_decoder_run(before,context.executions[index as int],events),
        |_:(),rest|private_resolution_after_decoders(context,index,before,prepared,rest))
}

pub(crate) open spec fn private_resolution_row_run(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<(PrivateHtPrecinctState,u64)> {
    if index>=context.executions.len(){Some((Err(part1_packet_header_error()),events))}
    else{let row=context.executions[index as int];
        match private_resolution_execution_admit(row.across,row.down,row.maximum_zero,row.decoders.len(),total,&context.limits){
            Err(error)=>Some((Err(error),events)),
            Ok((count,next))=>part2_jpip_snapshot_bind(
                part2_precinct_contexts_run(before.logical.states,before.logical.contexts,count,
                    row.across,row.maximum_zero,context.style,events),
                |contexts: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
                    private_resolution_after_contexts(context,index,before,private_resolution_prepare(before,row,contexts,next),rest)),
        }
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_resolution_rows_run(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState>
    decreases context.executions.len()-index,
{
    if index>=context.executions.len(){Some((Ok(before),events))}
    else{part2_jpip_snapshot_bind(private_resolution_row_run(context,index,before,total,events),
        |after:(PrivateHtPrecinctState,u64),rest|private_resolution_rows_run(context,index+1,after.0,after.1,rest))}
}

#[verifier::opaque]
pub(crate) open spec fn private_resolution_rows_value(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64)->Result<PrivateHtPrecinctState,crate::DecodeError>
    decreases context.executions.len()-index,
{
    if index>=context.executions.len(){Ok(before)}
    else{match private_resolution_row_value(context,index,before,total){
        Err(error)=>Err(error),Ok(after)=>private_resolution_rows_value(context,index+1,after.0,after.1),
    }}
}

pub(crate) open spec fn private_resolution_initial_run(context:PrivateResolutionInitialContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState> {
    if context.executions.len()>3{Some((Err(part1_packet_header_error()),events))}
    else{part2_jpip_snapshot_bind(part2_precinct_capacity_run(private_resolution_capacity(context),events),
        |_:(),rest|private_resolution_rows_run(context,0,private_resolution_initial(context),0,rest))}
}

pub(crate) open spec fn private_resolution_initial_value(context:PrivateResolutionInitialContext)->Result<PrivateHtPrecinctState,crate::DecodeError> {
    if context.executions.len()>3{Err(part1_packet_header_error())}
    else{private_resolution_rows_value(context,0,private_resolution_initial(context),0)}
}

pub(crate) open spec fn private_resolution_initial_result(context:PrivateResolutionInitialContext,
    result:Result<PrivateHtPrecinctState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_resolution_initial_run(context,events),result)
}

pub(crate) proof fn private_resolution_rows_reference(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64)
    ensures match private_resolution_rows_value(context,index,before,total){
        Err(error)=>Err(error),Ok(value)=>Ok(value.logical),
    }==part2_precinct_initialization_run(private_executions_public(context.executions),context.style,&context.limits,index,before.logical,total),
    decreases context.executions.len()-index,
{
    reveal_with_fuel(private_resolution_rows_value,1);
    reveal_with_fuel(part2_precinct_initialization_run,1);
    if index<context.executions.len(){
        if let Ok(after)=private_resolution_row_value(context,index,before,total){
            private_resolution_rows_reference(context,index+1,after.0,after.1);
        }
    }
}

pub(crate) proof fn private_resolution_initial_reference(context:PrivateResolutionInitialContext)
    ensures match private_resolution_initial_value(context){
        Err(error)=>Err(error),Ok(value)=>Ok(value.logical),
    }==part2_precinct_from_executions(context.component,context.resolution,context.precinct,context.style,private_executions_public(context.executions),&context.limits),
{
    if context.executions.len()<=3{
        private_resolution_rows_reference(context,0,private_resolution_initial(context),0);
    }
}

pub(crate) proof fn private_resolution_row_fields(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,after:(PrivateHtPrecinctState,u64))
    requires index<context.executions.len(),private_precinct_wf(before),
        private_execution_wf(context.executions[index as int]),
        private_resolution_row_value(context,index,before,total)==Ok(after),
    ensures private_precinct_wf(after.0),
        after.0.logical.component==before.logical.component,
        after.0.logical.resolution==before.logical.resolution,
        after.0.logical.precinct==before.logical.precinct,
{
    let row=context.executions[index as int];
    let old_len=before.logical.decoders.len();
    assert forall|i:int|0<=i<after.0.logical.decoders.len() implies #[trigger] private_ht_state_wf(
        PrivateHtDecoderState {logical:after.0.logical.decoders[i],packed:after.0.packed[i]}) by {
        if i<old_len{
            assert(private_ht_state_wf(PrivateHtDecoderState {logical:before.logical.decoders[i],packed:before.packed[i]}));
        }else{
            assert(private_ht_state_wf(row.decoders[i-old_len]));
        }
    }
}

pub(crate) proof fn private_resolution_rows_fields(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64)
    requires private_precinct_wf(before),
        forall|i:int|index<=i<context.executions.len() ==> #[trigger] private_execution_wf(context.executions[i]),
    ensures match private_resolution_rows_value(context,index,before,total){
        Err(_)=>true,Ok(after)=>private_precinct_wf(after)
            && after.logical.component==before.logical.component
            && after.logical.resolution==before.logical.resolution
            && after.logical.precinct==before.logical.precinct,
    },
    decreases context.executions.len()-index,
{
    reveal_with_fuel(private_resolution_rows_value,1);
    if index<context.executions.len(){
        if let Ok(after)=private_resolution_row_value(context,index,before,total){
            private_resolution_row_fields(context,index,before,total,after);
            private_resolution_rows_fields(context,index+1,after.0,after.1);
        }
    }
}

pub(crate) proof fn private_resolution_initial_fields(context:PrivateResolutionInitialContext)
    requires forall|i:int|0<=i<context.executions.len() ==> #[trigger] private_execution_wf(context.executions[i]),
    ensures match private_resolution_initial_value(context){
        Err(_)=>true,Ok(after)=>private_precinct_wf(after) && after.logical.component==context.component
            && after.logical.resolution==context.resolution
            && after.logical.precinct==context.precinct,
    },
{
    if context.executions.len()<=3{
        private_resolution_rows_fields(context,0,private_resolution_initial(context),0);
    }
}

pub(crate) proof fn private_resolution_row_contexts_error(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,error:crate::DecodeError)
    requires index<context.executions.len(),
        private_resolution_execution_admit(context.executions[index as int].across,context.executions[index as int].down,
            context.executions[index as int].maximum_zero,context.executions[index as int].decoders.len(),total,&context.limits).is_ok(),
        part2_precinct_contexts_result(before.logical.states,before.logical.contexts,context.executions[index as int].decoders.len() as usize,
            context.executions[index as int].across,context.executions[index as int].maximum_zero,context.style,Err(error)),
    ensures part2_cold_framed(|events|private_resolution_row_run(context,index,before,total,events),Err(error)),
{
    let row=context.executions[index as int];
    let admitted=private_resolution_execution_admit(row.across,row.down,row.maximum_zero,row.decoders.len(),total,&context.limits).get_Ok_0();
    part2_cold_bind(|events|part2_precinct_contexts_run(before.logical.states,before.logical.contexts,row.decoders.len() as usize,
        row.across,row.maximum_zero,context.style,events),
        |contexts: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
            private_resolution_after_contexts(context,index,before,private_resolution_prepare(before,row,contexts,admitted.1),rest),Err(error),Err(error));
}

pub(crate) proof fn private_resolution_row_after_observed(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,prepared:(Part1PacketPrecinctState,u64),
    result:Result<(PrivateHtPrecinctState,u64),crate::DecodeError>)
    requires index<context.executions.len(),
        part2_precinct_tree_prelude(before.logical,total,private_execution_public(context.executions[index as int]),context.style,&context.limits)==Ok(prepared),
        part2_precinct_contexts_result(before.logical.states,before.logical.contexts,context.executions[index as int].decoders.len() as usize,
            context.executions[index as int].across,context.executions[index as int].maximum_zero,context.style,Ok((prepared.0.states,prepared.0.contexts))),
        part2_cold_framed(|events|private_resolution_after_contexts(context,index,before,prepared,events),result),
    ensures part2_cold_framed(|events|private_resolution_row_run(context,index,before,total,events),result),
{
    let row=context.executions[index as int];
    part2_decode_eta(|events|private_resolution_after_contexts(context,index,before,prepared,events),result);
    part2_cold_bind(|events|part2_precinct_contexts_run(before.logical.states,before.logical.contexts,row.decoders.len() as usize,
        row.across,row.maximum_zero,context.style,events),
        |contexts: (Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
            private_resolution_after_contexts(context,index,before,private_resolution_prepare(before,row,contexts,prepared.1),rest),
        Ok((prepared.0.states,prepared.0.contexts)),result);
}

pub(crate) proof fn private_resolution_decoder_observed(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,prepared:(Part1PacketPrecinctState,u64),response:Result<(),crate::DecodeError>,
    result:Result<(PrivateHtPrecinctState,u64),crate::DecodeError>)
    requires index<context.executions.len(),
        part2_cold_framed(|events|private_resolution_decoder_run(before,context.executions[index as int],events),response),
        match response {
            Err(error)=>result==Err(error),
            Ok(())=>part2_cold_framed(|events|private_resolution_after_decoders(context,index,before,prepared,events),result),
        },
    ensures part2_cold_framed(|events|private_resolution_after_contexts(context,index,before,prepared,events),result),
{
    if response.is_ok(){part2_decode_eta(|events|private_resolution_after_decoders(context,index,before,prepared,events),result);}
    part2_cold_bind(|events|private_resolution_decoder_run(before,context.executions[index as int],events),
        |_:(),rest|private_resolution_after_decoders(context,index,before,prepared,rest),response,result);
}

pub(crate) proof fn private_resolution_inclusion_observed(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,prepared:(Part1PacketPrecinctState,u64),inclusion:Result<Part1TagTree,crate::DecodeError>,
    result:Result<(PrivateHtPrecinctState,u64),crate::DecodeError>)
    requires index<context.executions.len(),
        part2_cold_framed(|events|part2_precinct_tree_run(part2_precinct_tree_context(prepared,
            private_execution_public(context.executions[index as int]),index,false,None,&context.limits),events),inclusion),
        match inclusion {
            Err(error)=>result==Err(error),
            Ok(tree)=>part2_cold_framed(|events|private_resolution_after_inclusion(context,index,before,prepared,tree,events),result),
        },
    ensures part2_cold_framed(|events|private_resolution_after_decoders(context,index,before,prepared,events),result),
{
    if let Ok(tree)=inclusion{
        part2_decode_eta(|events|private_resolution_after_inclusion(context,index,before,prepared,tree,events),result);
    }
    part2_cold_bind(|events|part2_precinct_tree_run(part2_precinct_tree_context(prepared,
        private_execution_public(context.executions[index as int]),index,false,None,&context.limits),events),
        |tree,rest|private_resolution_after_inclusion(context,index,before,prepared,tree,rest),inclusion,result);
}

pub(crate) proof fn private_resolution_zero_observed(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,prepared:(Part1PacketPrecinctState,u64),inclusion:Part1TagTree,
    zero:Result<Part1TagTree,crate::DecodeError>)
    requires index<context.executions.len(),
        part2_cold_framed(|events|part2_precinct_tree_run(part2_precinct_tree_context(prepared,
            private_execution_public(context.executions[index as int]),index,true,Some(inclusion),&context.limits),events),zero),
    ensures part2_cold_framed(|events|private_resolution_after_inclusion(context,index,before,prepared,inclusion,events),
        match zero{Err(error)=>Err(error),Ok(tree)=>Ok((private_resolution_row_finish(
            before,prepared.0,context.executions[index as int],inclusion,tree),prepared.1))}),
{
    let result=match zero{Err(error)=>Err(error),Ok(tree)=>Ok((private_resolution_row_finish(
        before,prepared.0,context.executions[index as int],inclusion,tree),prepared.1))};
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_precinct_tree_run(part2_precinct_tree_context(prepared,
        private_execution_public(context.executions[index as int]),index,true,Some(inclusion),&context.limits),events),
        |tree,rest|Some((Ok((private_resolution_row_finish(before,prepared.0,
            context.executions[index as int],inclusion,tree),prepared.1)),rest)),zero,result);
}

pub(crate) proof fn private_resolution_row_value_from_trees(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,count:usize,next:u64,
    contexts:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),inclusion:Part1TagTree,zero:Part1TagTree)
    requires index<context.executions.len(),
        private_resolution_execution_admit(context.executions[index as int].across,context.executions[index as int].down,
            context.executions[index as int].maximum_zero,context.executions[index as int].decoders.len(),total,&context.limits)==Ok((count,next)),
        part2_precinct_contexts(before.logical.states,before.logical.contexts,count,context.executions[index as int].across,
            context.executions[index as int].maximum_zero,context.style)==Ok(contexts),
        part1_tag_initial(context.executions[index as int].across,context.executions[index as int].down,
            crate::limits::resource_tag_tree_node_limit(&context.limits))==Ok(inclusion),
        part1_tag_initial(context.executions[index as int].across,context.executions[index as int].down,
            crate::limits::resource_tag_tree_node_limit(&context.limits))==Ok(zero),
    ensures private_resolution_row_value(context,index,before,total)==Ok((private_resolution_row_finish(before,
        private_resolution_prepare(before,context.executions[index as int],contexts,next).0,
        context.executions[index as int],inclusion,zero),next)),
{}

pub(crate) proof fn private_resolution_row_normal(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64)
    ensures part2_cold_framed(|events|private_resolution_row_run(context,index,before,total,events),
        private_resolution_row_value(context,index,before,total)),
{
    let result=private_resolution_row_value(context,index,before,total);
    if index>=context.executions.len(){part2_cold_pure(result);}
    else{
        let row=context.executions[index as int];
        match private_resolution_execution_admit(row.across,row.down,row.maximum_zero,row.decoders.len(),total,&context.limits){
            Err(_)=>part2_cold_pure(result),
            Ok((count,next))=>{
                part2_precinct_contexts_normal(before.logical.states,before.logical.contexts,row.decoders.len() as usize,
                    row.across,row.maximum_zero,context.style);
                let contexts=part2_precinct_contexts(before.logical.states,before.logical.contexts,count,row.across,row.maximum_zero,context.style);
                match contexts {
                    Err(error)=>private_resolution_row_contexts_error(context,index,before,total,error),
                    Ok(values)=>{
                        let prepared=private_resolution_prepare(before,row,values,next);
                        if row.decoders.len()==0{part2_cold_pure::<()>(Ok(()));}
                        else{private_owner_capacity_observed(private_resolution_decoder_capacity(before,row),Ok(()));}
                        private_resolution_decoder_capacity_observed(before,row,Ok(()));
                        let inclusion=part1_tag_initial(row.across,row.down,crate::limits::resource_tag_tree_node_limit(&context.limits));
                        part2_precinct_tree_normal(part2_precinct_tree_context(prepared,private_execution_public(row),index,false,None,&context.limits));
                        if let Ok(tree)=inclusion {
                            let zero=part1_tag_initial(row.across,row.down,crate::limits::resource_tag_tree_node_limit(&context.limits));
                            assert(zero==Ok(tree));
                            private_resolution_row_value_from_trees(context,index,before,total,count,next,values,tree,tree);
                            part2_precinct_tree_normal(part2_precinct_tree_context(prepared,private_execution_public(row),index,true,Some(tree),&context.limits));
                            private_resolution_zero_observed(context,index,before,prepared,tree,zero);
                        }
                        private_resolution_inclusion_observed(context,index,before,prepared,inclusion,result);
                        private_resolution_decoder_observed(context,index,before,prepared,Ok(()),result);
                        private_resolution_row_after_observed(context,index,before,total,prepared,result);
                    },
                }
            },
        }
    }
}

pub(crate) proof fn private_resolution_rows_normal(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64)
    ensures part2_cold_framed(|events|private_resolution_rows_run(context,index,before,total,events),
        private_resolution_rows_value(context,index,before,total)),
    decreases context.executions.len()-index,
{
    reveal_with_fuel(private_resolution_rows_run,1);reveal_with_fuel(private_resolution_rows_value,1);
    let result=private_resolution_rows_value(context,index,before,total);
    if index>=context.executions.len(){part2_cold_pure(result);}
    else{
        let row=private_resolution_row_value(context,index,before,total);
        private_resolution_row_normal(context,index,before,total);
        if let Ok(after)=row{
            private_resolution_rows_normal(context,index+1,after.0,after.1);
            part2_decode_eta(|events|private_resolution_rows_run(context,index+1,after.0,after.1,events),result);
        }
        part2_cold_bind(|events|private_resolution_row_run(context,index,before,total,events),
            |after:(PrivateHtPrecinctState,u64),rest|private_resolution_rows_run(context,index+1,after.0,after.1,rest),row,result);
    }
}

pub(crate) proof fn private_resolution_initial_normal(context:PrivateResolutionInitialContext)
    requires context.executions.len()<=usize::MAX,
    ensures private_resolution_initial_result(context,private_resolution_initial_value(context)),
{
    let result=private_resolution_initial_value(context);
    if context.executions.len()>3{part2_cold_pure(result);}
    else{
        reveal(part2_precinct_capacity_result);
        part2_precinct_capacity_observed(private_resolution_capacity(context),Ok(()));
        private_resolution_rows_normal(context,0,private_resolution_initial(context),0);
        part2_decode_eta(|events|private_resolution_rows_run(context,0,private_resolution_initial(context),0,events),result);
        part2_cold_bind(|events|part2_precinct_capacity_run(private_resolution_capacity(context),events),
            |_:(),rest|private_resolution_rows_run(context,0,private_resolution_initial(context),0,rest),Ok(()),result);
    }
}

pub(crate) open spec fn private_resolution_prefix(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail| #[trigger] private_resolution_initial_run(context,prefix+tail)
        ==private_resolution_rows_run(context,index,before,total,tail)
}

pub(crate) proof fn private_resolution_row_error(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires index<context.executions.len(),private_resolution_prefix(context,index,before,total,prefix),
        private_resolution_initial_value(context)==private_resolution_rows_value(context,index,before,total),
        part2_cold_framed(|events|private_resolution_row_run(context,index,before,total,events),Err(error)),
        error!=crate::DecodeError::AllocationFailed ==> private_resolution_row_value(context,index,before,total)==Err(error),
    ensures private_resolution_initial_result(context,Err(error)),
        error!=crate::DecodeError::AllocationFailed ==> private_resolution_initial_value(context)==Err(error),
{
    assert forall|tail|private_resolution_initial_run(context,prefix+tail)==part2_jpip_snapshot_bind(
        private_resolution_row_run(context,index,before,total,tail),
        |after:(PrivateHtPrecinctState,u64),rest|private_resolution_rows_run(context,index+1,after.0,after.1,rest)) by {
        assert(private_resolution_initial_run(context,prefix+tail)==private_resolution_rows_run(context,index,before,total,tail));
        reveal_with_fuel(private_resolution_rows_run,1);
    }
    part2_decode_prefix_error(|events|private_resolution_initial_run(context,events),
        |events|private_resolution_row_run(context,index,before,total,events),
        |after:(PrivateHtPrecinctState,u64),rest|private_resolution_rows_run(context,index+1,after.0,after.1,rest),prefix,error);
    reveal_with_fuel(private_resolution_rows_value,1);
}

pub(crate) proof fn private_resolution_scalar_error(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,prefix:Seq<Part2JpipSnapshotEvent>,error:crate::DecodeError)
    requires index<context.executions.len(),private_resolution_prefix(context,index,before,total,prefix),
        private_resolution_initial_value(context)==private_resolution_rows_value(context,index,before,total),
        private_resolution_execution_admit(context.executions[index as int].across,context.executions[index as int].down,
            context.executions[index as int].maximum_zero,context.executions[index as int].decoders.len(),total,&context.limits)==Err(error),
    ensures private_resolution_initial_result(context,Err(error)),
        private_resolution_initial_value(context)==Err(error),
{
    part2_cold_pure::<(PrivateHtPrecinctState,u64)>(Err(error));
    private_resolution_row_error(context,index,before,total,prefix,error);
}

pub(crate) proof fn private_resolution_row_advance(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,prefix:Seq<Part2JpipSnapshotEvent>,after:(PrivateHtPrecinctState,u64))
    ->(extended:Seq<Part2JpipSnapshotEvent>)
    requires index<context.executions.len(),private_resolution_prefix(context,index,before,total,prefix),
        private_resolution_initial_value(context)==private_resolution_rows_value(context,index,before,total),
        part2_cold_framed(|events|private_resolution_row_run(context,index,before,total,events),Ok(after)),
        private_resolution_row_value(context,index,before,total)==Ok(after),
    ensures private_resolution_prefix(context,index+1,after.0,after.1,extended),
        private_resolution_initial_value(context)==private_resolution_rows_value(context,index+1,after.0,after.1),
{
    assert forall|tail|private_resolution_initial_run(context,prefix+tail)==part2_jpip_snapshot_bind(
        private_resolution_row_run(context,index,before,total,tail),
        |next:(PrivateHtPrecinctState,u64),rest|private_resolution_rows_run(context,index+1,next.0,next.1,rest)) by {
        assert(private_resolution_initial_run(context,prefix+tail)==private_resolution_rows_run(context,index,before,total,tail));
        reveal_with_fuel(private_resolution_rows_run,1);
    }
    reveal_with_fuel(private_resolution_rows_value,1);
    part2_decode_prefix_advance(|events|private_resolution_initial_run(context,events),
        |events|private_resolution_row_run(context,index,before,total,events),
        |next:(PrivateHtPrecinctState,u64),rest|private_resolution_rows_run(context,index+1,next.0,next.1,rest),prefix,after)
}

pub(crate) proof fn private_resolution_prefix_finish(context:PrivateResolutionInitialContext,index:nat,
    before:PrivateHtPrecinctState,total:u64,prefix:Seq<Part2JpipSnapshotEvent>)
    requires index>=context.executions.len(),private_resolution_prefix(context,index,before,total,prefix),
    ensures private_resolution_initial_result(context,Ok(before)),
{
    assert forall|tail|private_resolution_initial_run(context,prefix+tail)==Some((Ok(before),tail)) by {
        assert(private_resolution_initial_run(context,prefix+tail)==private_resolution_rows_run(context,index,before,total,tail));
        reveal_with_fuel(private_resolution_rows_run,1);
    }
    assert(part2_cold_prefix(|events|private_resolution_initial_run(context,events),prefix,Ok(before)));
}

}
