use super::*;
verus! {

pub struct PrivatePrecinctInitialContext {
    pub across:u32,pub down:u32,pub maximum_zero:u16,
    pub style:crate::tier1::Tier1CodingStyle,
    pub decoders:Seq<PrivateHtDecoderState>,
    pub blocks:u64,pub work:u64,pub tag_nodes:u64,
}

pub enum PrivateOwnerCapacityContext {
    Blocks {geometry:crate::decode::SubbandGeometry,grid:[u32;4],clip:[u32;4],shape:[u32;2],
        style:crate::tier1::Tier1CodingStyle,allowed:bool,bound:u8,count:usize},
    BlockAppend {source:Seq<PrivateHtDecoderState>,next:PrivateHtDecoderState},
    PlacementAppend {source:Seq<crate::decode::ProgressionCodeBlockPlacement>,next:crate::decode::ProgressionCodeBlockPlacement},
    PrecinctSubband {source:PrivatePrecinctInitialContext},
    PreparedAppend {source:Seq<Part1AssemblyTile>,next:Part1AssemblyTile},
}

pub(crate) open spec fn private_owner_capacity_count(context:PrivateOwnerCapacityContext)->usize {
    match context{PrivateOwnerCapacityContext::Blocks{count,..}=>count,_=>1usize}
}

pub(crate) open spec fn private_owner_capacity_run(context:PrivateOwnerCapacityContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::PrivateOwnerCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=private_owner_capacity_count(context){None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}

pub(crate) open spec fn private_owner_capacity_result(context:PrivateOwnerCapacityContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_owner_capacity_run(context,events),result)
}

pub(crate) proof fn private_owner_capacity_observed(context:PrivateOwnerCapacityContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures private_owner_capacity_result(context,result),
{
    let prefix=seq![Part2JpipSnapshotEvent::PrivateOwnerCapacity {
        context,elements:private_owner_capacity_count(context),succeeded:result.is_ok(),
    }];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|private_owner_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|private_owner_capacity_run(context,events),prefix,result));
}

pub(crate) open spec fn private_decoder_initial_calls_run(context:PrivateHtInitialContext,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<PrivateHtDecoderState> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::PrivateDecoderInitial {context:actual,calls}=>if context!=actual{None}else{
            match private_ht_initial_run(context,calls){
                Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},
                None=>None,
            }
        },
        _=>None,
    }}
}

pub(crate) open spec fn private_decoder_initial_calls_result(context:PrivateHtInitialContext,result:Result<PrivateHtDecoderState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_decoder_initial_calls_run(context,events),result)
}

pub(crate) proof fn private_decoder_initial_calls_observed(context:PrivateHtInitialContext,result:Result<PrivateHtDecoderState,crate::DecodeError>)
    requires private_ht_initial_result(context,result),
    ensures private_decoder_initial_calls_result(context,result),
{
    let run=|tail|private_ht_initial_run(context,tail);
    let calls=choose|prefix:Seq<Part2Tier1StorageEvent>| #[trigger] part2_tier1_storage_prefix(run,prefix,result);
    part2_tier1_storage_at(run,calls,result,Seq::empty());
    let prefix=seq![Part2JpipSnapshotEvent::PrivateDecoderInitial{context,calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|private_decoder_initial_calls_run(context,prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|private_decoder_initial_calls_run(context,events),prefix,result));
}

pub(crate) open spec fn private_precinct_admit(context:PrivatePrecinctInitialContext)->Result<usize,crate::DecodeError> {
    let count=context.across as nat*context.down as nat;
    if context.across==0 || context.down==0 || context.maximum_zero==0 || context.maximum_zero>crate::tier1::MAX_TIER1_BITPLANES {
        Err(part1_packet_header_error())
    }else if count>u64::MAX{Err(part1_block_placement_error(true))}
    else if count>context.blocks {Err(crate::DecodeError::LimitExceeded {
        resource:crate::Resource::CodeBlocks,limit:context.blocks,actual:count as u64,
    })}
    else if count>context.work {Err(crate::DecodeError::LimitExceeded {
        resource:crate::Resource::WorkUnits,limit:context.work,actual:count as u64,
    })}
    else if count>usize::MAX{Err(part1_block_placement_error(true))}
    else if count!=context.decoders.len(){Err(part1_packet_header_error())}
    else{Ok(count as usize)}
}

pub(crate) open spec fn private_precinct_initial_state(context:PrivatePrecinctInitialContext,
    prepared:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),inclusion:Part1TagTree,zero:Part1TagTree)->PrivateHtPrecinctState {
    PrivateHtPrecinctState {logical:Part1PacketPrecinctState {
        component:0,resolution:0,precinct:0,states:prepared.0,contexts:prepared.1,
        decoders:context.decoders.map_values(|d:PrivateHtDecoderState|d.logical),
        subbands:seq![Part1PacketSubbandState {
            orientation:crate::tier1::SubbandOrientation::Ll,first_decoder:0,decoder_count:context.decoders.len() as usize,
            code_blocks_across:context.across,code_blocks_down:context.down,
            inclusion_tree:inclusion,zero_bitplane_tree:zero,
        }],
    },packed:context.decoders.map_values(|d:PrivateHtDecoderState|d.packed)}
}

pub(crate) open spec fn private_precinct_tree_run(context:PrivatePrecinctInitialContext,inclusion:bool,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Part1TagTree> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::PrivatePrecinctTree{context:actual,inclusion:side,calls}=>if actual!=context || side!=inclusion{None}else{
            match part2_tag_storage_run(context.across,context.down,context.tag_nodes,calls){
                Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None,
            }
        },
        _=>None,
    }}
}

pub(crate) open spec fn private_precinct_tree_result(context:PrivatePrecinctInitialContext,inclusion:bool,result:Result<Part1TagTree,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_precinct_tree_run(context,inclusion,events),result)
}

pub(crate) proof fn private_precinct_tree_observed(context:PrivatePrecinctInitialContext,inclusion:bool,result:Result<Part1TagTree,crate::DecodeError>)
    requires part1_tag_storage_result(context.across,context.down,context.tag_nodes,result),
    ensures private_precinct_tree_result(context,inclusion,result),
{
    let calls=part2_tag_storage_witness(context.across,context.down,context.tag_nodes,result);
    let prefix=seq![Part2JpipSnapshotEvent::PrivatePrecinctTree{context,inclusion,calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|private_precinct_tree_run(context,inclusion,prefix+tail)==Some((result,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
        assert(part2_tag_storage_run(context.across,context.down,context.tag_nodes,calls+Seq::empty())==Some((result,Seq::empty())));
        assert(calls+Seq::empty() =~= calls);
    }
    assert(part2_cold_prefix(|events|private_precinct_tree_run(context,inclusion,events),prefix,result));
}

pub(crate) open spec fn private_precinct_after_contexts(context:PrivatePrecinctInitialContext,
    prepared:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState> {
    part2_jpip_snapshot_bind(private_owner_capacity_run(PrivateOwnerCapacityContext::PrecinctSubband{source:context},events),
        |_:(),rest|private_precinct_after_capacity(context,prepared,rest))
}

pub(crate) open spec fn private_precinct_after_capacity(context:PrivatePrecinctInitialContext,
    prepared:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState> {
    part2_jpip_snapshot_bind(private_precinct_tree_run(context,true,events),
        |inclusion:Part1TagTree,rest|private_precinct_after_inclusion(context,prepared,inclusion,rest))
}

pub(crate) open spec fn private_precinct_after_inclusion(context:PrivatePrecinctInitialContext,
    prepared:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),inclusion:Part1TagTree,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState> {
    part2_jpip_snapshot_bind(private_precinct_tree_run(context,false,events),
        |zero:Part1TagTree,rest|Some((Ok(private_precinct_initial_state(context,prepared,inclusion,zero)),rest)))
}

pub(crate) open spec fn private_precinct_initial_run(context:PrivatePrecinctInitialContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateHtPrecinctState> {
    match private_precinct_admit(context){
        Err(error)=>Some((Err(error),events)),
        Ok(count)=>part2_jpip_snapshot_bind(
            part2_precinct_contexts_run(Seq::empty(),Seq::empty(),count,context.across,context.maximum_zero,context.style,events),
            |prepared:(Seq<Part1CodeBlockPacketState>,Seq<crate::packet::CodeBlockPacketContext>),rest|
                private_precinct_after_contexts(context,prepared,rest)),
    }
}

pub(crate) open spec fn private_precinct_initial_result(context:PrivatePrecinctInitialContext,result:Result<PrivateHtPrecinctState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|private_precinct_initial_run(context,events),result)
}

pub(crate) open spec fn private_precinct_initial_value(context:PrivatePrecinctInitialContext)->Result<PrivateHtPrecinctState,crate::DecodeError> {
    match private_precinct_admit(context){
        Err(error)=>Err(error),
        Ok(count)=>match part2_precinct_contexts(Seq::empty(),Seq::empty(),count,context.across,context.maximum_zero,context.style){
            Err(error)=>Err(error),Ok(prepared)=>match part1_tag_initial(context.across,context.down,context.tag_nodes){
                Err(error)=>Err(error),Ok(inclusion)=>match part1_tag_initial(context.across,context.down,context.tag_nodes){
                    Err(error)=>Err(error),Ok(zero)=>Ok(private_precinct_initial_state(context,prepared,inclusion,zero)),
                },
            },
        },
    }
}

pub(crate) proof fn private_precinct_initial_normal(context:PrivatePrecinctInitialContext)
    ensures private_precinct_initial_result(context,private_precinct_initial_value(context)),
{
    let result=private_precinct_initial_value(context);
    match private_precinct_admit(context){
        Err(_)=>{part2_cold_pure(result);},
        Ok(count)=>{
            let prepared=part2_precinct_contexts(Seq::empty(),Seq::empty(),count,context.across,context.maximum_zero,context.style);
            part2_precinct_contexts_normal(Seq::empty(),Seq::empty(),count,context.across,context.maximum_zero,context.style);
            reveal(part2_precinct_contexts_result);
            if let Ok(initial)=prepared{
                let tree=part1_tag_initial(context.across,context.down,context.tag_nodes);
                part2_tag_storage_normal(context.across,context.down,context.tag_nodes);
                private_precinct_tree_observed(context,true,tree);
                if let Ok(inclusion)=tree{
                    private_precinct_tree_observed(context,false,tree);
                    part2_cold_pure(result);
                    part2_cold_bind(|events|private_precinct_tree_run(context,false,events),
                        |zero,rest|Some((Ok(private_precinct_initial_state(context,initial,inclusion,zero)),rest)),tree,result);
                    part2_decode_eta(|events|private_precinct_after_inclusion(context,initial,inclusion,events),result);
                }
                part2_cold_bind(|events|private_precinct_tree_run(context,true,events),
                    |inclusion,rest|private_precinct_after_inclusion(context,initial,inclusion,rest),tree,result);
                private_owner_capacity_observed(PrivateOwnerCapacityContext::PrecinctSubband{source:context},Ok(()));
                part2_decode_eta(|events|private_precinct_after_capacity(context,initial,events),result);
                part2_cold_bind(|events|private_owner_capacity_run(PrivateOwnerCapacityContext::PrecinctSubband{source:context},events),
                    |_:(),rest|private_precinct_after_capacity(context,initial,rest),Ok(()),result);
                part2_decode_eta(|events|private_precinct_after_contexts(context,initial,events),result);
            }
            part2_cold_bind(|events|part2_precinct_contexts_run(Seq::empty(),Seq::empty(),count,context.across,context.maximum_zero,context.style,events),
                |initial,rest|private_precinct_after_contexts(context,initial,rest),prepared,result);
        },
    }
}

pub(crate) proof fn private_precinct_reference(context:PrivatePrecinctInitialContext,limits:&crate::ResourceLimits)
    requires context.blocks==crate::limits::resource_code_block_limit(limits),
        context.work==crate::limits::resource_work_limit(limits),context.tag_nodes==crate::limits::resource_tag_tree_node_limit(limits),
    ensures (match private_precinct_initial_value(context){Err(error)=>Err(error),Ok(value)=>Ok(value.logical)})==
        part2_precinct_from_executions(0,0,0,context.style,seq![Part2PacketSubbandExecution {
            orientation:crate::tier1::SubbandOrientation::Ll,across:context.across,down:context.down,maximum_zero:context.maximum_zero,
            decoders:context.decoders.map_values(|d:PrivateHtDecoderState|d.logical),
        }],limits),
{
    reveal_with_fuel(part2_precinct_initialization_run,2);
    reveal(part2_precinct_execution);reveal(private_precinct_initial_value);
    assert(context.decoders.map_values(|d:PrivateHtDecoderState|d.logical).len()==context.decoders.len());
}
}
