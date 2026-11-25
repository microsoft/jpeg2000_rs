use super::*;
verus! {

pub struct PrivateResolutionTileExecution {
    pub precincts:Seq<PrivateHtPrecinctState>,
    pub progress:Part1TilePacketProgress,
}

pub type PrivateResolutionTileEffect=(Result<(),crate::DecodeError>,PrivateResolutionTileExecution);
pub type PrivateResolutionDecodeEffect=(Result<crate::packet::TilePacketDecode,crate::DecodeError>,Seq<PrivateHtPrecinctState>);

pub(crate) open spec fn private_precincts_logical(values:Seq<PrivateHtPrecinctState>)->Seq<Part1PacketPrecinctState> {
    values.map_values(|value:PrivateHtPrecinctState|value.logical)
}

pub(crate) open spec fn private_resolution_tile_logical(value:PrivateResolutionTileExecution)->Part1TilePacketExecution {
    Part1TilePacketExecution {precincts:private_precincts_logical(value.precincts),progress:value.progress}
}

pub(crate) open spec fn private_resolution_tile_wf(value:PrivateResolutionTileExecution)->bool {
    value.progress.packed_offset==0
        && forall|i:int|0<=i<value.precincts.len() ==> #[trigger] private_precinct_wf(value.precincts[i])
}

pub(crate) open spec fn private_resolution_tile_parameters(params:Part1TilePacketParameters)->bool {
    params.parts.len()==1 && params.grid.components==1 && params.grid.component_resolutions.len()==1
        && (match params.parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false})
        && (match params.parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false})
        && params.input.packed==seq![Seq::<u8>::empty()]
        && (params.selection.is_none() || params.selection==Some(params.grid.component_resolutions))
}

pub(crate) open spec fn private_resolution_packet_context(params:Part1TilePacketParameters,
    before:PrivateResolutionTileExecution,state:Part1TilePacketExecution,part:Part2OwnedTilePart,
    coordinate:crate::packet::PacketCoordinate,index:usize)->PrivatePrecinctPacketContext {
    PrivatePrecinctPacketContext {
        before:PrivateHtPrecinctState {
            logical:part1_precinct_context_layer(before.precincts[index as int].logical,coordinate.layer),
            packed:before.precincts[index as int].packed,
        },part,offset:state.progress.offset,sequence:(state.progress.packets&65535u64) as u16,
        caps:(params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work),
    }
}

pub(crate) open spec fn private_resolution_packet_finish(before:PrivateResolutionTileExecution,state:Part1TilePacketExecution,
    index:usize,seen:usize,packet:PrivatePrecinctPacketEffect)->PrivateResolutionTileEffect {
    let finished=part2_plane_tile_packet_finish(state,index,seen,None,(packet.0,packet.1.logical));
    (finished.0,PrivateResolutionTileExecution {
        precincts:before.precincts.update(index as int,packet.1),progress:finished.1.progress,
    })
}

pub(crate) open spec fn private_resolution_packet_run(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateResolutionTileEffect> {
    match part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>Some((Ok((result.0,PrivateResolutionTileExecution {
            precincts:before.precincts,progress:result.1.progress,
        })),calls)),
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>{
            if expected.is_some(){None}else{
                part2_tier1_storage_bind(private_precinct_packet_run(
                    private_resolution_packet_context(params,before,state,part,coordinate,index),calls),
                    |packet,rest|Some((Ok(private_resolution_packet_finish(before,state,index,seen,packet)),rest)))
            }
        },
    }
}

pub(crate) open spec fn private_resolution_packet_value(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate)->PrivateResolutionTileEffect {
    match part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>(result.0,PrivateResolutionTileExecution {
            precincts:before.precincts,progress:result.1.progress,
        }),
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>{
            if expected.is_some(){(Err(part1_packet_reader_error(state.progress.offset,crate::MalformedKind::InvalidPacketHeader)),before)}
            else{private_resolution_packet_finish(before,state,index,seen,private_precinct_packet_value(
                private_resolution_packet_context(params,before,state,part,coordinate,index)))}
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_resolution_tile_run(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateResolutionTileEffect>
    decreases before.progress.remaining_packets*2+1,
{
    match part2_plane_tile_run_admit(params,private_resolution_tile_logical(before)){
        Part2PlaneTileStep::Return(result)=>Some((Ok((result.0,PrivateResolutionTileExecution {
            precincts:before.precincts,progress:result.1.progress,
        })),calls)),
        Part2PlaneTileStep::Continue(after)=>if after.progress.remaining_packets<before.progress.remaining_packets {
            private_resolution_tile_run(params,PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress},calls)
        }else{None},
        Part2PlaneTileStep::Packet(coordinate,after)=>part2_tier1_storage_bind(
            private_resolution_packet_run(params,PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress},coordinate,calls),
            |packet,rest|private_resolution_tile_after_iteration(params,before.progress.remaining_packets,packet,rest)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_resolution_tile_after_iteration(params:Part1TilePacketParameters,budget:u64,
    packet:PrivateResolutionTileEffect,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateResolutionTileEffect>
    decreases budget*2,
{
    match packet.0{Err(_)=>Some((Ok(packet),calls)),Ok(())=>if packet.1.progress.remaining_packets<budget {
        private_resolution_tile_run(params,packet.1,calls)
    }else{None}}
}

#[verifier::opaque]
pub(crate) open spec fn private_resolution_tile_value(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution)->PrivateResolutionTileEffect
    decreases before.progress.remaining_packets,
{
    match part2_plane_tile_run_admit(params,private_resolution_tile_logical(before)){
        Part2PlaneTileStep::Return(result)=>(result.0,PrivateResolutionTileExecution {
            precincts:before.precincts,progress:result.1.progress,
        }),
        Part2PlaneTileStep::Continue(after)=>private_resolution_tile_value(params,
            PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress}),
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            let packet=private_resolution_packet_value(params,
                PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress},coordinate);
            match packet.0{Err(_)=>packet,Ok(())=>private_resolution_tile_value(params,packet.1)}
        },
    }
}

pub(crate) open spec fn private_resolution_packet_result(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate,result:PrivateResolutionTileEffect)->bool {
    part2_tier1_storage_framed(|calls|private_resolution_packet_run(params,before,coordinate,calls),Ok(result))
}

pub(crate) open spec fn private_resolution_tile_result(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    result:PrivateResolutionTileEffect)->bool {
    part2_tier1_storage_framed(|calls|private_resolution_tile_run(params,before,calls),Ok(result))
}

pub(crate) proof fn private_resolution_admission_fields(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate)
    requires private_resolution_tile_parameters(params),private_resolution_tile_wf(before),
    ensures match part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>result.1.precincts==private_precincts_logical(before.precincts)
            && result.1.progress.packed_offset==0,
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>
            index<before.precincts.len() && expected.is_none() && state.progress.packed_offset==0
            && state.precincts==private_precincts_logical(before.precincts)
            && part==params.parts[0] && state.progress.current_tile_part==0
            && coordinate.component==0
            && coordinate.resolution<params.grid.component_resolutions[0],
    },
{}

pub(crate) proof fn private_resolution_tile_step_fields(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution)
    requires private_resolution_tile_parameters(params),private_resolution_tile_wf(before),
    ensures match part2_plane_tile_run_admit(params,private_resolution_tile_logical(before)){
        Part2PlaneTileStep::Return(result)=>result.1.progress.packed_offset==0,
        Part2PlaneTileStep::Continue(after)=>after.progress.packed_offset==0
            && after.progress.remaining_packets<before.progress.remaining_packets,
        Part2PlaneTileStep::Packet(_,after)=>after.progress.packed_offset==0
            && after.progress.remaining_packets<before.progress.remaining_packets,
    },
{
    reveal_with_fuel(part1_tile_boundary_scan,2);
}

pub(crate) proof fn private_resolution_layer_fields(before:PrivateHtPrecinctState,layer:u16)
    requires private_precinct_wf(before),
    ensures private_precinct_wf(PrivateHtPrecinctState {logical:part1_precinct_context_layer(before.logical,layer),packed:before.packed}),
{}

pub(crate) proof fn private_resolution_packet_value_fields(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate)
    requires private_resolution_tile_parameters(params),private_resolution_tile_wf(before),
    ensures private_resolution_tile_wf(private_resolution_packet_value(params,before,coordinate).1),
        private_resolution_packet_value(params,before,coordinate).1.precincts.len()==before.precincts.len(),
        (private_resolution_packet_value(params,before,coordinate).0,
            private_resolution_tile_logical(private_resolution_packet_value(params,before,coordinate).1))
            ==part1_tile_packet(params,private_resolution_tile_logical(before),coordinate),
{
    private_resolution_admission_fields(params,before,coordinate);
    if let Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=
        part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate){
        let context=private_resolution_packet_context(params,before,state,part,coordinate,index);
        assert(private_precinct_wf(before.precincts[index as int]));
        private_resolution_layer_fields(before.precincts[index as int],coordinate.layer);
        private_precinct_packet_value_fields(context);
        let packet=private_precinct_packet_value(context);
        let result=private_resolution_packet_finish(before,state,index,seen,packet);
        assert(private_precincts_logical(result.1.precincts) =~=
            private_precincts_logical(before.precincts).update(index as int,packet.1.logical));
        assert forall|i:int|0<=i<result.1.precincts.len() implies #[trigger] private_precinct_wf(result.1.precincts[i]) by {
            if i!=index{assert(result.1.precincts[i]==before.precincts[i]);}
        }
    }
}

pub(crate) proof fn private_resolution_tile_value_fields(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution)
    requires private_resolution_tile_parameters(params),private_resolution_tile_wf(before),
    ensures private_resolution_tile_wf(private_resolution_tile_value(params,before).1),
        private_resolution_tile_value(params,before).1.precincts.len()==before.precincts.len(),
        (private_resolution_tile_value(params,before).0,private_resolution_tile_logical(private_resolution_tile_value(params,before).1))
            ==part1_tile_run(params,private_resolution_tile_logical(before)),
    decreases before.progress.remaining_packets,
{
    private_resolution_tile_step_fields(params,before);
    reveal_with_fuel(private_resolution_tile_value,1);reveal_with_fuel(part1_tile_run,1);
    match part2_plane_tile_run_admit(params,private_resolution_tile_logical(before)){
        Part2PlaneTileStep::Return(_)=>{},
        Part2PlaneTileStep::Continue(after)=>private_resolution_tile_value_fields(params,
            PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress}),
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            let current=PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress};
            private_resolution_packet_value_fields(params,current,coordinate);
            let packet=private_resolution_packet_value(params,current,coordinate);
            if packet.0.is_ok(){private_resolution_tile_value_fields(params,packet.1);}
        },
    }
}

pub(crate) proof fn private_resolution_packet_observed(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate,state:Part1TilePacketExecution,part:Part2OwnedTilePart,index:usize,seen:usize,
    packet:PrivatePrecinctPacketEffect)
    requires part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate)==
        (Part2PlaneTileAdmission::Packet{state,part,index,seen,expected:None}),
        private_precinct_packet_result(private_resolution_packet_context(params,before,state,part,coordinate,index),packet),
    ensures private_resolution_packet_result(params,before,coordinate,private_resolution_packet_finish(before,state,index,seen,packet)),
{
    let result=private_resolution_packet_finish(before,state,index,seen,packet);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(
        |calls|private_precinct_packet_run(private_resolution_packet_context(params,before,state,part,coordinate,index),calls),
        |actual,rest|Some((Ok(private_resolution_packet_finish(before,state,index,seen,actual)),rest)),Ok(packet),Ok(result));
}

pub(crate) proof fn private_resolution_packet_scalar(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate)==Part2PlaneTileAdmission::Return(result),
    ensures private_resolution_packet_result(params,before,coordinate,(result.0,PrivateResolutionTileExecution {
        precincts:before.precincts,progress:result.1.progress,
    })),
{
    part2_tier1_storage_pure(Ok((result.0,PrivateResolutionTileExecution {precincts:before.precincts,progress:result.1.progress})));
}

pub(crate) proof fn private_resolution_packet_normal(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate)
    requires private_resolution_tile_parameters(params),private_resolution_tile_wf(before),
    ensures private_resolution_packet_result(params,before,coordinate,private_resolution_packet_value(params,before,coordinate)),
{
    private_resolution_admission_fields(params,before,coordinate);
    match part2_plane_tile_packet_admit(params,private_resolution_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>private_resolution_packet_scalar(params,before,coordinate,result),
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>{
            let context=private_resolution_packet_context(params,before,state,part,coordinate,index);
            assert(private_precinct_wf(before.precincts[index as int]));
            private_resolution_layer_fields(before.precincts[index as int],coordinate.layer);
            private_precinct_packet_normal(context);
            private_resolution_packet_observed(params,before,coordinate,state,part,index,seen,private_precinct_packet_value(context));
        },
    }
}

pub(crate) proof fn private_resolution_tile_normal(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution)
    requires private_resolution_tile_parameters(params),private_resolution_tile_wf(before),
    ensures private_resolution_tile_result(params,before,private_resolution_tile_value(params,before)),
    decreases before.progress.remaining_packets,
{
    private_resolution_tile_step_fields(params,before);
    reveal_with_fuel(private_resolution_tile_run,2);reveal_with_fuel(private_resolution_tile_after_iteration,1);
    reveal_with_fuel(private_resolution_tile_value,1);
    let result=private_resolution_tile_value(params,before);
    match part2_plane_tile_run_admit(params,private_resolution_tile_logical(before)){
        Part2PlaneTileStep::Return(_)=>part2_tier1_storage_pure(Ok(result)),
        Part2PlaneTileStep::Continue(after)=>{
            let current=PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress};
            private_resolution_tile_normal(params,current);
            part2_tier1_storage_eta(|calls|private_resolution_tile_run(params,current,calls),Ok(result));
        },
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            let current=PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress};
            private_resolution_packet_normal(params,current,coordinate);
            private_resolution_packet_value_fields(params,current,coordinate);
            let packet=private_resolution_packet_value(params,current,coordinate);
            private_unit_result_fields(packet.0);
            if packet.0.is_err(){part2_tier1_storage_pure(Ok(result));}
            else{
                private_resolution_tile_normal(params,packet.1);
                part2_tier1_storage_eta(|calls|private_resolution_tile_run(params,packet.1,calls),Ok(result));
            }
            part2_tier1_storage_bind_frame(|calls|private_resolution_packet_run(params,current,coordinate,calls),
                |packet,rest|private_resolution_tile_after_iteration(params,before.progress.remaining_packets,packet,rest),Ok(packet),Ok(result));
        },
    }
}

pub(crate) proof fn private_resolution_run_scalar(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_plane_tile_run_admit(params,private_resolution_tile_logical(before))==Part2PlaneTileStep::Return(result),
    ensures forall|calls|private_resolution_tile_run(params,before,calls)==Some((Ok((result.0,PrivateResolutionTileExecution {
        precincts:before.precincts,progress:result.1.progress,
    })),calls)),
{
    reveal_with_fuel(private_resolution_tile_run,1);
}

pub(crate) proof fn private_resolution_run_continue(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    after:Part1TilePacketExecution)
    requires part2_plane_tile_run_admit(params,private_resolution_tile_logical(before))==Part2PlaneTileStep::Continue(after),
        after.progress.remaining_packets<before.progress.remaining_packets,
    ensures forall|calls|private_resolution_tile_run(params,before,calls)==private_resolution_tile_run(params,
        PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress},calls),
{
    reveal_with_fuel(private_resolution_tile_run,1);
}

pub(crate) proof fn private_resolution_run_packet_step(params:Part1TilePacketParameters,before:PrivateResolutionTileExecution,
    coordinate:crate::packet::PacketCoordinate,after:Part1TilePacketExecution)
    requires part2_plane_tile_run_admit(params,private_resolution_tile_logical(before))==Part2PlaneTileStep::Packet(coordinate,after),
    ensures forall|calls|private_resolution_tile_run(params,before,calls)==part2_tier1_storage_bind(
        private_resolution_packet_run(params,PrivateResolutionTileExecution {precincts:before.precincts,progress:after.progress},coordinate,calls),
        |packet,rest|private_resolution_tile_after_iteration(params,before.progress.remaining_packets,packet,rest)),
{
    reveal_with_fuel(private_resolution_tile_run,2);reveal_with_fuel(private_resolution_tile_after_iteration,1);
}

pub(crate) proof fn private_resolution_after_iteration_at(params:Part1TilePacketParameters,budget:u64,
    result:PrivateResolutionTileEffect,calls:Seq<Part2Tier1StorageEvent>)
    ensures private_resolution_tile_after_iteration(params,budget,result,calls)==match result.0{
        Err(_)=>Some((Ok(result),calls)),
        Ok(())=>if result.1.progress.remaining_packets<budget{private_resolution_tile_run(params,result.1,calls)}else{None},
    },
{
    reveal_with_fuel(private_resolution_tile_after_iteration,1);
    reveal_with_fuel(private_resolution_tile_run,1);
}

pub(crate) proof fn private_resolution_prefix_observed(params:Part1TilePacketParameters,initial:PrivateResolutionTileExecution,
    before:PrivateResolutionTileExecution,coordinate:crate::packet::PacketCoordinate,budget:u64,
    prefix:Seq<Part2Tier1StorageEvent>,result:PrivateResolutionTileEffect)->(extended:Seq<Part2Tier1StorageEvent>)
    requires private_resolution_packet_result(params,before,coordinate,result),
        forall|calls|private_resolution_tile_run(params,initial,prefix+calls)==part2_tier1_storage_bind(
            private_resolution_packet_run(params,before,coordinate,calls),
            |packet,rest|private_resolution_tile_after_iteration(params,budget,packet,rest)),
    ensures forall|calls|private_resolution_tile_run(params,initial,extended+calls)==private_resolution_tile_after_iteration(params,budget,result,calls),
        result.0.is_err() ==> private_resolution_tile_result(params,initial,result),
        result.0.is_ok() && result.1.progress.remaining_packets<budget ==> forall|calls|
            private_resolution_tile_run(params,initial,extended+calls)==private_resolution_tile_run(params,result.1,calls),
{
    private_unit_result_fields(result.0);
    let child=|calls|private_resolution_packet_run(params,before,coordinate,calls);
    let next=|packet,rest|private_resolution_tile_after_iteration(params,budget,packet,rest);
    let root=|calls|private_resolution_tile_run(params,initial,calls);
    let extended=part2_tier1_prefix_advance(root,child,next,prefix,result);
    assert(part2_tier1_phase(root,extended,|tail|next(result,tail)));
    assert forall|calls|root(extended+calls)==private_resolution_tile_after_iteration(params,budget,result,calls) by {}
    if result.0.is_err(){
        assert forall|calls|root(extended+calls)==Some((Ok(result),calls)) by {
            private_resolution_after_iteration_at(params,budget,result,calls);
        }
        part2_tier1_prefix_finish(root,extended,Ok(result));
        part2_tier1_storage_eta(root,Ok(result));
    }else if result.1.progress.remaining_packets<budget{
        assert forall|calls|root(extended+calls)==private_resolution_tile_run(params,result.1,calls) by {
            private_resolution_after_iteration_at(params,budget,result,calls);
        }
    }
    extended
}

pub(crate) open spec fn private_resolution_tile_calls_run(params:Part1TilePacketParameters,initial:PrivateResolutionTileExecution,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateResolutionTileEffect> {
    if events.len()==0{None}else{match events[0]{
        Part2JpipSnapshotEvent::PrivateResolutionTileCalls{params:actual,initial:before,calls}=>{
            if actual!=params || before!=initial{None}else{match private_resolution_tile_run(params,initial,calls){
                Some((Ok(effect),rest))=>if rest.len()==0{Some((Ok(effect),events.drop_first()))}else{None},
                _=>None,
            }}
        },
        _=>None,
    }}
}

pub(crate) proof fn private_resolution_tile_calls_observed(params:Part1TilePacketParameters,initial:PrivateResolutionTileExecution,
    result:PrivateResolutionTileEffect)
    requires private_resolution_tile_result(params,initial,result),
    ensures part2_cold_framed(|events|private_resolution_tile_calls_run(params,initial,events),Ok(result)),
{
    let run=|calls|private_resolution_tile_run(params,initial,calls);
    let calls=choose|calls| #[trigger] part2_tier1_storage_prefix(run,calls,Ok(result));
    part2_tier1_storage_at(run,calls,Ok(result),Seq::empty());
    let prefix=seq![Part2JpipSnapshotEvent::PrivateResolutionTileCalls{params,initial,calls}];
    assert forall|tail|private_resolution_tile_calls_run(params,initial,prefix+tail)==Some((Ok(result),tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|private_resolution_tile_calls_run(params,initial,events),prefix,Ok(result)));
}

pub(crate) open spec fn private_resolution_decode_after_progress(params:Part1TilePacketParameters,before:Seq<PrivateHtPrecinctState>,
    progress:Part1TilePacketProgress,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<PrivateResolutionDecodeEffect> {
    part2_jpip_snapshot_bind(private_resolution_tile_calls_run(params,PrivateResolutionTileExecution {precincts:before,progress},events),
        |effect:PrivateResolutionTileEffect,rest|Some((Ok(match effect.0{
            Err(error)=>(Err(error),effect.1.precincts),
            Ok(())=>(part1_tile_finish(params,effect.1.progress).0,effect.1.precincts),
        }),rest)))
}

pub(crate) open spec fn private_resolution_decode_run(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Option<(PrivateResolutionDecodeEffect,Seq<Part2JpipSnapshotEvent>)> {
    match part2_packet_input_run(parts,grid,private_precincts_logical(before),selection,limits,events){
        None=>None,Some((Err(error),rest))=>Some(((Err(error),before),rest)),
        Some((Ok(input),rest))=>{
            let params=part2_packet_parameters(parts,grid,input,selection,limits);
            match part2_progress_initial_run(params,rest){
                None=>None,Some((Err(error),tail))=>Some(((Err(error),before),tail)),
                Some((Ok(progress),tail))=>match private_resolution_decode_after_progress(params,before,progress,tail){
                    None=>None,Some((Err(error),suffix))=>Some(((Err(error),before),suffix)),
                    Some((Ok(effect),suffix))=>Some((effect,suffix)),
                },
            }
        },
    }
}

pub(crate) open spec fn private_resolution_decode_result(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    result:PrivateResolutionDecodeEffect)->bool {
    exists|prefix:Seq<Part2JpipSnapshotEvent>| #[trigger] private_resolution_decode_prefix(parts,grid,before,selection,limits,prefix,result)
}

pub(crate) open spec fn private_resolution_decode_prefix(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    prefix:Seq<Part2JpipSnapshotEvent>,result:PrivateResolutionDecodeEffect)->bool {
    forall|tail| #[trigger] private_resolution_decode_run(parts,grid,before,selection,limits,prefix+tail)==Some((result,tail))
}

pub(crate) open spec fn private_resolution_decode_value(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)->PrivateResolutionDecodeEffect {
    match part1_progression_tile_input_owned(parts,grid,private_precincts_logical(before),selection,limits){
        Err(error)=>(Err(error),before),
        Ok(input)=>{
            let params=part2_packet_parameters(parts,grid,input,selection,limits);
            match part1_tile_progress_initial(params){
                Err(error)=>(Err(error),before),
                Ok(progress)=>{
                    let effect=private_resolution_tile_value(params,PrivateResolutionTileExecution {precincts:before,progress});
                    match effect.0{
                        Err(error)=>(Err(error),effect.1.precincts),
                        Ok(())=>(part1_tile_finish(params,effect.1.progress).0,effect.1.precincts),
                    }
                },
            }
        },
    }
}

pub(crate) proof fn private_resolution_input_parameters(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation)
    requires parts.len()==1,grid.components==1,grid.component_resolutions.len()==1,
        (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false})
        && (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
        selection.is_none() || selection==Some(grid.component_resolutions),
        part1_progression_tile_input_owned(parts,grid,private_precincts_logical(before),selection,limits)==Ok(input),
    ensures private_resolution_tile_parameters(part2_packet_parameters(parts,grid,input,selection,limits)),
{
    reveal_with_fuel(part1_progression_payloads_owned,2);
    reveal(part1_packed_header_reassembly);
}

pub(crate) proof fn private_resolution_decode_value_fields(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)
    requires parts.len()==1,grid.components==1,grid.component_resolutions.len()==1,
        (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false})
        && (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
        selection.is_none() || selection==Some(grid.component_resolutions),
        forall|i:int|0<=i<before.len() ==> #[trigger] private_precinct_wf(before[i]),
    ensures private_resolution_decode_value(parts,grid,before,selection,limits).1.len()==before.len(),
        forall|i:int|0<=i<before.len() ==> #[trigger] private_precinct_wf(private_resolution_decode_value(parts,grid,before,selection,limits).1[i]),
        (private_resolution_decode_value(parts,grid,before,selection,limits).0,
            private_precincts_logical(private_resolution_decode_value(parts,grid,before,selection,limits).1))
            ==part1_progression_tile_decode_owned(parts,grid,private_precincts_logical(before),selection,limits),
{
    if let Ok(input)=part1_progression_tile_input_owned(parts,grid,private_precincts_logical(before),selection,limits){
        private_resolution_input_parameters(parts,grid,before,selection,limits,input);
        let params=part2_packet_parameters(parts,grid,input,selection,limits);
        if let Ok(progress)=part1_tile_progress_initial(params){
            private_resolution_tile_value_fields(params,PrivateResolutionTileExecution {precincts:before,progress});
        }
    }
}

pub(crate) proof fn private_resolution_input_error(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,error:crate::DecodeError)
    requires part2_packet_input_result(parts,grid,private_precincts_logical(before),selection,limits,Err(error)),
    ensures private_resolution_decode_result(parts,grid,before,selection,limits,(Err(error),before)),
{
    reveal(part2_packet_input_result);
    let child=|events|part2_packet_input_run(parts,grid,private_precincts_logical(before),selection,limits,events);
    let prefix=part2_cold_witness(child,Err(error));
    assert forall|tail|private_resolution_decode_run(parts,grid,before,selection,limits,prefix+tail)==Some(((Err(error),before),tail)) by {
        part2_cold_prefix_at(child,prefix,Err(error),tail);
    }
    assert(private_resolution_decode_prefix(parts,grid,before,selection,limits,prefix,(Err(error),before)));
}

pub(crate) proof fn private_resolution_progress_error(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    input:Part1TilePacketPreparation,error:crate::DecodeError)
    requires part2_packet_input_result(parts,grid,private_precincts_logical(before),selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Err(error)),
    ensures private_resolution_decode_result(parts,grid,before,selection,limits,(Err(error),before)),
{
    reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let first=|events|part2_packet_input_run(parts,grid,private_precincts_logical(before),selection,limits,events);
    let second=|events|part2_progress_initial_run(part2_packet_parameters(parts,grid,input,selection,limits),events);
    let p=part2_cold_witness(first,Ok(input));let q=part2_cold_witness(second,Err(error));
    assert forall|tail|private_resolution_decode_run(parts,grid,before,selection,limits,(p+q)+tail)==Some(((Err(error),before),tail)) by {
        assert((p+q)+tail =~= p+(q+tail));
        part2_cold_prefix_at(first,p,Ok(input),q+tail);
        part2_cold_prefix_at(second,q,Err(error),tail);
    }
    assert(private_resolution_decode_prefix(parts,grid,before,selection,limits,p+q,(Err(error),before)));
}

pub(crate) proof fn private_resolution_decode_observed(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    input:Part1TilePacketPreparation,progress:Part1TilePacketProgress,effect:PrivateResolutionTileEffect)
    requires part2_packet_input_result(parts,grid,private_precincts_logical(before),selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Ok(progress)),
        private_resolution_tile_result(part2_packet_parameters(parts,grid,input,selection,limits),
            PrivateResolutionTileExecution {precincts:before,progress},effect),
    ensures private_resolution_decode_result(parts,grid,before,selection,limits,match effect.0{
        Err(error)=>(Err(error),effect.1.precincts),
        Ok(())=>(part1_tile_finish(part2_packet_parameters(parts,grid,input,selection,limits),effect.1.progress).0,effect.1.precincts),
    }),
{
    reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let params=part2_packet_parameters(parts,grid,input,selection,limits);
    private_resolution_tile_calls_observed(params,PrivateResolutionTileExecution {precincts:before,progress},effect);
    let first=|events|part2_packet_input_run(parts,grid,private_precincts_logical(before),selection,limits,events);
    let second=|events|part2_progress_initial_run(params,events);
    let third=|events|private_resolution_tile_calls_run(params,PrivateResolutionTileExecution {precincts:before,progress},events);
    let p=part2_cold_witness(first,Ok(input));let q=part2_cold_witness(second,Ok(progress));let r=part2_cold_witness(third,Ok(effect));
    let result=match effect.0{Err(error)=>(Err(error),effect.1.precincts),Ok(())=>(part1_tile_finish(params,effect.1.progress).0,effect.1.precincts)};
    assert forall|tail|private_resolution_decode_run(parts,grid,before,selection,limits,((p+q)+r)+tail)==Some((result,tail)) by {
        assert(((p+q)+r)+tail =~= p+(q+(r+tail)));
        part2_cold_prefix_at(first,p,Ok(input),q+(r+tail));
        part2_cold_prefix_at(second,q,Ok(progress),r+tail);
        part2_cold_prefix_at(third,r,Ok(effect),tail);
    }
    assert(private_resolution_decode_prefix(parts,grid,before,selection,limits,(p+q)+r,result));
}

pub(crate) proof fn private_resolution_decode_normal(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    before:Seq<PrivateHtPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)
    requires parts.len()==1,grid.components==1,grid.component_resolutions.len()==1,
        (match parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false}),
        (match parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false}),
        selection.is_none() || selection==Some(grid.component_resolutions),
        forall|i:int|0<=i<before.len() ==> #[trigger] private_precinct_wf(before[i]),
    ensures private_resolution_decode_result(parts,grid,before,selection,limits,private_resolution_decode_value(parts,grid,before,selection,limits)),
{
    part2_packet_input_normal(parts,grid,private_precincts_logical(before),selection,limits);
    match part1_progression_tile_input_owned(parts,grid,private_precincts_logical(before),selection,limits){
        Err(error)=>private_resolution_input_error(parts,grid,before,selection,limits,error),
        Ok(input)=>{
            let params=part2_packet_parameters(parts,grid,input,selection,limits);
            private_resolution_input_parameters(parts,grid,before,selection,limits,input);
            part2_progress_initial_normal(params);
            match part1_tile_progress_initial(params){
                Err(error)=>private_resolution_progress_error(parts,grid,before,selection,limits,input,error),
                Ok(progress)=>{
                    let initial=PrivateResolutionTileExecution {precincts:before,progress};
                    private_resolution_tile_normal(params,initial);
                    private_resolution_decode_observed(parts,grid,before,selection,limits,input,progress,private_resolution_tile_value(params,initial));
                },
            }
        },
    }
}

}
