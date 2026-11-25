use super::*;
verus! {

pub struct PrivateTileExecution {
    pub precinct:PrivateHtPrecinctState,
    pub progress:Part1TilePacketProgress,
}

pub type PrivateTileEffect=(Result<(),crate::DecodeError>,PrivateTileExecution);

pub(crate) open spec fn private_tile_logical(state:PrivateTileExecution)->Part1TilePacketExecution {
    Part1TilePacketExecution{precincts:seq![state.precinct.logical],progress:state.progress}
}

pub(crate) open spec fn private_grid_shape(grid:Part1PacketGrid)->bool {
    grid.components==1 && grid.resolutions==1 && grid.component_resolutions==seq![1u8]
        && grid.maximum_precincts_per_resolution==1 && grid.precinct_counts==seq![1u32]
        && grid.precinct_offsets==seq![0usize,1usize] && grid.layers>0
        && grid.packet_count==grid.layers as u64
}

pub(crate) proof fn private_grid_layout_fields(grid:Part1PacketGrid,precinct:Part1PacketPrecinctState)
    requires private_grid_shape(grid),precinct.component==0,precinct.resolution==0,precinct.precinct==0,
    ensures part1_packet_grid_total_precincts(grid)==Ok(1u64),
        part1_packet_grid_precinct_index(grid,0,0,0)==Ok(0usize),
        part1_progression_precinct_layout(grid,seq![precinct])==Ok(()),
{
    assert((grid.layers as int)/(grid.layers as int)==1) by(nonlinear_arith)
        requires grid.layers>0;
    reveal_with_fuel(part1_progression_precinct_indices,2);
}

pub(crate) open spec fn private_precinct_wf(state:PrivateHtPrecinctState)->bool {
    state.logical.component==0
        && state.packed.len()==state.logical.decoders.len()
        && forall|i:int|0<=i<state.logical.decoders.len() ==> #[trigger] private_ht_state_wf(
            PrivateHtDecoderState{logical:state.logical.decoders[i],packed:state.packed[i]})
}

pub(crate) open spec fn private_tile_wf(state:PrivateTileExecution)->bool {
    private_precinct_wf(state.precinct) && state.precinct.logical.resolution==0 && state.precinct.logical.precinct==0
        && state.progress.packed_offset==0
}

pub(crate) open spec fn private_tile_parameters(params:Part1TilePacketParameters)->bool {
    private_grid_shape(params.grid) && params.parts.len()==1
        && (match params.parts[0].packed_packet_headers.source{Part1PackedHeaderSource::None=>true,_=>false})
        && (match params.parts[0].packet_lengths.source{Part1PacketLengthSource::None=>true,_=>false})
        && params.input.packed==seq![Seq::<u8>::empty()]
        && (params.selection.is_none() || params.selection==Some(seq![1u8]))
}

pub(crate) proof fn private_tile_step_fields(params:Part1TilePacketParameters,before:PrivateTileExecution)
    requires private_tile_parameters(params),private_tile_wf(before),
    ensures part1_tile_boundary(params,before.progress).1.packed_offset==0,
        match part2_plane_tile_run_admit(params,private_tile_logical(before)){
            Part2PlaneTileStep::Return(result)=>result.1.progress.packed_offset==0,
            Part2PlaneTileStep::Continue(after)=>after.progress.packed_offset==0
                && after.progress.remaining_packets<before.progress.remaining_packets,
            Part2PlaneTileStep::Packet(_,after)=>after.progress.packed_offset==0
                && after.progress.remaining_packets<before.progress.remaining_packets,
        },
{
    reveal_with_fuel(part1_tile_boundary_scan,2);
}

pub(crate) proof fn private_tile_admission_fields(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate)
    requires private_tile_parameters(params),private_tile_wf(before),
    ensures match part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>result.1.progress.packed_offset==0,
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>
            index==0 && expected.is_none() && state.progress.packed_offset==0
            && state.precincts==seq![before.precinct.logical] && part==params.parts[0]
            && state.progress.current_tile_part==0
            && coordinate.component==0 && coordinate.resolution==0 && coordinate.precinct==0,
    },
{}

pub(crate) open spec fn private_tile_after_packet(before:PrivateTileExecution,state:Part1TilePacketExecution,
    seen:usize,expected:Option<u32>,packet:PrivatePrecinctPacketEffect)->PrivateTileEffect {
    let finished=part2_plane_tile_packet_finish(state,0,seen,expected,(packet.0,packet.1.logical));
    (finished.0,PrivateTileExecution {
        precinct:PrivateHtPrecinctState{logical:finished.1.precincts[0],packed:packet.1.packed},
        progress:finished.1.progress,
    })
}

pub(crate) open spec fn private_tile_packet_context(params:Part1TilePacketParameters,before:PrivateTileExecution,
    state:Part1TilePacketExecution,part:Part2OwnedTilePart,coordinate:crate::packet::PacketCoordinate)->PrivatePrecinctPacketContext {
    PrivatePrecinctPacketContext {
        before:PrivateHtPrecinctState {
            logical:part1_precinct_context_layer(before.precinct.logical,coordinate.layer),packed:before.precinct.packed,
        },part,offset:state.progress.offset,sequence:(state.progress.packets&65535u64) as u16,
        caps:(params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work),
    }
}

pub(crate) open spec fn private_tile_packet_run(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<PrivateTileEffect> {
    match part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>Some((Ok((result.0,PrivateTileExecution {
            precinct:before.precinct,progress:result.1.progress,
        })),calls)),
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>{
            if index!=0 || expected.is_some(){None}else{
                part2_tier1_storage_bind(private_precinct_packet_run(private_tile_packet_context(params,before,state,part,coordinate),calls),
                    |packet,rest|Some((Ok(private_tile_after_packet(before,state,seen,expected,packet)),rest)))
            }
        },
    }
}

pub(crate) open spec fn private_tile_packet_value(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate)->PrivateTileEffect {
    match part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>(result.0,PrivateTileExecution {
            precinct:before.precinct,progress:result.1.progress,
        }),
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>{
            if index!=0 || expected.is_some(){(Err(part1_packet_reader_error(state.progress.offset,crate::MalformedKind::InvalidPacketHeader)),before)}
            else{private_tile_after_packet(before,state,seen,expected,
                private_precinct_packet_value(private_tile_packet_context(params,before,state,part,coordinate)))}
        },
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_tile_run(params:Part1TilePacketParameters,before:PrivateTileExecution,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateTileEffect>
    decreases before.progress.remaining_packets*2+1,
{
    match part2_plane_tile_run_admit(params,private_tile_logical(before)){
        Part2PlaneTileStep::Return(result)=>Some((Ok((result.0,PrivateTileExecution {
            precinct:before.precinct,progress:result.1.progress,
        })),calls)),
        Part2PlaneTileStep::Continue(after)=>if after.progress.remaining_packets<before.progress.remaining_packets {
            private_tile_run(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress},calls)
        }else{None},
        Part2PlaneTileStep::Packet(coordinate,after)=>part2_tier1_storage_bind(
            private_tile_packet_run(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress},coordinate,calls),
            |packet,rest|private_tile_after_iteration(params,before.progress.remaining_packets,packet,rest)),
    }
}

#[verifier::opaque]
pub(crate) open spec fn private_tile_after_iteration(params:Part1TilePacketParameters,budget:u64,packet:PrivateTileEffect,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<PrivateTileEffect>
    decreases budget*2,
{
    match packet.0{Err(_)=>Some((Ok(packet),calls)),Ok(())=>if packet.1.progress.remaining_packets<budget {
        private_tile_run(params,packet.1,calls)
    }else{None}}
}

#[verifier::opaque]
pub(crate) open spec fn private_tile_value(params:Part1TilePacketParameters,before:PrivateTileExecution)->PrivateTileEffect
    decreases before.progress.remaining_packets,
{
    match part2_plane_tile_run_admit(params,private_tile_logical(before)){
        Part2PlaneTileStep::Return(result)=>(result.0,PrivateTileExecution{precinct:before.precinct,progress:result.1.progress}),
        Part2PlaneTileStep::Continue(after)=>private_tile_value(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress}),
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            let packet=private_tile_packet_value(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress},coordinate);
            match packet.0{Err(_)=>packet,Ok(())=>private_tile_value(params,packet.1)}
        },
    }
}

pub(crate) open spec fn private_tile_packet_result(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate,result:PrivateTileEffect)->bool {
    part2_tier1_storage_framed(|calls|private_tile_packet_run(params,before,coordinate,calls),Ok(result))
}

pub(crate) open spec fn private_tile_run_result(params:Part1TilePacketParameters,before:PrivateTileExecution,result:PrivateTileEffect)->bool {
    part2_tier1_storage_framed(|calls|private_tile_run(params,before,calls),Ok(result))
}

pub(crate) proof fn private_tile_packet_observed(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate,state:Part1TilePacketExecution,part:Part2OwnedTilePart,seen:usize,
    packet:PrivatePrecinctPacketEffect)
    requires part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate)==
            (Part2PlaneTileAdmission::Packet{state,part,index:0,seen,expected:None}),
        private_precinct_packet_result(private_tile_packet_context(params,before,state,part,coordinate),packet),
    ensures private_tile_packet_result(params,before,coordinate,private_tile_after_packet(before,state,seen,None,packet)),
{
    let result=private_tile_after_packet(before,state,seen,None,packet);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(
        |calls|private_precinct_packet_run(private_tile_packet_context(params,before,state,part,coordinate),calls),
        |actual,rest|Some((Ok(private_tile_after_packet(before,state,seen,None,actual)),rest)),Ok(packet),Ok(result));
}

pub(crate) proof fn private_tile_packet_scalar(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate)==Part2PlaneTileAdmission::Return(result),
    ensures private_tile_packet_result(params,before,coordinate,(result.0,PrivateTileExecution {
        precinct:before.precinct,progress:result.1.progress,
    })),
{
    part2_tier1_storage_pure(Ok((result.0,PrivateTileExecution{precinct:before.precinct,progress:result.1.progress})));
}

pub(crate) proof fn private_tile_packet_value_fields(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate)
    requires private_tile_parameters(params),private_tile_wf(before),
    ensures private_tile_wf(private_tile_packet_value(params,before,coordinate).1),
        (private_tile_packet_value(params,before,coordinate).0,
            private_tile_logical(private_tile_packet_value(params,before,coordinate).1))
            ==part1_tile_packet(params,private_tile_logical(before),coordinate),
{
    private_tile_admission_fields(params,before,coordinate);
    if let Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=
        part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate) {
        let context=private_tile_packet_context(params,before,state,part,coordinate);
        private_precinct_packet_value_fields(context);
        let packet=private_precinct_packet_value(context);
        let finished=part2_plane_tile_packet_finish(state,index,seen,expected,(packet.0,packet.1.logical));
        assert(finished.1.precincts =~= seq![finished.1.precincts[0]]);
    }else if let Part2PlaneTileAdmission::Return(result)=
        part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate){
        assert(result.1.precincts =~= seq![before.precinct.logical]);
    }
}

pub(crate) proof fn private_tile_value_fields(params:Part1TilePacketParameters,before:PrivateTileExecution)
    requires private_tile_parameters(params),private_tile_wf(before),
    ensures private_tile_wf(private_tile_value(params,before).1),
        (private_tile_value(params,before).0,private_tile_logical(private_tile_value(params,before).1))
            ==part1_tile_run(params,private_tile_logical(before)),
    decreases before.progress.remaining_packets,
{
    private_tile_step_fields(params,before);
    reveal_with_fuel(private_tile_value,1);reveal_with_fuel(part1_tile_run,1);
    match part2_plane_tile_run_admit(params,private_tile_logical(before)){
        Part2PlaneTileStep::Return(_)=>{},
        Part2PlaneTileStep::Continue(after)=>private_tile_value_fields(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress}),
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            let current=PrivateTileExecution{precinct:before.precinct,progress:after.progress};
            private_tile_packet_value_fields(params,current,coordinate);
            let packet=private_tile_packet_value(params,current,coordinate);
            if packet.0.is_ok(){private_tile_value_fields(params,packet.1);}
        },
    }
}

pub(crate) proof fn private_tile_packet_normal(params:Part1TilePacketParameters,before:PrivateTileExecution,
    coordinate:crate::packet::PacketCoordinate)
    requires private_tile_parameters(params),private_tile_wf(before),
    ensures private_tile_packet_result(params,before,coordinate,private_tile_packet_value(params,before,coordinate)),
{
    private_tile_admission_fields(params,before,coordinate);
    match part2_plane_tile_packet_admit(params,private_tile_logical(before),coordinate){
        Part2PlaneTileAdmission::Return(result)=>{
            private_tile_packet_scalar(params,before,coordinate,result);
        },
        Part2PlaneTileAdmission::Packet{state,part,index,seen,expected}=>{
            assert(index==0 && expected.is_none());
            let context=private_tile_packet_context(params,before,state,part,coordinate);
            private_precinct_packet_normal(context);
            private_tile_packet_observed(params,before,coordinate,state,part,seen,private_precinct_packet_value(context));
        },
    }
}

pub(crate) proof fn private_tile_run_normal(params:Part1TilePacketParameters,before:PrivateTileExecution)
    requires private_tile_parameters(params),private_tile_wf(before),
    ensures private_tile_run_result(params,before,private_tile_value(params,before)),
    decreases before.progress.remaining_packets,
{
    private_tile_step_fields(params,before);
    reveal_with_fuel(private_tile_run,2);reveal_with_fuel(private_tile_after_iteration,1);reveal_with_fuel(private_tile_value,1);
    let result=private_tile_value(params,before);
    match part2_plane_tile_run_admit(params,private_tile_logical(before)){
        Part2PlaneTileStep::Return(_)=>{part2_tier1_storage_pure(Ok(result));},
        Part2PlaneTileStep::Continue(after)=>{
            private_tile_run_normal(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress});
            part2_tier1_storage_eta(|calls|private_tile_run(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress},calls),Ok(result));
        },
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            let current=PrivateTileExecution{precinct:before.precinct,progress:after.progress};
            private_tile_packet_normal(params,current,coordinate);
            private_tile_packet_value_fields(params,current,coordinate);
            let packet=private_tile_packet_value(params,current,coordinate);
            private_unit_result_fields(packet.0);
            if packet.0.is_err(){part2_tier1_storage_pure(Ok(result));}else{
                private_tile_run_normal(params,packet.1);
                part2_tier1_storage_eta(|calls|private_tile_run(params,packet.1,calls),Ok(result));
            }
            part2_tier1_storage_bind_frame(|calls|private_tile_packet_run(params,current,coordinate,calls),
                |packet,rest|private_tile_after_iteration(params,before.progress.remaining_packets,packet,rest),Ok(packet),Ok(result));
        },
    }
}

    pub(crate) proof fn private_tile_run_scalar(params:Part1TilePacketParameters,before:PrivateTileExecution,
        result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
        requires part2_plane_tile_run_admit(params,private_tile_logical(before))==Part2PlaneTileStep::Return(result),
        ensures forall|calls|private_tile_run(params,before,calls)==Some((Ok((result.0,PrivateTileExecution {
            precinct:before.precinct,progress:result.1.progress,
        })),calls)),
    {
        reveal_with_fuel(private_tile_run,1);
    }

    pub(crate) proof fn private_tile_run_continue(params:Part1TilePacketParameters,before:PrivateTileExecution,after:Part1TilePacketExecution)
        requires part2_plane_tile_run_admit(params,private_tile_logical(before))==Part2PlaneTileStep::Continue(after),
            after.progress.remaining_packets<before.progress.remaining_packets,
        ensures forall|calls|private_tile_run(params,before,calls)==private_tile_run(params,
            PrivateTileExecution{precinct:before.precinct,progress:after.progress},calls),
    {
        reveal_with_fuel(private_tile_run,1);
    }

    pub(crate) proof fn private_tile_run_packet_step(params:Part1TilePacketParameters,before:PrivateTileExecution,
        coordinate:crate::packet::PacketCoordinate,after:Part1TilePacketExecution)
        requires part2_plane_tile_run_admit(params,private_tile_logical(before))==Part2PlaneTileStep::Packet(coordinate,after),
        ensures forall|calls|private_tile_run(params,before,calls)==part2_tier1_storage_bind(
            private_tile_packet_run(params,PrivateTileExecution{precinct:before.precinct,progress:after.progress},coordinate,calls),
            |packet,rest|private_tile_after_iteration(params,before.progress.remaining_packets,packet,rest)),
    {
        reveal_with_fuel(private_tile_run,2);reveal_with_fuel(private_tile_after_iteration,1);
    }

    pub(crate) proof fn private_tile_prefix_observed(params:Part1TilePacketParameters,initial:PrivateTileExecution,
        before:PrivateTileExecution,coordinate:crate::packet::PacketCoordinate,budget:u64,
        prefix:Seq<Part2Tier1StorageEvent>,result:PrivateTileEffect)->(extended:Seq<Part2Tier1StorageEvent>)
        requires private_tile_packet_result(params,before,coordinate,result),
            forall|calls|private_tile_run(params,initial,prefix+calls)==part2_tier1_storage_bind(
                private_tile_packet_run(params,before,coordinate,calls),|packet,rest|private_tile_after_iteration(params,budget,packet,rest)),
        ensures forall|calls|private_tile_run(params,initial,extended+calls)==private_tile_after_iteration(params,budget,result,calls),
            result.0.is_err() ==> private_tile_run_result(params,initial,result),
            result.0.is_ok() && result.1.progress.remaining_packets<budget ==> forall|calls|
                private_tile_run(params,initial,extended+calls)==private_tile_run(params,result.1,calls),
    {
        reveal(private_tile_after_iteration);
        reveal_with_fuel(private_tile_run,1);
        private_unit_result_fields(result.0);
        let child=|calls|private_tile_packet_run(params,before,coordinate,calls);
        let next=|packet,rest|private_tile_after_iteration(params,budget,packet,rest);
        let root=|calls|private_tile_run(params,initial,calls);
        let extended=part2_tier1_prefix_advance(root,child,next,prefix,result);
        assert(part2_tier1_phase(root,extended,|tail|next(result,tail)));
        assert forall|calls|root(extended+calls)==private_tile_after_iteration(params,budget,result,calls) by {}
        if result.0.is_err(){
            private_tile_after_iteration_error(params,budget,result);
            assert forall|calls|root(extended+calls)==Some((Ok(result),calls)) by {}
            part2_tier1_prefix_finish(root,extended,Ok(result));
            part2_tier1_storage_eta(root,Ok(result));
        }else if result.1.progress.remaining_packets<budget{
            private_tile_after_iteration_continue(params,budget,result);
            assert forall|calls|private_tile_run(params,initial,extended+calls)==private_tile_run(params,result.1,calls) by {
                reveal_with_fuel(private_tile_after_iteration,2);
                assert(private_tile_run(params,initial,extended+calls)==private_tile_after_iteration(params,budget,result,calls));
            }
        }
        extended
}

pub(crate) proof fn private_tile_after_iteration_error(params:Part1TilePacketParameters,budget:u64,result:PrivateTileEffect)
    requires result.0.is_err(),
    ensures forall|calls| #[trigger] private_tile_after_iteration(params,budget,result,calls)==Some((Ok(result),calls)),
{
    assert forall|calls| #[trigger] private_tile_after_iteration(params,budget,result,calls)==Some((Ok(result),calls)) by {
        private_tile_after_iteration_at(params,budget,result,calls);
    }
}

pub(crate) proof fn private_tile_after_iteration_continue(params:Part1TilePacketParameters,budget:u64,result:PrivateTileEffect)
    requires result.0==Ok(()),result.1.progress.remaining_packets<budget,
    ensures forall|calls| #[trigger] private_tile_after_iteration(params,budget,result,calls)==private_tile_run(params,result.1,calls),
{
    assert forall|calls| #[trigger] private_tile_after_iteration(params,budget,result,calls)==private_tile_run(params,result.1,calls) by {
        private_tile_after_iteration_at(params,budget,result,calls);
    }
}

pub(crate) proof fn private_tile_after_iteration_at(params:Part1TilePacketParameters,budget:u64,result:PrivateTileEffect,calls:Seq<Part2Tier1StorageEvent>)
    ensures private_tile_after_iteration(params,budget,result,calls)==match result.0{
        Err(_)=>Some((Ok(result),calls)),Ok(())=>if result.1.progress.remaining_packets<budget{
            private_tile_run(params,result.1,calls)
        }else{None}},
{
    reveal_with_fuel(private_tile_after_iteration,1);
    reveal_with_fuel(private_tile_run,1);
}
}
