//! Actual packet selection, physical length ownership and tile iteration.
use super::*;
verus! {
pub(crate) open spec fn part2_plane_tile_precinct_run(params:Part1TilePacketParameters,part:Part2OwnedTilePart,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,expected:Option<u32>,precinct:Part1PacketPrecinctState,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrecinctPayloadResult> {
    let layered=part1_precinct_context_layer(precinct,coordinate.layer);
    if p.current_tile_part>=params.input.packed.len(){Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidTilePart)),layered)),calls))}
    else if params.selection.is_some() && coordinate.component as nat>=params.selection.unwrap().len(){
        Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidCodingStyle)),layered)),calls))
    }else{
        let decode=match params.selection{None=>true,Some(counts)=>coordinate.resolution<counts[coordinate.component as int]};
        part2_plane_precinct_run(layered,part,p.offset,params.input.packed[p.current_tile_part as int],p.packed_offset,expected,(p.packets & 65535u64) as u16,decode,
            params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work,calls)
    }
}
pub(crate) open spec fn part2_plane_tile_precinct_result(params:Part1TilePacketParameters,part:Part2OwnedTilePart,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,expected:Option<u32>,precinct:Part1PacketPrecinctState,result:Part1PrecinctPayloadResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_tile_precinct_run(params,part,p,coordinate,expected,precinct,calls),Ok(result))
}
pub(crate) proof fn part2_plane_tile_precinct_normal(params:Part1TilePacketParameters,part:Part2OwnedTilePart,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,expected:Option<u32>,precinct:Part1PacketPrecinctState)
    ensures part2_plane_tile_precinct_result(params,part,p,coordinate,expected,precinct,part1_tile_precinct_packet_owned(params,part,p,coordinate,expected,precinct)),
{
    let result=part1_tile_precinct_packet_owned(params,part,p,coordinate,expected,precinct);
    if p.current_tile_part>=params.input.packed.len() || (params.selection.is_some() && coordinate.component as nat>=params.selection.unwrap().len()){
        part2_tier1_storage_pure(Ok(result));
    }else{
        let layered=part1_precinct_context_layer(precinct,coordinate.layer);
        let decode=match params.selection{None=>true,Some(counts)=>coordinate.resolution<counts[coordinate.component as int]};
        part2_plane_precinct_normal(layered,part,p.offset,params.input.packed[p.current_tile_part as int],p.packed_offset,expected,(p.packets & 65535u64) as u16,decode,
            params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work);
        part2_tier1_storage_eta(|calls|part2_plane_precinct_run(layered,part,p.offset,params.input.packed[p.current_tile_part as int],p.packed_offset,expected,(p.packets & 65535u64) as u16,decode,
            params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work,calls),Ok(result));
    }
}
pub(crate) proof fn part2_plane_tile_precinct_observed(params:Part1TilePacketParameters,part:Part2OwnedTilePart,p:Part1TilePacketProgress,
    coordinate:crate::packet::PacketCoordinate,expected:Option<u32>,precinct:Part1PacketPrecinctState,decode:bool,result:Part1PrecinctPayloadResult)
    requires p.current_tile_part<params.input.packed.len(),
        params.selection.is_none() || (coordinate.component as nat)<params.selection.unwrap().len(),
        decode==match params.selection{None=>true,Some(counts)=>coordinate.resolution<counts[coordinate.component as int]},
        part2_plane_precinct_result(part1_precinct_context_layer(precinct,coordinate.layer),part,p.offset,params.input.packed[p.current_tile_part as int],p.packed_offset,expected,(p.packets & 65535u64) as u16,decode,
            params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work,result),
    ensures part2_plane_tile_precinct_result(params,part,p,coordinate,expected,precinct,result),
{part2_tier1_storage_eta(|calls|part2_plane_precinct_run(part1_precinct_context_layer(precinct,coordinate.layer),part,p.offset,params.input.packed[p.current_tile_part as int],p.packed_offset,expected,(p.packets & 65535u64) as u16,decode,
    params.caps.blocks,params.caps.header,params.caps.passes,params.caps.bytes,params.caps.input,params.caps.work,calls),Ok(result));}
pub enum Part2PlaneTileAdmission {
    Return((Result<(),crate::DecodeError>,Part1TilePacketExecution)),
    Packet {state:Part1TilePacketExecution,part:Part2OwnedTilePart,index:usize,seen:usize,expected:Option<u32>},
}
pub(crate) open spec fn part2_plane_tile_packet_admit(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate)->Part2PlaneTileAdmission {
    if s.progress.current_tile_part>=params.parts.len(){Part2PlaneTileAdmission::Return((Err(crate::DecodeError::MalformedInput {offset:params.input.payload_bytes,kind:crate::MalformedKind::Truncated}),s))}
    else{
        let part=params.parts[s.progress.current_tile_part as int];let slot=part1_tile_packet_slot(params.grid,coordinate);
        let duplicate=match slot{Err(_)=>false,Ok((_,seen))=>seen<s.progress.seen.len() && s.progress.seen[seen as int]};
        if duplicate{Part2PlaneTileAdmission::Return((Ok(()),s))}else{
            let length=part1_tile_packet_length_owned(part,s.progress);let after=Part1TilePacketExecution {progress:length.1,..s};
            match length.0{
                Err(error)=>Part2PlaneTileAdmission::Return((Err(error),after)),
                Ok(expected)=>match slot{
                    Err(error)=>Part2PlaneTileAdmission::Return((Err(error),after)),Ok((index,seen))=>{
                        if seen>=after.progress.seen.len(){Part2PlaneTileAdmission::Return((Err(part1_packet_reader_error(after.progress.offset,crate::MalformedKind::InvalidPacketHeader)),after))}
                        else if after.progress.seen[seen as int]{Part2PlaneTileAdmission::Return((Ok(()),after))}
                        else if index>=after.precincts.len(){Part2PlaneTileAdmission::Return((Err(part1_packet_reader_error(after.progress.offset,crate::MalformedKind::InvalidPacketHeader)),after))}
                        else{Part2PlaneTileAdmission::Packet {state:after,part,index,seen,expected}}
                    },
                },
            }
        }
    }
}
pub(crate) open spec fn part2_plane_tile_packet_finish(s:Part1TilePacketExecution,index:usize,seen:usize,expected:Option<u32>,packet:Part1PrecinctPayloadResult)
    ->(Result<(),crate::DecodeError>,Part1TilePacketExecution) {
    let after=Part1TilePacketExecution {precincts:s.precincts.update(index as int,packet.1),..s};
    match packet.0{Err(error)=>(Err(error),after),Ok((decoded,tile,packed))=>{
        let account=part1_tile_account(after.progress,decoded,tile,packed,expected,seen);
        (account.0,Part1TilePacketExecution {progress:account.1,..after})
    }}
}
pub(crate) open spec fn part2_plane_tile_packet_run(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1TilePacketExecution)> {
    match part2_plane_tile_packet_admit(params,s,coordinate){
        Part2PlaneTileAdmission::Return(result)=>Some((Ok(result),calls)),
        Part2PlaneTileAdmission::Packet {state,part,index,seen,expected}=>part2_tier1_storage_bind(part2_plane_tile_precinct_run(params,part,state.progress,coordinate,expected,state.precincts[index as int],calls),
            |packet:Part1PrecinctPayloadResult,rest|Some((Ok(part2_plane_tile_packet_finish(state,index,seen,expected,packet)),rest))),
    }
}
pub(crate) open spec fn part2_plane_tile_packet_result(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,
    result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))->bool {
    part2_tier1_storage_framed(|calls|part2_plane_tile_packet_run(params,s,coordinate,calls),Ok(result))
}
pub(crate) proof fn part2_plane_tile_packet_normal(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate)
    ensures part2_plane_tile_packet_result(params,s,coordinate,part1_tile_packet(params,s,coordinate)),
{
    let result=part1_tile_packet(params,s,coordinate);
    match part2_plane_tile_packet_admit(params,s,coordinate){
        Part2PlaneTileAdmission::Return(_)=>{part2_tier1_storage_pure(Ok(result));},
        Part2PlaneTileAdmission::Packet {state,part,index,seen,expected}=>{
            part2_plane_tile_precinct_normal(params,part,state.progress,coordinate,expected,state.precincts[index as int]);
            let packet=part1_tile_precinct_packet_owned(params,part,state.progress,coordinate,expected,state.precincts[index as int]);part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_plane_tile_precinct_run(params,part,state.progress,coordinate,expected,state.precincts[index as int],calls),
                |packet:Part1PrecinctPayloadResult,rest|Some((Ok(part2_plane_tile_packet_finish(state,index,seen,expected,packet)),rest)),Ok(packet),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_tile_packet_observed(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,
    state:Part1TilePacketExecution,part:Part2OwnedTilePart,index:usize,seen:usize,expected:Option<u32>,packet:Part1PrecinctPayloadResult)
    requires part2_plane_tile_packet_admit(params,s,coordinate)==(Part2PlaneTileAdmission::Packet {state,part,index,seen,expected}),
        part2_plane_tile_precinct_result(params,part,state.progress,coordinate,expected,state.precincts[index as int],packet),
    ensures part2_plane_tile_packet_result(params,s,coordinate,part2_plane_tile_packet_finish(state,index,seen,expected,packet)),
{
    let result=part2_plane_tile_packet_finish(state,index,seen,expected,packet);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_plane_tile_precinct_run(params,part,state.progress,coordinate,expected,state.precincts[index as int],calls),
        |packet:Part1PrecinctPayloadResult,rest|Some((Ok(part2_plane_tile_packet_finish(state,index,seen,expected,packet)),rest)),Ok(packet),Ok(result));
}
pub enum Part2PlaneTileStep {
    Return((Result<(),crate::DecodeError>,Part1TilePacketExecution)),
    Continue(Part1TilePacketExecution),
    Packet(crate::packet::PacketCoordinate,Part1TilePacketExecution),
}
pub(crate) open spec fn part2_plane_tile_run_admit(params:Part1TilePacketParameters,s:Part1TilePacketExecution)->Part2PlaneTileStep {
    let next=part1_progression_iterator_next(s.progress.iterator);
    let s=Part1TilePacketExecution {progress:Part1TilePacketProgress {iterator:next.1,..s.progress},..s};
    match next.0{
        Err(error)=>Part2PlaneTileStep::Return((Err(error),s)),Ok(None)=>Part2PlaneTileStep::Return((Ok(()),s)),
        Ok(Some(coordinate))=>{
            if s.progress.remaining_packets==0{Part2PlaneTileStep::Return((Err(ht_reader_error(crate::MalformedKind::InvalidProgressionOrderChange)),s))}
            else{
                let s=Part1TilePacketExecution {progress:Part1TilePacketProgress {remaining_packets:(s.progress.remaining_packets-1) as u64,..s.progress},..s};
                if s.progress.current_tile_part==params.parts.len(){
                    let omitted=part1_tile_omit_packet(params,s.progress,coordinate,s.precincts.len() as usize);
                    let after=Part1TilePacketExecution {progress:omitted.1,..s};
                    match omitted.0{Err(error)=>Part2PlaneTileStep::Return((Err(error),after)),Ok(())=>Part2PlaneTileStep::Continue(after)}
                }else{
                    let boundary=part1_tile_boundary(params,s.progress);let after=Part1TilePacketExecution {progress:boundary.1,..s};
                    match boundary.0{
                        Err(error)=>Part2PlaneTileStep::Return((Err(error),after)),
                        Ok((changed,more))=>if !changed{Part2PlaneTileStep::Packet(coordinate,after)}
                        else if more{Part2PlaneTileStep::Continue(after)}else{
                            let omitted=part1_tile_omit_packet(params,after.progress,coordinate,after.precincts.len() as usize);
                            let final_state=Part1TilePacketExecution {progress:omitted.1,..after};
                            match omitted.0{Err(error)=>Part2PlaneTileStep::Return((Err(error),final_state)),Ok(())=>Part2PlaneTileStep::Continue(final_state)}
                        },
                    }
                }
            }
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_plane_tile_run(params:Part1TilePacketParameters,s:Part1TilePacketExecution,calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1TilePacketExecution)>
    decreases s.progress.remaining_packets*2+1,
{
    match part2_plane_tile_run_admit(params,s){
        Part2PlaneTileStep::Return(result)=>Some((Ok(result),calls)),
        Part2PlaneTileStep::Continue(after)=>if after.progress.remaining_packets<s.progress.remaining_packets{part2_plane_tile_run(params,after,calls)}else{None},
        Part2PlaneTileStep::Packet(coordinate,after)=>part2_tier1_storage_bind(part2_plane_tile_packet_run(params,after,coordinate,calls),
            |packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|part2_plane_tile_after_packet(params,s.progress.remaining_packets,packet,rest)),
    }
}
pub(crate) open spec fn part2_plane_tile_after_packet(params:Part1TilePacketParameters,budget:u64,packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),calls:Seq<Part2Tier1StorageEvent>)
    ->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1TilePacketExecution)>
    decreases budget*2,
{
    match packet.0{Err(_)=>Some((Ok(packet),calls)),Ok(())=>if packet.1.progress.remaining_packets<budget{part2_plane_tile_run(params,packet.1,calls)}else{None}}
}
pub(crate) open spec fn part2_plane_tile_run_result(params:Part1TilePacketParameters,s:Part1TilePacketExecution,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))->bool {
    part2_tier1_storage_framed(|calls|part2_plane_tile_run(params,s,calls),Ok(result))
}
pub(crate) proof fn part2_plane_tile_run_normal(params:Part1TilePacketParameters,s:Part1TilePacketExecution)
    ensures part2_plane_tile_run_result(params,s,part1_tile_run(params,s)),
    decreases s.progress.remaining_packets*2+1,
{
    reveal_with_fuel(part2_plane_tile_run,2);reveal_with_fuel(part2_plane_tile_after_packet,1);reveal_with_fuel(part1_tile_run,1);
    let result=part1_tile_run(params,s);
    match part2_plane_tile_run_admit(params,s){
        Part2PlaneTileStep::Return(_)=>{part2_tier1_storage_pure(Ok(result));},
        Part2PlaneTileStep::Continue(after)=>{
            assert(after.progress.remaining_packets<s.progress.remaining_packets);
            part2_plane_tile_run_normal(params,after);part2_tier1_storage_eta(|calls|part2_plane_tile_run(params,after,calls),Ok(result));
        },
        Part2PlaneTileStep::Packet(coordinate,after)=>{
            part2_plane_tile_packet_normal(params,after,coordinate);let packet=part1_tile_packet(params,after,coordinate);
            if packet.0.is_ok(){
                assert(packet.1.progress.remaining_packets<s.progress.remaining_packets);
                part2_plane_tile_run_normal(params,packet.1);part2_tier1_storage_eta(|calls|part2_plane_tile_run(params,packet.1,calls),Ok(result));
            }else{part2_tier1_storage_pure(Ok(result));}
            part2_tier1_storage_bind_frame(|calls|part2_plane_tile_packet_run(params,after,coordinate,calls),
                |packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|part2_plane_tile_after_packet(params,s.progress.remaining_packets,packet,rest),Ok(packet),Ok(result));
        },
    }
}
pub(crate) proof fn part2_plane_tile_packet_frames(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,
    result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_plane_tile_packet_result(params,s,coordinate,result),
    ensures part2_tier1_storage_framed(|calls|part2_plane_tile_packet_run(params,s,coordinate,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1TilePacketExecution)>|
            (forall|calls| #[trigger] other(calls)==part2_plane_tile_packet_run(params,s,coordinate,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{part2_tier1_storage_eta(|calls|part2_plane_tile_packet_run(params,s,coordinate,calls),Ok(result));}
pub(crate) proof fn part2_plane_tile_run_packet_step(params:Part1TilePacketParameters,s:Part1TilePacketExecution,coordinate:crate::packet::PacketCoordinate,after:Part1TilePacketExecution)
    requires part2_plane_tile_run_admit(params,s)==Part2PlaneTileStep::Packet(coordinate,after),
    ensures forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_plane_tile_run(params,s,calls)==part2_tier1_storage_bind(part2_plane_tile_packet_run(params,after,coordinate,calls),
        |packet:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|part2_plane_tile_after_packet(params,s.progress.remaining_packets,packet,rest)),
{reveal_with_fuel(part2_plane_tile_run,2);reveal_with_fuel(part2_plane_tile_after_packet,1);}
pub(crate) proof fn part2_plane_tile_run_continue(params:Part1TilePacketParameters,s:Part1TilePacketExecution,after:Part1TilePacketExecution)
    requires part2_plane_tile_run_admit(params,s)==Part2PlaneTileStep::Continue(after),after.progress.remaining_packets<s.progress.remaining_packets,
    ensures forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_plane_tile_run(params,s,calls)==part2_plane_tile_run(params,after,calls),
{reveal_with_fuel(part2_plane_tile_run,2);reveal_with_fuel(part2_plane_tile_after_packet,1);}
pub(crate) proof fn part2_plane_tile_run_join(params:Part1TilePacketParameters,s:Part1TilePacketExecution,
    root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Result<(),crate::DecodeError>,Part1TilePacketExecution)>,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_tier1_storage_framed(root,Ok(result)),forall|calls| #[trigger] root(calls)==part2_plane_tile_run(params,s,calls),
    ensures part2_plane_tile_run_result(params,s,result),
{part2_tier1_storage_eta(root,Ok(result));}
}
