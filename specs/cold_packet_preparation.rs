//! Fresh outer packet-owner storage, distinct from inner packed-byte reassembly.
use super::*;
verus! {
pub enum Part2PacketPreparationContext {
    Packed { parts: Seq<Part2OwnedTilePart>, tile: u16 },
    Seen { parts: Seq<Part2OwnedTilePart>, grid: Part1PacketGrid, selection: Option<Seq<u8>> },
}
pub(crate) open spec fn part2_preparation_count(context: Part2PacketPreparationContext) -> usize {
    match context {
        Part2PacketPreparationContext::Packed { parts, .. } => parts.len() as usize,
        Part2PacketPreparationContext::Seen { grid, .. } => grid.packet_count as usize,
    }
}
pub(crate) open spec fn part2_preparation_capacity_run(context: Part2PacketPreparationContext,
    events: Seq<Part2JpipSnapshotEvent>) -> Part2ColdRun<()> {
    let count=part2_preparation_count(context);
    if count==0 {Some((Ok(()),events))} else if events.len()==0 {None} else {
        match events[0] {
            Part2JpipSnapshotEvent::PacketPreparationCapacity {context:actual,elements,succeeded} =>
                if actual!=context || elements!=count {None}
                else {Some((if succeeded {Ok(())} else {Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
            _=>None,
        }
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_preparation_capacity_result(context: Part2PacketPreparationContext, result: Result<(),crate::DecodeError>) -> bool {
    part2_cold_framed(|events|part2_preparation_capacity_run(context,events),result)
}
pub(crate) proof fn part2_preparation_observed(context: Part2PacketPreparationContext,result: Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_preparation_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_preparation_capacity_result(context,result),
{
    reveal(part2_preparation_capacity_result);
    let count=part2_preparation_count(context);
    let calls=if count==0 {Seq::empty()} else {seq![Part2JpipSnapshotEvent::PacketPreparationCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_preparation_capacity_run(context,calls+tail)==Some((result,tail)) by {
        if count==0 {assert(calls+tail =~= tail);} else {assert((calls+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_preparation_capacity_run(context,events),calls,result));
}
pub(crate) open spec fn part2_preparation_initial(tile:u16)->Part1TilePacketPreparation {
    Part1TilePacketPreparation {tile_index:tile,index:0,payload_bytes:0,packed_payload_bytes:0,declared_packets:0,all_lengths:true,packed:Seq::empty()}
}
pub(crate) open spec fn part2_prepare_payloads_run(parts:Seq<Part2OwnedTilePart>,tile:u16,maximum:u64,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Part1TilePacketPreparation> {
    part2_jpip_snapshot_bind(part2_preparation_capacity_run(Part2PacketPreparationContext::Packed {parts,tile},events),
        |_:(),rest|part2_payloads_run(parts,part2_preparation_initial(tile),maximum,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_prepare_payloads_result(parts:Seq<Part2OwnedTilePart>,tile:u16,maximum:u64,
    result:Result<Part1TilePacketPreparation,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_prepare_payloads_run(parts,tile,maximum,events),result)
}
pub(crate) proof fn part2_prepare_payloads_normal(parts:Seq<Part2OwnedTilePart>,tile:u16,maximum:u64)
    ensures part2_prepare_payloads_result(parts,tile,maximum,part1_progression_payloads_owned(parts,part2_preparation_initial(tile),maximum)),
{
    reveal(part2_prepare_payloads_result);reveal(part2_payloads_result);reveal(part2_preparation_capacity_result);
    part2_preparation_observed(Part2PacketPreparationContext::Packed {parts,tile},Ok(()));
    part2_payloads_normal(parts,part2_preparation_initial(tile),maximum);
    let result=part1_progression_payloads_owned(parts,part2_preparation_initial(tile),maximum);
    part2_decode_eta(|events|part2_payloads_run(parts,part2_preparation_initial(tile),maximum,events),result);
    part2_cold_bind(|events|part2_preparation_capacity_run(Part2PacketPreparationContext::Packed {parts,tile},events),
        |_:(),rest|part2_payloads_run(parts,part2_preparation_initial(tile),maximum,rest),Ok(()),result);
}
pub(crate) proof fn part2_prepare_payloads_capacity_error(parts:Seq<Part2OwnedTilePart>,tile:u16,maximum:u64)
    requires part2_preparation_capacity_result(Part2PacketPreparationContext::Packed {parts,tile},Err(crate::DecodeError::AllocationFailed)),
    ensures part2_prepare_payloads_result(parts,tile,maximum,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_prepare_payloads_result);reveal(part2_preparation_capacity_result);
    part2_cold_bind(|events|part2_preparation_capacity_run(Part2PacketPreparationContext::Packed {parts,tile},events),
        |_:(),rest|part2_payloads_run(parts,part2_preparation_initial(tile),maximum,rest),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_prepare_payloads_inner_error(parts:Seq<Part2OwnedTilePart>,tile:u16,maximum:u64,error:crate::DecodeError)
    requires part2_preparation_capacity_result(Part2PacketPreparationContext::Packed {parts,tile},Ok(())),
        part2_payloads_result(parts,part2_preparation_initial(tile),maximum,Err(error)),
    ensures part2_prepare_payloads_result(parts,tile,maximum,Err(error)),
{
    reveal(part2_prepare_payloads_result);reveal(part2_preparation_capacity_result);reveal(part2_payloads_result);
    part2_decode_eta(|events|part2_payloads_run(parts,part2_preparation_initial(tile),maximum,events),Err(error));
    part2_cold_bind(|events|part2_preparation_capacity_run(Part2PacketPreparationContext::Packed {parts,tile},events),
        |_:(),rest|part2_payloads_run(parts,part2_preparation_initial(tile),maximum,rest),Ok(()),Err(error));
}
pub(crate) open spec fn part2_packet_parameters(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,input:Part1TilePacketPreparation,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits)->Part1TilePacketParameters {
    Part1TilePacketParameters {parts,grid,input,selection,caps:Part1TilePacketCaps {
        work:crate::limits::resource_work_limit(limits),header:crate::limits::resource_packet_header_byte_limit(limits),
        blocks:crate::limits::resource_code_block_limit(limits),passes:crate::limits::resource_code_block_pass_limit(limits),
        bytes:crate::limits::resource_code_block_byte_limit(limits),input:crate::limits::resource_input_byte_limit(limits),
    }}
}
pub(crate) open spec fn part2_progress_context(params:Part1TilePacketParameters)->Part2PacketPreparationContext {
    Part2PacketPreparationContext::Seen {parts:params.parts,grid:params.grid,selection:params.selection}
}
pub(crate) open spec fn part2_progress_initial_run(params:Part1TilePacketParameters,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1TilePacketProgress> {
    let initial=part1_tile_progress_initial(params);
    match initial {
        Err(error)=>Some((Err(error),events)),
        Ok(_) =>part2_jpip_snapshot_bind(part2_preparation_capacity_run(part2_progress_context(params),events),|_:(),rest|Some((initial,rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_progress_initial_result(params:Part1TilePacketParameters,result:Result<Part1TilePacketProgress,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_progress_initial_run(params,events),result)
}
pub(crate) proof fn part2_progress_initial_normal(params:Part1TilePacketParameters)
    ensures part2_progress_initial_result(params,part1_tile_progress_initial(params)),
{
    reveal(part2_progress_initial_result);reveal(part2_preparation_capacity_result);
    let initial=part1_tile_progress_initial(params);
    match initial {
        Err(_)=>{part2_cold_pure::<Part1TilePacketProgress>(initial);},
        Ok(_)=>{
            part2_preparation_observed(part2_progress_context(params),Ok(()));
            part2_cold_pure(initial);
            part2_cold_bind(|events|part2_preparation_capacity_run(part2_progress_context(params),events),|_:(),rest|Some((initial,rest)),Ok(()),initial);
        },
    }
}
pub(crate) proof fn part2_progress_initial_refused(params:Part1TilePacketParameters)
    requires part1_tile_progress_initial(params).is_ok(),
        part2_preparation_capacity_result(part2_progress_context(params),Err(crate::DecodeError::AllocationFailed)),
    ensures part2_progress_initial_result(params,Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part2_progress_initial_result);reveal(part2_preparation_capacity_result);
    part2_cold_bind(|events|part2_preparation_capacity_run(part2_progress_context(params),events),
        |_:(),rest|Some((part1_tile_progress_initial(params),rest)),Err(crate::DecodeError::AllocationFailed),Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_packet_stages_actual(owned:bool,parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    precincts:Seq<Part1PacketPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,
    input:Part1TilePacketPreparation,progress:Result<Part1TilePacketProgress,crate::DecodeError>)
    requires part2_packet_input_result(parts,grid,precincts,selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),progress),
    ensures part2_packet_result(owned,parts,grid,precincts,selection,limits,match progress {
        Err(error)=>(Err(error),precincts),Ok(_)=>part1_progression_tile_decode_owned(parts,grid,precincts,selection,limits),
    }),
{
   if let Ok(p)=progress {
       part2_packet_stage_values(parts,grid,precincts,selection,limits,input,p);
       let params=part2_packet_parameters(parts,grid,input,selection,limits);
       let initial=Part1TilePacketExecution {progress:p,precincts};
       part2_plane_tile_run_normal(owned,params,initial);
       let result=part1_tile_run(params,initial);
       part2_packet_run_observed(owned,parts,grid,precincts,selection,limits,input,p,result);
   }else{
    reveal(part2_packet_result);reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let before=|events|part2_packet_input_run(parts,grid,precincts,selection,limits,events);
    let after=|events|part2_progress_initial_run(part2_packet_parameters(parts,grid,input,selection,limits),events);
    let first=part2_cold_witness(before,Ok(input));
    let second=part2_cold_witness(after,progress);
    let result=match progress {Err(error)=>(Err(error),precincts),Ok(_)=>part1_progression_tile_decode_owned(parts,grid,precincts,selection,limits)};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_packet_run(owned,parts,grid,precincts,selection,limits,(first+second)+tail)==Some((result,tail)) by {
        assert((first+second)+tail =~= first+(second+tail));
        part2_cold_prefix_at(before,first,Ok(input),second+tail);
        part2_cold_prefix_at(after,second,progress,tail);
    }
    assert(part2_packet_prefix(owned,parts,grid,precincts,selection,limits,first+second,result));
   }
}
pub(crate) proof fn part2_packet_progress_error(owned:bool,parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,
    precincts:Seq<Part1PacketPrecinctState>,selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,error:crate::DecodeError)
    requires part2_packet_input_result(parts,grid,precincts,selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Err(error)),
    ensures part2_packet_result(owned,parts,grid,precincts,selection,limits,(Err(error),precincts)),
{
    part2_packet_stages_actual(owned,parts,grid,precincts,selection,limits,input,Err(error));
}
}
