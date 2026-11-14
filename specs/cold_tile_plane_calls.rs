//! A tile-run caller envelope, not an additional physical storage request.
use super::*;
verus! {
pub(crate) open spec fn part2_tile_plane_calls_run(params:Part1TilePacketParameters,initial:Part1TilePacketExecution,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<(Result<(),crate::DecodeError>,Part1TilePacketExecution)> {
    if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::TilePlaneCalls {params:actual,initial:before,calls}=>if actual!=params || before!=initial{None}else{
            match part2_plane_tile_run(params,initial,calls){
                Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None,
            }
        },
        _=>None,
    }}
}
pub(crate) proof fn part2_tile_plane_calls_observed(params:Part1TilePacketParameters,initial:Part1TilePacketExecution,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_plane_tile_run_result(params,initial,result),
    ensures part2_cold_framed(|events|part2_tile_plane_calls_run(params,initial,events),Ok(result)),
{
    reveal(part2_plane_tile_run_result);
    let raw=|calls|part2_plane_tile_run(params,initial,calls);
    let calls=choose|calls| #[trigger] part2_tier1_storage_prefix(raw,calls,Ok(result));
    assert(calls+Seq::empty() =~= calls);
    part2_tier1_storage_at(raw,calls,Ok(result),Seq::empty());
    let prefix=seq![Part2JpipSnapshotEvent::TilePlaneCalls {params,initial,calls}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_tile_plane_calls_run(params,initial,prefix+tail)==Some((Ok(result),tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_tile_plane_calls_run(params,initial,events),prefix,Ok(result)));
    part2_decode_eta(|events|part2_tile_plane_calls_run(params,initial,events),Ok(result));
}
pub(crate) open spec fn part2_packet_plane_finish(params:Part1TilePacketParameters,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    ->(Result<crate::packet::TilePacketDecode,crate::DecodeError>,Seq<Part1PacketPrecinctState>) {
    (match result.0{Err(error)=>Err(error),Ok(())=>part1_tile_finish(params,result.1.progress).0},result.1.precincts)
}
pub(crate) open spec fn part2_packet_after_progress_run(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,progress:Part1TilePacketProgress,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<(Result<crate::packet::TilePacketDecode,crate::DecodeError>,Seq<Part1PacketPrecinctState>)> {
    let params=part2_packet_parameters(parts,grid,input,selection,limits);
    part2_jpip_snapshot_bind(part2_tile_plane_calls_run(params,Part1TilePacketExecution {progress,precincts},events),
        |result:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|Some((Ok(part2_packet_plane_finish(params,result)),rest)))
}
pub(crate) proof fn part2_packet_after_progress_observed(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,progress:Part1TilePacketProgress,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_plane_tile_run_result(part2_packet_parameters(parts,grid,input,selection,limits),Part1TilePacketExecution {progress,precincts},result),
    ensures part2_cold_framed(|events|part2_packet_after_progress_run(parts,grid,precincts,selection,limits,input,progress,events),
        Ok(part2_packet_plane_finish(part2_packet_parameters(parts,grid,input,selection,limits),result))),
{
    let params=part2_packet_parameters(parts,grid,input,selection,limits);
    let initial=Part1TilePacketExecution {progress,precincts};
    part2_tile_plane_calls_observed(params,initial,result);
    part2_cold_pure(Ok(part2_packet_plane_finish(params,result)));
    part2_cold_bind(|events|part2_tile_plane_calls_run(params,initial,events),
        |result:(Result<(),crate::DecodeError>,Part1TilePacketExecution),rest|Some((Ok(part2_packet_plane_finish(params,result)),rest)),Ok(result),Ok(part2_packet_plane_finish(params,result)));
}
pub(crate) proof fn part2_packet_stage_values(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,progress:Part1TilePacketProgress)
    requires part2_packet_input_result(parts,grid,precincts,selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Ok(progress)),
    ensures part1_progression_tile_input_owned(parts,grid,precincts,selection,limits)==Ok(input),
        part1_tile_progress_initial(part2_packet_parameters(parts,grid,input,selection,limits))==Ok(progress),
{
    reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let first=|events|part2_packet_input_run(parts,grid,precincts,selection,limits,events);
    let calls=part2_cold_witness(first,Ok(input));part2_cold_prefix_at(first,calls,Ok(input),Seq::empty());assert(calls+Seq::empty() =~= calls);
    let params=part2_packet_parameters(parts,grid,input,selection,limits);
    let second=|events|part2_progress_initial_run(params,events);
    let next=part2_cold_witness(second,Ok(progress));part2_cold_prefix_at(second,next,Ok(progress),Seq::empty());assert(next+Seq::empty() =~= next);
}
pub(crate) proof fn part2_packet_run_observed(parts:Seq<Part2OwnedTilePart>,grid:Part1PacketGrid,precincts:Seq<Part1PacketPrecinctState>,
    selection:Option<Seq<u8>>,limits:&crate::ResourceLimits,input:Part1TilePacketPreparation,progress:Part1TilePacketProgress,result:(Result<(),crate::DecodeError>,Part1TilePacketExecution))
    requires part2_packet_input_result(parts,grid,precincts,selection,limits,Ok(input)),
        part2_progress_initial_result(part2_packet_parameters(parts,grid,input,selection,limits),Ok(progress)),
        part2_plane_tile_run_result(part2_packet_parameters(parts,grid,input,selection,limits),Part1TilePacketExecution {progress,precincts},result),
    ensures part2_packet_result(parts,grid,precincts,selection,limits,part2_packet_plane_finish(part2_packet_parameters(parts,grid,input,selection,limits),result)),
{
    reveal(part2_packet_result);reveal(part2_packet_input_result);reveal(part2_progress_initial_result);
    let before=|events|part2_packet_input_run(parts,grid,precincts,selection,limits,events);
    let after=|events|part2_progress_initial_run(part2_packet_parameters(parts,grid,input,selection,limits),events);
    let first=part2_cold_witness(before,Ok(input));let second=part2_cold_witness(after,Ok(progress));
    part2_packet_after_progress_observed(parts,grid,precincts,selection,limits,input,progress,result);
    let child=|events|part2_packet_after_progress_run(parts,grid,precincts,selection,limits,input,progress,events);
    let output=part2_packet_plane_finish(part2_packet_parameters(parts,grid,input,selection,limits),result);
    let third=part2_cold_witness(child,Ok(output));
    let prefix=(first+second)+third;
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_packet_run(parts,grid,precincts,selection,limits,prefix+tail)==Some((output,tail)) by{
        assert(prefix+tail =~= first+(second+(third+tail)));
        part2_cold_prefix_at(before,first,Ok(input),second+(third+tail));
        part2_cold_prefix_at(after,second,Ok(progress),third+tail);
        part2_cold_prefix_at(child,third,Ok(output),tail);
    }
    assert(part2_packet_prefix(parts,grid,precincts,selection,limits,prefix,output));
}
}
