//! Input-derived packet acquisition with actual rollback-copy responses.
use super::*;
verus! {
pub(crate) struct Part2CopyPacketDecode {
    pub coordinate:crate::packet::PacketCoordinate,pub execution:usize,pub part:Part2OwnedTilePart,
    pub id:Part2JpipDatabin,pub prefix:Seq<u8>,pub offset:u64,pub sequence:u16,
}
pub(crate) enum Part2CopyPacketStep {
    Return(Result<Part2JpipSnapshotPacketState,crate::DecodeError>),
    Next(Part2JpipSnapshotPacketState),
    Decode(Part2CopyPacketDecode),
}
pub(crate) open spec fn part2_copy_packet_admit(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,index:nat,state:Part2JpipSnapshotPacketState)->Part2CopyPacketStep {
    if index>=order.len(){Part2CopyPacketStep::Return(Ok(state))}else{
        let coordinate=order[index as int].0;let execution=order[index as int].1;
        if execution as nat>=state.blocked.len(){Part2CopyPacketStep::Return(Err(part2_jpip_range_overflow(0)))}
        else if state.blocked[execution as int]{Part2CopyPacketStep::Next(state)}
        else if state.transition as nat>=parts.len(){Part2CopyPacketStep::Return(Err(part2_jpip_cache_error(0,crate::MalformedKind::InvalidTilePart)))}
        else if execution as nat>=databins.len() || execution as nat>=state.offsets.len(){Part2CopyPacketStep::Return(Err(part2_jpip_range_overflow(0)))}
        else{
            let id=databins[execution as int];let prefix=part2_jpip_cache_prefix(input.cache,id);let offset=state.offsets[execution as int];
            if offset>usize::MAX as u64{Part2CopyPacketStep::Return(Err(part2_jpip_range_overflow(0)))}
            else if offset as nat>=prefix.len(){Part2CopyPacketStep::Next(Part2JpipSnapshotPacketState {blocked:state.blocked.update(execution as int,true),..state})}
            else if execution as nat>=state.precincts.len(){Part2CopyPacketStep::Return(Err(part2_jpip_range_overflow(0)))}
            else{Part2CopyPacketStep::Decode(Part2CopyPacketDecode {coordinate,execution,part:parts[state.transition as int],id,prefix,offset,sequence:((index as usize)&65535) as u16})}
        }
    }
}
pub(crate) open spec fn part2_copy_packet_finish(input:Part2JpipSnapshotInput<'_>,transitions:Seq<Part2JpipTransition>,
    before:Part2JpipSnapshotPacketState,admit:Part2CopyPacketDecode,decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState))
    ->Result<Part2JpipSnapshotPacketState,crate::DecodeError> {
    let execution=admit.execution;let coordinate=admit.coordinate;let offset=admit.offset;let prefix=admit.prefix;
    let state=Part2JpipSnapshotPacketState {precincts:before.precincts.update(execution as int,decoded.1),..before};
    match decoded.0 {
        Err(crate::DecodeError::MalformedInput {offset:_,kind:crate::MalformedKind::Truncated}) if !part2_jpip_cache_complete(input.cache,admit.id)=>
            Ok(Part2JpipSnapshotPacketState {blocked:state.blocked.update(execution as int,true),..state}),
        Err(error)=>Err(error),
        Ok(consumed)=>if consumed==0{Err(part2_jpip_cache_error(offset,crate::MalformedKind::InvalidPacketLength))}
        else if offset as nat+consumed as nat>usize::MAX as nat{Err(part2_jpip_range_overflow(offset))}
        else{
            let end=offset as nat+consumed as nat;
            if end>prefix.len(){Err(part2_jpip_cache_error(offset,crate::MalformedKind::Truncated))}
            else if execution as nat>=state.parsed.len() || coordinate.layer as nat>=state.parsed[execution as int].len(){Err(part2_jpip_range_overflow(0))}
            else if state.packets==u64::MAX || state.bytes as nat+(consumed as u64) as nat>u64::MAX as nat{Err(part2_jpip_range_overflow(0))}
            else if state.transition as nat>=transitions.len(){Err(part2_jpip_cache_error(0,crate::MalformedKind::InvalidTilePart))}
            else if state.transition==usize::MAX{Err(part2_jpip_range_overflow(0))}
            else{
                let packets=(state.packets+1) as u64;let bytes=(state.bytes as nat+(consumed as u64) as nat) as u64;
                let transition=transitions[state.transition as int];
                let boundary=match transition.2{Some(count)=>packets==count,None=>match transition.3{Some(length)=>bytes==length,None=>false}};
                let advance=boundary && state.transition as nat+1<transitions.len();
                Ok(Part2JpipSnapshotPacketState {
                    parsed:state.parsed.update(execution as int,state.parsed[execution as int].update(coordinate.layer as int,Some(prefix.subrange(offset as int,end as int)))),
                    offsets:state.offsets.update(execution as int,end as u64),transition:if advance{(state.transition+1) as usize}else{state.transition},
                    packets:if advance{0}else{packets},bytes:if advance{0}else{bytes},..state})
            }
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_copy_packets_run(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,index:nat,state:Part2JpipSnapshotPacketState,events:Seq<Part2JpipSnapshotEvent>)
    ->Part2ColdRun<Part2JpipSnapshotPacketState>
    decreases if index<order.len(){order.len()-index}else{0},
{
    match part2_copy_packet_admit(input,parts,databins,order,index,state){
        Part2CopyPacketStep::Return(result)=>Some((result,events)),
        Part2CopyPacketStep::Next(after)=>part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,events),
        Part2CopyPacketStep::Decode(admit)=>part2_jpip_snapshot_bind(
            part2_jpip_packet_copy_run(state.precincts[admit.execution as int],admit.part,admit.prefix.subrange(admit.offset as int,admit.prefix.len() as int),admit.sequence,admit.coordinate.layer,input.limits,events),
            |decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState),rest|match part2_copy_packet_finish(input,transitions,state,admit,decoded){
                Err(error)=>Some((Err(error),rest)),Ok(after)=>part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,rest),
            }),
    }
}
pub(crate) proof fn part2_copy_packets_normal(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,index:nat,state:Part2JpipSnapshotPacketState)
    ensures part2_cold_framed(|events|part2_copy_packets_run(input,parts,transitions,databins,order,index,state,events),
        part2_jpip_snapshot_parse_packets(input,parts,transitions,databins,order,index,state)),
    decreases if index<order.len(){order.len()-index}else{0},
{
    reveal_with_fuel(part2_copy_packets_run,1);reveal_with_fuel(part2_jpip_snapshot_parse_packets,1);
    let result=part2_jpip_snapshot_parse_packets(input,parts,transitions,databins,order,index,state);
    match part2_copy_packet_admit(input,parts,databins,order,index,state){
        Part2CopyPacketStep::Return(_)=>{part2_cold_pure(result);},
        Part2CopyPacketStep::Next(after)=>{
            part2_copy_packets_normal(input,parts,transitions,databins,order,index+1,after);
            part2_decode_eta(|events|part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,events),result);
        },
        Part2CopyPacketStep::Decode(admit)=>{
            let source=state.precincts[admit.execution as int];let data=admit.prefix.subrange(admit.offset as int,admit.prefix.len() as int);
            let decoded=part2_jpip_snapshot_decode_packet(source,admit.part,data,admit.sequence,admit.coordinate.layer,input.limits);
            part2_jpip_packet_copy_normal(source,admit.part,data,admit.sequence,admit.coordinate.layer,input.limits);
            part2_jpip_packet_copy_frames(source,admit.part,data,admit.sequence,admit.coordinate.layer,input.limits,decoded);
            match part2_copy_packet_finish(input,transitions,state,admit,decoded){
                Err(_)=>{part2_cold_pure(result);},
                Ok(after)=>{
                    part2_copy_packets_normal(input,parts,transitions,databins,order,index+1,after);
                    part2_decode_eta(|events|part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,events),result);
                },
            }
            part2_cold_bind(|events|part2_jpip_packet_copy_run(source,admit.part,data,admit.sequence,admit.coordinate.layer,input.limits,events),
                |decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState),rest|match part2_copy_packet_finish(input,transitions,state,admit,decoded){
                    Err(error)=>Some((Err(error),rest)),Ok(after)=>part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,rest),
                },Ok(decoded),result);
        },
    }
}
pub(crate) proof fn part2_copy_packets_skip(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,index:nat,state:Part2JpipSnapshotPacketState,after:Part2JpipSnapshotPacketState)
    requires part2_copy_packet_admit(input,parts,databins,order,index,state)==Part2CopyPacketStep::Next(after),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_copy_packets_run(input,parts,transitions,databins,order,index,state,events)
        ==part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,events),
{reveal_with_fuel(part2_copy_packets_run,1);}
pub(crate) proof fn part2_copy_packets_end(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,index:nat,state:Part2JpipSnapshotPacketState)
    requires index>=order.len(),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_copy_packets_run(input,parts,transitions,databins,order,index,state,events)==Some((Ok(state),events)),
{reveal_with_fuel(part2_copy_packets_run,1);}
pub(crate) proof fn part2_copy_packets_decode(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,index:nat,state:Part2JpipSnapshotPacketState,admit:Part2CopyPacketDecode)
    requires part2_copy_packet_admit(input,parts,databins,order,index,state)==Part2CopyPacketStep::Decode(admit),
    ensures forall|events:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_copy_packets_run(input,parts,transitions,databins,order,index,state,events)
        ==part2_jpip_snapshot_bind(part2_jpip_packet_copy_run(state.precincts[admit.execution as int],admit.part,
            admit.prefix.subrange(admit.offset as int,admit.prefix.len() as int),admit.sequence,admit.coordinate.layer,input.limits,events),
            |decoded:(Result<usize,crate::DecodeError>,Part1PacketPrecinctState),rest|match part2_copy_packet_finish(input,transitions,state,admit,decoded){
                Err(error)=>Some((Err(error),rest)),Ok(after)=>part2_copy_packets_run(input,parts,transitions,databins,order,index+1,after,rest),
            }),
{reveal_with_fuel(part2_copy_packets_run,1);}
pub(crate) open spec fn part2_copy_packets_normal_calls(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,initial:Part2JpipSnapshotPacketState)->Seq<Part2JpipSnapshotEvent> {
    let run=|events|part2_copy_packets_run(input,parts,transitions,databins,order,0,initial,events);
    choose|calls| #[trigger] part2_cold_prefix(run,calls,
        part2_jpip_snapshot_parse_packets(input,parts,transitions,databins,order,0,initial))
}
pub(crate) proof fn part2_copy_packets_normal_calls_known(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,initial:Part2JpipSnapshotPacketState)
    ensures part2_cold_prefix(|events|part2_copy_packets_run(input,parts,transitions,databins,order,0,initial,events),
        part2_copy_packets_normal_calls(input,parts,transitions,databins,order,initial),
        part2_jpip_snapshot_parse_packets(input,parts,transitions,databins,order,0,initial)),
{part2_copy_packets_normal(input,parts,transitions,databins,order,0,initial);}
pub(crate) proof fn part2_copy_packets_normal_at(input:Part2JpipSnapshotInput<'_>,parts:Seq<Part2OwnedTilePart>,transitions:Seq<Part2JpipTransition>,
    databins:Seq<Part2JpipDatabin>,order:Part2JpipSnapshotOrder,initial:Part2JpipSnapshotPacketState,tail:Seq<Part2JpipSnapshotEvent>)
    ensures part2_copy_packets_run(input,parts,transitions,databins,order,0,initial,
        part2_copy_packets_normal_calls(input,parts,transitions,databins,order,initial)+tail)
        ==Some((part2_jpip_snapshot_parse_packets(input,parts,transitions,databins,order,0,initial),tail)),
{
    part2_copy_packets_normal_calls_known(input,parts,transitions,databins,order,initial);
    part2_cold_prefix_at(|events|part2_copy_packets_run(input,parts,transitions,databins,order,0,initial,events),
        part2_copy_packets_normal_calls(input,parts,transitions,databins,order,initial),
        part2_jpip_snapshot_parse_packets(input,parts,transitions,databins,order,0,initial),tail);
}
}
