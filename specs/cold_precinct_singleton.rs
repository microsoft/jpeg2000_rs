//! The actual public singleton execution wrapper, before precinct admission.
use super::*;
verus! {
pub open spec fn part2_precinct_singleton_execution(geometry:crate::packet::PacketPrecinctGeometry,decoders:Seq<Tier1DecoderState>)->Part2PacketSubbandExecution {
    Part2PacketSubbandExecution {orientation:crate::tier1::SubbandOrientation::Ll,
        across:geometry.code_blocks_across,down:geometry.code_blocks_down,
        maximum_zero:geometry.maximum_zero_bitplanes,decoders}
}
#[verifier::opaque]
pub(crate) open spec fn part2_singleton_capacity_run(execution:Part2PacketSubbandExecution,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::PrecinctSingletonCapacity {execution:actual,elements,succeeded}=>
            if actual!=execution || elements!=1{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_singleton_values_run(execution:Part2PacketSubbandExecution,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2PacketSubbandExecution>> {
    part2_jpip_snapshot_bind(part2_singleton_capacity_run(execution,events),
        |_:(),rest|Some((Ok(seq![execution]),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_singleton_values_result(execution:Part2PacketSubbandExecution,result:Result<Seq<Part2PacketSubbandExecution>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_singleton_values_run(execution,events),result)
}
pub(crate) proof fn part2_singleton_values_observed(execution:Part2PacketSubbandExecution,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || result==Err(crate::DecodeError::AllocationFailed),
    ensures part2_singleton_values_result(execution,match result{Err(error)=>Err(error),Ok(())=>Ok(seq![execution])}),
{
    reveal(part2_singleton_values_result);reveal(part2_singleton_values_run);reveal(part2_singleton_capacity_run);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(seq![execution])};
    let prefix=seq![Part2JpipSnapshotEvent::PrecinctSingletonCapacity {execution,elements:1,succeeded:result.is_ok()}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_singleton_values_run(execution,prefix+tail)==Some((value,tail)) by{
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_singleton_values_run(execution,events),prefix,value));
}
#[verifier::opaque]
pub(crate) open spec fn part2_precinct_singleton_run(geometry:crate::packet::PacketPrecinctGeometry,style:crate::tier1::Tier1CodingStyle,
    decoders:Seq<Tier1DecoderState>,limits:&crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part1PacketPrecinctState> {
    part2_jpip_snapshot_bind(part2_singleton_values_run(part2_precinct_singleton_execution(geometry,decoders),events),
        |executions:Seq<Part2PacketSubbandExecution>,rest|part2_precinct_state_run(
            geometry.component,geometry.resolution,geometry.precinct,style,executions,limits,rest))
}
pub closed spec fn part1_precinct_singleton_storage_result(geometry:crate::packet::PacketPrecinctGeometry,style:crate::tier1::Tier1CodingStyle,
    decoders:Seq<Tier1DecoderState>,limits:&crate::ResourceLimits,result:Result<Part1PacketPrecinctState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_precinct_singleton_run(geometry,style,decoders,limits,events),result)
}
pub closed spec fn part1_precinct_subbands_storage_result(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits,result:Result<Part1PacketPrecinctState,crate::DecodeError>)->bool {
    part2_precinct_state_result(component,resolution,precinct,style,executions,limits,result)
}
pub(crate) proof fn part2_precinct_subbands_observed(component:u16,resolution:u8,precinct:u32,style:crate::tier1::Tier1CodingStyle,
    executions:Seq<Part2PacketSubbandExecution>,limits:&crate::ResourceLimits,result:Result<Part1PacketPrecinctState,crate::DecodeError>)
    requires part2_precinct_state_result(component,resolution,precinct,style,executions,limits,result),
    ensures part1_precinct_subbands_storage_result(component,resolution,precinct,style,executions,limits,result),
{}
pub(crate) proof fn part2_precinct_singleton_observed(geometry:crate::packet::PacketPrecinctGeometry,style:crate::tier1::Tier1CodingStyle,
    decoders:Seq<Tier1DecoderState>,limits:&crate::ResourceLimits,first:Result<Seq<Part2PacketSubbandExecution>,crate::DecodeError>,
    result:Result<Part1PacketPrecinctState,crate::DecodeError>)
    requires part2_singleton_values_result(part2_precinct_singleton_execution(geometry,decoders),first),
        match first {Err(error)=>result==Err(error),Ok(executions)=>part1_precinct_subbands_storage_result(
            geometry.component,geometry.resolution,geometry.precinct,style,executions,limits,result)},
    ensures part1_precinct_singleton_storage_result(geometry,style,decoders,limits,result),
{
    reveal(part2_singleton_values_result);reveal(part2_precinct_singleton_run);
    let execution=part2_precinct_singleton_execution(geometry,decoders);
    if let Ok(executions)=first{
        part2_precinct_state_frames(geometry.component,geometry.resolution,geometry.precinct,style,executions,limits,result);
    }
    part2_cold_bind(|events|part2_singleton_values_run(execution,events),
        |executions:Seq<Part2PacketSubbandExecution>,rest|part2_precinct_state_run(
            geometry.component,geometry.resolution,geometry.precinct,style,executions,limits,rest),first,result);
}
pub(crate) proof fn part2_precinct_singleton_normal(geometry:crate::packet::PacketPrecinctGeometry,style:crate::tier1::Tier1CodingStyle,
    decoders:Seq<Tier1DecoderState>,limits:&crate::ResourceLimits)
    ensures part1_precinct_singleton_storage_result(geometry,style,decoders,limits,
        part2_precinct_from_executions(geometry.component,geometry.resolution,geometry.precinct,style,
            seq![part2_precinct_singleton_execution(geometry,decoders)],limits)),
{
    let execution=part2_precinct_singleton_execution(geometry,decoders);
    let result=part2_precinct_from_executions(geometry.component,geometry.resolution,geometry.precinct,style,seq![execution],limits);
    part2_singleton_values_observed(execution,Ok(()));
    part2_precinct_state_normal(geometry.component,geometry.resolution,geometry.precinct,style,seq![execution],limits);
    part2_precinct_singleton_observed(geometry,style,decoders,limits,Ok(seq![execution]),result);
}
}
