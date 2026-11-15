//! Actual fresh outer rollback owners before the ordered TagTree children.
use super::*;
verus! {
pub enum Part2RollbackOwnerContext {
    States {source:Seq<Part1CodeBlockPacketState>},
    Contexts {states:Seq<Part1CodeBlockPacketState>,source:Seq<crate::packet::CodeBlockPacketContext>},
    Subbands {source:Seq<Part1PacketSubbandState>},
}
pub(crate) open spec fn part2_rollback_owner_count(context:Part2RollbackOwnerContext)->nat {
    match context {Part2RollbackOwnerContext::States {source}=>source.len(),
        Part2RollbackOwnerContext::Contexts {source,..}=>source.len(),
        Part2RollbackOwnerContext::Subbands {source}=>source.len()}
}
#[verifier::opaque]
pub(crate) open spec fn part2_rollback_owner_run(context:Part2RollbackOwnerContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_rollback_owner_count(context);
    if count==0{Some((Ok(()),events))}else if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::RollbackOwnerCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_rollback_owner_result(context:Part2RollbackOwnerContext,result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_rollback_owner_run(context,events),result)
}
pub(crate) proof fn part2_rollback_owner_observed(context:Part2RollbackOwnerContext,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_rollback_owner_count(context)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_rollback_owner_result(context,result),
{
    reveal(part2_rollback_owner_result);reveal(part2_rollback_owner_run);
    let count=part2_rollback_owner_count(context);
    let prefix=if count==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::RollbackOwnerCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_rollback_owner_run(context,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_rollback_owner_run(context,events),prefix,result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_subbands_owner_run(source:Seq<Part1PacketSubbandState>,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part1PacketSubbandState>> {
    part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Subbands {source},events),
        |_:(),rest|part2_subbands_copy_run(source,0,Seq::empty(),rest))
}
pub(crate) proof fn part2_subbands_owner_error(source:Seq<Part1PacketSubbandState>,error:crate::DecodeError)
    requires part2_rollback_owner_result(Part2RollbackOwnerContext::Subbands {source},Err(error)),
    ensures part2_subbands_copy_result(source,Err(error)),
{
    reveal(part2_subbands_copy_result);reveal(part2_subbands_owner_run);reveal(part2_rollback_owner_result);
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::Subbands {source},events),
        |_:(),rest|part2_subbands_copy_run(source,0,Seq::empty(),rest),Err(error),Err(error));
}
pub(crate) proof fn part2_subbands_owner_start(source:Seq<Part1PacketSubbandState>)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_rollback_owner_result(Part2RollbackOwnerContext::Subbands {source},Ok(())),
    ensures part2_cold_phase(|events|part2_subbands_owner_run(source,events),prefix,
        |events|part2_subbands_copy_run(source,0,Seq::empty(),events)),
{
    reveal(part2_rollback_owner_result);reveal(part2_subbands_owner_run);
    let first=|events|part2_rollback_owner_run(Part2RollbackOwnerContext::Subbands {source},events);
    let prefix=part2_cold_witness(first,Ok(()));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_subbands_owner_run(source,prefix+tail)
        ==part2_subbands_copy_run(source,0,Seq::empty(),tail) by{part2_cold_prefix_at(first,prefix,Ok(()),tail);}
    prefix
}
pub(crate) proof fn part2_subbands_owner_normal(source:Seq<Part1PacketSubbandState>)
    ensures part2_subbands_copy_result(source,Ok(source)),
{
    reveal(part2_subbands_copy_result);reveal(part2_subbands_owner_run);reveal(part2_rollback_owner_result);
    part2_rollback_owner_observed(Part2RollbackOwnerContext::Subbands {source},Ok(()));
    part2_subbands_copy_normal_at(source,0,Seq::empty());
    assert(Seq::empty()+source.subrange(0,source.len() as int) =~= source);
    part2_decode_eta(|events|part2_subbands_copy_run(source,0,Seq::empty(),events),Ok(source));
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::Subbands {source},events),
        |_:(),rest|part2_subbands_copy_run(source,0,Seq::empty(),rest),Ok(()),Ok(source));
}
#[verifier::opaque]
pub(crate) open spec fn part2_rollback_snapshot_run(initial:Part1PacketPrecinctState,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part1PacketSubbandState>> {
    part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::States {source:initial.states},events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},rest),
            |_:(),tail|part2_subbands_owner_run(initial.subbands,tail)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_rollback_snapshot_result(initial:Part1PacketPrecinctState,result:Result<Seq<Part1PacketSubbandState>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_rollback_snapshot_run(initial,events),result)
}
pub(crate) proof fn part2_rollback_snapshot_states_error(initial:Part1PacketPrecinctState,error:crate::DecodeError)
    requires part2_rollback_owner_result(Part2RollbackOwnerContext::States {source:initial.states},Err(error)),
    ensures part2_rollback_snapshot_result(initial,Err(error)),
{
    reveal(part2_rollback_snapshot_result);reveal(part2_rollback_snapshot_run);reveal(part2_rollback_owner_result);
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::States {source:initial.states},events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},rest),
            |_:(),tail|part2_subbands_owner_run(initial.subbands,tail)),Err(error),Err(error));
}
pub(crate) proof fn part2_rollback_snapshot_contexts_error(initial:Part1PacketPrecinctState,error:crate::DecodeError)
    requires part2_rollback_owner_result(Part2RollbackOwnerContext::States {source:initial.states},Ok(())),
        part2_rollback_owner_result(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},Err(error)),
    ensures part2_rollback_snapshot_result(initial,Err(error)),
{
    reveal(part2_rollback_snapshot_result);reveal(part2_rollback_snapshot_run);reveal(part2_rollback_owner_result);
    let next=|_:(),tail|part2_subbands_owner_run(initial.subbands,tail);
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},events),next,Err(error),Err(error));
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},events),next),Err(error));
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::States {source:initial.states},events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},rest),next),Ok(()),Err(error));
}
pub(crate) proof fn part2_rollback_snapshot_subbands(initial:Part1PacketPrecinctState,result:Result<Seq<Part1PacketSubbandState>,crate::DecodeError>)
    requires part2_rollback_owner_result(Part2RollbackOwnerContext::States {source:initial.states},Ok(())),
        part2_rollback_owner_result(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},Ok(())),
        part2_subbands_copy_result(initial.subbands,result),
    ensures part2_rollback_snapshot_result(initial,result),
{
    reveal(part2_rollback_snapshot_result);reveal(part2_rollback_snapshot_run);reveal(part2_rollback_owner_result);reveal(part2_subbands_copy_result);
    part2_decode_eta(|events|part2_subbands_owner_run(initial.subbands,events),result);
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},events),
        |_:(),tail|part2_subbands_owner_run(initial.subbands,tail),Ok(()),result);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},events),
        |_:(),tail|part2_subbands_owner_run(initial.subbands,tail)),result);
    part2_cold_bind(|events|part2_rollback_owner_run(Part2RollbackOwnerContext::States {source:initial.states},events),
        |_:(),rest|part2_jpip_snapshot_bind(part2_rollback_owner_run(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},rest),
            |_:(),tail|part2_subbands_owner_run(initial.subbands,tail)),Ok(()),result);
}
pub(crate) proof fn part2_rollback_snapshot_normal(initial:Part1PacketPrecinctState)
    ensures part2_rollback_snapshot_result(initial,Ok(initial.subbands)),
{
    part2_rollback_owner_observed(Part2RollbackOwnerContext::States {source:initial.states},Ok(()));
    part2_rollback_owner_observed(Part2RollbackOwnerContext::Contexts {states:initial.states,source:initial.contexts},Ok(()));
    part2_subbands_owner_normal(initial.subbands);
    part2_rollback_snapshot_subbands(initial,Ok(initial.subbands));
}
}
