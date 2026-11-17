//! Ordered owned-header copies with actual capacity replies and framed tails.
use super::*;
verus! {
pub enum Part2HeaderCloneRole {
    Icc,
    PaletteColumns,
    PaletteValues,
    Mappings,
    Definitions,
}
pub(crate) open spec fn part2_header_clone_role(index:nat)->Part2HeaderCloneRole {
    if index==0 {Part2HeaderCloneRole::Icc}
    else if index==1 {Part2HeaderCloneRole::PaletteColumns}
    else if index==2 {Part2HeaderCloneRole::PaletteValues}
    else if index==3 {Part2HeaderCloneRole::Mappings}
    else {Part2HeaderCloneRole::Definitions}
}
pub(crate) open spec fn part2_header_clone_count(source:Part2RawJp2Header,role:Part2HeaderCloneRole)->nat {
    match role {
        Part2HeaderCloneRole::Icc=>match source.color.3 {None=>0,Some(bytes)=>bytes.len()},
        Part2HeaderCloneRole::PaletteColumns=>match source.palette {None=>0,Some(palette)=>palette.1.len()},
        Part2HeaderCloneRole::PaletteValues=>match source.palette {None=>0,Some(palette)=>palette.2.len()},
        Part2HeaderCloneRole::Mappings=>source.mappings.len(),
        Part2HeaderCloneRole::Definitions=>source.definitions.len(),
    }
}
pub(crate) open spec fn part2_header_clone_capacity_run(source:Part2RawJp2Header,role:Part2HeaderCloneRole,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_header_clone_count(source,role);
    if count==0 {Some((Ok(()),events))}
    else if events.len()==0 {None}
    else {match events[0] {
        Part2JpipSnapshotEvent::HeaderCloneCapacity {source:actual,role:actual_role,elements,succeeded}=>
            if actual!=source || actual_role!=role || elements!=count {None}
            else {Some((if succeeded {Ok(())} else {Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_header_clone_capacity_result(source:Part2RawJp2Header,role:Part2HeaderCloneRole,
    response:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_header_clone_capacity_run(source,role,events),response)
}
pub(crate) proof fn part2_header_clone_capacity_observed(source:Part2RawJp2Header,role:Part2HeaderCloneRole,
    response:Result<(),crate::DecodeError>)
    requires response==Ok(()) ||
        (response==Err(crate::DecodeError::AllocationFailed) && part2_header_clone_count(source,role)>0),
    ensures part2_header_clone_capacity_result(source,role,response),
{
    let count=part2_header_clone_count(source,role);
    let prefix=if count==0 {Seq::empty()} else {
        seq![Part2JpipSnapshotEvent::HeaderCloneCapacity {source,role,elements:count,succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_header_clone_capacity_run(source,role,prefix+tail)==Some((response,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}
        else {assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_header_clone_capacity_run(source,role,events),prefix,response));
}
pub(crate) proof fn part2_header_clone_capacity_frames(source:Part2RawJp2Header,role:Part2HeaderCloneRole,
    response:Result<(),crate::DecodeError>)
    requires part2_header_clone_capacity_result(source,role,response),
    ensures part2_cold_framed(|events|part2_header_clone_capacity_run(source,role,events),response),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_header_clone_capacity_run(source,role,events)) ==>
                #[trigger] part2_cold_framed(other,response),
{
    part2_decode_eta(|events|part2_header_clone_capacity_run(source,role,events),response);
}
#[verifier::opaque]
pub(crate) open spec fn part2_header_clone_prefix_run(source:Part2RawJp2Header,count:nat,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>
    decreases count,
{
    if count==0 {Some((Ok(()),events))}
    else {part2_jpip_snapshot_bind(part2_header_clone_prefix_run(source,(count-1) as nat,events),
        |_:(),rest|part2_header_clone_capacity_run(source,part2_header_clone_role((count-1) as nat),rest))}
}
pub(crate) open spec fn part2_header_clone_storage_run(source:Part2RawJp2Header,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header> {
    part2_jpip_snapshot_bind(part2_header_clone_prefix_run(source,5,events),
        |_:(),rest|Some((Ok(source),rest)))
}
pub closed spec fn part2_header_clone_storage_result(source:Part2RawJp2Header,
    result:Result<Part2RawJp2Header,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_header_clone_storage_run(source,events),result)
}
pub(crate) proof fn part2_header_clone_prefix_normal(source:Part2RawJp2Header,count:nat)
    ensures part2_cold_framed(|events|part2_header_clone_prefix_run(source,count,events),Ok(())),
    decreases count,
{
    reveal_with_fuel(part2_header_clone_prefix_run,1);
    if count==0 {part2_cold_pure(Ok(()));}
    else {
        part2_header_clone_prefix_normal(source,(count-1) as nat);
        let role=part2_header_clone_role((count-1) as nat);
        part2_header_clone_capacity_observed(source,role,Ok(()));
        part2_header_clone_capacity_frames(source,role,Ok(()));
        part2_cold_bind(|events|part2_header_clone_prefix_run(source,(count-1) as nat,events),
            |_:(),rest|part2_header_clone_capacity_run(source,role,rest),Ok(()),Ok(()));
    }
}
pub(crate) proof fn part2_header_clone_prefix_error(source:Part2RawJp2Header,from:nat,to:nat,error:crate::DecodeError)
    requires from<=to,
        part2_cold_framed(|events|part2_header_clone_prefix_run(source,from,events),Err(error)),
    ensures part2_cold_framed(|events|part2_header_clone_prefix_run(source,to,events),Err(error)),
    decreases to-from,
{
    if from<to {
        reveal_with_fuel(part2_header_clone_prefix_run,1);
        part2_header_clone_prefix_error(source,from,(to-1) as nat,error);
        part2_cold_bind(|events|part2_header_clone_prefix_run(source,(to-1) as nat,events),
            |_:(),rest|part2_header_clone_capacity_run(source,part2_header_clone_role((to-1) as nat),rest),
            Err(error),Err(error));
    }
}
pub(crate) proof fn part2_header_clone_stage(source:Part2RawJp2Header,index:nat,response:Result<(),crate::DecodeError>)
    requires index<5,
        response==Ok(()) || response==Err(crate::DecodeError::AllocationFailed),
        part2_cold_framed(|events|part2_header_clone_prefix_run(source,index,events),Ok(())),
        part2_header_clone_capacity_result(source,part2_header_clone_role(index),response),
    ensures response.is_ok() ==>
            part2_cold_framed(|events|part2_header_clone_prefix_run(source,index+1,events),Ok(())),
        response.is_err() ==> part2_header_clone_storage_result(source,Err(response.get_Err_0())),
{
    reveal_with_fuel(part2_header_clone_prefix_run,1);
    part2_header_clone_capacity_frames(source,part2_header_clone_role(index),response);
    part2_cold_bind(|events|part2_header_clone_prefix_run(source,index,events),
        |_:(),rest|part2_header_clone_capacity_run(source,part2_header_clone_role(index),rest),Ok(()),response);
    if let Err(error)=response {
        part2_header_clone_prefix_error(source,index+1,5,error);
        part2_cold_bind(|events|part2_header_clone_prefix_run(source,5,events),
            |_:(),rest|Some((Ok(source),rest)),Err(error),Err(error));
    }
}
pub(crate) proof fn part2_header_clone_success(source:Part2RawJp2Header)
    requires part2_cold_framed(|events|part2_header_clone_prefix_run(source,5,events),Ok(())),
    ensures part2_header_clone_storage_result(source,Ok(source)),
{
    part2_cold_pure(Ok(source));
    part2_cold_bind(|events|part2_header_clone_prefix_run(source,5,events),
        |_:(),rest|Some((Ok(source),rest)),Ok(()),Ok(source));
}
pub(crate) proof fn part2_header_clone_copied<T>(source:Part2RawJp2Header,index:nat,input:Seq<T>,
    result:Result<Vec<T>,crate::DecodeError>)
    requires index<5,
        part2_header_clone_count(source,part2_header_clone_role(index))==input.len(),
        storage_copy_result(input,result),
        part2_cold_framed(|events|part2_header_clone_prefix_run(source,index,events),Ok(())),
    ensures result.is_ok() ==>
            part2_cold_framed(|events|part2_header_clone_prefix_run(source,index+1,events),Ok(())),
        result.is_err() ==> part2_header_clone_storage_result(source,Err(result.get_Err_0())),
{
    let response=crate::allocation::inspection_capacity_outcome(result);
    part2_header_clone_capacity_observed(source,part2_header_clone_role(index),response);
    part2_header_clone_stage(source,index,response);
}
pub(crate) proof fn part2_header_clone_storage_normal(source:Part2RawJp2Header)
    ensures part2_header_clone_storage_result(source,Ok(source)),
{
    part2_header_clone_prefix_normal(source,5);
    part2_header_clone_success(source);
}
pub(crate) proof fn part2_header_clone_storage_frames(source:Part2RawJp2Header,
    result:Result<Part2RawJp2Header,crate::DecodeError>)
    requires part2_header_clone_storage_result(source,result),
    ensures part2_cold_framed(|events|part2_header_clone_storage_run(source,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header>|
            (forall|events| #[trigger] other(events)==part2_header_clone_storage_run(source,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_header_clone_storage_run(source,events),result);
}
pub(crate) open spec fn part2_association_clone_storage_run(source:Part2RawCodestreamAssociation,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawCodestreamAssociation> {
    match source.2 {
        None=>Some((Ok(source),events)),
        Some(header)=>part2_jpip_snapshot_bind(part2_header_clone_storage_run(header,events),
            |cloned:Part2RawJp2Header,rest|Some((Ok((source.0,source.1,Some(cloned))),rest))),
    }
}
pub closed spec fn part2_association_clone_storage_result(source:Part2RawCodestreamAssociation,
    result:Result<Part2RawCodestreamAssociation,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_association_clone_storage_run(source,events),result)
}
pub(crate) proof fn part2_association_clone_from_header(source:Part2RawCodestreamAssociation,
    result:Result<Part2RawJp2Header,crate::DecodeError>)
    requires source.2.is_some(),part2_header_clone_storage_result(source.2.get_Some_0(),result),
    ensures part2_association_clone_storage_result(source,match result {
        Err(error)=>Err(error),Ok(cloned)=>Ok((source.0,source.1,Some(cloned))),
    }),
{
    let header=source.2.get_Some_0();
    let outcome=match result {Err(error)=>Err(error),Ok(cloned)=>Ok((source.0,source.1,Some(cloned)))};
    part2_header_clone_storage_frames(header,result);
    if result.is_ok() {part2_cold_pure(outcome);}
    part2_cold_bind(|events|part2_header_clone_storage_run(header,events),
        |cloned:Part2RawJp2Header,rest|Some((Ok((source.0,source.1,Some(cloned))),rest)),result,outcome);
}
pub(crate) proof fn part2_association_clone_storage_normal(source:Part2RawCodestreamAssociation)
    ensures part2_association_clone_storage_result(source,Ok(source)),
{
    match source.2 {
        None=>part2_cold_pure(Ok(source)),
        Some(header)=>{
            part2_header_clone_storage_normal(header);
            part2_association_clone_from_header(source,Ok(header));
        },
    }
}
pub(crate) proof fn part2_association_clone_storage_frames(source:Part2RawCodestreamAssociation,
    result:Result<Part2RawCodestreamAssociation,crate::DecodeError>)
    requires part2_association_clone_storage_result(source,result),
    ensures part2_cold_framed(|events|part2_association_clone_storage_run(source,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawCodestreamAssociation>|
            (forall|events| #[trigger] other(events)==part2_association_clone_storage_run(source,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_association_clone_storage_run(source,events),result);
}
}
