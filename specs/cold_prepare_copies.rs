//! Fresh raw LL and reconstructed-plane sample copies at their actual frontiers.
use super::*;
verus! {
pub enum Part2PrepareCopyRole {InitialLl,PreparedPlane}
#[verifier::opaque]
pub(crate) open spec fn part2_prepare_copy_capacity_run(role:Part2PrepareCopyRole,count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::PrepareCopyCapacity {role:actual,elements,succeeded}=>
            if actual!=role || elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_prepare_samples_run(role:Part2PrepareCopyRole,source:Seq<i64>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<i64>> {
    part2_tier1_storage_bind(part2_prepare_copy_capacity_run(role,source.len(),calls),|_:(),rest|Some((Ok(source),rest)))
}
pub(crate) open spec fn part2_prepare_samples_result(role:Part2PrepareCopyRole,source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_samples_run(role,source,calls),result)
}
pub(crate) proof fn part2_prepare_samples_observed(role:Part2PrepareCopyRole,source:Seq<i64>,result:Result<Seq<i64>,crate::DecodeError>)
    requires match result{Ok(values)=>values==source,Err(error)=>source.len()>0 && error==crate::DecodeError::AllocationFailed},
    ensures part2_prepare_samples_result(role,source,result),
{
    reveal(part2_prepare_copy_capacity_run);
    let prefix=if source.len()==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::PrepareCopyCapacity {role,elements:source.len(),succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_prepare_samples_run(role,source,prefix+tail)==Some((result,tail)) by{
        if source.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_prepare_samples_run(role,source,calls),prefix,result));
}
pub(crate) open spec fn part2_prepare_initial_run(ll:Part1WorkingSubbandModel,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    part2_tier1_storage_bind(part2_prepare_samples_run(Part2PrepareCopyRole::InitialLl,ll.3,calls),
        |values:Seq<i64>,rest|Some((Ok((ll.0,ll.1,values,1usize)),rest)))
}
pub(crate) open spec fn part2_prepare_initial_result(ll:Part1WorkingSubbandModel,result:Result<Part1PrepareFold,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_initial_run(ll,calls),result)
}
pub(crate) proof fn part2_prepare_initial_observed(ll:Part1WorkingSubbandModel,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_prepare_samples_result(Part2PrepareCopyRole::InitialLl,ll.3,result),
    ensures part2_prepare_initial_result(ll,match result{Err(error)=>Err(error),Ok(values)=>Ok((ll.0,ll.1,values,1usize))}),
{
    let after=match result{Err(error)=>Err(error),Ok(values)=>Ok((ll.0,ll.1,values,1usize))};
    if result.is_ok(){part2_tier1_storage_pure(after);}
    part2_tier1_storage_bind_frame(|calls|part2_prepare_samples_run(Part2PrepareCopyRole::InitialLl,ll.3,calls),
        |values:Seq<i64>,rest|Some((Ok((ll.0,ll.1,values,1usize)),rest)),result,after);
}
pub(crate) proof fn part2_prepare_initial_normal(ll:Part1WorkingSubbandModel)
    ensures part2_prepare_initial_result(ll,Ok((ll.0,ll.1,ll.3,1usize))),
{
    part2_prepare_samples_observed(Part2PrepareCopyRole::InitialLl,ll.3,Ok(ll.3));
    part2_prepare_initial_observed(ll,Ok(ll.3));
}
pub(crate) open spec fn part2_prepare_plane_copy_run(plane:Part1ReconstructedPlane,first_detail:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1PrepareFold> {
    part2_tier1_storage_bind(part2_prepare_samples_run(Part2PrepareCopyRole::PreparedPlane,plane.3,calls),
        |values:Seq<i64>,rest|Some((Ok((plane.0,plane.1,values,first_detail)),rest)))
}
pub(crate) open spec fn part2_prepare_plane_copy_result(plane:Part1ReconstructedPlane,first_detail:usize,result:Result<Part1PrepareFold,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_prepare_plane_copy_run(plane,first_detail,calls),result)
}
pub(crate) proof fn part2_prepare_plane_copy_observed(plane:Part1ReconstructedPlane,first_detail:usize,result:Result<Seq<i64>,crate::DecodeError>)
    requires part2_prepare_samples_result(Part2PrepareCopyRole::PreparedPlane,plane.3,result),
    ensures part2_prepare_plane_copy_result(plane,first_detail,match result{Err(error)=>Err(error),Ok(values)=>Ok((plane.0,plane.1,values,first_detail))}),
{
    let after=match result{Err(error)=>Err(error),Ok(values)=>Ok((plane.0,plane.1,values,first_detail))};
    if result.is_ok(){part2_tier1_storage_pure(after);}
    part2_tier1_storage_bind_frame(|calls|part2_prepare_samples_run(Part2PrepareCopyRole::PreparedPlane,plane.3,calls),
        |values:Seq<i64>,rest|Some((Ok((plane.0,plane.1,values,first_detail)),rest)),result,after);
}
pub(crate) proof fn part2_prepare_plane_copy_normal(plane:Part1ReconstructedPlane,first_detail:usize)
    ensures part2_prepare_plane_copy_result(plane,first_detail,part1_prepare_copy_plane(plane,first_detail)),
{
    part2_prepare_samples_observed(Part2PrepareCopyRole::PreparedPlane,plane.3,Ok(plane.3));
    part2_prepare_plane_copy_observed(plane,first_detail,Ok(plane.3));
}
}
