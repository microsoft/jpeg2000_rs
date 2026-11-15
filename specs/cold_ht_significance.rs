//! Fresh source-significance flags after the actual refinement output and readers.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_cleanup_significance_capacity_run(count:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::CleanupSignificanceCapacity {elements,succeeded}=>
            if elements!=count{None}else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
pub(crate) open spec fn part2_cleanup_significance_capacity_result(count:nat,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_cleanup_significance_capacity_run(count,calls),result)
}
pub(crate) proof fn part2_cleanup_significance_capacity_observed(count:nat,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (count>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_cleanup_significance_capacity_result(count,result),
{
    reveal(part2_cleanup_significance_capacity_run);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::CleanupSignificanceCapacity {elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_cleanup_significance_capacity_run(count,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_cleanup_significance_capacity_run(count,calls),prefix,result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_cleanup_significance_run(coefficients:Seq<Tier1RawCoefficient>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<bool>> {
    part2_tier1_storage_bind(part2_cleanup_significance_capacity_run(coefficients.len(),calls),
        |_:(),rest|Some((Ok(ht_cleanup_significance(coefficients)),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_cleanup_significance_result(coefficients:Seq<Tier1RawCoefficient>,result:Result<Seq<bool>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_cleanup_significance_run(coefficients,calls),result)
}
pub(crate) proof fn part2_cleanup_significance_normal(coefficients:Seq<Tier1RawCoefficient>)
    ensures part2_cleanup_significance_result(coefficients,Ok(ht_cleanup_significance(coefficients))),
{
    reveal(part2_cleanup_significance_result);reveal(part2_cleanup_significance_run);
    part2_cleanup_significance_capacity_observed(coefficients.len(),Ok(()));
    part2_tier1_storage_pure(Ok(ht_cleanup_significance(coefficients)));
    part2_tier1_storage_bind_frame(|calls|part2_cleanup_significance_capacity_run(coefficients.len(),calls),
        |_:(),rest|Some((Ok(ht_cleanup_significance(coefficients)),rest)),Ok(()),Ok(ht_cleanup_significance(coefficients)));
}
pub(crate) proof fn part2_cleanup_significance_refused(coefficients:Seq<Tier1RawCoefficient>,error:crate::DecodeError)
    requires part2_cleanup_significance_capacity_result(coefficients.len(),Err(error)),
    ensures part2_cleanup_significance_result(coefficients,Err(error)),
{
    reveal(part2_cleanup_significance_result);reveal(part2_cleanup_significance_run);
    part2_tier1_storage_bind_frame(|calls|part2_cleanup_significance_capacity_run(coefficients.len(),calls),
        |_:(),rest|Some((Ok(ht_cleanup_significance(coefficients)),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_cleanup_significance_frames(coefficients:Seq<Tier1RawCoefficient>,result:Result<Seq<bool>,crate::DecodeError>)
    requires part2_cleanup_significance_result(coefficients,result),
    ensures part2_tier1_storage_framed(|calls|part2_cleanup_significance_run(coefficients,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<bool>>|
            (forall|calls| #[trigger] other(calls)==part2_cleanup_significance_run(coefficients,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    reveal(part2_cleanup_significance_result);
    part2_tier1_storage_eta(|calls|part2_cleanup_significance_run(coefficients,calls),result);
}
}
