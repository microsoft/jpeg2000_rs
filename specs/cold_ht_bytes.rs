//! Actual fresh refinement-byte owner copies, not retained-buffer growth.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_ht_bytes_run(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<u8>> {
    if source.len()==0{Some((Ok(source),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::RefinementBytes {role:actual,source:before,elements,succeeded}=>
            if actual!=role || before!=source || elements!=source.len(){None}else{
                Some((if succeeded{Ok(source)}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_bytes_result(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,result:Result<Seq<u8>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_bytes_run(source,role,calls),result)
}
pub(crate) proof fn part2_ht_bytes_observed(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (source.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_ht_bytes_result(source,role,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_ht_bytes_result);reveal(part2_ht_bytes_run);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    let prefix=if source.len()==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::RefinementBytes {role,source,elements:source.len(),succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_ht_bytes_run(source,role,prefix+tail)==Some((value,tail)) by{
        if source.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_ht_bytes_run(source,role,calls),prefix,value));
}
pub(crate) proof fn part2_ht_bytes_normal(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_ht_bytes_result(source,role,Ok(source)),
{part2_ht_bytes_observed(source,role,Ok(()));}
pub(crate) proof fn part2_ht_bytes_frames(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,result:Result<Seq<u8>,crate::DecodeError>)
    requires part2_ht_bytes_result(source,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_bytes_run(source,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<u8>>|
            (forall|calls| #[trigger] other(calls)==part2_ht_bytes_run(source,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_ht_bytes_result);part2_tier1_storage_eta(|calls|part2_ht_bytes_run(source,role,calls),result);}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_run(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_ht_bytes_run(before.ht_refinement_data,role,calls),|_:Seq<u8>,rest|Some((Ok(before),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_result(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1DecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_duplicate_run(before,role,calls),result)
}
pub(crate) proof fn part2_ht_duplicate_observed(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,result:Result<Seq<u8>,crate::DecodeError>)
    requires part2_ht_bytes_result(before.ht_refinement_data,role,result),
    ensures part2_ht_duplicate_result(before,role,match result{Err(error)=>Err(error),Ok(_)=>Ok(before)}),
{
    reveal(part2_ht_duplicate_result);reveal(part2_ht_duplicate_run);
    let value=match result{Err(error)=>Err(error),Ok(_)=>Ok(before)};
    part2_ht_bytes_frames(before.ht_refinement_data,role,result);
    if result.is_ok(){part2_tier1_storage_pure(Ok(before));}
    part2_tier1_storage_bind_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),|_:Seq<u8>,rest|Some((Ok(before),rest)),result,value);
}
pub(crate) proof fn part2_ht_duplicate_normal(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_ht_duplicate_result(before,role,Ok(before)),
{
    part2_ht_bytes_normal(before.ht_refinement_data,role);
    part2_ht_duplicate_observed(before,role,Ok(before.ht_refinement_data));
}
pub(crate) proof fn part2_ht_duplicate_frames(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1DecoderState,crate::DecodeError>)
    requires part2_ht_duplicate_result(before,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_duplicate_run(before,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState>|
            (forall|calls| #[trigger] other(calls)==part2_ht_duplicate_run(before,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_ht_duplicate_result);part2_tier1_storage_eta(|calls|part2_ht_duplicate_run(before,role,calls),result);}
}
