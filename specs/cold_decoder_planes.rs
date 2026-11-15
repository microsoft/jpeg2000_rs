//! Raw coefficient-owner copies at the actual checked decoder Clone fields.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_decoder_plane_run(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,cleanup:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane> {
    let count=source.coefficients.len();
    if count==0{Some((Ok(source),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::DecoderPlaneCopy {source:actual,role:path,cleanup:optional,elements,succeeded}=>
            if actual!=source || path!=role || optional!=cleanup || elements!=count{None}else{
                Some((if succeeded{Ok(source)}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_decoder_plane_result(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,cleanup:bool,result:Result<Tier1RawPlane,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_decoder_plane_run(source,role,cleanup,calls),result)
}
pub(crate) proof fn part2_decoder_plane_observed(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,cleanup:bool,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (source.coefficients.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_decoder_plane_result(source,role,cleanup,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_decoder_plane_result);reveal(part2_decoder_plane_run);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    let prefix=if source.coefficients.len()==0{Seq::empty()}else{
        seq![Part2Tier1StorageEvent::DecoderPlaneCopy {source,role,cleanup,elements:source.coefficients.len(),succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_decoder_plane_run(source,role,cleanup,prefix+tail)==Some((value,tail)) by{
        if source.coefficients.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_decoder_plane_run(source,role,cleanup,calls),prefix,value));
}
pub(crate) proof fn part2_decoder_plane_normal(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,cleanup:bool)
    ensures part2_decoder_plane_result(source,role,cleanup,Ok(source)),
{part2_decoder_plane_observed(source,role,cleanup,Ok(()));}
pub(crate) proof fn part2_decoder_plane_frames(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,cleanup:bool,result:Result<Tier1RawPlane,crate::DecodeError>)
    requires part2_decoder_plane_result(source,role,cleanup,result),
    ensures part2_tier1_storage_framed(|calls|part2_decoder_plane_run(source,role,cleanup,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane>|
            (forall|calls| #[trigger] other(calls)==part2_decoder_plane_run(source,role,cleanup,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_decoder_plane_result);part2_tier1_storage_eta(|calls|part2_decoder_plane_run(source,role,cleanup,calls),result);}
#[verifier::opaque]
pub(crate) open spec fn part2_decoder_cleanup_run(source:Option<Tier1RawPlane>,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Option<Tier1RawPlane>> {
    match source{None=>Some((Ok(None),calls)),Some(plane)=>part2_tier1_storage_bind(part2_decoder_plane_run(plane,role,true,calls),
        |copied:Tier1RawPlane,rest|Some((Ok(Some(copied)),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_decoder_cleanup_result(source:Option<Tier1RawPlane>,role:crate::tier1::HtRefinementCopyRole,result:Result<Option<Tier1RawPlane>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_decoder_cleanup_run(source,role,calls),result)
}
pub(crate) proof fn part2_decoder_cleanup_none(role:crate::tier1::HtRefinementCopyRole)
    ensures part2_decoder_cleanup_result(None,role,Ok(None)),
{reveal(part2_decoder_cleanup_result);reveal(part2_decoder_cleanup_run);part2_tier1_storage_pure::<Option<Tier1RawPlane>>(Ok(None));}
pub(crate) proof fn part2_decoder_cleanup_observed(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1RawPlane,crate::DecodeError>)
    requires part2_decoder_plane_result(source,role,true,result),
    ensures part2_decoder_cleanup_result(Some(source),role,match result{Err(error)=>Err(error),Ok(value)=>Ok(Some(value))}),
{
    reveal(part2_decoder_cleanup_result);reveal(part2_decoder_cleanup_run);
    let value=match result{Err(error)=>Err(error),Ok(value)=>Ok(Some(value))};
    part2_decoder_plane_frames(source,role,true,result);
    if result.is_ok(){part2_tier1_storage_pure(value);}
    part2_tier1_storage_bind_frame(|calls|part2_decoder_plane_run(source,role,true,calls),|copied:Tier1RawPlane,rest|Some((Ok(Some(copied)),rest)),result,value);
}
pub(crate) proof fn part2_decoder_cleanup_normal(source:Option<Tier1RawPlane>,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_decoder_cleanup_result(source,role,Ok(source)),
{
    match source{None=>{part2_decoder_cleanup_none(role);},Some(plane)=>{
        part2_decoder_plane_normal(plane,role,true);part2_decoder_cleanup_observed(plane,role,Ok(plane));
    }}
}
pub(crate) proof fn part2_decoder_cleanup_frames(source:Option<Tier1RawPlane>,role:crate::tier1::HtRefinementCopyRole,result:Result<Option<Tier1RawPlane>,crate::DecodeError>)
    requires part2_decoder_cleanup_result(source,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_decoder_cleanup_run(source,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Option<Tier1RawPlane>>|
            (forall|calls| #[trigger] other(calls)==part2_decoder_cleanup_run(source,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_decoder_cleanup_result);part2_tier1_storage_eta(|calls|part2_decoder_cleanup_run(source,role,calls),result);}
}
