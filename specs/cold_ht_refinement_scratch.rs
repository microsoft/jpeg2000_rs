//! Actual fresh claimed/stuffed masks after the real forward/optional reverse readers.
use super::*;
verus! {
pub struct Part2HtRefinementScratchContext {
    pub forward_length:nat,pub reverse_length:nat,pub bytes:usize,pub has_reverse:bool,pub work:u64,
    pub claimed:Option<Seq<u8>>,
}
pub(crate) open spec fn part2_ht_scratch_context(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,stuffed:bool)->Part2HtRefinementScratchContext {
    Part2HtRefinementScratchContext {forward_length:forward.len(),reverse_length:reverse.len(),bytes,has_reverse,work,
        claimed:if stuffed{Some(Seq::new(bytes as nat,|_:int|0u8))}else{None}}
}
pub(crate) open spec fn part2_ht_scratch_admit(forward:Seq<u8>,reverse:Seq<u8>,has_reverse:bool,work:u64)
    ->Result<(HtForwardRefinementState,Option<HtReverseRefinementState>),crate::DecodeError> {
    match ht_forward_refinement_initial(forward,work){
        Err(error)=>Err(error),Ok(first)=>if has_reverse{match ht_reverse_refinement_initial(reverse,work){
            Err(error)=>Err(error),Ok(second)=>Ok((first,Some(second))),
        }}else{Ok((first,None))},
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_scratch_capacity_run(context:Part2HtRefinementScratchContext,stuffed:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    if context.bytes==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::RefinementScratchCapacity {context:actual,stuffed:field,elements,succeeded}=>
            if actual!=context || field!=stuffed || elements!=context.bytes{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_scratch_capacity_result(context:Part2HtRefinementScratchContext,stuffed:bool,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_scratch_capacity_run(context,stuffed,calls),result)
}
pub(crate) proof fn part2_ht_scratch_capacity_observed(context:Part2HtRefinementScratchContext,stuffed:bool,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (context.bytes>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_ht_scratch_capacity_result(context,stuffed,result),
{
    reveal(part2_ht_scratch_capacity_result);reveal(part2_ht_scratch_capacity_run);
    let prefix=if context.bytes==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::RefinementScratchCapacity {context,stuffed,elements:context.bytes,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_ht_scratch_capacity_run(context,stuffed,prefix+tail)==Some((result,tail)) by{
        if context.bytes==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_ht_scratch_capacity_run(context,stuffed,calls),prefix,result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_scratch_stuffed(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtRefinementReadersState> {
    part2_tier1_storage_bind(part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,true),true,calls),
        |_:(),rest|Some((ht_refinement_readers_initial(forward,reverse,bytes,has_reverse,work),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_scratch_run(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtRefinementReadersState> {
    match part2_ht_scratch_admit(forward,reverse,has_reverse,work){
        Err(error)=>Some((Err(error),calls)),Ok(_)=>
            part2_tier1_storage_bind(part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,calls),
                |_:(),rest|part2_ht_scratch_stuffed(forward,reverse,bytes,has_reverse,work,rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_scratch_result(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,result:Result<HtRefinementReadersState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_scratch_run(forward,reverse,bytes,has_reverse,work,calls),result)
}
pub(crate) proof fn part2_ht_scratch_normal(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64)
    ensures part2_ht_scratch_result(forward,reverse,bytes,has_reverse,work,ht_refinement_readers_initial(forward,reverse,bytes,has_reverse,work)),
{
    reveal(part2_ht_scratch_result);reveal(part2_ht_scratch_capacity_result);reveal(part2_ht_scratch_stuffed);reveal(part2_ht_scratch_run);
    let result=ht_refinement_readers_initial(forward,reverse,bytes,has_reverse,work);
    match part2_ht_scratch_admit(forward,reverse,has_reverse,work){
        Err(_)=>{part2_tier1_storage_pure(result);},Ok(_)=>{
            part2_ht_scratch_capacity_observed(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,true),true,Ok(()));
            part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,true),true,calls),
                |_:(),rest|Some((result,rest)),Ok(()),result);
            part2_tier1_storage_eta(|calls|part2_ht_scratch_stuffed(forward,reverse,bytes,has_reverse,work,calls),result);
            part2_ht_scratch_capacity_observed(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,Ok(()));
            part2_tier1_storage_bind_frame(|calls|part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,calls),
                |_:(),rest|part2_ht_scratch_stuffed(forward,reverse,bytes,has_reverse,work,rest),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_ht_scratch_first_error(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,error:crate::DecodeError)
    requires part2_ht_scratch_admit(forward,reverse,has_reverse,work).is_ok(),
        part2_ht_scratch_capacity_result(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,Err(error)),
    ensures part2_ht_scratch_result(forward,reverse,bytes,has_reverse,work,Err(error)),
{
    reveal(part2_ht_scratch_result);reveal(part2_ht_scratch_capacity_result);reveal(part2_ht_scratch_run);
    part2_tier1_storage_bind_frame(|calls|part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,calls),
        |_:(),rest|part2_ht_scratch_stuffed(forward,reverse,bytes,has_reverse,work,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_ht_scratch_second_observed(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,copied:Result<(),crate::DecodeError>)
    requires part2_ht_scratch_admit(forward,reverse,has_reverse,work).is_ok(),
        part2_ht_scratch_capacity_result(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,true),true,copied),
    ensures part2_ht_scratch_result(forward,reverse,bytes,has_reverse,work,
        match copied{Err(error)=>Err(error),Ok(())=>ht_refinement_readers_initial(forward,reverse,bytes,has_reverse,work)}),
{
    reveal(part2_ht_scratch_result);reveal(part2_ht_scratch_capacity_result);reveal(part2_ht_scratch_stuffed);reveal(part2_ht_scratch_run);
    let result=match copied{Err(error)=>Err(error),Ok(())=>ht_refinement_readers_initial(forward,reverse,bytes,has_reverse,work)};
    if copied.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,true),true,calls),
        |_:(),rest|Some((ht_refinement_readers_initial(forward,reverse,bytes,has_reverse,work),rest)),copied,result);
    part2_tier1_storage_eta(|calls|part2_ht_scratch_stuffed(forward,reverse,bytes,has_reverse,work,calls),result);
    part2_ht_scratch_capacity_observed(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_ht_scratch_capacity_run(part2_ht_scratch_context(forward,reverse,bytes,has_reverse,work,false),false,calls),
        |_:(),rest|part2_ht_scratch_stuffed(forward,reverse,bytes,has_reverse,work,rest),Ok(()),result);
}
pub(crate) proof fn part2_ht_scratch_frames(forward:Seq<u8>,reverse:Seq<u8>,bytes:usize,has_reverse:bool,work:u64,result:Result<HtRefinementReadersState,crate::DecodeError>)
    requires part2_ht_scratch_result(forward,reverse,bytes,has_reverse,work,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_scratch_run(forward,reverse,bytes,has_reverse,work,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtRefinementReadersState>|
            (forall|calls| #[trigger] other(calls)==part2_ht_scratch_run(forward,reverse,bytes,has_reverse,work,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    reveal(part2_ht_scratch_result);
    part2_tier1_storage_eta(|calls|part2_ht_scratch_run(forward,reverse,bytes,has_reverse,work,calls),result);
}
}
