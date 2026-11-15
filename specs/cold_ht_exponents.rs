//! Fresh previous/current exponent-row owners after the real cleanup plane/reader.
use super::*;
verus! {
pub struct Part2HtExponentContext {
    pub plane_width:u16,pub plane_height:u16,pub metadata_width:u16,pub metadata_height:u16,pub input:Seq<u8>,
    pub maximum_u:u8,pub bitplanes:u16,pub work:u64,pub previous:Option<Seq<u8>>,
}
pub(crate) open spec fn part2_ht_exponent_count(metadata:HtMetadataOutput)->nat {(metadata.width as nat+1)/2+1}
pub(crate) open spec fn part2_ht_exponent_context(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,
    maximum_u:u8,bitplanes:u16,work:u64,current:bool)->Part2HtExponentContext {
    Part2HtExponentContext {plane_width:plane.width,plane_height:plane.height,metadata_width:metadata.width,metadata_height:metadata.height,
        input:cleanup.mag_sgn.bytes,maximum_u,bitplanes,work,
        previous:if current{Some(Seq::new(part2_ht_exponent_count(metadata),|_:int|0u8))}else{None}}
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_exponent_capacity_run(context:Part2HtExponentContext,current:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=(context.metadata_width as nat+1)/2+1;
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::HtExponentCapacity {context:actual,current:field,elements,succeeded}=>
            if actual!=context || field!=current || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_exponent_capacity_result(context:Part2HtExponentContext,current:bool,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_exponent_capacity_run(context,current,calls),result)
}
pub(crate) proof fn part2_ht_exponent_capacity_observed(context:Part2HtExponentContext,current:bool,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (((context.metadata_width as nat+1)/2+1)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_ht_exponent_capacity_result(context,current,result),
{
    reveal(part2_ht_exponent_capacity_result);reveal(part2_ht_exponent_capacity_run);
    let count=(context.metadata_width as nat+1)/2+1;
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::HtExponentCapacity {context,current,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_ht_exponent_capacity_run(context,current,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_ht_exponent_capacity_run(context,current,calls),prefix,result));
}
pub(crate) proof fn part2_ht_exponent_capacity_frames(context:Part2HtExponentContext,current:bool,result:Result<(),crate::DecodeError>)
    requires part2_ht_exponent_capacity_result(context,current,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_exponent_capacity_run(context,current,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()>|
            (forall|calls| #[trigger] other(calls)==part2_ht_exponent_capacity_run(context,current,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_ht_exponent_capacity_result);part2_tier1_storage_eta(|calls|part2_ht_exponent_capacity_run(context,current,calls),result);}
pub(crate) open spec fn part2_ht_exponent_ready(cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,work:u64)->Result<nat,crate::DecodeError> {
    match ht_magsgn_initial(cleanup.mag_sgn.bytes,work){
        Err(error)=>Err(error),Ok(_)=>{
            let quads=(metadata.width as nat+1)/2;
            if metadata.width as nat+1>usize::MAX || quads+1>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else if quads==0{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
            else{Ok(quads+1)}
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_exponent_current(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,
    maximum_u:u8,bitplanes:u16,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,crate::tier1::Tier1PassStatistics)> {
    part2_tier1_storage_bind(part2_ht_exponent_capacity_run(part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,true),true,calls),
        |_:(),rest|Some((ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_exponent_after_plane(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,
    maximum_u:u8,bitplanes:u16,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(Tier1RawPlane,crate::tier1::Tier1PassStatistics)> {
    match part2_ht_exponent_ready(cleanup,metadata,work){
        Err(_)=>Some((ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work),calls)),
        Ok(_)=>part2_tier1_storage_bind(part2_ht_exponent_capacity_run(part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,false),false,calls),
            |_:(),rest|part2_ht_exponent_current(plane,cleanup,metadata,maximum_u,bitplanes,work,rest)),
    }
}
pub(crate) proof fn part2_ht_exponent_after_normal(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,work:u64)
    ensures part2_tier1_storage_framed(|calls|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,work,calls),
        ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work)),
{
    reveal(part2_ht_exponent_after_plane);reveal(part2_ht_exponent_current);
    let result=ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work);
    match part2_ht_exponent_ready(cleanup,metadata,work){
        Err(_)=>{part2_tier1_storage_pure(result);},
        Ok(_)=>{
            let previous=part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,false);
            let current=part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,true);
            part2_ht_exponent_capacity_observed(previous,false,Ok(()));part2_ht_exponent_capacity_observed(current,true,Ok(()));
            part2_ht_exponent_capacity_frames(current,true,Ok(()));part2_tier1_storage_pure(result);
            part2_tier1_storage_bind_frame(|calls|part2_ht_exponent_capacity_run(current,true,calls),
                |_:(),rest|Some((result,rest)),Ok(()),result);
            part2_tier1_storage_eta(|calls|part2_ht_exponent_current(plane,cleanup,metadata,maximum_u,bitplanes,work,calls),result);
            part2_ht_exponent_capacity_frames(previous,false,Ok(()));
            part2_tier1_storage_bind_frame(|calls|part2_ht_exponent_capacity_run(previous,false,calls),
                |_:(),rest|part2_ht_exponent_current(plane,cleanup,metadata,maximum_u,bitplanes,work,rest),Ok(()),result);
        },
    }
}
pub(crate) proof fn part2_ht_exponent_join(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,work:u64,
    result:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>)
    requires metadata.width!=0,part1_tier1_plane_storage_result(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,tier1_empty_plane(plane.width,plane.height)),
        tier1_empty_plane(plane.width,plane.height).is_ok(),
        part2_tier1_storage_framed(|calls|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,work,calls),result),
    ensures part2_plane_cleanup_result(plane,cleanup,metadata,maximum_u,bitplanes,work,result),
{
    let output=tier1_empty_plane(plane.width,plane.height);
    part2_tier1_plane_frames(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,output);
    part2_tier1_storage_eta(|calls|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,work,calls),result);
    part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,calls),
        |_:Tier1RawPlane,rest|part2_ht_exponent_after_plane(plane,cleanup,metadata,maximum_u,bitplanes,work,rest),output,result);
}
pub(crate) proof fn part2_ht_exponent_first_error(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,work:u64,error:crate::DecodeError)
    requires metadata.width!=0,part1_tier1_plane_storage_result(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,tier1_empty_plane(plane.width,plane.height)),
        tier1_empty_plane(plane.width,plane.height).is_ok(),part2_ht_exponent_ready(cleanup,metadata,work).is_ok(),
        part2_ht_exponent_capacity_result(part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,false),false,Err(error)),
    ensures part2_plane_cleanup_result(plane,cleanup,metadata,maximum_u,bitplanes,work,Err(error)),
{
    reveal(part2_ht_exponent_after_plane);
    let context=part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,false);
    part2_ht_exponent_capacity_frames(context,false,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_ht_exponent_capacity_run(context,false,calls),
        |_:(),rest|part2_ht_exponent_current(plane,cleanup,metadata,maximum_u,bitplanes,work,rest),Err(error),Err(error));
    part2_ht_exponent_join(plane,cleanup,metadata,maximum_u,bitplanes,work,Err(error));
}
pub(crate) proof fn part2_ht_exponent_current_observed(plane:Tier1RawPlane,cleanup:HtCleanupSegmentState,metadata:HtMetadataOutput,maximum_u:u8,bitplanes:u16,work:u64,copied:Result<(),crate::DecodeError>)
    requires metadata.width!=0,part1_tier1_plane_storage_result(plane.width,plane.height,crate::tier1::CoefficientStorageRole::CleanupOutput,tier1_empty_plane(plane.width,plane.height)),
        tier1_empty_plane(plane.width,plane.height).is_ok(),part2_ht_exponent_ready(cleanup,metadata,work).is_ok(),
        part2_ht_exponent_capacity_result(part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,false),false,Ok(())),
        part2_ht_exponent_capacity_result(part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,true),true,copied),
    ensures part2_plane_cleanup_result(plane,cleanup,metadata,maximum_u,bitplanes,work,
        match copied{Err(error)=>Err(error),Ok(())=>ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work)}),
{
    reveal(part2_ht_exponent_after_plane);reveal(part2_ht_exponent_current);
    let result=match copied{Err(error)=>Err(error),Ok(())=>ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work)};
    let previous=part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,false);
    let current=part2_ht_exponent_context(plane,cleanup,metadata,maximum_u,bitplanes,work,true);
    part2_ht_exponent_capacity_frames(current,true,copied);
    if copied.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_ht_exponent_capacity_run(current,true,calls),
        |_:(),rest|Some((ht_cleanup_plane(plane,cleanup,metadata,maximum_u,bitplanes,work),rest)),copied,result);
    part2_tier1_storage_eta(|calls|part2_ht_exponent_current(plane,cleanup,metadata,maximum_u,bitplanes,work,calls),result);
    part2_ht_exponent_capacity_frames(previous,false,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_ht_exponent_capacity_run(previous,false,calls),
        |_:(),rest|part2_ht_exponent_current(plane,cleanup,metadata,maximum_u,bitplanes,work,rest),Ok(()),result);
    part2_ht_exponent_join(plane,cleanup,metadata,maximum_u,bitplanes,work,result);
}
}
