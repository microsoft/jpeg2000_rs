//! The one additional real owner before the unchanged ordered bitplane owners.
use super::*;
verus! {
pub(crate) struct Part2CompactLegacyCaps {
    pub legacy:Part2LegacyCaps,
    pub decoded:u64,
    pub wide_bytes:usize,
}
pub(crate) open spec fn compact_capacity_run(width:usize,height:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=width as nat*height as nat;
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::CompactInitialCapacity {width:actual_width,height:actual_height,elements,succeeded}=>
            if actual_width!=width || actual_height!=height || elements!=count{None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn compact_capacity_result(width:usize,height:usize,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|compact_capacity_run(width,height,calls),result)
}
pub(crate) proof fn compact_capacity_observed(width:usize,height:usize,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (width*height>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures compact_capacity_result(width,height,result),
{
    reveal(compact_capacity_result);
    let prefix=if width*height==0{Seq::empty()}else{
        seq![Part2Tier1StorageEvent::CompactInitialCapacity {width,height,elements:width as nat*height as nat,succeeded:result.is_ok()}]
    };
    assert forall|tail:Seq<Part2Tier1StorageEvent>|compact_capacity_run(width,height,prefix+tail)==Some((result,tail)) by{
        if width*height==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|compact_capacity_run(width,height,calls),prefix,result));
}
pub(crate) open spec fn compact_initial_run(width:usize,height:usize,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<(usize,usize,Seq<u64>)> {
    part2_tier1_storage_bind(compact_capacity_run(width,height,calls),
        |_:(),rest|Some((Ok((width,height,Seq::new(width as nat*height as nat,|_:int|0x3f_0000_0000u64))),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn compact_initial_result(width:usize,height:usize,result:Result<(usize,usize,Seq<u64>),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|compact_initial_run(width,height,calls),result)
}
pub(crate) proof fn compact_initial_observed(width:usize,height:usize,result:Result<(),crate::DecodeError>)
    requires compact_capacity_result(width,height,result),
    ensures compact_initial_result(width,height,match result{
        Err(error)=>Err(error),Ok(())=>Ok((width,height,Seq::new(width as nat*height as nat,|_:int|0x3f_0000_0000u64))),
    }),
{
    reveal(compact_capacity_result);reveal(compact_initial_result);
    let value=(width,height,Seq::new(width as nat*height as nat,|_:int|0x3f_0000_0000u64));
    part2_tier1_storage_pure(Ok(value));
    part2_tier1_storage_bind_frame(|calls|compact_capacity_run(width,height,calls),
        |_:(),rest|Some((Ok(value),rest)),result,match result{Err(error)=>Err(error),Ok(())=>Ok(value)});
}
pub(crate) proof fn compact_initial_normal(width:usize,height:usize)
    ensures compact_initial_result(width,height,Ok((width,height,Seq::new(width as nat*height as nat,|_:int|0x3f_0000_0000u64)))),
{
    compact_capacity_observed(width,height,Ok(()));
    compact_initial_observed(width,height,Ok(()));
}
pub(crate) open spec fn compact_inner_run(initial:Part1LegacySegmentRun,count:u32,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentPassEffect> {
    part2_tier1_storage_resume(compact_capacity_run(initial.decoder.plane.width as usize,initial.decoder.plane.height as usize,calls),
        |allocated:Result<(),crate::DecodeError>,rest|match allocated{
            Err(error)=>Some((Ok((Err(error),initial.decoder,initial.symbols)),rest)),
            Ok(())=>part2_legacy_inner_body_run(initial,count,rest),
        })
}
#[verifier::opaque]
pub(crate) open spec fn compact_inner_result(initial:Part1LegacySegmentRun,count:u32,result:Part1LegacySegmentPassEffect)->bool {
    part2_tier1_storage_framed(|calls|compact_inner_run(initial,count,calls),Ok(result))
        && (result.0!=Err(crate::DecodeError::AllocationFailed)
            ==> result==part1_legacy_segment_finish(part1_legacy_segment_run(initial,count as nat)))
}
pub(crate) proof fn compact_inner_first_error(initial:Part1LegacySegmentRun,count:u32,error:crate::DecodeError)
    requires compact_capacity_result(initial.decoder.plane.width as usize,initial.decoder.plane.height as usize,Err(error)),
    ensures compact_inner_result(initial,count,(Err(error),initial.decoder,initial.symbols)),
{
    reveal(compact_capacity_result);reveal(compact_inner_result);
    let width=initial.decoder.plane.width as usize;
    let height=initial.decoder.plane.height as usize;
    assert(error==crate::DecodeError::AllocationFailed) by{
        let run=|calls|compact_capacity_run(width,height,calls);
        let prefix=choose|prefix|#[trigger] part2_tier1_storage_prefix(run,prefix,Err(error));
        part2_tier1_storage_at(run,prefix,Err(error),Seq::empty());
        match run(prefix+Seq::empty()){None=>{},Some((Ok(_),_))=>{},Some((Err(_),_))=>{}}
    }
    part2_tier1_storage_pure::<Part1LegacySegmentPassEffect>(Ok((Err(error),initial.decoder,initial.symbols)));
    part2_tier1_resume_frame(|calls|compact_capacity_run(width,height,calls),
        |allocated:Result<(),crate::DecodeError>,rest|match allocated{
            Err(error)=>Some((Ok((Err(error),initial.decoder,initial.symbols)),rest)),
            Ok(())=>part2_legacy_inner_body_run(initial,count,rest),
        },Err(error),Ok((Err(error),initial.decoder,initial.symbols)));
}
pub(crate) proof fn compact_inner_observed(initial:Part1LegacySegmentRun,count:u32,inner:Part1LegacySegmentPassEffect)
    requires compact_capacity_result(initial.decoder.plane.width as usize,initial.decoder.plane.height as usize,Ok(())),
        part2_legacy_inner_body_result(initial,count,inner),
        inner.0!=Err(crate::DecodeError::AllocationFailed)
            ==> inner==part1_legacy_segment_finish(part1_legacy_segment_run(initial,count as nat)),
    ensures compact_inner_result(initial,count,inner),
{
    reveal(compact_capacity_result);reveal(compact_inner_result);
    part2_legacy_inner_body_frames(initial,count,inner);
    part2_tier1_resume_frame(|calls|compact_capacity_run(initial.decoder.plane.width as usize,initial.decoder.plane.height as usize,calls),
        |allocated:Result<(),crate::DecodeError>,rest|match allocated{
            Err(error)=>Some((Ok((Err(error),initial.decoder,initial.symbols)),rest)),
            Ok(())=>part2_legacy_inner_body_run(initial,count,rest),
        },Ok(()),Ok(inner));
}
pub(crate) proof fn compact_inner_normal(initial:Part1LegacySegmentRun,count:u32)
    ensures compact_inner_result(initial,count,part1_legacy_segment_finish(part1_legacy_segment_run(initial,count as nat))),
{
    compact_capacity_observed(initial.decoder.plane.width as usize,initial.decoder.plane.height as usize,Ok(()));
    part2_legacy_inner_body_normal(initial,count);
    compact_inner_observed(initial,count,part1_legacy_segment_finish(part1_legacy_segment_run(initial,count as nat)));
}
pub(crate) open spec fn compact_selected_inner_run(initial:Part1LegacySegmentRun,count:u32,caps:Part2CompactLegacyCaps,allowed:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentPassEffect> {
    if allowed && compact_eligible(initial.decoder,count,caps.decoded,caps.wide_bytes){
        compact_inner_run(initial,count,calls)
    }else{
        part2_legacy_inner_body_run(initial,count,calls)
    }
}
}
