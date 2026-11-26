//! Actual mutable HT decoder state around the shared fresh plane constructors.
use super::*;
verus! {
pub(crate) open spec fn part2_ht_following(passes:u32)->nat {if passes==0{0nat}else{(passes-1) as nat}}
pub(crate) open spec fn part2_ht_coeff_after_refinement(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    output:(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),refinement:HtRefinementSegmentState,
    refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    let cleared=ht_clear_refinement_state(before);
    match refined{
        Err(error)=>Some((Ok((Err(error),cleared)),calls)),
        Ok(value)=>if tier1_statistics_merge(output.2,value.1).0.is_err(){
            Some((Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)),calls))
        }else{part2_tier1_storage_resume(part2_ht_bytes_run(refinement.encoded,crate::tier1::HtRefinementCopyRole::CleanupRetention,calls),
            |copied:Result<Seq<u8>,crate::DecodeError>,rest|Some((Ok(match copied{
                Err(error)=>(Err(error),cleared),Ok(_)=>ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)
            }),rest)))},
    }
}
pub(crate) open spec fn part2_ht_coeff_after_prepare(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match prepared {
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(output)=>{
            let cleared=ht_clear_refinement_state(before);
            match segments.refinement {
                None=>Some((Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)),calls)),
                Some(refinement)=>{
                    let following=if passes==0{0nat}else{(passes-1) as nat};
                    if following>u8::MAX{Some((Ok((Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),cleared)),calls))}
                    else{part2_tier1_storage_resume(part2_plane_refinement_run(output.1,refinement,following as u8,output.3,cleared.style.vertical_causal_context,work,calls),
                        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
                            part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,refined,rest))}
                },
            }
        },
    }
}
pub(crate) open spec fn part2_ht_coeff_run(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    part2_tier1_storage_resume(part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest))
}
pub(crate) open spec fn part2_ht_coeff_result(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_coeff_run(before,segments,passes,maximum_u,skipped,work,calls),Ok(result))
}
pub(crate) proof fn part2_ht_coeff_after_refinement_normal(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    output:(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),refinement:HtRefinementSegmentState)
    requires ht_cleanup_prepare(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work)==Ok(output),
        segments.refinement==Some(refinement),part2_ht_following(passes)<=u8::MAX,
    ensures part2_tier1_storage_framed(|calls|part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,
        ht_refinement_plane(output.1,refinement,part2_ht_following(passes) as u8,output.3,before.style.vertical_causal_context,work),calls),
        Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work))),
{
    let result=ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work);
    match ht_refinement_plane(output.1,refinement,part2_ht_following(passes) as u8,output.3,before.style.vertical_causal_context,work){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(value)=>if tier1_statistics_merge(output.2,value.1).0.is_err(){part2_tier1_storage_pure(Ok(result));}else{
            let role=crate::tier1::HtRefinementCopyRole::CleanupRetention;
            part2_ht_bytes_normal(refinement.encoded,role);part2_ht_bytes_frames(refinement.encoded,role,Ok(refinement.encoded));
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_resume_frame(|calls|part2_ht_bytes_run(refinement.encoded,role,calls),
                |copied:Result<Seq<u8>,crate::DecodeError>,rest|Some((Ok(match copied{
                    Err(error)=>(Err(error),ht_clear_refinement_state(before)),Ok(_)=>result}),rest)),Ok(refinement.encoded),Ok(result));
        },
    }
}
pub(crate) proof fn part2_ht_coeff_after_normal(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64)
    ensures part2_tier1_storage_framed(|calls|part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,
        ht_cleanup_prepare(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work),calls),
        Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work))),
{
    let result=ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work);
    match ht_cleanup_prepare(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work) {
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(output)=>match segments.refinement {
            None=>{part2_tier1_storage_pure(Ok(result));},
            Some(refinement)=>{
                let following=if passes==0{0nat}else{(passes-1) as nat};
                if following>u8::MAX{part2_tier1_storage_pure(Ok(result));}else{
                    let cleared=ht_clear_refinement_state(before);
                    part2_plane_refinement_normal(output.1,refinement,following as u8,output.3,cleared.style.vertical_causal_context,work);
                    let refined=ht_refinement_plane(output.1,refinement,following as u8,output.3,cleared.style.vertical_causal_context,work);
                    part2_ht_coeff_after_refinement_normal(before,segments,passes,maximum_u,skipped,work,output,refinement);
                    part2_tier1_storage_eta(|calls|part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,refined,calls),Ok(result));
                    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(output.1,refinement,following as u8,output.3,cleared.style.vertical_causal_context,work,calls),
                        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
                            part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,refined,rest),refined,Ok(result));
                }
            },
        },
    }
}
pub(crate) proof fn part2_ht_coeff_normal(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64)
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)),
{
    part2_plane_prepare_normal(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan);
    let prepared=ht_cleanup_prepare(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work);
    part2_ht_coeff_after_normal(before,segments,passes,maximum_u,skipped,work);
    part2_tier1_storage_eta(|calls|part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,calls),
        Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),prepared,
        Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)));
}
pub(crate) proof fn part2_ht_coeff_prepare_error(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,error:crate::DecodeError)
    requires part2_plane_prepare_result(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,Err(error)),
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,(Err(error),before)),
{
    part2_tier1_storage_pure::<HtDecoderResult>(Ok((Err(error),before)));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),Err(error),Ok((Err(error),before)));
}
pub(crate) proof fn part2_ht_coeff_refinement_error(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    output:(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),refinement:HtRefinementSegmentState,error:crate::DecodeError)
    requires segments.refinement==Some(refinement),part2_ht_following(passes)<=u8::MAX,
        part2_plane_prepare_result(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,Ok(output)),
        part2_plane_refinement_result(output.1,refinement,part2_ht_following(passes) as u8,output.3,before.style.vertical_causal_context,work,Err(error)),
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,(Err(error),ht_clear_refinement_state(before))),
{
    let cleared=ht_clear_refinement_state(before);let result=(Err(error),cleared);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,Err(error),calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(output.1,refinement,part2_ht_following(passes) as u8,output.3,cleared.style.vertical_causal_context,work,calls),
        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
            part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,refined,rest),Err(error),Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),Ok(output),Ok(result));
}
pub(crate) proof fn part2_ht_coeff_bytes_error(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    output:(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),refinement:HtRefinementSegmentState,
    refined:(Tier1RawPlane,crate::tier1::Tier1PassStatistics),error:crate::DecodeError)
    requires segments.refinement==Some(refinement),part2_ht_following(passes)<=u8::MAX,
        part2_plane_prepare_result(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,Ok(output)),
        part2_plane_refinement_result(output.1,refinement,part2_ht_following(passes) as u8,output.3,before.style.vertical_causal_context,work,Ok(refined)),
        tier1_statistics_merge(output.2,refined.1).0.is_ok(),
        part2_ht_bytes_result(refinement.encoded,crate::tier1::HtRefinementCopyRole::CleanupRetention,Err(error)),
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,(Err(error),ht_clear_refinement_state(before))),
{
    let result=(Err(error),ht_clear_refinement_state(before));let role=crate::tier1::HtRefinementCopyRole::CleanupRetention;
    part2_ht_bytes_frames(refinement.encoded,role,Err(error));part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_ht_bytes_run(refinement.encoded,role,calls),
        |copied:Result<Seq<u8>,crate::DecodeError>,rest|Some((Ok(match copied{Err(error)=>(Err(error),ht_clear_refinement_state(before)),
            Ok(_)=>ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)}),rest)),Err(error),Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,Ok(refined),calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(output.1,refinement,part2_ht_following(passes) as u8,output.3,before.style.vertical_causal_context,work,calls),
        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
            part2_ht_coeff_after_refinement(before,segments,passes,maximum_u,skipped,work,output,refinement,refined,rest),Ok(refined),Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,Ok(output),calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,before.private_plan,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),Ok(output),Ok(result));
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_replay_admit(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64)
    ->Result<Option<(Tier1RawPlane,HtRefinementSegmentState,u8)>,crate::DecodeError> {
    let total=before.ht_refinement_passes as nat+passes as nat;
    if !ht_block_coding_enabled(before.style.block_coding) || before.next_pass==0 || !before.ht_current_set_has_cleanup
        || before.next_pass%3==0 || passes==0 || total>2 {Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else{match before.ht_cleanup_plane {
        None=>Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
        Some(cleanup)=>{
            let next=before.decoded_bytes as nat+(input.len() as u64) as nat;
            if next>u64::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else if next>maximum_bytes{Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlockBytes,limit:maximum_bytes,actual:next as u64})}
            else{
                let data=before.ht_refinement_data+input;
                if data.len()>2046{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
                else if data.len()==0{Ok(None)}else{Ok(Some((cleanup,HtRefinementSegmentState {
                    encoded:data,significance_propagation:HtSubstreamState {bytes:data,offset:0,forward:true},
                    magnitude_refinement:HtSubstreamState {bytes:data,offset:0,forward:false}},total as u8)))}
            }
        },
    }}
}
pub(crate) proof fn part2_ht_replay_original_projection(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    ensures ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)==match part2_ht_replay_admit(before,input,passes,maximum_bytes){
        Err(error)=>(Err(error),before),
        Ok(None)=>ht_finish_refinement_contribution(Tier1DecoderState {ht_refinement_passes:(before.ht_refinement_passes as nat+passes as nat) as u8,..before},
            passes,0,(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,tier1_statistics_zero(),false),
        Ok(Some(args))=>match ht_refinement_plane(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work){
            Err(error)=>(Err(error),before),
            Ok(value)=>ht_finish_refinement_contribution(Tier1DecoderState {plane:value.0,ht_refinement_data:before.ht_refinement_data+input,ht_refinement_passes:args.2,..before},
                passes,input.len(),(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,value.1,true),
        },
    },
{reveal(ht_decode_refinement_contribution);reveal(part2_ht_replay_admit);}
pub(crate) open spec fn part2_ht_replay_route_admitted(before:Tier1DecoderState,passes:u8)->bool {
    ht_block_coding_enabled(before.style.block_coding) && before.next_pass!=0 && before.ht_current_set_has_cleanup
        && before.next_pass%3!=0 && passes!=0 && before.ht_refinement_passes as nat+passes as nat<=2
}
pub(crate) open spec fn part2_ht_replay_copy_admitted(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64)->bool {
    part2_ht_replay_route_admitted(before,passes)
        && before.ht_cleanup_plane.is_some() && before.decoded_bytes as nat+(input.len() as u64) as nat<=u64::MAX
        && before.decoded_bytes as nat+(input.len() as u64) as nat<=maximum_bytes
}
pub(crate) proof fn part2_ht_replay_admission_fields(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64)
    ensures
        (!part2_ht_replay_route_admitted(before,passes) || before.ht_cleanup_plane.is_none()) ==>
            part2_ht_replay_admit(before,input,passes,maximum_bytes)==Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
        (part2_ht_replay_route_admitted(before,passes) && before.ht_cleanup_plane.is_some() && before.decoded_bytes as nat+(input.len() as u64) as nat>u64::MAX) ==>
            part2_ht_replay_admit(before,input,passes,maximum_bytes)==Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),
        (part2_ht_replay_route_admitted(before,passes) && before.ht_cleanup_plane.is_some() && before.decoded_bytes as nat+(input.len() as u64) as nat<=u64::MAX
            && before.decoded_bytes as nat+(input.len() as u64) as nat>maximum_bytes) ==>
            part2_ht_replay_admit(before,input,passes,maximum_bytes)==Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlockBytes,limit:maximum_bytes,actual:(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64}),
        (part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes) && (before.ht_refinement_data+input).len()>2046) ==>
            part2_ht_replay_admit(before,input,passes,maximum_bytes)==Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),
        (part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes) && (before.ht_refinement_data+input).len()==0) ==>
            part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(None),
        (part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes) && 0<(before.ht_refinement_data+input).len()<=2046) ==>
            part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(Some((before.ht_cleanup_plane.unwrap(),HtRefinementSegmentState {
                encoded:before.ht_refinement_data+input,
                significance_propagation:HtSubstreamState {bytes:before.ht_refinement_data+input,offset:0,forward:true},
                magnitude_refinement:HtSubstreamState {bytes:before.ht_refinement_data+input,offset:0,forward:false}},
                (before.ht_refinement_passes as nat+passes as nat) as u8))),
{reveal(part2_ht_replay_admit);}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_replay_after_copy(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match part2_ht_replay_admit(before,input,passes,maximum_bytes) {
        Ok(Some(args))=>part2_tier1_storage_resume(part2_plane_refinement_run(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,calls),
            |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
                Some((Ok(match refined {Err(error)=>(Err(error),before),Ok(_)=>ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)}),rest))),
        _=>Some((Ok(ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),calls)),
    }
}
#[verifier::opaque]
    pub(crate) open spec fn part2_ht_replay_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
        if !part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes){Some((Ok(ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),calls))}
        else{part2_tier1_storage_resume(part2_ht_bytes_run(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,calls),
            |copied:Result<Seq<u8>,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(_)=>part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,rest)})}
    }
pub closed spec fn part2_ht_replay_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_replay_run(before,input,passes,maximum_bytes,work,calls),Ok(result))
        && (result.0!=Err(crate::DecodeError::AllocationFailed) ==> result==ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work))
}
pub(crate) proof fn part2_ht_replay_primary_consequence(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,result:HtDecoderResult)
    requires part2_ht_replay_result(before,input,passes,maximum_bytes,work,result),
    ensures result.0!=Err(crate::DecodeError::AllocationFailed) ==> result==ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work),
{}
pub(crate) proof fn part2_ht_replay_early_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    ensures !part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes) ==>
        part2_ht_replay_result(before,input,passes,maximum_bytes,work,ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),
{
    reveal(part2_ht_replay_run);
    if !part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes){
        part2_tier1_storage_pure(Ok(ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)));
    }
}
pub(crate) proof fn part2_ht_replay_copied_pure(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    requires part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes),
        part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Ok(before.ht_refinement_data)),
        match part2_ht_replay_admit(before,input,passes,maximum_bytes){Ok(Some(_))=>false,_=>true},
    ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),
{
    reveal(part2_ht_replay_run);reveal(part2_ht_replay_after_copy);
    let result=ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work);
    let role=crate::tier1::HtRefinementCopyRole::RetainedReplay;
    part2_ht_bytes_frames(before.ht_refinement_data,role,Ok(before.ht_refinement_data));part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,calls),Ok(result));
    part2_tier1_resume_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),
        |copied:Result<Seq<u8>,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(_)=>part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,rest)},Ok(before.ht_refinement_data),Ok(result));
}
pub(crate) proof fn part2_ht_replay_after_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    ensures part2_tier1_storage_framed(|calls|part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,calls),Ok(ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work))),
{
    reveal(part2_ht_replay_after_copy);
    part2_ht_replay_original_projection(before,input,passes,maximum_bytes,work);
    let result=ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work);
    match part2_ht_replay_admit(before,input,passes,maximum_bytes) {
        Ok(Some(args))=>{
            part2_plane_refinement_normal(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work);
            let refined=ht_refinement_plane(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work);
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_resume_frame(|calls|part2_plane_refinement_run(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,calls),
                |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|Some((Ok(match refined {Err(error)=>(Err(error),before),Ok(_)=>result}),rest)),refined,Ok(result));
        },
        _=>{part2_tier1_storage_pure(Ok(result));},
    }
}
    pub(crate) proof fn part2_ht_replay_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
        ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),
    {
        reveal(part2_ht_replay_run);
        let result=ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work);
        if !part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes){part2_tier1_storage_pure(Ok(result));}
        else{
            let role=crate::tier1::HtRefinementCopyRole::RetainedReplay;
            part2_ht_bytes_normal(before.ht_refinement_data,role);part2_ht_bytes_frames(before.ht_refinement_data,role,Ok(before.ht_refinement_data));
            part2_ht_replay_after_normal(before,input,passes,maximum_bytes,work);
            part2_tier1_storage_eta(|calls|part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,calls),Ok(result));
            part2_tier1_resume_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),
                |copied:Result<Seq<u8>,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
                    Ok(_)=>part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,rest)},Ok(before.ht_refinement_data),Ok(result));
        }
    }
    pub(crate) proof fn part2_ht_replay_copy_error(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,error:crate::DecodeError)
        requires part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes),
            error==crate::DecodeError::AllocationFailed,
            part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Err(error)),
        ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(error),before)),
    {
        reveal(part2_ht_replay_run);
        let role=crate::tier1::HtRefinementCopyRole::RetainedReplay;
        part2_ht_bytes_frames(before.ht_refinement_data,role,Err(error));part2_tier1_storage_pure::<HtDecoderResult>(Ok((Err(error),before)));
        part2_tier1_resume_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),
            |copied:Result<Seq<u8>,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(_)=>part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,rest)},Err(error),Ok((Err(error),before)));
    }
pub(crate) proof fn part2_ht_replay_error(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,args:(Tier1RawPlane,HtRefinementSegmentState,u8),error:crate::DecodeError)
    requires part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(Some(args)),
        part2_plane_refinement_result(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,Err(error)),
        part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Ok(before.ht_refinement_data)),
        error!=crate::DecodeError::AllocationFailed ==> ht_refinement_plane(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work)==Err(error),
    ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(error),before)),
{
    reveal(part2_ht_replay_admit);
    reveal(part2_ht_replay_run);reveal(part2_ht_replay_after_copy);
    part2_ht_replay_original_projection(before,input,passes,maximum_bytes,work);
    let result=(Err(error),before);part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,calls),
        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
            Some((Ok(match refined {Err(error)=>(Err(error),before),Ok(_)=>ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)}),rest)),Err(error),Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,calls),Ok(result));
    let role=crate::tier1::HtRefinementCopyRole::RetainedReplay;part2_ht_bytes_frames(before.ht_refinement_data,role,Ok(before.ht_refinement_data));
    part2_tier1_resume_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),
        |copied:Result<Seq<u8>,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(_)=>part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,rest)},Ok(before.ht_refinement_data),Ok(result));
}
pub(crate) proof fn part2_ht_replay_committed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,
    args:(Tier1RawPlane,HtRefinementSegmentState,u8),plane:Tier1RawPlane,statistics:crate::tier1::Tier1PassStatistics)
    requires part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(Some(args)),
        part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Ok(before.ht_refinement_data)),
        part2_plane_refinement_result(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,Ok((plane,statistics))),
        ht_refinement_plane(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work)==Ok((plane,statistics)),
    ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,
        ht_finish_refinement_contribution(Tier1DecoderState {plane,ht_refinement_data:before.ht_refinement_data+input,ht_refinement_passes:args.2,..before},
            passes,input.len(),(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,statistics,true)),
        ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)==
            ht_finish_refinement_contribution(Tier1DecoderState {plane,ht_refinement_data:before.ht_refinement_data+input,ht_refinement_passes:args.2,..before},
                passes,input.len(),(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,statistics,true),
{
    reveal(part2_ht_replay_admit);
    reveal(part2_ht_replay_run);reveal(part2_ht_replay_after_copy);
    part2_ht_replay_original_projection(before,input,passes,maximum_bytes,work);
    let result=ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,calls),
        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
            Some((Ok(match refined{Err(error)=>(Err(error),before),Ok(_)=>result}),rest)),Ok((plane,statistics)),Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,calls),Ok(result));
    let role=crate::tier1::HtRefinementCopyRole::RetainedReplay;part2_ht_bytes_frames(before.ht_refinement_data,role,Ok(before.ht_refinement_data));
    part2_tier1_resume_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),
        |copied:Result<Seq<u8>,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(_)=>part2_ht_replay_after_copy(before,input,passes,maximum_bytes,work,rest)},Ok(before.ht_refinement_data),Ok(result));
}
pub(crate) open spec fn part2_ht_segments_admit(before:Tier1DecoderState,cleanup:Seq<u8>,cleanup_passes:u8,refinement:Option<Seq<u8>>,refinement_passes:u8,
    maximum_passes:u32,maximum_bytes:u64,work:u64)->Result<(HtBlockSegmentsState,u32,u8,u16),crate::DecodeError> {
    if !ht_block_coding_enabled(before.style.block_coding) || before.next_pass%3!=0 || cleanup_passes!=1 || refinement_passes>2
        || (refinement_passes==0)!=refinement.is_none(){Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else if before.ht_sets_seen>0 && !before.allow_multiple_ht_sets{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else{
        let passes=cleanup_passes as nat+refinement_passes as nat;let next=before.next_pass as nat+passes;
        if next>u32::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
        else if next>before.maximum_passes{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
        else if next>maximum_passes{Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlockPasses,limit:maximum_passes as u64,actual:next as u64})}
        else{match ht_significant_bitplanes(before.maximum_passes){
            Err(error)=>Err(error),Ok(bits)=>if refinement_passes>0 && bits<2{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}else{
                match ht_parse_block_segments(cleanup,refinement,maximum_bytes) {
                    Err(error)=>Err(error),Ok(segments)=>{
                        let next_bytes=before.decoded_bytes as nat+segments.bytes as nat;
                        let coefficient_work=(before.plane.coefficients.len() as u64) as nat*(refinement_passes as nat+1);
                        let actual=coefficient_work+segments.bytes as nat+passes;
                        if next_bytes>u64::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                        else if next_bytes>maximum_bytes{Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlockBytes,limit:maximum_bytes,actual:next_bytes as u64})}
                        else if actual>u64::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                        else if actual>work{Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::WorkUnits,limit:work,actual:actual as u64})}
                        else{
                            let skipped=before.next_pass/3;
                            if skipped>u16::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
                            else{let missing=match before.zero_bitplanes{None=>0nat,Some(value)=>value as nat};
                                Ok((segments,passes as u32,part15_cleanup_u_bound(missing,skipped as nat,before.ht_magnitude_bound as nat) as u8,skipped as u16))}
                        }
                    },
                }
            },
        }}
    }
}
pub(crate) open spec fn part2_ht_segments_run(before:Tier1DecoderState,cleanup:Seq<u8>,cleanup_passes:u8,refinement:Option<Seq<u8>>,refinement_passes:u8,
    maximum_passes:u32,maximum_bytes:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match part2_ht_segments_admit(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work){
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(args)=>part2_ht_coeff_run(before,args.0,args.1,args.2,args.3,work,calls),
    }
}
pub closed spec fn part2_ht_segments_result(before:Tier1DecoderState,cleanup:Seq<u8>,cleanup_passes:u8,refinement:Option<Seq<u8>>,refinement_passes:u8,
    maximum_passes:u32,maximum_bytes:u64,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_segments_run(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,calls),Ok(result))
}
pub(crate) proof fn part2_ht_segments_normal(before:Tier1DecoderState,cleanup:Seq<u8>,cleanup_passes:u8,refinement:Option<Seq<u8>>,refinement_passes:u8,
    maximum_passes:u32,maximum_bytes:u64,work:u64)
    ensures part2_ht_segments_result(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,
        ht_decode_segments(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work)),
{
    let result=ht_decode_segments(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work);
    match part2_ht_segments_admit(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work) {
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(args)=>{
            part2_ht_coeff_normal(before,args.0,args.1,args.2,args.3,work);
            part2_tier1_storage_eta(|calls|part2_ht_coeff_run(before,args.0,args.1,args.2,args.3,work,calls),Ok(result));
        },
    }
}
pub(crate) proof fn part2_ht_segments_observed(before:Tier1DecoderState,cleanup:Seq<u8>,cleanup_passes:u8,refinement:Option<Seq<u8>>,refinement_passes:u8,
    maximum_passes:u32,maximum_bytes:u64,work:u64,args:(HtBlockSegmentsState,u32,u8,u16),result:HtDecoderResult)
    requires part2_ht_segments_admit(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work)==Ok(args),
        part2_ht_coeff_result(before,args.0,args.1,args.2,args.3,work,result),
    ensures part2_ht_segments_result(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,result),
{part2_tier1_storage_eta(|calls|part2_ht_coeff_run(before,args.0,args.1,args.2,args.3,work,calls),Ok(result));}
pub(crate) open spec fn part2_ht_staged_admit(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32)->Result<Tier1DecoderState,crate::DecodeError> {
    if passes==0 || input.len()==0{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}else{
        match ht_packet_pass_group(passes) {
            Err(error)=>Err(error),Ok(group)=>if group.refinement_passes!=0{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}else{
                let skipped=ht_placeholder_group_run(before,group.placeholder_passes as nat,maximum_passes);
                match skipped.0{Err(error)=>Err(error),Ok(())=>Ok(skipped.1)}
            },
        }
    }
}
pub(crate) open spec fn part2_ht_staged_copy_admitted(input:Seq<u8>,passes:u8)->bool {
    passes!=0 && input.len()!=0 && match ht_packet_pass_group(passes){Err(_)=>false,Ok(group)=>group.refinement_passes==0}
}
pub(crate) open spec fn part2_ht_staged_after_duplicate(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match part2_ht_staged_admit(before,input,passes,maximum_passes){
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(staged)=>part2_tier1_storage_bind(part2_ht_segments_run(staged,input,1,None,0,maximum_passes,maximum_bytes,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(match decoded.0{
                Err(error)=>(Err(error),before),Ok(result)=>(Ok(crate::tier1::Tier1SegmentDecode {passes:passes as u32,..result}),decoded.1)
            }),rest))),
    }
}
    pub(crate) open spec fn part2_ht_staged_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
        if !part2_ht_staged_copy_admitted(input,passes){Some((Ok(ht_decode_staged_group(before,input,passes,maximum_passes,maximum_bytes,work)),calls))}
        else{part2_tier1_storage_resume(part2_ht_duplicate_run(before,crate::tier1::HtRefinementCopyRole::HtStaging,calls),
            |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(_)=>part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,rest)})}
    }
pub(crate) open spec fn part2_ht_staged_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result))
}
pub(crate) proof fn part2_ht_staged_after_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64)
    ensures part2_tier1_storage_framed(|calls|part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(ht_decode_staged_group(before,input,passes,maximum_passes,maximum_bytes,work))),
{
    let result=ht_decode_staged_group(before,input,passes,maximum_passes,maximum_bytes,work);
    match part2_ht_staged_admit(before,input,passes,maximum_passes){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(staged)=>{
            part2_ht_segments_normal(staged,input,1,None,0,maximum_passes,maximum_bytes,work);
            let decoded=ht_decode_segments(staged,input,1,None,0,maximum_passes,maximum_bytes,work);
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_ht_segments_run(staged,input,1,None,0,maximum_passes,maximum_bytes,work,calls),
                |decoded:HtDecoderResult,rest|Some((Ok(match decoded.0{
                    Err(error)=>(Err(error),before),Ok(result)=>(Ok(crate::tier1::Tier1SegmentDecode {passes:passes as u32,..result}),decoded.1)
                }),rest)),Ok(decoded),Ok(result));
        },
    }
}
    pub(crate) proof fn part2_ht_staged_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64)
        ensures part2_ht_staged_result(before,input,passes,maximum_passes,maximum_bytes,work,ht_decode_staged_group(before,input,passes,maximum_passes,maximum_bytes,work)),
    {
        let result=ht_decode_staged_group(before,input,passes,maximum_passes,maximum_bytes,work);
        if !part2_ht_staged_copy_admitted(input,passes){part2_tier1_storage_pure(Ok(result));}else{
            let role=crate::tier1::HtRefinementCopyRole::HtStaging;
            part2_ht_duplicate_normal(before,role);part2_ht_duplicate_frames(before,role,Ok(before));
            part2_ht_staged_after_normal(before,input,passes,maximum_passes,maximum_bytes,work);
            part2_tier1_storage_eta(|calls|part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result));
            part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,role,calls),
                |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
                    Ok(_)=>part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,rest)},Ok(before),Ok(result));
        }
    }
    pub(crate) proof fn part2_ht_staged_duplicate_error(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,error:crate::DecodeError)
        requires part2_ht_staged_copy_admitted(input,passes),
            part2_ht_duplicate_result(before,crate::tier1::HtRefinementCopyRole::HtStaging,Err(error)),
        ensures part2_ht_staged_result(before,input,passes,maximum_passes,maximum_bytes,work,(Err(error),before)),
    {
        let role=crate::tier1::HtRefinementCopyRole::HtStaging;
        part2_ht_duplicate_frames(before,role,Err(error));part2_tier1_storage_pure::<HtDecoderResult>(Ok((Err(error),before)));
        part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,role,calls),
            |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(_)=>part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,rest)},Err(error),Ok((Err(error),before)));
    }
pub(crate) proof fn part2_ht_staged_observed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,
    staged:Tier1DecoderState,decoded:HtDecoderResult)
    requires part2_ht_staged_admit(before,input,passes,maximum_passes)==Ok(staged),
        part2_ht_segments_result(staged,input,1,None,0,maximum_passes,maximum_bytes,work,decoded),
        part2_ht_duplicate_result(before,crate::tier1::HtRefinementCopyRole::HtStaging,Ok(before)),
    ensures part2_ht_staged_result(before,input,passes,maximum_passes,maximum_bytes,work,match decoded.0{
        Err(error)=>(Err(error),before),Ok(result)=>(Ok(crate::tier1::Tier1SegmentDecode {passes:passes as u32,..result}),decoded.1)
    }),
{
    let result=match decoded.0{Err(error)=>(Err(error),before),Ok(result)=>(Ok(crate::tier1::Tier1SegmentDecode {passes:passes as u32,..result}),decoded.1)};
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_ht_segments_run(staged,input,1,None,0,maximum_passes,maximum_bytes,work,calls),
        |decoded:HtDecoderResult,rest|Some((Ok(match decoded.0{
            Err(error)=>(Err(error),before),Ok(result)=>(Ok(crate::tier1::Tier1SegmentDecode {passes:passes as u32,..result}),decoded.1)
        }),rest)),Ok(decoded),Ok(result));
    part2_tier1_storage_eta(|calls|part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result));
    let role=crate::tier1::HtRefinementCopyRole::HtStaging;part2_ht_duplicate_frames(before,role,Ok(before));
    part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,role,calls),
        |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{Err(error)=>Some((Ok((Err(error),before)),rest)),
            Ok(_)=>part2_ht_staged_after_duplicate(before,input,passes,maximum_passes,maximum_bytes,work,rest)},Ok(before),Ok(result));
}
pub(crate) open spec fn part2_plane_segment_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    if passes!=0 && ht_group_route(before){part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls)}
    else if passes==0{Some((Ok(part1_tier1_segment(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work)),calls))}
    else{part2_legacy_segment_run(before,input,passes as u32,part2_legacy_caps(maximum_passes,maximum_bytes,maximum_input,work),calls)}
}
pub closed spec fn part2_plane_segment_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_plane_segment_run(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,calls),Ok(result))
}
pub(crate) proof fn part2_plane_segment_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64)
    ensures part2_plane_segment_result(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,part1_tier1_segment(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work)),
{
    let result=part1_tier1_segment(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work);
    if passes!=0 && ht_group_route(before){part2_ht_staged_normal(before,input,passes,maximum_passes,maximum_bytes,work);
        part2_tier1_storage_eta(|calls|part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result));}
    else if passes==0{part2_tier1_storage_pure(Ok(result));}
    else{
        let caps=part2_legacy_caps(maximum_passes,maximum_bytes,maximum_input,work);
        part2_legacy_segment_normal(before,input,passes as u32,caps);
        part2_legacy_segment_frames(before,input,passes as u32,caps,result);
        part2_tier1_storage_eta(|calls|part2_legacy_segment_run(before,input,passes as u32,caps,calls),Ok(result));
    }
}
pub(crate) proof fn part2_plane_segment_observed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,result:HtDecoderResult)
    requires passes!=0,ht_group_route(before),part2_ht_staged_result(before,input,passes,maximum_passes,maximum_bytes,work,result),
    ensures part2_plane_segment_result(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,result),
{part2_tier1_storage_eta(|calls|part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result));}
pub(crate) proof fn part2_plane_segment_legacy_observed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,result:HtDecoderResult)
    requires passes!=0,!ht_group_route(before),
        part2_legacy_segment_result(before,input,passes as u32,part2_legacy_caps(maximum_passes,maximum_bytes,maximum_input,work),result),
    ensures part2_plane_segment_result(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,result),
{
    let caps=part2_legacy_caps(maximum_passes,maximum_bytes,maximum_input,work);
    part2_legacy_segment_frames(before,input,passes as u32,caps,result);
    part2_tier1_storage_eta(|calls|part2_legacy_segment_run(before,input,passes as u32,caps,calls),Ok(result));
}
pub(crate) proof fn part2_ht_replay_frames(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,result:HtDecoderResult)
    requires part2_ht_replay_result(before,input,passes,maximum_bytes,work,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_replay_run(before,input,passes,maximum_bytes,work,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult>|
            (forall|calls| #[trigger] other(calls)==part2_ht_replay_run(before,input,passes,maximum_bytes,work,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{part2_tier1_storage_eta(|calls|part2_ht_replay_run(before,input,passes,maximum_bytes,work,calls),Ok(result));}
pub(crate) proof fn part2_ht_segments_frames(before:Tier1DecoderState,cleanup:Seq<u8>,cleanup_passes:u8,refinement:Option<Seq<u8>>,refinement_passes:u8,
    maximum_passes:u32,maximum_bytes:u64,work:u64,result:HtDecoderResult)
    requires part2_ht_segments_result(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_segments_run(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult>|
            (forall|calls| #[trigger] other(calls)==part2_ht_segments_run(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,calls))
                ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{part2_tier1_storage_eta(|calls|part2_ht_segments_run(before,cleanup,cleanup_passes,refinement,refinement_passes,maximum_passes,maximum_bytes,work,calls),Ok(result));}
pub(crate) proof fn part2_plane_segment_frames(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,result:HtDecoderResult)
    requires part2_plane_segment_result(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,result),
    ensures part2_tier1_storage_framed(|calls|part2_plane_segment_run(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,calls),Ok(result)),
{part2_tier1_storage_eta(|calls|part2_plane_segment_run(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,calls),Ok(result));}
}
