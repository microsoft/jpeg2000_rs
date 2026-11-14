//! Actual mutable HT decoder state around the shared fresh plane constructors.
use super::*;
verus! {
pub(crate) open spec fn part2_ht_following(passes:u32)->nat {if passes==0{0nat}else{(passes-1) as nat}}
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
                            Some((Ok(match refined {Err(error)=>(Err(error),cleared),Ok(_)=>ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)}),rest)))}
                },
            }
        },
    }
}
pub(crate) open spec fn part2_ht_coeff_run(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    part2_tier1_storage_resume(part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest))
}
pub(crate) open spec fn part2_ht_coeff_result(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_coeff_run(before,segments,passes,maximum_u,skipped,work,calls),Ok(result))
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
                    part2_tier1_storage_pure(Ok(result));
                    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(output.1,refinement,following as u8,output.3,cleared.style.vertical_causal_context,work,calls),
                        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
                            Some((Ok(match refined {Err(error)=>(Err(error),cleared),Ok(_)=>result}),rest)),refined,Ok(result));
                }
            },
        },
    }
}
pub(crate) proof fn part2_ht_coeff_normal(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64)
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)),
{
    part2_plane_prepare_normal(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work);
    let prepared=ht_cleanup_prepare(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work);
    part2_ht_coeff_after_normal(before,segments,passes,maximum_u,skipped,work);
    part2_tier1_storage_eta(|calls|part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,calls),
        Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),prepared,
        Ok(ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)));
}
pub(crate) proof fn part2_ht_coeff_prepare_error(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,error:crate::DecodeError)
    requires part2_plane_prepare_result(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,Err(error)),
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,(Err(error),before)),
{
    part2_tier1_storage_pure::<HtDecoderResult>(Ok((Err(error),before)));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),Err(error),Ok((Err(error),before)));
}
pub(crate) proof fn part2_ht_coeff_refinement_error(before:Tier1DecoderState,segments:HtBlockSegmentsState,passes:u32,maximum_u:u8,skipped:u16,work:u64,
    output:(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),refinement:HtRefinementSegmentState,error:crate::DecodeError)
    requires segments.refinement==Some(refinement),part2_ht_following(passes)<=u8::MAX,
        part2_plane_prepare_result(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,Ok(output)),
        part2_plane_refinement_result(output.1,refinement,part2_ht_following(passes) as u8,output.3,before.style.vertical_causal_context,work,Err(error)),
    ensures part2_ht_coeff_result(before,segments,passes,maximum_u,skipped,work,(Err(error),ht_clear_refinement_state(before))),
{
    let cleared=ht_clear_refinement_state(before);let result=(Err(error),cleared);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(output.1,refinement,part2_ht_following(passes) as u8,output.3,cleared.style.vertical_causal_context,work,calls),
        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
            Some((Ok(match refined {Err(error)=>(Err(error),cleared),Ok(_)=>ht_coefficient_symbols(before,segments,passes,maximum_u,skipped,work)}),rest)),Err(error),Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_prepare_run(before.plane,segments.cleanup,before.maximum_passes,maximum_u,skipped,work,calls),
        |prepared:Result<(Tier1RawPlane,Tier1RawPlane,crate::tier1::Tier1PassStatistics,u16),crate::DecodeError>,rest|
            part2_ht_coeff_after_prepare(before,segments,passes,maximum_u,skipped,work,prepared,rest),Ok(output),Ok(result));
}
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
pub(crate) open spec fn part2_ht_replay_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match part2_ht_replay_admit(before,input,passes,maximum_bytes) {
        Ok(Some(args))=>part2_tier1_storage_resume(part2_plane_refinement_run(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,calls),
            |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
                Some((Ok(match refined {Err(error)=>(Err(error),before),Ok(_)=>ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)}),rest))),
        _=>Some((Ok(ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),calls)),
    }
}
pub closed spec fn part2_ht_replay_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_replay_run(before,input,passes,maximum_bytes,work,calls),Ok(result))
}
pub(crate) proof fn part2_ht_replay_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)),
{
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
pub(crate) proof fn part2_ht_replay_error(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,args:(Tier1RawPlane,HtRefinementSegmentState,u8),error:crate::DecodeError)
    requires part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(Some(args)),
        part2_plane_refinement_result(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,Err(error)),
    ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(error),before)),
{
    let result=(Err(error),before);part2_tier1_storage_pure(Ok(result));
    part2_tier1_resume_frame(|calls|part2_plane_refinement_run(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,calls),
        |refined:Result<(Tier1RawPlane,crate::tier1::Tier1PassStatistics),crate::DecodeError>,rest|
            Some((Ok(match refined {Err(error)=>(Err(error),before),Ok(_)=>ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work)}),rest)),Err(error),Ok(result));
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
pub(crate) open spec fn part2_ht_staged_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match part2_ht_staged_admit(before,input,passes,maximum_passes){
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(staged)=>part2_tier1_storage_bind(part2_ht_segments_run(staged,input,1,None,0,maximum_passes,maximum_bytes,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(match decoded.0{
                Err(error)=>(Err(error),before),Ok(result)=>(Ok(crate::tier1::Tier1SegmentDecode {passes:passes as u32,..result}),decoded.1)
            }),rest))),
    }
}
pub(crate) open spec fn part2_ht_staged_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result))
}
pub(crate) proof fn part2_ht_staged_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64)
    ensures part2_ht_staged_result(before,input,passes,maximum_passes,maximum_bytes,work,ht_decode_staged_group(before,input,passes,maximum_passes,maximum_bytes,work)),
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
pub(crate) proof fn part2_ht_staged_observed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,work:u64,
    staged:Tier1DecoderState,decoded:HtDecoderResult)
    requires part2_ht_staged_admit(before,input,passes,maximum_passes)==Ok(staged),
        part2_ht_segments_result(staged,input,1,None,0,maximum_passes,maximum_bytes,work,decoded),
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
}
pub(crate) open spec fn part2_plane_segment_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    if passes!=0 && ht_group_route(before){part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls)}
    else{Some((Ok(part1_tier1_segment(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work)),calls))}
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
    else{part2_tier1_storage_pure(Ok(result));}
}
pub(crate) proof fn part2_plane_segment_observed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_passes:u32,maximum_bytes:u64,maximum_input:u64,work:u64,result:HtDecoderResult)
    requires passes!=0,ht_group_route(before),part2_ht_staged_result(before,input,passes,maximum_passes,maximum_bytes,work,result),
    ensures part2_plane_segment_result(before,input,passes,maximum_passes,maximum_bytes,maximum_input,work,result),
{part2_tier1_storage_eta(|calls|part2_ht_staged_run(before,input,passes,maximum_passes,maximum_bytes,work,calls),Ok(result));}
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
