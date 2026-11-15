//! Source-derived packet HT segment production over actual coefficient responses.
use super::*;
verus! {
pub(crate) open spec fn part2_packet_ht_route_finish(decoded:HtDecoderResult)->HtPlaceholderRunResult {
    (match decoded.0{Err(error)=>Err(error),Ok(_)=>Ok(())},decoded.1)
}
pub(crate) open spec fn part2_packet_ht_route_run(before:Tier1DecoderState,body:Seq<u8>,passes:u8,pass_limit:u32,byte_limit:u64,work:u64,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtPlaceholderRunResult> {
    if before.next_pass%3==0 && passes==1 && body.len()>0 {
        part2_tier1_storage_bind(part2_ht_segments_run(before,body,1,None,0,pass_limit,byte_limit,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(part2_packet_ht_route_finish(decoded)),rest)))
    }else if before.next_pass%3!=0 && before.ht_current_set_has_cleanup{
        part2_tier1_storage_bind(part2_ht_replay_run(before,body,passes,byte_limit,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(part2_packet_ht_route_finish(decoded)),rest)))
    }else{Some((Ok(ht_packet_segment_route(before,body,passes,pass_limit,byte_limit,work)),calls))}
}
pub(crate) open spec fn part2_packet_ht_route_result(before:Tier1DecoderState,body:Seq<u8>,passes:u8,pass_limit:u32,byte_limit:u64,work:u64,result:HtPlaceholderRunResult)->bool {
    part2_tier1_storage_framed(|calls|part2_packet_ht_route_run(before,body,passes,pass_limit,byte_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_packet_ht_route_normal(before:Tier1DecoderState,body:Seq<u8>,passes:u8,pass_limit:u32,byte_limit:u64,work:u64)
    ensures part2_packet_ht_route_result(before,body,passes,pass_limit,byte_limit,work,ht_packet_segment_route(before,body,passes,pass_limit,byte_limit,work)),
{
    let result=ht_packet_segment_route(before,body,passes,pass_limit,byte_limit,work);
    if before.next_pass%3==0 && passes==1 && body.len()>0 {
        part2_ht_segments_normal(before,body,1,None,0,pass_limit,byte_limit,work);
        let decoded=ht_decode_segments(before,body,1,None,0,pass_limit,byte_limit,work);
        part2_ht_segments_frames(before,body,1,None,0,pass_limit,byte_limit,work,decoded);
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_ht_segments_run(before,body,1,None,0,pass_limit,byte_limit,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(part2_packet_ht_route_finish(decoded)),rest)),Ok(decoded),Ok(result));
    }else if before.next_pass%3!=0 && before.ht_current_set_has_cleanup{
        part2_ht_replay_normal(before,body,passes,byte_limit,work);let decoded=ht_decode_refinement_contribution(before,body,passes,byte_limit,work);
        part2_ht_replay_frames(before,body,passes,byte_limit,work,decoded);
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_ht_replay_run(before,body,passes,byte_limit,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(part2_packet_ht_route_finish(decoded)),rest)),Ok(decoded),Ok(result));
    }else{part2_tier1_storage_pure(Ok(result));}
}
pub(crate) proof fn part2_packet_ht_route_observed(before:Tier1DecoderState,body:Seq<u8>,passes:u8,pass_limit:u32,byte_limit:u64,work:u64,decoded:HtDecoderResult)
    requires if before.next_pass%3==0 {
        passes==1 && body.len()>0 && part2_ht_segments_result(before,body,1,None,0,pass_limit,byte_limit,work,decoded)
    }else{before.ht_current_set_has_cleanup && part2_ht_replay_result(before,body,passes,byte_limit,work,decoded)},
    ensures part2_packet_ht_route_result(before,body,passes,pass_limit,byte_limit,work,part2_packet_ht_route_finish(decoded)),
{
    let result=part2_packet_ht_route_finish(decoded);part2_tier1_storage_pure(Ok(result));
    if before.next_pass%3==0 {
        part2_ht_segments_frames(before,body,1,None,0,pass_limit,byte_limit,work,decoded);
        part2_tier1_storage_bind_frame(|calls|part2_ht_segments_run(before,body,1,None,0,pass_limit,byte_limit,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(part2_packet_ht_route_finish(decoded)),rest)),Ok(decoded),Ok(result));
    }else{
        part2_ht_replay_frames(before,body,passes,byte_limit,work,decoded);
        part2_tier1_storage_bind_frame(|calls|part2_ht_replay_run(before,body,passes,byte_limit,work,calls),
            |decoded:HtDecoderResult,rest|Some((Ok(part2_packet_ht_route_finish(decoded)),rest)),Ok(decoded),Ok(result));
    }
}
pub(crate) open spec fn part2_packet_ht_segment_admit(segment:crate::packet::CodeBlockSegmentContribution,body:Seq<u8>,offset:usize)->Result<usize,crate::DecodeError> {
    let length=segment.data_length as nat;let end=offset as nat+length;
    if segment.passes==0 || segment.passes>2{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else if length>usize::MAX || end>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
    else if offset>body.len() || end>body.len(){Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}else{Ok(end as usize)}
}
pub(crate) open spec fn part2_packet_ht_segment_finish(decoded:HtPlaceholderRunResult,segment:crate::packet::CodeBlockSegmentContribution,
    offset:usize,passes:u32,end:usize)->HtPacketSegmentResult {
    match decoded.0{
        Err(error)=>(Err(error),decoded.1,offset,passes),
        Ok(())=>if passes as nat+segment.passes as nat>u32::MAX{(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),decoded.1,offset,passes)}
            else{(Ok(()),decoded.1,end,(passes+segment.passes) as u32)},
    }
}
pub(crate) open spec fn part2_packet_ht_segment_run(before:Tier1DecoderState,segment:crate::packet::CodeBlockSegmentContribution,body:Seq<u8>,offset:usize,passes:u32,
    pass_limit:u32,byte_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtPacketSegmentResult> {
    match part2_packet_ht_segment_admit(segment,body,offset){
        Err(error)=>Some((Ok((Err(error),before,offset,passes)),calls)),
        Ok(end)=>part2_tier1_storage_bind(part2_packet_ht_route_run(before,body.subrange(offset as int,end as int),segment.passes,pass_limit,byte_limit,work,calls),
            |decoded:HtPlaceholderRunResult,rest|Some((Ok(part2_packet_ht_segment_finish(decoded,segment,offset,passes,end)),rest))),
    }
}
pub(crate) open spec fn part2_packet_ht_segment_result(before:Tier1DecoderState,segment:crate::packet::CodeBlockSegmentContribution,body:Seq<u8>,offset:usize,passes:u32,
    pass_limit:u32,byte_limit:u64,work:u64,result:HtPacketSegmentResult)->bool {
    part2_tier1_storage_framed(|calls|part2_packet_ht_segment_run(before,segment,body,offset,passes,pass_limit,byte_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_packet_ht_segment_normal(before:Tier1DecoderState,segment:crate::packet::CodeBlockSegmentContribution,body:Seq<u8>,offset:usize,passes:u32,
    pass_limit:u32,byte_limit:u64,work:u64)
    ensures part2_packet_ht_segment_result(before,segment,body,offset,passes,pass_limit,byte_limit,work,
        ht_packet_segment_body(before,segment,body,offset,passes,pass_limit,byte_limit,work)),
{
    let result=ht_packet_segment_body(before,segment,body,offset,passes,pass_limit,byte_limit,work);
    match part2_packet_ht_segment_admit(segment,body,offset){
        Err(_)=>{part2_tier1_storage_pure(Ok(result));},
        Ok(end)=>{
            let bytes=body.subrange(offset as int,end as int);
            part2_packet_ht_route_normal(before,bytes,segment.passes,pass_limit,byte_limit,work);
            let decoded=ht_packet_segment_route(before,bytes,segment.passes,pass_limit,byte_limit,work);
            part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_packet_ht_route_run(before,bytes,segment.passes,pass_limit,byte_limit,work,calls),
                |decoded:HtPlaceholderRunResult,rest|Some((Ok(part2_packet_ht_segment_finish(decoded,segment,offset,passes,end)),rest)),Ok(decoded),Ok(result));
        },
    }
}
pub(crate) proof fn part2_packet_ht_segment_observed(before:Tier1DecoderState,segment:crate::packet::CodeBlockSegmentContribution,body:Seq<u8>,offset:usize,passes:u32,
    pass_limit:u32,byte_limit:u64,work:u64,end:usize,decoded:HtPlaceholderRunResult)
    requires part2_packet_ht_segment_admit(segment,body,offset)==Ok(end),
        part2_packet_ht_route_result(before,body.subrange(offset as int,end as int),segment.passes,pass_limit,byte_limit,work,decoded),
    ensures part2_packet_ht_segment_result(before,segment,body,offset,passes,pass_limit,byte_limit,work,part2_packet_ht_segment_finish(decoded,segment,offset,passes,end)),
{
    let result=part2_packet_ht_segment_finish(decoded,segment,offset,passes,end);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_packet_ht_route_run(before,body.subrange(offset as int,end as int),segment.passes,pass_limit,byte_limit,work,calls),
        |decoded:HtPlaceholderRunResult,rest|Some((Ok(part2_packet_ht_segment_finish(decoded,segment,offset,passes,end)),rest)),Ok(decoded),Ok(result));
}
pub(crate) open spec fn part2_packet_ht_body_next(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,progress:HtPacketBodyProgress,
    pass_limit:u32,byte_limit:u64,work:u64,step:HtPacketSegmentResult,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtPacketBodyRunResult>
    decreases if progress.segment_index<header.segment_count{(header.segment_count as int-progress.segment_index as int)*2}else{0int},
{
    if progress.segment_index>=header.segment_count{Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidPacketHeader)),state,progress)),calls))}else{
    let after=HtPacketBodyProgress {offset:step.2,decoded_passes:step.3,..progress};
    match step.0{
        Err(error)=>Some((Ok((Err(error),step.1,after)),calls)),
        Ok(())=>if progress.segment_index==u8::MAX{Some((Ok((Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),step.1,after)),calls))}
        else{part2_packet_ht_body_run(step.1,header,body,HtPacketBodyProgress {segment_index:(progress.segment_index+1) as u8,..after},pass_limit,byte_limit,work,calls)},
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_packet_ht_body_run(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,progress:HtPacketBodyProgress,
    pass_limit:u32,byte_limit:u64,work:u64,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtPacketBodyRunResult>
    decreases if progress.segment_index<header.segment_count{(header.segment_count as int-progress.segment_index as int)*2+1}else{0int},
{
    if progress.segment_index>=header.segment_count{Some((Ok((Ok(()),state,progress)),calls))}else{
        match part1_code_block_segment(header,progress.segment_index){
            Err(error)=>Some((Ok((Err(error),state,progress)),calls)),
            Ok(segment)=>part2_tier1_storage_bind(part2_packet_ht_segment_run(state,segment,body,progress.offset,progress.decoded_passes,pass_limit,byte_limit,work,calls),
                |step:HtPacketSegmentResult,rest|part2_packet_ht_body_next(state,header,body,progress,pass_limit,byte_limit,work,step,rest)),
        }
    }
}
pub(crate) open spec fn part2_packet_ht_body_result(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,progress:HtPacketBodyProgress,
    pass_limit:u32,byte_limit:u64,work:u64,result:HtPacketBodyRunResult)->bool {
    part2_tier1_storage_framed(|calls|part2_packet_ht_body_run(state,header,body,progress,pass_limit,byte_limit,work,calls),Ok(result))
}
pub(crate) proof fn part2_packet_ht_body_normal(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,progress:HtPacketBodyProgress,
    pass_limit:u32,byte_limit:u64,work:u64)
    ensures part2_packet_ht_body_result(state,header,body,progress,pass_limit,byte_limit,work,ht_packet_body_run(state,header,body,progress,pass_limit,byte_limit,work)),
    decreases if progress.segment_index<header.segment_count{(header.segment_count as int-progress.segment_index as int)*2+1}else{0int},
{
    reveal_with_fuel(part2_packet_ht_body_run,2);reveal_with_fuel(part2_packet_ht_body_next,1);reveal_with_fuel(ht_packet_body_run,1);
    let result=ht_packet_body_run(state,header,body,progress,pass_limit,byte_limit,work);
    if progress.segment_index>=header.segment_count{part2_tier1_storage_pure(Ok(result));}else{
        match part1_code_block_segment(header,progress.segment_index){
            Err(_)=>{part2_tier1_storage_pure(Ok(result));},
            Ok(segment)=>{
                part2_packet_ht_segment_normal(state,segment,body,progress.offset,progress.decoded_passes,pass_limit,byte_limit,work);
                let step=ht_packet_segment_body(state,segment,body,progress.offset,progress.decoded_passes,pass_limit,byte_limit,work);
                if step.0.is_ok() && progress.segment_index<u8::MAX{
                    let after=HtPacketBodyProgress {segment_index:(progress.segment_index+1) as u8,offset:step.2,decoded_passes:step.3};
                    part2_packet_ht_body_normal(step.1,header,body,after,pass_limit,byte_limit,work);
                    part2_tier1_storage_eta(|calls|part2_packet_ht_body_run(step.1,header,body,after,pass_limit,byte_limit,work,calls),Ok(result));
                }else{part2_tier1_storage_pure(Ok(result));}
                part2_tier1_storage_bind_frame(|calls|part2_packet_ht_segment_run(state,segment,body,progress.offset,progress.decoded_passes,pass_limit,byte_limit,work,calls),
                    |step:HtPacketSegmentResult,rest|part2_packet_ht_body_next(state,header,body,progress,pass_limit,byte_limit,work,step,rest),Ok(step),Ok(result));
            },
        }
    }
}
    pub(crate) proof fn part2_packet_ht_segment_frames(before:Tier1DecoderState,segment:crate::packet::CodeBlockSegmentContribution,body:Seq<u8>,offset:usize,passes:u32,
        pass_limit:u32,byte_limit:u64,work:u64,result:HtPacketSegmentResult)
        requires part2_packet_ht_segment_result(before,segment,body,offset,passes,pass_limit,byte_limit,work,result),
        ensures part2_tier1_storage_framed(|calls|part2_packet_ht_segment_run(before,segment,body,offset,passes,pass_limit,byte_limit,work,calls),Ok(result)),
            forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtPacketSegmentResult>|
                (forall|calls| #[trigger] other(calls)==part2_packet_ht_segment_run(before,segment,body,offset,passes,pass_limit,byte_limit,work,calls))
                    ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
    {part2_tier1_storage_eta(|calls|part2_packet_ht_segment_run(before,segment,body,offset,passes,pass_limit,byte_limit,work,calls),Ok(result));}
    pub(crate) proof fn part2_packet_ht_body_step(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,progress:HtPacketBodyProgress,
        pass_limit:u32,byte_limit:u64,work:u64,segment:crate::packet::CodeBlockSegmentContribution)
        requires progress.segment_index<header.segment_count,part1_code_block_segment(header,progress.segment_index)==Ok(segment),
        ensures forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] part2_packet_ht_body_run(state,header,body,progress,pass_limit,byte_limit,work,calls)
            ==part2_tier1_storage_bind(part2_packet_ht_segment_run(state,segment,body,progress.offset,progress.decoded_passes,pass_limit,byte_limit,work,calls),
                |step:HtPacketSegmentResult,rest|part2_packet_ht_body_next(state,header,body,progress,pass_limit,byte_limit,work,step,rest)),
    {reveal_with_fuel(part2_packet_ht_body_run,2);reveal_with_fuel(part2_packet_ht_body_next,1);}
    pub(crate) proof fn part2_packet_ht_body_join(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,progress:HtPacketBodyProgress,
        pass_limit:u32,byte_limit:u64,work:u64,root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtPacketBodyRunResult>,result:HtPacketBodyRunResult)
        requires part2_tier1_storage_framed(root,Ok(result)),forall|calls| #[trigger] root(calls)==part2_packet_ht_body_run(state,header,body,progress,pass_limit,byte_limit,work,calls),
        ensures part2_packet_ht_body_result(state,header,body,progress,pass_limit,byte_limit,work,result),
    {part2_tier1_storage_eta(root,Ok(result));}
    pub(crate) open spec fn part2_packet_ht_segments_finish(header:Part1CodeBlockContribution,body:Seq<u8>,decoded:HtPacketBodyRunResult)->HtCodeBlockBodyResult {
        match decoded.0{
            Err(error)=>(Err(error),decoded.1),
            Ok(())=>if decoded.2.offset!=body.len() || decoded.2.decoded_passes!=header.new_passes {
                (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),decoded.1)
            }else{(Ok(crate::packet::CodeBlockBodyDecode {segments:header.segment_count,passes:decoded.2.decoded_passes,bytes:header.data_length}),decoded.1)},
        }
    }
    pub(crate) open spec fn part2_packet_ht_segments_run(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,work:u64,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult> {
        if header.segment_count==0{Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),state)),calls))}else{
            part2_tier1_storage_bind(part2_packet_ht_body_run(state,header,body,HtPacketBodyProgress {segment_index:0,offset:0,decoded_passes:0},pass_limit,byte_limit,work,calls),
                |decoded:HtPacketBodyRunResult,rest|Some((Ok(part2_packet_ht_segments_finish(header,body,decoded)),rest)))
        }
    }
    pub(crate) open spec fn part2_packet_ht_segments_result(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,work:u64,result:HtCodeBlockBodyResult)->bool {
        part2_tier1_storage_framed(|calls|part2_packet_ht_segments_run(state,header,body,pass_limit,byte_limit,work,calls),Ok(result))
    }
    pub(crate) proof fn part2_packet_ht_segments_normal(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,work:u64)
        ensures part2_packet_ht_segments_result(state,header,body,pass_limit,byte_limit,work,ht_packet_body_segments(state,header,body,pass_limit,byte_limit,work)),
    {
        let result=ht_packet_body_segments(state,header,body,pass_limit,byte_limit,work);
        if header.segment_count==0{part2_tier1_storage_pure(Ok(result));}else{
            let progress=HtPacketBodyProgress {segment_index:0,offset:0,decoded_passes:0};
            part2_packet_ht_body_normal(state,header,body,progress,pass_limit,byte_limit,work);
            let decoded=ht_packet_body_run(state,header,body,progress,pass_limit,byte_limit,work);part2_tier1_storage_pure(Ok(result));
            part2_tier1_storage_bind_frame(|calls|part2_packet_ht_body_run(state,header,body,progress,pass_limit,byte_limit,work,calls),
                |decoded:HtPacketBodyRunResult,rest|Some((Ok(part2_packet_ht_segments_finish(header,body,decoded)),rest)),Ok(decoded),Ok(result));
        }
    }
    pub(crate) proof fn part2_packet_ht_segments_observed(state:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,work:u64,decoded:HtPacketBodyRunResult)
        requires header.segment_count>0,
            part2_packet_ht_body_result(state,header,body,HtPacketBodyProgress {segment_index:0,offset:0,decoded_passes:0},pass_limit,byte_limit,work,decoded),
        ensures part2_packet_ht_segments_result(state,header,body,pass_limit,byte_limit,work,part2_packet_ht_segments_finish(header,body,decoded)),
    {
        let result=part2_packet_ht_segments_finish(header,body,decoded);part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_packet_ht_body_run(state,header,body,HtPacketBodyProgress {segment_index:0,offset:0,decoded_passes:0},pass_limit,byte_limit,work,calls),
            |decoded:HtPacketBodyRunResult,rest|Some((Ok(part2_packet_ht_segments_finish(header,body,decoded)),rest)),Ok(decoded),Ok(result));
    }
    pub(crate) open spec fn part2_plane_body_staged_run(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult> {
        let prepared=part1_code_block_body_prepare(before,header,body);
        match prepared.0{
            Err(error)=>Some((Ok((Err(error),prepared.1)),calls)),
            Ok(())=>if header.high_throughput{part2_packet_ht_segments_run(prepared.1,header,body,pass_limit,byte_limit,work,calls)}
                else{Some((Ok(part1_legacy_code_block_body(prepared.1,header,body,pass_limit,byte_limit,input_limit,work)),calls))},
        }
    }
    pub(crate) open spec fn part2_plane_body_staged_result(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:HtCodeBlockBodyResult)->bool {
        part2_tier1_storage_framed(|calls|part2_plane_body_staged_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
    }
    pub(crate) proof fn part2_plane_body_staged_normal(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
        ensures part2_plane_body_staged_result(before,header,body,pass_limit,byte_limit,input_limit,work,part1_code_block_body_staged(before,header,body,pass_limit,byte_limit,input_limit,work)),
    {
        let result=part1_code_block_body_staged(before,header,body,pass_limit,byte_limit,input_limit,work);
        let prepared=part1_code_block_body_prepare(before,header,body);
        if prepared.0.is_ok() && header.high_throughput{
            part2_packet_ht_segments_normal(prepared.1,header,body,pass_limit,byte_limit,work);
            part2_tier1_storage_eta(|calls|part2_packet_ht_segments_run(prepared.1,header,body,pass_limit,byte_limit,work,calls),Ok(result));
        }else{part2_tier1_storage_pure(Ok(result));}
    }
    pub(crate) proof fn part2_plane_body_staged_observed(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:HtCodeBlockBodyResult)
        requires part1_code_block_body_prepare(before,header,body).0==Ok(()),header.high_throughput,
            part2_packet_ht_segments_result(part1_code_block_body_prepare(before,header,body).1,header,body,pass_limit,byte_limit,work,result),
        ensures part2_plane_body_staged_result(before,header,body,pass_limit,byte_limit,input_limit,work,result),
    {part2_tier1_storage_eta(|calls|part2_packet_ht_segments_run(part1_code_block_body_prepare(before,header,body).1,header,body,pass_limit,byte_limit,work,calls),Ok(result));}
    pub(crate) open spec fn part2_plane_body_after_duplicate(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult> {
        part2_tier1_storage_bind(part2_plane_body_staged_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),
            |staged:HtCodeBlockBodyResult,rest|Some((Ok(match staged.0{Err(error)=>(Err(error),before),Ok(_)=>staged}),rest)))
    }
    pub(crate) open spec fn part2_plane_body_transaction_run(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,
        calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult> {
        part2_tier1_storage_resume(part2_ht_duplicate_run(before,crate::tier1::HtRefinementCopyRole::PacketStaging,calls),
            |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{
                Err(error)=>Some((Ok((Err(error),before)),rest)),
                Ok(_)=>part2_plane_body_after_duplicate(before,header,body,pass_limit,byte_limit,input_limit,work,rest),
            })
    }
    pub closed spec fn part2_plane_body_transaction_result(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:HtCodeBlockBodyResult)->bool {
        part2_tier1_storage_framed(|calls|part2_plane_body_transaction_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result))
    }
    pub(crate) proof fn part2_plane_body_transaction_normal(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64)
        ensures part2_plane_body_transaction_result(before,header,body,pass_limit,byte_limit,input_limit,work,part1_code_block_body_transaction(before,header,body,pass_limit,byte_limit,input_limit,work)),
    {
        let result=part1_code_block_body_transaction(before,header,body,pass_limit,byte_limit,input_limit,work);
        part2_ht_duplicate_normal(before,crate::tier1::HtRefinementCopyRole::PacketStaging);
        part2_plane_body_staged_normal(before,header,body,pass_limit,byte_limit,input_limit,work);
        let staged=part1_code_block_body_staged(before,header,body,pass_limit,byte_limit,input_limit,work);
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_plane_body_staged_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),
            |staged:HtCodeBlockBodyResult,rest|Some((Ok(match staged.0{Err(error)=>(Err(error),before),Ok(_)=>staged}),rest)),Ok(staged),Ok(result));
        part2_tier1_storage_eta(|calls|part2_plane_body_after_duplicate(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result));
        part2_ht_duplicate_frames(before,crate::tier1::HtRefinementCopyRole::PacketStaging,Ok(before));
        part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,crate::tier1::HtRefinementCopyRole::PacketStaging,calls),
            |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{
                Err(error)=>Some((Ok((Err(error),before)),rest)),Ok(_)=>part2_plane_body_after_duplicate(before,header,body,pass_limit,byte_limit,input_limit,work,rest),
            },Ok(before),Ok(result));
    }
    pub(crate) proof fn part2_plane_body_transaction_observed(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,staged:HtCodeBlockBodyResult)
        requires part2_plane_body_staged_result(before,header,body,pass_limit,byte_limit,input_limit,work,staged),
            part2_ht_duplicate_result(before,crate::tier1::HtRefinementCopyRole::PacketStaging,Ok(before)),
        ensures part2_plane_body_transaction_result(before,header,body,pass_limit,byte_limit,input_limit,work,match staged.0{Err(error)=>(Err(error),before),Ok(_)=>staged}),
    {
        let result=match staged.0{Err(error)=>(Err(error),before),Ok(_)=>staged};part2_tier1_storage_pure(Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_plane_body_staged_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),
            |staged:HtCodeBlockBodyResult,rest|Some((Ok(match staged.0{Err(error)=>(Err(error),before),Ok(_)=>staged}),rest)),Ok(staged),Ok(result));
        part2_tier1_storage_eta(|calls|part2_plane_body_after_duplicate(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result));
        part2_ht_duplicate_frames(before,crate::tier1::HtRefinementCopyRole::PacketStaging,Ok(before));
        part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,crate::tier1::HtRefinementCopyRole::PacketStaging,calls),
            |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{
                Err(error)=>Some((Ok((Err(error),before)),rest)),Ok(_)=>part2_plane_body_after_duplicate(before,header,body,pass_limit,byte_limit,input_limit,work,rest),
            },Ok(before),Ok(result));
    }
    pub(crate) proof fn part2_plane_body_duplicate_error(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,error:crate::DecodeError)
        requires part2_ht_duplicate_result(before,crate::tier1::HtRefinementCopyRole::PacketStaging,Err(error)),
        ensures part2_plane_body_transaction_result(before,header,body,pass_limit,byte_limit,input_limit,work,(Err(error),before)),
    {
        let result=(Err(error),before);
        part2_ht_duplicate_frames(before,crate::tier1::HtRefinementCopyRole::PacketStaging,Err(error));
        part2_tier1_storage_pure(Ok(result));
        part2_tier1_resume_frame(|calls|part2_ht_duplicate_run(before,crate::tier1::HtRefinementCopyRole::PacketStaging,calls),
            |copied:Result<Tier1DecoderState,crate::DecodeError>,rest|match copied{
                Err(error)=>Some((Ok((Err(error),before)),rest)),Ok(_)=>part2_plane_body_after_duplicate(before,header,body,pass_limit,byte_limit,input_limit,work,rest),
            },Err(error),Ok(result));
    }
    pub(crate) proof fn part2_plane_body_transaction_frames(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,pass_limit:u32,byte_limit:u64,input_limit:u64,work:u64,result:HtCodeBlockBodyResult)
        requires part2_plane_body_transaction_result(before,header,body,pass_limit,byte_limit,input_limit,work,result),
        ensures part2_tier1_storage_framed(|calls|part2_plane_body_transaction_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result)),
            forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult>|
                (forall|calls| #[trigger] other(calls)==part2_plane_body_transaction_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls))
                    ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
    {part2_tier1_storage_eta(|calls|part2_plane_body_transaction_run(before,header,body,pass_limit,byte_limit,input_limit,work,calls),Ok(result));}
}
