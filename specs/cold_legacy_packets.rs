//! Actual legacy packet folds bind snapshot/restoration responses and partial progress.
use super::*;
verus! {
pub(crate) open spec fn part2_legacy_packet_admit(s:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>)->Result<(crate::packet::CodeBlockSegmentContribution,usize),crate::DecodeError> {
    match part1_code_block_segment(header,s.segment_index){
        Err(error)=>Err(error),Ok(segment)=>{
            let end=s.offset as nat+segment.data_length as nat;
            if segment.data_length as nat>usize::MAX || end>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
            else if end>body.len(){Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
            else{Ok((segment,end as usize))}
        },
    }
}
pub(crate) open spec fn part2_legacy_packet_after_decode(before:Part1LegacyPacketProgress,segment:crate::packet::CodeBlockSegmentContribution,end:usize,decoded:Part2LegacyResult)->Part1LegacyPacketEffect {
    let state=Part1LegacyPacketProgress {decoder:decoded.1,..before};
    match decoded.0{
        Err(error)=>(Err(error),state),
        Ok(())=>if state.decoded_passes as nat+segment.passes as nat>u32::MAX{(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state)}
        else{
            let state=Part1LegacyPacketProgress {decoded_passes:(state.decoded_passes+segment.passes) as u32,offset:end,..state};
            if state.segment_index==u8::MAX{(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),state)}
            else{(Ok(()),Part1LegacyPacketProgress {segment_index:(state.segment_index+1) as u8,..state})}
        },
    }
}
pub(crate) open spec fn part2_legacy_packet_step_run(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyPacketEffect> {
    match part2_legacy_packet_admit(before,header,body){
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok((segment,end))=>part2_tier1_storage_bind(part2_legacy_contribution_run(before.decoder,body.subrange(before.offset as int,end as int),segment.passes,caps,calls),
            |decoded:Part2LegacyResult,rest|Some((Ok(part2_legacy_packet_after_decode(before,segment,end,decoded)),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_packet_step_result(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,result:Part1LegacyPacketEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_packet_step_run(before,header,body,caps,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_packet_step_observed(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
    segment:crate::packet::CodeBlockSegmentContribution,end:usize,decoded:Part2LegacyResult)
    requires part2_legacy_packet_admit(before,header,body)==Ok((segment,end)),
        part2_legacy_contribution_result(before.decoder,body.subrange(before.offset as int,end as int),segment.passes,caps,decoded),
    ensures part2_legacy_packet_step_result(before,header,body,caps,part2_legacy_packet_after_decode(before,segment,end,decoded)),
{
    reveal(part2_legacy_packet_step_result);
    let input=body.subrange(before.offset as int,end as int);
    let result=part2_legacy_packet_after_decode(before,segment,end,decoded);
    part2_legacy_contribution_frames(before.decoder,input,segment.passes,caps,decoded);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_contribution_run(before.decoder,input,segment.passes,caps,calls),
        |decoded:Part2LegacyResult,rest|Some((Ok(part2_legacy_packet_after_decode(before,segment,end,decoded)),rest)),Ok(decoded),Ok(result));
}
pub(crate) proof fn part2_legacy_packet_step_normal(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps)
    ensures part2_legacy_packet_step_result(before,header,body,caps,part1_legacy_code_block_segment(before,header,body,caps.passes,caps.bytes,caps.input,caps.work)),
{
    reveal(part2_legacy_packet_step_result);reveal(part1_legacy_code_block_segment);
    match part2_legacy_packet_admit(before,header,body){
        Err(error)=>{part2_tier1_storage_pure::<Part1LegacyPacketEffect>(Ok((Err(error),before)));},
        Ok((segment,end))=>{
            let input=body.subrange(before.offset as int,end as int);
            part2_legacy_contribution_normal(before.decoder,input,segment.passes,caps);
            part2_legacy_packet_step_observed(before,header,body,caps,segment,end,
                part1_legacy_contribution(before.decoder,input,segment.passes,caps.passes,caps.bytes,caps.input,caps.work));
        },
    }
}
pub(crate) proof fn part2_legacy_packet_step_frames(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,result:Part1LegacyPacketEffect)
    requires part2_legacy_packet_step_result(before,header,body,caps,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_packet_step_run(before,header,body,caps,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyPacketEffect>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_packet_step_run(before,header,body,caps,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_packet_step_result);part2_tier1_storage_eta(|calls|part2_legacy_packet_step_run(before,header,body,caps,calls),Ok(result));}
pub(crate) open spec fn part2_legacy_packet_fold(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,remaining:nat,caps:Part2LegacyCaps,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyPacketEffect>
    decreases remaining,
{
    if remaining==0{Some((Ok((Ok(()),before)),calls))}
    else{part2_tier1_storage_bind(part2_legacy_packet_step_run(before,header,body,caps,calls),|step:Part1LegacyPacketEffect,rest|
        match step.0{Err(_)=>Some((Ok(step),rest)),Ok(())=>part2_legacy_packet_fold(step.1,header,body,(remaining-1) as nat,caps,rest)})}
}
pub(crate) proof fn part2_legacy_packet_fold_normal(before:Part1LegacyPacketProgress,header:Part1CodeBlockContribution,body:Seq<u8>,remaining:nat,caps:Part2LegacyCaps)
    ensures part2_tier1_storage_framed(|calls|part2_legacy_packet_fold(before,header,body,remaining,caps,calls),
        Ok(part1_legacy_code_block_run(before,header,body,remaining,caps.passes,caps.bytes,caps.input,caps.work))),
    decreases remaining,
{
    let result=part1_legacy_code_block_run(before,header,body,remaining,caps.passes,caps.bytes,caps.input,caps.work);
    if remaining==0{part2_tier1_storage_pure(Ok(result));}
    else{
        part2_legacy_packet_step_normal(before,header,body,caps);
        let step=part1_legacy_code_block_segment(before,header,body,caps.passes,caps.bytes,caps.input,caps.work);
        part2_legacy_packet_step_frames(before,header,body,caps,step);
        let next=|step:Part1LegacyPacketEffect,rest|match step.0{Err(_)=>Some((Ok(step),rest)),Ok(())=>part2_legacy_packet_fold(step.1,header,body,(remaining-1) as nat,caps,rest)};
        match step.0{
            Err(_)=>{part2_tier1_storage_pure(Ok(step));},
            Ok(())=>{
                part2_legacy_packet_fold_normal(step.1,header,body,(remaining-1) as nat,caps);
                part2_tier1_storage_eta(|calls|part2_legacy_packet_fold(step.1,header,body,(remaining-1) as nat,caps,calls),Ok(result));
            }
        }
        part2_tier1_storage_eta(|calls|next(step,calls),Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_legacy_packet_step_run(before,header,body,caps,calls),|step:Part1LegacyPacketEffect,rest|
            match step.0{Err(_)=>Some((Ok(step),rest)),Ok(())=>part2_legacy_packet_fold(step.1,header,body,(remaining-1) as nat,caps,rest)},Ok(step),Ok(result));
    }
}
pub(crate) open spec fn part2_legacy_packet_body_run(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult> {
    part2_tier1_storage_bind(part2_legacy_packet_fold(Part1LegacyPacketProgress {decoder:before,segment_index:0,offset:0,decoded_passes:0},header,body,header.segment_count as nat,caps,calls),
        |run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_packet_body_result(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,result:HtCodeBlockBodyResult)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_packet_body_normal(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps)
    ensures part2_legacy_packet_body_result(before,header,body,caps,part1_legacy_code_block_body(before,header,body,caps.passes,caps.bytes,caps.input,caps.work)),
{
    reveal(part2_legacy_packet_body_result);reveal(part1_legacy_code_block_body);
    let initial=Part1LegacyPacketProgress {decoder:before,segment_index:0,offset:0,decoded_passes:0};
    let run=part1_legacy_code_block_run(initial,header,body,header.segment_count as nat,caps.passes,caps.bytes,caps.input,caps.work);
    part2_legacy_packet_fold_normal(initial,header,body,header.segment_count as nat,caps);
    part2_tier1_storage_eta(|calls|part2_legacy_packet_fold(initial,header,body,header.segment_count as nat,caps,calls),Ok(run));
    part2_tier1_storage_pure(Ok(part1_legacy_code_block_finish(run,header,body)));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_packet_fold(initial,header,body,header.segment_count as nat,caps,calls),
        |run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest)),Ok(run),Ok(part1_legacy_code_block_finish(run,header,body)));
}
pub(crate) proof fn part2_legacy_packet_body_start(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps)
    ensures part2_tier1_phase(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),Seq::empty(),
        |calls|part2_tier1_storage_bind(part2_legacy_packet_fold(Part1LegacyPacketProgress {decoder:before,segment_index:0,offset:0,decoded_passes:0},header,body,header.segment_count as nat,caps,calls),
            |run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest)))),
{}
pub(crate) proof fn part2_legacy_packet_body_frames(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,result:HtCodeBlockBodyResult)
    requires part2_legacy_packet_body_result(before,header,body,caps,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtCodeBlockBodyResult>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_packet_body_run(before,header,body,caps,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_packet_body_result);part2_tier1_storage_eta(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),Ok(result));}
pub(crate) proof fn part2_legacy_packet_body_step(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
    current:Part1LegacyPacketProgress,remaining:nat,prefix:Seq<Part2Tier1StorageEvent>,effect:Part1LegacyPacketEffect)->(joined:Seq<Part2Tier1StorageEvent>)
    requires remaining>0,
        part2_tier1_phase(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),prefix,
            |calls|part2_tier1_storage_bind(part2_legacy_packet_fold(current,header,body,remaining,caps,calls),
                |run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest)))),
        part2_legacy_packet_step_result(current,header,body,caps,effect),
    ensures part2_tier1_phase(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),joined,
        |calls|match effect.0{
            Err(_)=>Some((Ok(part1_legacy_code_block_finish(effect,header,body)),calls)),
            Ok(())=>part2_tier1_storage_bind(part2_legacy_packet_fold(effect.1,header,body,(remaining-1) as nat,caps,calls),
                |run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest))),
        }),
{
    let root=|calls|part2_legacy_packet_body_run(before,header,body,caps,calls);
    let child=|calls|part2_legacy_packet_step_run(current,header,body,caps,calls);
    let finish=|run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest));
    let next=|step:Part1LegacyPacketEffect,rest|match step.0{
        Err(_)=>Some((Ok(part1_legacy_code_block_finish(step,header,body)),rest)),
        Ok(())=>part2_tier1_storage_bind(part2_legacy_packet_fold(step.1,header,body,(remaining-1) as nat,caps,rest),finish),
    };
    assert forall|tail:Seq<Part2Tier1StorageEvent>|root(prefix+tail)==part2_tier1_storage_bind(child(tail),next) by{
        reveal_with_fuel(part2_legacy_packet_fold,1);
        match part2_legacy_packet_step_run(current,header,body,caps,tail){
            None=>{},Some((Err(_),_))=>{},Some((Ok(step),_))=>{match step.0{Err(_)=>{},Ok(())=>{}}}
        }
    }
    part2_legacy_packet_step_frames(current,header,body,caps,effect);
    part2_tier1_prefix_advance(root,child,next,prefix,effect)
}
pub(crate) proof fn part2_legacy_packet_body_finish(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,prefix:Seq<Part2Tier1StorageEvent>,effect:Part1LegacyPacketEffect)
    requires part2_tier1_phase(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),prefix,
        |calls|Some((Ok(part1_legacy_code_block_finish(effect,header,body)),calls))),
    ensures part2_legacy_packet_body_result(before,header,body,caps,part1_legacy_code_block_finish(effect,header,body)),
{
    reveal(part2_legacy_packet_body_result);
    part2_tier1_prefix_finish(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),prefix,Ok(part1_legacy_code_block_finish(effect,header,body)));
}
pub(crate) proof fn part2_legacy_packet_body_end(before:Tier1DecoderState,header:Part1CodeBlockContribution,body:Seq<u8>,caps:Part2LegacyCaps,
    current:Part1LegacyPacketProgress,prefix:Seq<Part2Tier1StorageEvent>)
    requires part2_tier1_phase(|calls|part2_legacy_packet_body_run(before,header,body,caps,calls),prefix,
        |calls|part2_tier1_storage_bind(part2_legacy_packet_fold(current,header,body,0,caps,calls),
            |run:Part1LegacyPacketEffect,rest|Some((Ok(part1_legacy_code_block_finish(run,header,body)),rest)))),
    ensures part2_legacy_packet_body_result(before,header,body,caps,part1_legacy_code_block_finish((Ok(()),current),header,body)),
{part2_legacy_packet_body_finish(before,header,body,caps,prefix,(Ok(()),current));}
}
