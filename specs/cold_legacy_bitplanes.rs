//! Ordered bitplane construction responses inside actual legacy pass/segment folds.
use super::*;
verus! {
pub(crate) open spec fn part2_legacy_step_after_pass(before:Part1LegacySegmentRun,kind:crate::tier1::Tier1PassKind,decoded:Part1LegacySegmentPassEffect)->Part1LegacySegmentEffect {
    let state=Part1LegacySegmentRun {decoder:decoded.1,symbols:decoded.2,..before};
    match decoded.0{
        Err(error)=>(Err(error),state),
        Ok(statistics)=>{
            let merged=tier1_statistics_merge(state.statistics,statistics);
            let state=Part1LegacySegmentRun {statistics:merged.1,..state};
            match merged.0{
                Err(error)=>(Err(error),state),
                Ok(())=>{
                    let advanced=part1_legacy_advance(state.decoder,kind);
                    let state=Part1LegacySegmentRun {decoder:advanced.1,..state};
                    match advanced.0{
                        Err(error)=>(Err(error),state),
                        Ok(())=>if state.symbols is Raw{
                            (Ok(()),Part1LegacySegmentRun {decoder:if state.decoder.style.reset_contexts{
                                Tier1DecoderState {reset_contexts_before_mq:true,..state.decoder}
                            }else{state.decoder},..state})
                        }else{
                            let mq=state.symbols->Mq_0;
                            (Ok(()),Part1LegacySegmentRun {symbols:Part1LegacySymbols::Mq(
                                if state.decoder.style.reset_contexts{part1_legacy_initialized(mq)}else{mq}),..state})
                        },
                    }
                },
            }
        },
    }
}
pub(crate) open spec fn part2_legacy_inner_step_run(before:Part1LegacySegmentRun,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentEffect> {
    let plan=part1_legacy_plan(before.decoder.style,before.decoder.next_pass);
    if (plan.coding_mode is Raw)!=(before.symbols is Raw){Some((Ok((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before)),calls))}
    else{part2_tier1_storage_bind(part2_legacy_pass_run(before.decoder,before.symbols,plan.kind,calls),
        |decoded:Part1LegacySegmentPassEffect,rest|Some((Ok(part2_legacy_step_after_pass(before,plan.kind,decoded)),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_inner_step_result(before:Part1LegacySegmentRun,result:Part1LegacySegmentEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_inner_step_run(before,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_inner_step_observed(before:Part1LegacySegmentRun,kind:crate::tier1::Tier1PassKind,decoded:Part1LegacySegmentPassEffect)
    requires part1_legacy_plan(before.decoder.style,before.decoder.next_pass).kind==kind,
        (part1_legacy_plan(before.decoder.style,before.decoder.next_pass).coding_mode is Raw)==(before.symbols is Raw),
        part2_legacy_pass_result(before.decoder,before.symbols,kind,decoded),
    ensures part2_legacy_inner_step_result(before,part2_legacy_step_after_pass(before,kind,decoded)),
{
    reveal(part2_legacy_inner_step_result);
    let result=part2_legacy_step_after_pass(before,kind,decoded);
    part2_legacy_pass_frames(before.decoder,before.symbols,kind,decoded);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_pass_run(before.decoder,before.symbols,kind,calls),
        |decoded:Part1LegacySegmentPassEffect,rest|Some((Ok(part2_legacy_step_after_pass(before,kind,decoded)),rest)),Ok(decoded),Ok(result));
}
pub(crate) proof fn part2_legacy_inner_step_normal(before:Part1LegacySegmentRun)
    ensures part2_legacy_inner_step_result(before,part1_legacy_segment_step(before)),
{
    reveal(part2_legacy_inner_step_result);reveal(part1_legacy_segment_step);
    let plan=part1_legacy_plan(before.decoder.style,before.decoder.next_pass);
    if (plan.coding_mode is Raw)!=(before.symbols is Raw){part2_tier1_storage_pure(Ok(part1_legacy_segment_step(before)));}
    else{
        part2_legacy_pass_normal(before.decoder,before.symbols,plan.kind);
        part2_legacy_inner_step_observed(before,plan.kind,part1_legacy_decode_pass(before.decoder,before.symbols,plan.kind));
    }
}
pub(crate) proof fn part2_legacy_inner_step_frames(before:Part1LegacySegmentRun,result:Part1LegacySegmentEffect)
    requires part2_legacy_inner_step_result(before,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_inner_step_run(before,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentEffect>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_inner_step_run(before,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_inner_step_result);part2_tier1_storage_eta(|calls|part2_legacy_inner_step_run(before,calls),Ok(result));}
pub(crate) open spec fn part2_legacy_inner_fold(before:Part1LegacySegmentRun,remaining:nat,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentEffect>
    decreases remaining,
{
    if remaining==0{Some((Ok((Ok(()),before)),calls))}
    else{part2_tier1_storage_bind(part2_legacy_inner_step_run(before,calls),|step:Part1LegacySegmentEffect,rest|
        match step.0{Err(_)=>Some((Ok(step),rest)),Ok(())=>part2_legacy_inner_fold(step.1,(remaining-1) as nat,rest)})}
}
pub(crate) proof fn part2_legacy_inner_fold_normal(before:Part1LegacySegmentRun,remaining:nat)
    ensures part2_tier1_storage_framed(|calls|part2_legacy_inner_fold(before,remaining,calls),Ok(part1_legacy_segment_run(before,remaining))),
    decreases remaining,
{
    let result=part1_legacy_segment_run(before,remaining);
    if remaining==0{part2_tier1_storage_pure(Ok(result));}
    else{
        let step=part1_legacy_segment_step(before);
        part2_legacy_inner_step_normal(before);part2_legacy_inner_step_frames(before,step);
        let next=|step:Part1LegacySegmentEffect,rest|match step.0{Err(_)=>Some((Ok(step),rest)),Ok(())=>part2_legacy_inner_fold(step.1,(remaining-1) as nat,rest)};
        match step.0{
            Err(_)=>{part2_tier1_storage_pure(Ok(step));},
            Ok(())=>{part2_legacy_inner_fold_normal(step.1,(remaining-1) as nat);
                part2_tier1_storage_eta(|calls|part2_legacy_inner_fold(step.1,(remaining-1) as nat,calls),Ok(result));},
        }
        part2_tier1_storage_eta(|calls|next(step,calls),Ok(result));
        part2_tier1_storage_bind_frame(|calls|part2_legacy_inner_step_run(before,calls),next,Ok(step),Ok(result));
    }
}
pub(crate) open spec fn part2_legacy_inner_body_run(before:Part1LegacySegmentRun,count:u32,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentPassEffect> {
    part2_tier1_storage_bind(part2_legacy_inner_fold(before,count as nat,calls),
        |effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_inner_body_result(before:Part1LegacySegmentRun,count:u32,result:Part1LegacySegmentPassEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_inner_body_run(before,count,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_inner_body_normal(before:Part1LegacySegmentRun,count:u32)
    ensures part2_legacy_inner_body_result(before,count,part1_legacy_segment_finish(part1_legacy_segment_run(before,count as nat))),
{
    reveal(part2_legacy_inner_body_result);
    let run=part1_legacy_segment_run(before,count as nat);
    part2_legacy_inner_fold_normal(before,count as nat);
    part2_tier1_storage_eta(|calls|part2_legacy_inner_fold(before,count as nat,calls),Ok(run));
    part2_tier1_storage_pure(Ok(part1_legacy_segment_finish(run)));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_inner_fold(before,count as nat,calls),
        |effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest)),Ok(run),Ok(part1_legacy_segment_finish(run)));
}
pub(crate) proof fn part2_legacy_inner_body_frames(before:Part1LegacySegmentRun,count:u32,result:Part1LegacySegmentPassEffect)
    requires part2_legacy_inner_body_result(before,count,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_inner_body_run(before,count,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentPassEffect>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_inner_body_run(before,count,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_inner_body_result);part2_tier1_storage_eta(|calls|part2_legacy_inner_body_run(before,count,calls),Ok(result));}
pub(crate) proof fn part2_legacy_inner_body_start(before:Part1LegacySegmentRun,count:u32)
    ensures part2_tier1_phase(|calls|part2_legacy_inner_body_run(before,count,calls),Seq::empty(),
        |calls|part2_tier1_storage_bind(part2_legacy_inner_fold(before,count as nat,calls),
            |effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest)))),
{}
pub(crate) proof fn part2_legacy_inner_body_step(before:Part1LegacySegmentRun,count:u32,current:Part1LegacySegmentRun,remaining:nat,
    prefix:Seq<Part2Tier1StorageEvent>,effect:Part1LegacySegmentEffect)->(joined:Seq<Part2Tier1StorageEvent>)
    requires remaining>0,part2_legacy_inner_step_result(current,effect),
        part2_tier1_phase(|calls|part2_legacy_inner_body_run(before,count,calls),prefix,
            |calls|part2_tier1_storage_bind(part2_legacy_inner_fold(current,remaining,calls),
                |effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest)))),
    ensures part2_tier1_phase(|calls|part2_legacy_inner_body_run(before,count,calls),joined,
        |calls|match effect.0{
            Err(_)=>Some((Ok(part1_legacy_segment_finish(effect)),calls)),
            Ok(())=>part2_tier1_storage_bind(part2_legacy_inner_fold(effect.1,(remaining-1) as nat,calls),
                |effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest))),
        }),
{
    let root=|calls|part2_legacy_inner_body_run(before,count,calls);
    let child=|calls|part2_legacy_inner_step_run(current,calls);
    let finish=|effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest));
    let next=|step:Part1LegacySegmentEffect,rest|match step.0{Err(_)=>Some((Ok(part1_legacy_segment_finish(step)),rest)),
        Ok(())=>part2_tier1_storage_bind(part2_legacy_inner_fold(step.1,(remaining-1) as nat,rest),finish)};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|root(prefix+tail)==part2_tier1_storage_bind(child(tail),next) by{
        reveal_with_fuel(part2_legacy_inner_fold,1);
        match child(tail){None=>{},Some((Err(_),_))=>{},Some((Ok(step),_))=>{match step.0{Err(_)=>{},Ok(())=>{}}}}
    }
    part2_legacy_inner_step_frames(current,effect);
    part2_tier1_prefix_advance(root,child,next,prefix,effect)
}
pub(crate) proof fn part2_legacy_inner_body_finish(before:Part1LegacySegmentRun,count:u32,prefix:Seq<Part2Tier1StorageEvent>,effect:Part1LegacySegmentEffect)
    requires part2_tier1_phase(|calls|part2_legacy_inner_body_run(before,count,calls),prefix,
        |calls|Some((Ok(part1_legacy_segment_finish(effect)),calls))),
    ensures part2_legacy_inner_body_result(before,count,part1_legacy_segment_finish(effect)),
{
    reveal(part2_legacy_inner_body_result);
    part2_tier1_prefix_finish(|calls|part2_legacy_inner_body_run(before,count,calls),prefix,Ok(part1_legacy_segment_finish(effect)));
}
pub(crate) proof fn part2_legacy_inner_body_end(before:Part1LegacySegmentRun,count:u32,current:Part1LegacySegmentRun,prefix:Seq<Part2Tier1StorageEvent>)
    requires part2_tier1_phase(|calls|part2_legacy_inner_body_run(before,count,calls),prefix,
        |calls|part2_tier1_storage_bind(part2_legacy_inner_fold(current,0,calls),
            |effect:Part1LegacySegmentEffect,rest|Some((Ok(part1_legacy_segment_finish(effect)),rest)))),
    ensures part2_legacy_inner_body_result(before,count,part1_legacy_segment_finish((Ok(()),current))),
{part2_legacy_inner_body_finish(before,count,prefix,(Ok(()),current));}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_segment_prepared(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps)->Result<Part1LegacySegmentRun,crate::DecodeError> {
    match part1_legacy_segment_admission(before,input,count,caps.passes,caps.bytes){
        Err(error)=>Err(error),
        Ok(())=>if part1_legacy_plan(before.style,before.next_pass).coding_mode is Mq{
            match part1_mq_initial(input,caps.input,caps.work){
                Err(error)=>Err(error),Ok(mq)=>{
                    let ready=part1_legacy_segment_setup(before,mq);
                    Ok(Part1LegacySegmentRun {decoder:ready.0,symbols:Part1LegacySymbols::Mq(ready.1),statistics:tier1_statistics_zero()})
                },
            }
        }else{match part1_raw_reader_initial(input,caps.input,caps.work){
            Err(error)=>Err(error),Ok(raw)=>Ok(Part1LegacySegmentRun {decoder:before,symbols:Part1LegacySymbols::Raw(raw),statistics:tier1_statistics_zero()}),
        }},
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_segment_finish(before:Tier1DecoderState,input:Seq<u8>,count:u32,inner:Part1LegacySegmentPassEffect)->HtDecoderResult {
    if part1_legacy_plan(before.style,before.next_pass).coding_mode is Mq{part1_legacy_segment_mq_finish(inner,input.len(),count)}
    else{part1_legacy_segment_raw_finish(inner,input.len(),count)}
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_segment_run(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult> {
    match part2_legacy_segment_prepared(before,input,count,caps){
        Err(error)=>Some((Ok((Err(error),before)),calls)),
        Ok(initial)=>part2_tier1_storage_bind(part2_legacy_inner_body_run(initial,count,calls),
            |inner:Part1LegacySegmentPassEffect,rest|Some((Ok(part2_legacy_segment_finish(before,input,count,inner)),rest))),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_segment_result(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps,result:HtDecoderResult)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_segment_run(before,input,count,caps,calls),Ok(result))
        && (result.0!=Err(crate::DecodeError::AllocationFailed) ==> result==part1_legacy_segment(before,input,count,caps.passes,caps.bytes,caps.input,caps.work))
}
pub(crate) proof fn part2_legacy_segment_observed(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps,initial:Part1LegacySegmentRun,inner:Part1LegacySegmentPassEffect)
    requires part2_legacy_segment_prepared(before,input,count,caps)==Ok(initial),part2_legacy_inner_body_result(initial,count,inner),
        inner.0!=Err(crate::DecodeError::AllocationFailed) ==> inner==part1_legacy_segment_finish(part1_legacy_segment_run(initial,count as nat)),
    ensures part2_legacy_segment_result(before,input,count,caps,part2_legacy_segment_finish(before,input,count,inner)),
{
    reveal(part2_legacy_segment_result);reveal(part2_legacy_segment_run);reveal(part2_legacy_segment_prepared);reveal(part2_legacy_segment_finish);
    reveal(part1_legacy_segment);
    let result=part2_legacy_segment_finish(before,input,count,inner);
    part2_legacy_inner_body_frames(initial,count,inner);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_inner_body_run(initial,count,calls),
        |inner:Part1LegacySegmentPassEffect,rest|Some((Ok(part2_legacy_segment_finish(before,input,count,inner)),rest)),Ok(inner),Ok(result));
}
pub(crate) proof fn part2_legacy_segment_normal(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps)
    ensures part2_legacy_segment_result(before,input,count,caps,part1_legacy_segment(before,input,count,caps.passes,caps.bytes,caps.input,caps.work)),
{
    reveal(part2_legacy_segment_result);reveal(part2_legacy_segment_run);reveal(part2_legacy_segment_prepared);reveal(part2_legacy_segment_finish);reveal(part1_legacy_segment);
    match part2_legacy_segment_prepared(before,input,count,caps){
        Err(error)=>{part2_tier1_storage_pure::<HtDecoderResult>(Ok((Err(error),before)));},
        Ok(initial)=>{
            part2_legacy_inner_body_normal(initial,count);
            part2_legacy_segment_observed(before,input,count,caps,initial,part1_legacy_segment_finish(part1_legacy_segment_run(initial,count as nat)));
        },
    }
}
pub(crate) proof fn part2_legacy_segment_prepared_equation(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps)
    ensures part2_legacy_segment_prepared(before,input,count,caps)==
        match part1_legacy_segment_admission(before,input,count,caps.passes,caps.bytes){
            Err(error)=>Err(error),Ok(())=>if part1_legacy_plan(before.style,before.next_pass).coding_mode is Mq{
                match part1_mq_initial(input,caps.input,caps.work){Err(error)=>Err(error),Ok(mq)=>{
                    let ready=part1_legacy_segment_setup(before,mq);
                    Ok(Part1LegacySegmentRun {decoder:ready.0,symbols:Part1LegacySymbols::Mq(ready.1),statistics:tier1_statistics_zero()})
                }}
            }else{match part1_raw_reader_initial(input,caps.input,caps.work){Err(error)=>Err(error),Ok(raw)=>
                Ok(Part1LegacySegmentRun {decoder:before,symbols:Part1LegacySymbols::Raw(raw),statistics:tier1_statistics_zero()})}},
        },
{reveal(part2_legacy_segment_prepared);}
pub(crate) proof fn part2_legacy_segment_prepared_error(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps,error:crate::DecodeError)
    requires part2_legacy_segment_prepared(before,input,count,caps)==Err(error),
    ensures part2_legacy_segment_result(before,input,count,caps,(Err(error),before)),
{
    reveal(part2_legacy_segment_result);reveal(part2_legacy_segment_run);reveal(part2_legacy_segment_prepared);reveal(part1_legacy_segment);
    part2_tier1_storage_pure::<HtDecoderResult>(Ok((Err(error),before)));
}
pub(crate) proof fn part2_legacy_segment_finish_equation(before:Tier1DecoderState,input:Seq<u8>,count:u32,inner:Part1LegacySegmentPassEffect)
    ensures part2_legacy_segment_finish(before,input,count,inner)==
        if part1_legacy_plan(before.style,before.next_pass).coding_mode is Mq{part1_legacy_segment_mq_finish(inner,input.len(),count)}
        else{part1_legacy_segment_raw_finish(inner,input.len(),count)},
{reveal(part2_legacy_segment_finish);}
pub(crate) proof fn part2_legacy_segment_primary_consequence(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps,result:HtDecoderResult)
    requires part2_legacy_segment_result(before,input,count,caps,result),
    ensures result.0!=Err(crate::DecodeError::AllocationFailed) ==> result==part1_legacy_segment(before,input,count,caps.passes,caps.bytes,caps.input,caps.work),
{reveal(part2_legacy_segment_result);}
pub(crate) proof fn part2_legacy_segment_frames(before:Tier1DecoderState,input:Seq<u8>,count:u32,caps:Part2LegacyCaps,result:HtDecoderResult)
    requires part2_legacy_segment_result(before,input,count,caps,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_segment_run(before,input,count,caps,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<HtDecoderResult>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_segment_run(before,input,count,caps,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_segment_result);part2_tier1_storage_eta(|calls|part2_legacy_segment_run(before,input,count,caps,calls),Ok(result));}
}
