//! Cut 1: a checked opaque continuation certificate for the native finish.
use super::*;
verus! {
pub(crate) struct Part2ReplayFinish {
    pub before:Tier1DecoderState,pub input:Seq<u8>,pub passes:u8,pub maximum_bytes:u64,pub work:u64,
    pub plane:Tier1RawPlane,pub data:Seq<u8>,pub refinement_passes:u8,pub next_bytes:u64,
    pub statistics:crate::tier1::Tier1PassStatistics,pub bytes:nat,pub replayed:bool,
}
#[verifier::opaque]
pub(crate) open spec fn part2_replay_prepared(t:Part2ReplayFinish,phase:nat,s:Tier1DecoderState)->Tier1DecoderState {
    if phase==0{Tier1DecoderState {plane:t.plane,ht_refinement_data:t.data,ht_refinement_passes:t.refinement_passes,..s}}
        else if phase==1{Tier1DecoderState {ht_refinement_data:t.data,ht_refinement_passes:t.refinement_passes,..s}}
        else if phase==2{Tier1DecoderState {ht_refinement_passes:t.refinement_passes,..s}}else{s}
}
#[verifier::opaque]
pub(crate) open spec fn part2_replay_remaining(t:Part2ReplayFinish,phase:nat,s:Tier1DecoderState)->HtDecoderResult {
    let prepared=part2_replay_prepared(t,phase,s);
    if phase<=3{ht_finish_refinement_contribution(prepared,t.passes,t.bytes,t.next_bytes,t.statistics,t.replayed)}
    else if phase==4{
        if s.decoded_segments==u32::MAX{(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),s)}
        else{
            let s=Tier1DecoderState {decoded_segments:(s.decoded_segments+1) as u32,..s};
            let s=if t.replayed{Tier1DecoderState {decoded_bytes:t.next_bytes,..s}}else{s};
            if t.bytes>u32::MAX{(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),s)}
            else{(Ok(crate::tier1::Tier1SegmentDecode {passes:t.passes as u32,bytes:t.bytes as u32,statistics:t.statistics}),s)}
        }
    }else{
        let s=if phase==5 && t.replayed{Tier1DecoderState {decoded_bytes:t.next_bytes,..s}}else{s};
        if t.bytes>u32::MAX{(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),s)}
        else{(Ok(crate::tier1::Tier1SegmentDecode {passes:t.passes as u32,bytes:t.bytes as u32,statistics:t.statistics}),s)}
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_replay_phase(t:Part2ReplayFinish,phase:nat,s:Tier1DecoderState)->bool {
    phase<=6 && part2_ht_replay_result(t.before,t.input,t.passes,t.maximum_bytes,t.work,part2_replay_remaining(t,phase,s))
}
pub(crate) proof fn part2_replay_finish_from_child(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64,
    args:(Tier1RawPlane,HtRefinementSegmentState,u8),plane:Tier1RawPlane,statistics:crate::tier1::Tier1PassStatistics)->(t:Part2ReplayFinish)
    requires part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(Some(args)),
        part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Ok(before.ht_refinement_data)),
        part2_plane_refinement_result(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work,Ok((plane,statistics))),
        ht_refinement_plane(args.0,args.1,args.2,before.ht_decoded_bitplanes,before.style.vertical_causal_context,work)==Ok((plane,statistics)),
    ensures t.before==before,t.input==input,t.passes==passes,t.maximum_bytes==maximum_bytes,t.work==work,
        t.plane==plane,t.data==before.ht_refinement_data+input,t.refinement_passes==args.2,t.statistics==statistics,
        t.bytes==input.len(),t.next_bytes==(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,t.replayed,
        part2_replay_phase(t,0,before),
{
    reveal(part2_replay_phase);reveal(part2_replay_remaining);reveal(part2_replay_prepared);
    part2_ht_replay_committed(before,input,passes,maximum_bytes,work,args,plane,statistics);
    Part2ReplayFinish {before,input,passes,maximum_bytes,work,plane,data:before.ht_refinement_data+input,
        refinement_passes:args.2,next_bytes:(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,
        statistics,bytes:input.len(),replayed:true}
}
pub(crate) proof fn part2_replay_finish_empty(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)->(t:Part2ReplayFinish)
    requires part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes),
        part2_ht_replay_admit(before,input,passes,maximum_bytes)==Ok(None),
        part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Ok(before.ht_refinement_data)),
    ensures t.before==before,t.input==input,t.passes==passes,t.maximum_bytes==maximum_bytes,t.work==work,
        t.refinement_passes==(before.ht_refinement_passes as nat+passes as nat) as u8,t.statistics==tier1_statistics_zero(),
        t.bytes==0,!t.replayed,part2_replay_phase(t,2,before),
{
    reveal(part2_replay_phase);reveal(part2_replay_remaining);reveal(part2_replay_prepared);
    part2_ht_replay_copied_pure(before,input,passes,maximum_bytes,work);
    part2_ht_replay_original_projection(before,input,passes,maximum_bytes,work);
    Part2ReplayFinish {before,input,passes,maximum_bytes,work,plane:before.plane,data:before.ht_refinement_data+input,
        refinement_passes:(before.ht_refinement_passes as nat+passes as nat) as u8,
        next_bytes:(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64,
        statistics:tier1_statistics_zero(),bytes:0,replayed:false}
}
pub(crate) open spec fn part2_replay_step(t:Part2ReplayFinish,phase:nat,s:Tier1DecoderState)->Tier1DecoderState {
    if phase==0{Tier1DecoderState {plane:t.plane,..s}}
    else if phase==1{Tier1DecoderState {ht_refinement_data:t.data,..s}}
    else if phase==2{Tier1DecoderState {ht_refinement_passes:t.refinement_passes,..s}}
    else if phase==3{Tier1DecoderState {next_pass:(s.next_pass as nat+t.passes as nat) as u32,..s}}
    else if phase==4{Tier1DecoderState {decoded_segments:(s.decoded_segments+1) as u32,..s}}
    else if t.replayed{Tier1DecoderState {decoded_bytes:t.next_bytes,..s}}else{s}
}
pub(crate) proof fn part2_replay_owner_equation(t:Part2ReplayFinish,phase:nat,prior:Tier1DecoderState,actual:Tier1DecoderState)
    requires phase<3,actual==part2_replay_step(t,phase,prior),
    ensures part2_replay_prepared(t,phase,prior)==part2_replay_prepared(t,phase+1,actual),
        part2_replay_remaining(t,phase,prior)==part2_replay_remaining(t,phase+1,actual),
{
    reveal(part2_replay_prepared);
    if phase==0 {} else if phase==1 {} else {assert(phase==2);}
    assert(part2_replay_prepared(t,phase,prior)==part2_replay_prepared(t,phase+1,actual));
    reveal(part2_replay_remaining);
}
pub(crate) proof fn part2_replay_pass_equation(t:Part2ReplayFinish,prior:Tier1DecoderState,actual:Tier1DecoderState)
    requires prior.next_pass as nat+t.passes as nat<=u32::MAX,actual==part2_replay_step(t,3,prior),
    ensures part2_replay_remaining(t,3,prior)==part2_replay_remaining(t,4,actual),
{
    reveal(part2_replay_remaining);reveal(part2_replay_prepared);reveal(ht_finish_refinement_contribution);
}
pub(crate) proof fn part2_replay_segment_equation(t:Part2ReplayFinish,prior:Tier1DecoderState,actual:Tier1DecoderState)
    requires prior.decoded_segments<u32::MAX,actual==part2_replay_step(t,4,prior),
    ensures part2_replay_remaining(t,4,prior)==part2_replay_remaining(t,5,actual),
{reveal(part2_replay_remaining);}
pub(crate) proof fn part2_replay_bytes_equation(t:Part2ReplayFinish,prior:Tier1DecoderState,actual:Tier1DecoderState)
    requires actual==part2_replay_step(t,5,prior),
    ensures part2_replay_remaining(t,5,prior)==part2_replay_remaining(t,6,actual),
{reveal(part2_replay_remaining);}
pub(crate) proof fn part2_replay_advance(t:Part2ReplayFinish,phase:nat,prior:Tier1DecoderState,actual:Tier1DecoderState)
    requires part2_replay_phase(t,phase,prior),phase<6,actual==part2_replay_step(t,phase,prior),
        phase==3 ==> prior.next_pass as nat+t.passes as nat<=u32::MAX,
        phase==4 ==> prior.decoded_segments<u32::MAX,
    ensures part2_replay_phase(t,phase+1,actual),
{
    if phase<3{part2_replay_owner_equation(t,phase,prior,actual);}
    else if phase==3{part2_replay_pass_equation(t,prior,actual);}
    else if phase==4{part2_replay_segment_equation(t,prior,actual);}
    else{assert(phase==5);part2_replay_bytes_equation(t,prior,actual);}
    reveal(part2_replay_phase);
}
pub(crate) proof fn part2_replay_counter_error(t:Part2ReplayFinish,phase:nat,s:Tier1DecoderState)
    requires part2_replay_phase(t,phase,s),
        (phase==3 && s.next_pass as nat+t.passes as nat>u32::MAX)
        || (phase==4 && s.decoded_segments==u32::MAX)
        || (phase==6 && t.bytes>u32::MAX),
    ensures part2_ht_replay_result(t.before,t.input,t.passes,t.maximum_bytes,t.work,(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),s)),
        (Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),s)==ht_decode_refinement_contribution(t.before,t.input,t.passes,t.maximum_bytes,t.work),
{
    reveal(part2_replay_phase);reveal(part2_replay_remaining);reveal(part2_replay_prepared);reveal(ht_finish_refinement_contribution);
    part2_ht_replay_primary_consequence(t.before,t.input,t.passes,t.maximum_bytes,t.work,(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),s));
}
pub(crate) proof fn part2_replay_return(t:Part2ReplayFinish,s:Tier1DecoderState)
    requires part2_replay_phase(t,6,s),t.bytes<=u32::MAX,
    ensures part2_ht_replay_result(t.before,t.input,t.passes,t.maximum_bytes,t.work,
        (Ok(crate::tier1::Tier1SegmentDecode {passes:t.passes as u32,bytes:t.bytes as u32,statistics:t.statistics}),s)),
        (Ok(crate::tier1::Tier1SegmentDecode {passes:t.passes as u32,bytes:t.bytes as u32,statistics:t.statistics}),s)
            ==ht_decode_refinement_contribution(t.before,t.input,t.passes,t.maximum_bytes,t.work),
{
    reveal(part2_replay_phase);reveal(part2_replay_remaining);
    part2_ht_replay_primary_consequence(t.before,t.input,t.passes,t.maximum_bytes,t.work,
        (Ok(crate::tier1::Tier1SegmentDecode {passes:t.passes as u32,bytes:t.bytes as u32,statistics:t.statistics}),s));
}
pub(crate) proof fn part2_replay_entry(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    ensures
        (!part2_ht_replay_route_admitted(before,passes) || before.ht_cleanup_plane.is_none()) ==>
            part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before)),
        (part2_ht_replay_route_admitted(before,passes) && before.ht_cleanup_plane.is_some() && before.decoded_bytes as nat+(input.len() as u64) as nat>u64::MAX) ==>
            part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow)),before)),
        (part2_ht_replay_route_admitted(before,passes) && before.ht_cleanup_plane.is_some() && before.decoded_bytes as nat+(input.len() as u64) as nat<=u64::MAX
            && before.decoded_bytes as nat+(input.len() as u64) as nat>maximum_bytes) ==>
            part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::CodeBlockBytes,limit:maximum_bytes,actual:(before.decoded_bytes as nat+(input.len() as u64) as nat) as u64}),before)),
{
    part2_ht_replay_early_result(before,input,passes,maximum_bytes,work);
    part2_ht_replay_original_projection(before,input,passes,maximum_bytes,work);
    part2_ht_replay_admission_fields(before,input,passes,maximum_bytes);
}
pub(crate) proof fn part2_replay_late_error(before:Tier1DecoderState,input:Seq<u8>,passes:u8,maximum_bytes:u64,work:u64)
    requires part2_ht_replay_copy_admitted(before,input,passes,maximum_bytes),
        (before.ht_refinement_data+input).len()>2046,
        part2_ht_bytes_result(before.ht_refinement_data,crate::tier1::HtRefinementCopyRole::RetainedReplay,Ok(before.ht_refinement_data)),
    ensures part2_ht_replay_result(before,input,passes,maximum_bytes,work,(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before)),
        (Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before)==ht_decode_refinement_contribution(before,input,passes,maximum_bytes,work),
{
    part2_ht_replay_admission_fields(before,input,passes,maximum_bytes);
    part2_ht_replay_original_projection(before,input,passes,maximum_bytes,work);
    part2_ht_replay_copied_pure(before,input,passes,maximum_bytes,work);
    part2_ht_replay_primary_consequence(before,input,passes,maximum_bytes,work,(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before));
}
}
