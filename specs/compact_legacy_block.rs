//! Whole-block producer invariants for the actual fresh compact MQ loop.
use super::*;
verus! {
pub(crate) proof fn compact_budget_monotone(before:Tier1DecoderState,passes:u32,decoded:u64,wide_bytes:usize)
    requires compact_eligible(before,passes,decoded,wide_bytes),
    ensures compact_eligible(before,passes,u64::MAX,0),
{
    let cells=before.plane.width as nat*before.plane.height as nat;
    assert(cells*10<=40960) by(nonlinear_arith) requires cells<=4096;
}
pub(crate) proof fn compact_fresh_projection(width:usize,height:usize,words:Seq<u64>,plane:Tier1RawPlane)
    requires compact_shape(width,height,words),plane.width==width,plane.height==height,
        plane.coefficients.len()==words.len(),compact_pristine(plane),
        forall|i:int|0<=i<words.len() ==> #[trigger] words[i]==0x3f_0000_0000u64,
    ensures compact_plane(width,height,words)==plane,
{
    compact_empty_word();
    assert(compact_plane(width,height,words).coefficients =~= plane.coefficients);
}
pub(crate) proof fn compact_initial_metadata(width:usize,height:usize,words:Seq<u64>,bp:u16,state:Part1LegacyBitplane)
    requires compact_cache(width,height,words),bp<31,
        forall|i:int|0<=i<words.len() ==> #[trigger] compact_precision_word(words[i]),
        forall|i:int|0<=i<words.len() && #[trigger] compact_coefficient(words[i]).significant ==> ((words[i]>>32)&63)>bp,
        part1_legacy_bitplane_initial(compact_plane(width,height,words),bp)==Ok(state),
    ensures compact_membership(width,height,words,state),compact_before_frontier(words,state,false),
        !state.significance_propagation_complete,!state.magnitude_refinement_complete,!state.cleanup_complete,
        (forall|i:int|0<=i<words.len() ==> !compact_coefficient(words[i]).significant) ==> compact_before_frontier(words,state,true),
{
    assert forall|i:int|0<=i<words.len() implies {
        let significant=compact_coefficient(words[i]).significant;
        let tag=(words[i]>>32)&63;
        if #[trigger] state.significant_before[i]{significant && tag>=state.bitplane}
        else{significant ==> tag==state.bitplane}
    } by{}
}
pub(crate) open spec fn compact_block_bitplane(top:u16,pass:u32)->u16 {
    if pass>=3*(top as nat+1)-2{0u16}else{(top as int-(pass as int+2)/3) as u16}
}
pub(crate) proof fn compact_block_schedule(top:u16,pass:u32)
    requires top<31,pass<3*(top as nat+1)-2,
    ensures pass<91,3*(top as nat+1)-2<=91,compact_block_bitplane(top,pass)<=top,
        (part1_legacy_pass_kind(pass) is Cleanup)==(pass%3==0),
        (part1_legacy_pass_kind(pass) is SignificancePropagation)==(pass%3==1),
        (part1_legacy_pass_kind(pass) is MagnitudeRefinement)==(pass%3==2),
        if part1_legacy_pass_kind(pass) is Cleanup{
            if pass+1<3*(top as nat+1)-2{
                compact_block_bitplane(top,pass)>0 &&
                compact_block_bitplane(top,(pass+1) as u32)==compact_block_bitplane(top,pass)-1
            }else{compact_block_bitplane(top,pass)==0 && compact_block_bitplane(top,(pass+1) as u32)==0}
        }else{compact_block_bitplane(top,(pass+1) as u32)==compact_block_bitplane(top,pass)},
{
    assert(pass%3==0 || pass%3==1 || pass%3==2);
}
#[verifier::opaque]
pub(crate) open spec fn compact_block_phase(top:u16,pass:u32,width:usize,height:usize,words:Seq<u64>,
    bp:u16,state:Option<Part1LegacyBitplane>)->bool {
    let maximum=3*(top as nat+1)-2;
    top<31 && pass<=maximum && bp==compact_block_bitplane(top,pass)
        && compact_cache(width,height,words)
        && (forall|i:int|0<=i<words.len() ==> #[trigger] compact_precision_word(words[i]))
        && match state{
            None=>(pass==0 || pass%3==1)
                && (pass==0 ==> forall|i:int|0<=i<words.len() ==> !compact_coefficient(words[i]).significant)
                && (pass<maximum ==> forall|i:int|0<=i<words.len() && #[trigger] compact_coefficient(words[i]).significant
                    ==> ((words[i]>>32)&63)>bp),
            Some(state)=>pass>0 && pass%3!=1
                && compact_membership(width,height,words,state) && state.bitplane==bp
                && state.significance_propagation_complete && !state.cleanup_complete
                && state.magnitude_refinement_complete==(pass%3==0)
                && compact_before_frontier(words,state,pass%3==0),
        }
}
pub(crate) proof fn compact_phase_initial(top:u16,width:usize,height:usize,words:Seq<u64>)
    requires top<31,compact_cache(width,height,words),
        forall|i:int|0<=i<words.len() ==> #[trigger] compact_precision_word(words[i]),
        forall|i:int|0<=i<words.len() ==> !compact_coefficient(words[i]).significant,
    ensures compact_block_phase(top,0,width,height,words,top,None),
{reveal(compact_block_phase);}
pub(crate) proof fn compact_phase_prepare(top:u16,pass:u32,width:usize,height:usize,words:Seq<u64>,bp:u16,
    before:Option<Part1LegacyBitplane>,state:Part1LegacyBitplane)
    requires compact_block_phase(top,pass,width,height,words,bp,before),pass<3*(top as nat+1)-2,
        match before{None=>part1_legacy_bitplane_initial(compact_plane(width,height,words),bp)==Ok(state),Some(value)=>value==state},
    ensures compact_membership(width,height,words,state),state.bitplane==bp,
        compact_pass_order(state,part1_legacy_pass_kind(pass)),
        compact_before_frontier(words,state,part1_legacy_pass_kind(pass) is Cleanup),
{
    reveal(compact_block_phase);
    compact_block_schedule(top,pass);
    if before.is_none(){compact_initial_metadata(width,height,words,bp,state);}
}
pub(crate) proof fn compact_cleanup_tags(width:usize,height:usize,words:Seq<u64>,state:Part1LegacyBitplane)
    requires compact_membership(width,height,words,state),compact_before_frontier(words,state,true),
    ensures forall|i:int|0<=i<words.len() && #[trigger] compact_coefficient(words[i]).significant ==> ((words[i]>>32)&63)==state.bitplane,
{
    assert forall|i:int|0<=i<words.len() && #[trigger] compact_coefficient(words[i]).significant implies ((words[i]>>32)&63)==state.bitplane by{
        if state.significant_before[i]{assert(((words[i]>>32)&63)==state.bitplane);}
    }
}
pub(crate) proof fn compact_phase_after_pass(top:u16,pass:u32,width:usize,height:usize,before_words:Seq<u64>,after_words:Seq<u64>,bp:u16,
    before:Option<Part1LegacyBitplane>,ready:Part1LegacyBitplane,after:Part1LegacyBitplane)
    requires compact_block_phase(top,pass,width,height,before_words,bp,before),pass<3*(top as nat+1)-2,
        compact_membership(width,height,before_words,ready),ready.bitplane==bp,
        compact_pass_order(ready,part1_legacy_pass_kind(pass)),
        compact_membership(width,height,after_words,after),
        compact_pass_flags(ready,after,part1_legacy_pass_kind(pass),true),
        compact_before_frontier(after_words,after,!(part1_legacy_pass_kind(pass) is SignificancePropagation)),
    ensures compact_block_phase(top,(pass+1) as u32,width,height,after_words,compact_block_bitplane(top,(pass+1) as u32),
        if part1_legacy_pass_kind(pass) is Cleanup{None}else{Some(after)}),
{
    reveal(compact_block_phase);
    compact_block_schedule(top,pass);
    if part1_legacy_pass_kind(pass) is Cleanup{compact_cleanup_tags(width,height,after_words,after);}
}
pub(crate) proof fn compact_total_merge(total:crate::tier1::Tier1PassStatistics,pass:crate::tier1::Tier1PassStatistics,cells:nat,completed:u32)
    requires cells<=4096,completed<91,compact_statistics_le(total,(16*cells*completed) as nat),compact_statistics_le(pass,(16*cells) as nat),
    ensures tier1_statistics_merge(total,pass).0==Ok(()),
        compact_statistics_le(tier1_statistics_merge(total,pass).1,(16*cells*(completed+1)) as nat),
        tier1_statistics_merge(total,pass).1.coefficients_scanned==total.coefficients_scanned+pass.coefficients_scanned,
        tier1_statistics_merge(total,pass).1.coding_symbols==total.coding_symbols+pass.coding_symbols,
        tier1_statistics_merge(total,pass).1.newly_significant==total.newly_significant+pass.newly_significant,
        tier1_statistics_merge(total,pass).1.refined_coefficients==total.refined_coefficients+pass.refined_coefficients,
        tier1_statistics_merge(total,pass).1.run_mode_columns==total.run_mode_columns+pass.run_mode_columns,
{
    assert(16*cells*(completed+1)<=u32::MAX) by(nonlinear_arith)
        requires cells<=4096,completed<91;
    assert(16*cells*completed+16*cells==16*cells*(completed+1)) by(nonlinear_arith);
    let a=tier1_statistics_increment(total,0,pass.coefficients_scanned);
    assert(a.0==Ok(()));
    let b=tier1_statistics_merge_step(a,1,pass.coding_symbols);
    assert(b.0==Ok(()));
    let c=tier1_statistics_merge_step(b,2,pass.newly_significant);
    assert(c.0==Ok(()));
    let d=tier1_statistics_merge_step(c,3,pass.refined_coefficients);
    assert(d.0==Ok(()));
    let e=tier1_statistics_merge_step(d,4,pass.run_mode_columns);
    assert(e.0==Ok(()));
    assert(tier1_statistics_merge(total,pass)==e);
}
pub(crate) proof fn compact_phase_shape(top:u16,pass:u32,width:usize,height:usize,words:Seq<u64>,bp:u16,state:Option<Part1LegacyBitplane>)
    requires compact_block_phase(top,pass,width,height,words,bp,state),
    ensures compact_shape(width,height,words),compact_cache(width,height,words),bp<31,
        bp==compact_block_bitplane(top,pass),
        forall|i:int|0<=i<words.len() ==> #[trigger] compact_precision_word(words[i]),
{
    reveal(compact_block_phase);
    if pass<3*(top as nat+1)-2{compact_block_schedule(top,pass);}
}
pub(crate) proof fn compact_area_bound(width:usize,height:usize,words:Seq<u64>)
    requires compact_shape(width,height,words),
    ensures compact_stripe_bound(width,height)==16*words.len(),
{
    assert(compact_stripe_bound(width,height)==16*words.len()) by(nonlinear_arith)
        requires words.len()==width*height;
}
pub(crate) proof fn compact_pass_observed(before:Tier1DecoderState,reader:Part1MqState,kind:crate::tier1::Tier1PassKind,
    ready:Tier1DecoderState,pass:Part1LegacyPassEffect)
    requires part2_legacy_ensure_result(before,(Ok(()),ready)),part1_legacy_ensure_bitplane(before)==(Ok(()),ready),
        ready.bitplane_state.is_some(),!ready.style.segmentation_symbols,
        pass==compact_pass_model(ready.plane,ready.bitplane_state->Some_0,Part1LegacySymbols::Mq(reader),
            kind,ready.orientation,ready.style.vertical_causal_context),
    ensures part2_legacy_pass_result(before,Part1LegacySymbols::Mq(reader),kind,
        (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..ready},pass.3)),
        pass.0!=Err(crate::DecodeError::AllocationFailed) ==>
            (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..ready},pass.3)
                ==part1_legacy_decode_pass(before,Part1LegacySymbols::Mq(reader),kind),
{
    reveal(compact_pass_model);
    part2_legacy_mq_ready_contract(before,reader,kind,(Ok(()),ready));
}
#[verifier::opaque]
pub(crate) open spec fn compact_normal_suffix(initial:Part1LegacySegmentRun,passes:u32,current:Part1LegacySegmentRun,remaining:nat)->bool {
    part1_legacy_segment_run(initial,passes as nat)==part1_legacy_segment_run(current,remaining)
}
pub(crate) proof fn compact_normal_start(initial:Part1LegacySegmentRun,passes:u32)
    ensures compact_normal_suffix(initial,passes,initial,passes as nat),
{reveal(compact_normal_suffix);}
pub(crate) proof fn compact_normal_step(initial:Part1LegacySegmentRun,passes:u32,current:Part1LegacySegmentRun,remaining:nat,
    kind:crate::tier1::Tier1PassKind,pass:Part1LegacySegmentPassEffect)
    requires compact_normal_suffix(initial,passes,current,remaining),remaining>0,
        part2_legacy_pass_result(current.decoder,current.symbols,kind,pass),pass.0!=Err(crate::DecodeError::AllocationFailed),
        part1_legacy_plan(current.decoder.style,current.decoder.next_pass).kind==kind,
        (part1_legacy_plan(current.decoder.style,current.decoder.next_pass).coding_mode is Raw)==(current.symbols is Raw),
    ensures ({
        let step=part2_legacy_step_after_pass(current,kind,pass);
        match step.0{
            Err(_)=>part1_legacy_segment_finish(step)==part1_legacy_segment_finish(part1_legacy_segment_run(initial,passes as nat)),
            Ok(())=>compact_normal_suffix(initial,passes,step.1,(remaining-1) as nat),
        }
    }),
{
    reveal(compact_normal_suffix);reveal(part1_legacy_segment_step);
    part2_legacy_pass_primary_consequence(current.decoder,current.symbols,kind,pass);
    assert(part1_legacy_segment_step(current)==part2_legacy_step_after_pass(current,kind,pass));
    reveal_with_fuel(part1_legacy_segment_run,1);
}
pub(crate) proof fn compact_normal_finish(initial:Part1LegacySegmentRun,passes:u32,current:Part1LegacySegmentRun)
    requires compact_normal_suffix(initial,passes,current,0),
    ensures (Ok(current.statistics),current.decoder,current.symbols)==part1_legacy_segment_finish(part1_legacy_segment_run(initial,passes as nat)),
{
    reveal(compact_normal_suffix);reveal_with_fuel(part1_legacy_segment_run,1);
}
}
