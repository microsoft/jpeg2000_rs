//! Checked native-store/model-frame and error-exit cutpoints for the compact loop.
use super::*;
verus! {
pub(crate) open spec fn compact_substitute_plane(physical:Tier1DecoderState,plane:Tier1RawPlane)->Tier1DecoderState {
    Tier1DecoderState {plane,..physical}
}
#[verifier::opaque]
pub(crate) open spec fn compact_physical_frame(initial:Tier1DecoderState,current:Tier1DecoderState)->bool {
    current==(Tier1DecoderState {
        next_pass:current.next_pass,bitplane:current.bitplane,bitplane_state:current.bitplane_state,..initial
    })
}
pub(crate) proof fn compact_physical_start(initial:Tier1DecoderState)
    ensures compact_physical_frame(initial,initial),
{reveal(compact_physical_frame);}
pub(crate) proof fn compact_physical_updated(initial:Tier1DecoderState,before:Tier1DecoderState,after:Tier1DecoderState)
    requires compact_physical_frame(initial,before),
        after==(Tier1DecoderState {next_pass:after.next_pass,bitplane:after.bitplane,bitplane_state:after.bitplane_state,..before}),
    ensures compact_physical_frame(initial,after),
{reveal(compact_physical_frame);}
pub(crate) proof fn compact_physical_fields(initial:Tier1DecoderState,current:Tier1DecoderState)
    requires compact_physical_frame(initial,current),
    ensures current.plane==initial.plane,current.style==initial.style,current.orientation==initial.orientation,
        current.maximum_passes==initial.maximum_passes,
{reveal(compact_physical_frame);}
pub(crate) proof fn compact_pass_store_frame(before:Tier1DecoderState,after:Tier1DecoderState,old_plane:Tier1RawPlane,new_plane:Tier1RawPlane)
    requires after==(Tier1DecoderState {bitplane_state:after.bitplane_state,..before}),
    ensures after.plane==before.plane,
        compact_substitute_plane(after,new_plane)==(Tier1DecoderState {
            plane:new_plane,bitplane_state:after.bitplane_state,..compact_substitute_plane(before,old_plane)
        }),
{}
#[verifier::opaque]
pub(crate) open spec fn compact_advance_frame(before:Tier1DecoderState,after:Tier1DecoderState,kind:crate::tier1::Tier1PassKind)->bool {
    part1_legacy_advance(before,kind)==(Ok(()),after)
}
pub(crate) proof fn compact_advance_fields(before:Tier1DecoderState,after:Tier1DecoderState,kind:crate::tier1::Tier1PassKind)
    requires compact_advance_frame(before,after,kind),
    ensures after==(Tier1DecoderState {next_pass:after.next_pass,bitplane:after.bitplane,bitplane_state:after.bitplane_state,..before}),
{reveal(compact_advance_frame);}
pub(crate) proof fn compact_success_store_frame(before:Part1LegacySegmentRun,kind:crate::tier1::Tier1PassKind,
    pass:Part1LegacySegmentPassEffect,statistics:crate::tier1::Tier1PassStatistics,
    physical:Tier1DecoderState,advanced:Tier1DecoderState,plane:Tier1RawPlane,total:crate::tier1::Tier1PassStatistics,
    after:Part1LegacySegmentRun)
    requires pass.0==Ok(statistics),pass.1==compact_substitute_plane(physical,plane),
        !physical.style.reset_contexts,
        tier1_statistics_merge(before.statistics,statistics)==(Ok(()),total),
        compact_advance_frame(physical,advanced,kind),
        after==(Part1LegacySegmentRun {decoder:compact_substitute_plane(advanced,plane),symbols:pass.2,statistics:total}),
    ensures part2_legacy_step_after_pass(before,kind,pass)==(Ok(()),after),advanced.plane==physical.plane,
{
    reveal(compact_advance_frame);
    assert(part1_legacy_advance(compact_substitute_plane(physical,plane),kind)
        ==(Ok(()),compact_substitute_plane(advanced,plane)));
}
#[verifier::opaque]
pub(crate) open spec fn compact_loop_progress(initial:Part1LegacySegmentRun,passes:u32,prefix:Seq<Part2Tier1StorageEvent>,
    current:Part1LegacySegmentRun,remaining:nat)->bool {
    compact_normal_suffix(initial,passes,current,remaining) && compact_cold_suffix(initial,passes,prefix,current,remaining)
}
pub(crate) proof fn compact_progress_start(initial:Part1LegacySegmentRun,passes:u32)
    ensures compact_loop_progress(initial,passes,Seq::empty(),initial,passes as nat),
{
    reveal(compact_loop_progress);
    compact_normal_start(initial,passes);compact_cold_start(initial,passes);
}
pub(crate) proof fn compact_allocation_error_exit(initial:Part1LegacySegmentRun,passes:u32,current:Part1LegacySegmentRun,
    remaining:nat,prefix:Seq<Part2Tier1StorageEvent>,kind:crate::tier1::Tier1PassKind,error:crate::DecodeError)
    requires compact_loop_progress(initial,passes,prefix,current,remaining),remaining>0,
        error==crate::DecodeError::AllocationFailed,current.symbols is Mq,
        part2_legacy_ensure_result(current.decoder,(Err(error),current.decoder)),
        part1_legacy_plan(current.decoder.style,current.decoder.next_pass).kind==kind,
        part1_legacy_plan(current.decoder.style,current.decoder.next_pass).coding_mode is Mq,
    ensures part2_legacy_inner_body_result(initial,passes,(Err(error),current.decoder,current.symbols)),
{
    reveal(compact_loop_progress);
    part2_legacy_mq_ready_contract(current.decoder,current.symbols->Mq_0,kind,(Err(error),current.decoder));
    let pass=(Err(error),current.decoder,current.symbols);
    part2_legacy_inner_step_observed(current,kind,pass);
    let expected=part2_legacy_step_after_pass(current,kind,pass);
    compact_cold_step(initial,passes,current,remaining,prefix,expected);
}
pub(crate) proof fn compact_pass_error_exit(initial:Part1LegacySegmentRun,passes:u32,current:Part1LegacySegmentRun,remaining:nat,
    prefix:Seq<Part2Tier1StorageEvent>,kind:crate::tier1::Tier1PassKind,pass:Part1LegacySegmentPassEffect)
    requires compact_loop_progress(initial,passes,prefix,current,remaining),remaining>0,pass.0.is_err(),
        part2_legacy_pass_result(current.decoder,current.symbols,kind,pass),
        part1_legacy_plan(current.decoder.style,current.decoder.next_pass).kind==kind,
        (part1_legacy_plan(current.decoder.style,current.decoder.next_pass).coding_mode is Raw)==(current.symbols is Raw),
    ensures part2_legacy_inner_body_result(initial,passes,pass),
        pass.0!=Err(crate::DecodeError::AllocationFailed) ==>
            pass==part1_legacy_segment_finish(part1_legacy_segment_run(initial,passes as nat)),
{
    reveal(compact_loop_progress);
    part2_legacy_inner_step_observed(current,kind,pass);
    let expected=part2_legacy_step_after_pass(current,kind,pass);
    if pass.0!=Err(crate::DecodeError::AllocationFailed){compact_normal_step(initial,passes,current,remaining,kind,pass);}
    compact_cold_step(initial,passes,current,remaining,prefix,expected);
    match pass.0{Err(_)=>{},Ok(_)=>{}}
}
pub(crate) proof fn compact_progress_continue(initial:Part1LegacySegmentRun,passes:u32,current:Part1LegacySegmentRun,remaining:nat,
    prefix:Seq<Part2Tier1StorageEvent>,kind:crate::tier1::Tier1PassKind,pass:Part1LegacySegmentPassEffect,
    after:Part1LegacySegmentRun)->(joined:Seq<Part2Tier1StorageEvent>)
    requires compact_loop_progress(initial,passes,prefix,current,remaining),remaining>0,pass.0.is_ok(),
        part2_legacy_pass_result(current.decoder,current.symbols,kind,pass),
        part1_legacy_plan(current.decoder.style,current.decoder.next_pass).kind==kind,
        (part1_legacy_plan(current.decoder.style,current.decoder.next_pass).coding_mode is Raw)==(current.symbols is Raw),
        part2_legacy_step_after_pass(current,kind,pass)==(Ok(()),after),
    ensures compact_loop_progress(initial,passes,joined,after,(remaining-1) as nat),
{
    reveal(compact_loop_progress);
    part2_legacy_inner_step_observed(current,kind,pass);
    compact_normal_step(initial,passes,current,remaining,kind,pass);
    compact_cold_step(initial,passes,current,remaining,prefix,(Ok(()),after))
}
pub(crate) proof fn compact_progress_finish(initial:Part1LegacySegmentRun,passes:u32,prefix:Seq<Part2Tier1StorageEvent>,current:Part1LegacySegmentRun)
    requires compact_loop_progress(initial,passes,prefix,current,0),
    ensures part2_legacy_inner_body_result(initial,passes,(Ok(current.statistics),current.decoder,current.symbols)),
        (Ok(current.statistics),current.decoder,current.symbols)==part1_legacy_segment_finish(part1_legacy_segment_run(initial,passes as nat)),
{
    reveal(compact_loop_progress);
    compact_normal_finish(initial,passes,current);compact_cold_finish(initial,passes,prefix,current);
}
}
