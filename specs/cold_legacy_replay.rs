//! Input-derived legacy snapshot and fallible restoration, including partial writes.
use super::*;
verus! {
pub struct Part2LegacyCaps {pub passes:u32,pub bytes:u64,pub input:u64,pub work:u64}
pub(crate) open spec fn part2_legacy_caps(passes:u32,bytes:u64,input:u64,work:u64)->Part2LegacyCaps {Part2LegacyCaps {passes,bytes,input,work}}
pub type Part2LegacyResult=(Result<(),crate::DecodeError>,Tier1DecoderState);
pub(crate) open spec fn part2_legacy_snapshot_flags(before:Tier1DecoderState,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1LegacyFrame> {
    part2_tier1_storage_bind(part2_nested_bitplane_option_run(before.bitplane_state,crate::tier1::HtRefinementCopyRole::LegacySnapshot,true,calls),
        |_:Option<Part1LegacyBitplane>,rest|Some((Ok(part1_legacy_snapshot(before)),rest)))
}
pub(crate) open spec fn part2_legacy_snapshot_run(before:Tier1DecoderState,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1LegacyFrame> {
    part2_tier1_storage_bind(part2_nested_plane_run(before.plane,crate::tier1::HtRefinementCopyRole::LegacySnapshot,calls),
        |_:Tier1RawPlane,rest|part2_legacy_snapshot_flags(before,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_snapshot_result(before:Tier1DecoderState,result:Result<Tier1LegacyFrame,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_snapshot_run(before,calls),result)
}
pub(crate) proof fn part2_legacy_snapshot_plane_error(before:Tier1DecoderState,error:crate::DecodeError)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(before.plane,crate::tier1::HtRefinementCopyRole::LegacySnapshot,calls),Err(error)),
    ensures part2_legacy_snapshot_result(before,Err(error)),
{
    reveal(part2_legacy_snapshot_result);
    part2_tier1_storage_eta(|calls|part2_nested_plane_run(before.plane,crate::tier1::HtRefinementCopyRole::LegacySnapshot,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_nested_plane_run(before.plane,crate::tier1::HtRefinementCopyRole::LegacySnapshot,calls),
        |_:Tier1RawPlane,rest|part2_legacy_snapshot_flags(before,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_legacy_snapshot_observed(before:Tier1DecoderState,copied:Result<Option<Part1LegacyBitplane>,crate::DecodeError>)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(before.plane,crate::tier1::HtRefinementCopyRole::LegacySnapshot,calls),Ok(before.plane)),
        part2_nested_bitplane_option_result(before.bitplane_state,crate::tier1::HtRefinementCopyRole::LegacySnapshot,true,copied),
    ensures part2_legacy_snapshot_result(before,match copied{Err(error)=>Err(error),Ok(_)=>Ok(part1_legacy_snapshot(before))}),
{
    reveal(part2_legacy_snapshot_result);
    let role=crate::tier1::HtRefinementCopyRole::LegacySnapshot;
    let value=match copied{Err(error)=>Err(error),Ok(_)=>Ok(part1_legacy_snapshot(before))};
    part2_nested_option_frames(before.bitplane_state,|source,rest|part2_nested_bitplane_run(source,role,true,rest),copied);
    if copied.is_ok(){part2_tier1_storage_pure(Ok(part1_legacy_snapshot(before)));}
    part2_tier1_storage_bind_frame(|calls|part2_nested_bitplane_option_run(before.bitplane_state,role,true,calls),
        |_:Option<Part1LegacyBitplane>,rest|Some((Ok(part1_legacy_snapshot(before)),rest)),copied,value);
    part2_tier1_storage_eta(|calls|part2_legacy_snapshot_flags(before,calls),value);
    part2_tier1_storage_eta(|calls|part2_nested_plane_run(before.plane,role,calls),Ok(before.plane));
    part2_tier1_storage_bind_frame(|calls|part2_nested_plane_run(before.plane,role,calls),|_:Tier1RawPlane,rest|part2_legacy_snapshot_flags(before,rest),Ok(before.plane),value);
}
pub(crate) proof fn part2_legacy_snapshot_normal(before:Tier1DecoderState)
    ensures part2_legacy_snapshot_result(before,Ok(part1_legacy_snapshot(before))),
{
    let role=crate::tier1::HtRefinementCopyRole::LegacySnapshot;
    part2_nested_plane_observed(before.plane,role,Ok(()));
    part2_nested_bitplane_option_normal(before.bitplane_state,role,true);
    part2_legacy_snapshot_observed(before,Ok(before.bitplane_state));
}
pub(crate) proof fn part2_legacy_snapshot_frames(before:Tier1DecoderState,result:Result<Tier1LegacyFrame,crate::DecodeError>)
    requires part2_legacy_snapshot_result(before,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_snapshot_run(before,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1LegacyFrame>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_snapshot_run(before,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_legacy_snapshot_result);part2_tier1_storage_eta(|calls|part2_legacy_snapshot_run(before,calls),result);}
pub(crate) open spec fn part2_legacy_restore_partial(before:Tier1DecoderState,source:Tier1LegacyFrame)->Tier1DecoderState {
    Tier1DecoderState {plane:source.plane,next_pass:source.next_pass,bitplane:source.bitplane,..before}
}
pub(crate) open spec fn part2_legacy_restore_flags(before:Tier1DecoderState,source:Tier1LegacyFrame,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    part2_tier1_storage_resume(part2_nested_bitplane_option_run(source.bitplane_state,crate::tier1::HtRefinementCopyRole::LegacyRestore,true,calls),
        |copied:Result<Option<Part1LegacyBitplane>,crate::DecodeError>,rest|Some((Ok(match copied{
            Err(error)=>(Err(error),part2_legacy_restore_partial(before,source)),Ok(_)=>(Ok(()),part1_legacy_restore(before,source))
        }),rest)))
}
pub(crate) open spec fn part2_legacy_restore_after_plane(before:Tier1DecoderState,source:Tier1LegacyFrame,copied:Result<Tier1RawPlane,crate::DecodeError>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    match copied{Err(error)=>Some((Ok((Err(error),before)),calls)),Ok(_)=>part2_legacy_restore_flags(before,source,calls)}
}
pub(crate) open spec fn part2_legacy_restore_run(before:Tier1DecoderState,source:Tier1LegacyFrame,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    part2_tier1_storage_resume(part2_nested_plane_run(source.plane,crate::tier1::HtRefinementCopyRole::LegacyRestore,calls),
        |copied:Result<Tier1RawPlane,crate::DecodeError>,rest|part2_legacy_restore_after_plane(before,source,copied,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_restore_result(before:Tier1DecoderState,source:Tier1LegacyFrame,result:Part2LegacyResult)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_restore_run(before,source,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_restore_plane_error(before:Tier1DecoderState,source:Tier1LegacyFrame,error:crate::DecodeError)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(source.plane,crate::tier1::HtRefinementCopyRole::LegacyRestore,calls),Err(error)),
    ensures part2_legacy_restore_result(before,source,(Err(error),before)),
{
    reveal(part2_legacy_restore_result);
    part2_tier1_storage_eta(|calls|part2_nested_plane_run(source.plane,crate::tier1::HtRefinementCopyRole::LegacyRestore,calls),Err(error));
    part2_tier1_storage_pure::<Part2LegacyResult>(Ok((Err(error),before)));
    part2_tier1_resume_frame(|calls|part2_nested_plane_run(source.plane,crate::tier1::HtRefinementCopyRole::LegacyRestore,calls),
        |copied:Result<Tier1RawPlane,crate::DecodeError>,rest|part2_legacy_restore_after_plane(before,source,copied,rest),Err(error),Ok((Err(error),before)));
}
pub(crate) proof fn part2_legacy_restore_observed(before:Tier1DecoderState,source:Tier1LegacyFrame,copied:Result<Option<Part1LegacyBitplane>,crate::DecodeError>)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(source.plane,crate::tier1::HtRefinementCopyRole::LegacyRestore,calls),Ok(source.plane)),
        part2_nested_bitplane_option_result(source.bitplane_state,crate::tier1::HtRefinementCopyRole::LegacyRestore,true,copied),
    ensures part2_legacy_restore_result(before,source,match copied{
        Err(error)=>(Err(error),part2_legacy_restore_partial(before,source)),Ok(_)=>(Ok(()),part1_legacy_restore(before,source))}),
{
    reveal(part2_legacy_restore_result);
    let role=crate::tier1::HtRefinementCopyRole::LegacyRestore;
    let value=match copied{Err(error)=>(Err(error),part2_legacy_restore_partial(before,source)),Ok(_)=>(Ok(()),part1_legacy_restore(before,source))};
    part2_nested_option_frames(source.bitplane_state,|value,rest|part2_nested_bitplane_run(value,role,true,rest),copied);
    part2_tier1_storage_pure(Ok(value));
    part2_tier1_resume_frame(|calls|part2_nested_bitplane_option_run(source.bitplane_state,role,true,calls),
        |copied:Result<Option<Part1LegacyBitplane>,crate::DecodeError>,rest|Some((Ok(match copied{
            Err(error)=>(Err(error),part2_legacy_restore_partial(before,source)),Ok(_)=>(Ok(()),part1_legacy_restore(before,source))
        }),rest)),copied,Ok(value));
    part2_tier1_storage_eta(|calls|part2_legacy_restore_flags(before,source,calls),Ok(value));
    part2_tier1_storage_eta(|calls|part2_nested_plane_run(source.plane,role,calls),Ok(source.plane));
    part2_tier1_resume_frame(|calls|part2_nested_plane_run(source.plane,role,calls),
        |copied:Result<Tier1RawPlane,crate::DecodeError>,rest|part2_legacy_restore_after_plane(before,source,copied,rest),Ok(source.plane),Ok(value));
}
pub(crate) proof fn part2_legacy_restore_normal(before:Tier1DecoderState,source:Tier1LegacyFrame)
    ensures part2_legacy_restore_result(before,source,(Ok(()),part1_legacy_restore(before,source))),
{
    let role=crate::tier1::HtRefinementCopyRole::LegacyRestore;
    part2_nested_plane_observed(source.plane,role,Ok(()));part2_nested_bitplane_option_normal(source.bitplane_state,role,true);
    part2_legacy_restore_observed(before,source,Ok(source.bitplane_state));
}
pub(crate) proof fn part2_legacy_restore_frames(before:Tier1DecoderState,source:Tier1LegacyFrame,result:Part2LegacyResult)
    requires part2_legacy_restore_result(before,source,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_restore_run(before,source,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_restore_run(before,source,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_restore_result);part2_tier1_storage_eta(|calls|part2_legacy_restore_run(before,source,calls),Ok(result));}
pub(crate) open spec fn part2_legacy_replay_clear(before:Tier1DecoderState)->Tier1DecoderState {Tier1DecoderState {legacy_segment:None,..before}}
pub(crate) open spec fn part2_legacy_replay_source(before:Tier1DecoderState)->Tier1LegacyFrame {
    match before.legacy_segment{Some(source)=>source,None=>part1_legacy_snapshot(part2_legacy_replay_clear(before))}
}
pub(crate) open spec fn part2_legacy_replay_finish(source:Tier1LegacyFrame,caps:Part2LegacyCaps,restored:Part2LegacyResult)->Part2LegacyResult {
    match restored.0{Err(_)=>restored,Ok(())=>part1_legacy_contribution_finish(
        part1_legacy_segment(restored.1,source.input,source.passes,caps.passes,caps.bytes,caps.input,caps.work),source)}
}
pub(crate) open spec fn part2_legacy_replay_after_source(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,source:Tier1LegacyFrame,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    let appended=part1_legacy_append(source,input,replay);
    part2_tier1_storage_bind(part2_legacy_restore_run(part2_legacy_replay_clear(before),appended,calls),
        |restored:Part2LegacyResult,rest|Some((Ok(part2_legacy_replay_finish(appended,caps,restored)),rest)))
}
pub(crate) open spec fn part2_legacy_replay_run(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    match before.legacy_segment{
        Some(source)=>part2_legacy_replay_after_source(before,input,replay,caps,source,calls),
        None=>part2_tier1_storage_resume(part2_legacy_snapshot_run(part2_legacy_replay_clear(before),calls),
            |copied:Result<Tier1LegacyFrame,crate::DecodeError>,rest|match copied{
                Err(error)=>Some((Ok((Err(error),part2_legacy_replay_clear(before))),rest)),
                Ok(source)=>part2_legacy_replay_after_source(before,input,replay,caps,source,rest),
            }),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_replay_result(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,result:Part2LegacyResult)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_replay_run(before,input,replay,caps,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_replay_bind(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,result:Part2LegacyResult)
    requires part2_legacy_snapshot_result(part2_legacy_replay_clear(before),Ok(part2_legacy_replay_source(before))) || before.legacy_segment.is_some(),
        part2_tier1_storage_framed(|calls|part2_legacy_replay_after_source(before,input,replay,caps,part2_legacy_replay_source(before),calls),Ok(result)),
    ensures part2_legacy_replay_result(before,input,replay,caps,result),
{
    reveal(part2_legacy_replay_result);
    if before.legacy_segment.is_none(){
        let copied=Ok(part2_legacy_replay_source(before));
        part2_legacy_snapshot_frames(part2_legacy_replay_clear(before),copied);
        part2_tier1_storage_eta(|calls|part2_legacy_replay_after_source(before,input,replay,caps,part2_legacy_replay_source(before),calls),Ok(result));
        part2_tier1_resume_frame(|calls|part2_legacy_snapshot_run(part2_legacy_replay_clear(before),calls),
            |copied:Result<Tier1LegacyFrame,crate::DecodeError>,rest|match copied{
                Err(error)=>Some((Ok((Err(error),part2_legacy_replay_clear(before))),rest)),
                Ok(source)=>part2_legacy_replay_after_source(before,input,replay,caps,source,rest),
            },copied,Ok(result));
    }else{part2_tier1_storage_eta(|calls|part2_legacy_replay_after_source(before,input,replay,caps,part2_legacy_replay_source(before),calls),Ok(result));}
}
pub(crate) proof fn part2_legacy_replay_snapshot_error(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,error:crate::DecodeError)
    requires before.legacy_segment.is_none(),part2_legacy_snapshot_result(part2_legacy_replay_clear(before),Err(error)),
    ensures part2_legacy_replay_result(before,input,replay,caps,(Err(error),part2_legacy_replay_clear(before))),
{
    reveal(part2_legacy_replay_result);
    part2_legacy_snapshot_frames(part2_legacy_replay_clear(before),Err(error));
    part2_tier1_storage_pure::<Part2LegacyResult>(Ok((Err(error),part2_legacy_replay_clear(before))));
    part2_tier1_resume_frame(|calls|part2_legacy_snapshot_run(part2_legacy_replay_clear(before),calls),
        |copied:Result<Tier1LegacyFrame,crate::DecodeError>,rest|match copied{
            Err(error)=>Some((Ok((Err(error),part2_legacy_replay_clear(before))),rest)),
            Ok(source)=>part2_legacy_replay_after_source(before,input,replay,caps,source,rest),
        },Err(error),Ok((Err(error),part2_legacy_replay_clear(before))));
}
pub(crate) proof fn part2_legacy_replay_restored(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,restored:Part2LegacyResult)
    requires part2_legacy_snapshot_result(part2_legacy_replay_clear(before),Ok(part2_legacy_replay_source(before))) || before.legacy_segment.is_some(),
        part2_legacy_restore_result(part2_legacy_replay_clear(before),part1_legacy_append(part2_legacy_replay_source(before),input,replay),restored),
    ensures part2_legacy_replay_result(before,input,replay,caps,part2_legacy_replay_finish(part1_legacy_append(part2_legacy_replay_source(before),input,replay),caps,restored)),
{
    let source=part1_legacy_append(part2_legacy_replay_source(before),input,replay);
    let result=part2_legacy_replay_finish(source,caps,restored);
    part2_legacy_restore_frames(part2_legacy_replay_clear(before),source,restored);
    part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_restore_run(part2_legacy_replay_clear(before),source,calls),
        |restored:Part2LegacyResult,rest|Some((Ok(part2_legacy_replay_finish(source,caps,restored)),rest)),Ok(restored),Ok(result));
    part2_legacy_replay_bind(before,input,replay,caps,result);
}
pub(crate) proof fn part2_legacy_replay_normal(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps)
    ensures part2_legacy_replay_result(before,input,replay,caps,part1_legacy_replay(before,input,replay,caps.passes,caps.bytes,caps.input,caps.work)),
{
    reveal(part1_legacy_replay);
    let source=part1_legacy_append(part2_legacy_replay_source(before),input,replay);
    if before.legacy_segment.is_none(){part2_legacy_snapshot_normal(part2_legacy_replay_clear(before));}
    part2_legacy_restore_normal(part2_legacy_replay_clear(before),source);
    part2_legacy_replay_restored(before,input,replay,caps,(Ok(()),part1_legacy_restore(part2_legacy_replay_clear(before),source)));
}
pub(crate) proof fn part2_legacy_replay_frames(before:Tier1DecoderState,input:Seq<u8>,replay:u32,caps:Part2LegacyCaps,result:Part2LegacyResult)
    requires part2_legacy_replay_result(before,input,replay,caps,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_replay_run(before,input,replay,caps,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_replay_run(before,input,replay,caps,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_replay_result);part2_tier1_storage_eta(|calls|part2_legacy_replay_run(before,input,replay,caps,calls),Ok(result));}
pub(crate) open spec fn part2_legacy_contribution_after_admission(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps,
    admitted:(Result<(u32,u32,u32),crate::DecodeError>,Tier1DecoderState),calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    match admitted.0{
        Err(error)=>Some((Ok((Err(error),admitted.1)),calls)),
        Ok((replay,next,last))=>if admitted.1.legacy_segment.is_none() && (next==admitted.1.maximum_passes || part1_legacy_plan(admitted.1.style,last).terminates_segment){
            Some((Ok(part1_legacy_contribution(before,input,passes,caps.passes,caps.bytes,caps.input,caps.work)),calls))
        }else{part2_legacy_replay_run(admitted.1,input,replay,caps,calls)},
    }
}
pub(crate) open spec fn part2_legacy_contribution_run(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    part2_legacy_contribution_after_admission(before,input,passes,caps,part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work),calls)
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_contribution_result(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps,result:Part2LegacyResult)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_contribution_run(before,input,passes,caps,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_contribution_pure(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps)
    requires match part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work){
        (Ok((_,next,last)),state)=>state.legacy_segment.is_none() && (next==state.maximum_passes || part1_legacy_plan(state.style,last).terminates_segment),
        _=>true,
    },
    ensures part2_legacy_contribution_result(before,input,passes,caps,part1_legacy_contribution(before,input,passes,caps.passes,caps.bytes,caps.input,caps.work)),
{reveal(part2_legacy_contribution_result);reveal(part1_legacy_contribution);part2_tier1_storage_pure(Ok(part1_legacy_contribution(before,input,passes,caps.passes,caps.bytes,caps.input,caps.work)));}
pub(crate) proof fn part2_legacy_contribution_observed(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps,replay:u32,next:u32,last:u32,result:Part2LegacyResult)
    requires part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work).0==Ok((replay,next,last)),
        ! (part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work).1.legacy_segment.is_none()
            && (next==part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work).1.maximum_passes
                || part1_legacy_plan(part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work).1.style,last).terminates_segment)),
        part2_legacy_replay_result(part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work).1,input,replay,caps,result),
    ensures part2_legacy_contribution_result(before,input,passes,caps,result),
{
    reveal(part2_legacy_contribution_result);
    part2_legacy_replay_frames(part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work).1,input,replay,caps,result);
}
pub(crate) proof fn part2_legacy_contribution_normal(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps)
    ensures part2_legacy_contribution_result(before,input,passes,caps,part1_legacy_contribution(before,input,passes,caps.passes,caps.bytes,caps.input,caps.work)),
{
    reveal(part1_legacy_contribution);
    let admitted=part1_legacy_contribution_admission(before,input,passes,caps.bytes,caps.work);
    match admitted.0{
        Err(_)=>{part2_legacy_contribution_pure(before,input,passes,caps);},
        Ok((replay,next,last))=>if admitted.1.legacy_segment.is_none() && (next==admitted.1.maximum_passes || part1_legacy_plan(admitted.1.style,last).terminates_segment){
            part2_legacy_contribution_pure(before,input,passes,caps);
        }else{
            part2_legacy_replay_normal(admitted.1,input,replay,caps);
            part2_legacy_contribution_observed(before,input,passes,caps,replay,next,last,part1_legacy_replay(admitted.1,input,replay,caps.passes,caps.bytes,caps.input,caps.work));
        },
    }
}
pub(crate) proof fn part2_legacy_contribution_frames(before:Tier1DecoderState,input:Seq<u8>,passes:u8,caps:Part2LegacyCaps,result:Part2LegacyResult)
    requires part2_legacy_contribution_result(before,input,passes,caps,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_contribution_run(before,input,passes,caps,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_contribution_run(before,input,passes,caps,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_contribution_result);part2_tier1_storage_eta(|calls|part2_legacy_contribution_run(before,input,passes,caps,calls),Ok(result));}
}
