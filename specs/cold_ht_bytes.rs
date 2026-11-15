//! Actual fresh refinement-byte owner copies, not retained-buffer growth.
use super::*;
verus! {
#[verifier::opaque]
pub(crate) open spec fn part2_ht_bytes_run(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<u8>> {
    if source.len()==0{Some((Ok(source),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::RefinementBytes {role:actual,source:before,elements,succeeded}=>
            if actual!=role || before!=source || elements!=source.len(){None}else{
                Some((if succeeded{Ok(source)}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_bytes_result(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,result:Result<Seq<u8>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_bytes_run(source,role,calls),result)
}
pub(crate) proof fn part2_ht_bytes_observed(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (source.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_ht_bytes_result(source,role,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_ht_bytes_result);reveal(part2_ht_bytes_run);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    let prefix=if source.len()==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::RefinementBytes {role,source,elements:source.len(),succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_ht_bytes_run(source,role,prefix+tail)==Some((value,tail)) by{
        if source.len()==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_ht_bytes_run(source,role,calls),prefix,value));
}
pub(crate) proof fn part2_ht_bytes_normal(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_ht_bytes_result(source,role,Ok(source)),
{part2_ht_bytes_observed(source,role,Ok(()));}
pub(crate) proof fn part2_ht_bytes_frames(source:Seq<u8>,role:crate::tier1::HtRefinementCopyRole,result:Result<Seq<u8>,crate::DecodeError>)
    requires part2_ht_bytes_result(source,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_bytes_run(source,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Seq<u8>>|
            (forall|calls| #[trigger] other(calls)==part2_ht_bytes_run(source,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_ht_bytes_result);part2_tier1_storage_eta(|calls|part2_ht_bytes_run(source,role,calls),result);}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_after_cleanup(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_ht_bytes_run(before.ht_refinement_data,role,calls),|_:Seq<u8>,rest|Some((Ok(before),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_after_primary(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_nested_bitplane_option_run(before.bitplane_state,role,false,calls),
        |_:Option<Part1LegacyBitplane>,rest|part2_ht_duplicate_after_bitplane(before,role,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_after_bitplane(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_nested_legacy_option_run(before.legacy_segment,role,calls),
        |_:Option<Tier1LegacyFrame>,rest|part2_ht_duplicate_after_legacy(before,role,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_after_legacy(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_decoder_cleanup_run(before.ht_cleanup_plane,role,calls),
        |_:Option<Tier1RawPlane>,rest|part2_ht_duplicate_after_cleanup(before,role,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_run(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_decoder_plane_run(before.plane,role,false,calls),
        |_:Tier1RawPlane,rest|part2_ht_duplicate_after_primary(before,role,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_ht_duplicate_result(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1DecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_ht_duplicate_run(before,role,calls),result)
}
pub(crate) proof fn part2_ht_duplicate_observed(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,result:Result<Seq<u8>,crate::DecodeError>)
    requires part2_ht_bytes_result(before.ht_refinement_data,role,result),
        part2_decoder_plane_result(before.plane,role,false,Ok(before.plane)),
        part2_nested_bitplane_option_result(before.bitplane_state,role,false,Ok(before.bitplane_state)),
        part2_nested_legacy_option_result(before.legacy_segment,role,Ok(before.legacy_segment)),
        part2_decoder_cleanup_result(before.ht_cleanup_plane,role,Ok(before.ht_cleanup_plane)),
    ensures part2_ht_duplicate_result(before,role,match result{Err(error)=>Err(error),Ok(_)=>Ok(before)}),
{
    reveal(part2_ht_duplicate_after_legacy);reveal(part2_ht_duplicate_after_cleanup);
    let value=match result{Err(error)=>Err(error),Ok(_)=>Ok(before)};
    part2_ht_bytes_frames(before.ht_refinement_data,role,result);
    if result.is_ok(){part2_tier1_storage_pure(Ok(before));}
    part2_tier1_storage_bind_frame(|calls|part2_ht_bytes_run(before.ht_refinement_data,role,calls),|_:Seq<u8>,rest|Some((Ok(before),rest)),result,value);
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_cleanup(before,role,calls),value);
    part2_decoder_cleanup_frames(before.ht_cleanup_plane,role,Ok(before.ht_cleanup_plane));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_cleanup_run(before.ht_cleanup_plane,role,calls),
        |_:Option<Tier1RawPlane>,rest|part2_ht_duplicate_after_cleanup(before,role,rest),Ok(before.ht_cleanup_plane),value);
    part2_ht_duplicate_nested_join(before,role,value);
}
pub(crate) proof fn part2_ht_duplicate_nested_join(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,value:Result<Tier1DecoderState,crate::DecodeError>)
    requires part2_decoder_plane_result(before.plane,role,false,Ok(before.plane)),
        part2_nested_bitplane_option_result(before.bitplane_state,role,false,Ok(before.bitplane_state)),
        part2_nested_legacy_option_result(before.legacy_segment,role,Ok(before.legacy_segment)),
        part2_tier1_storage_framed(|calls|part2_ht_duplicate_after_legacy(before,role,calls),value),
    ensures part2_ht_duplicate_result(before,role,value),
{
    reveal(part2_ht_duplicate_result);reveal(part2_ht_duplicate_run);reveal(part2_ht_duplicate_after_primary);reveal(part2_ht_duplicate_after_bitplane);
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_legacy(before,role,calls),value);
    part2_nested_option_frames(before.legacy_segment,|source,rest|part2_nested_legacy_run(source,role,rest),Ok(before.legacy_segment));
    part2_tier1_storage_bind_frame(|calls|part2_nested_legacy_option_run(before.legacy_segment,role,calls),
        |_:Option<Tier1LegacyFrame>,rest|part2_ht_duplicate_after_legacy(before,role,rest),Ok(before.legacy_segment),value);
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_bitplane(before,role,calls),value);
    part2_nested_option_frames(before.bitplane_state,|source,rest|part2_nested_bitplane_run(source,role,false,rest),Ok(before.bitplane_state));
    part2_tier1_storage_bind_frame(|calls|part2_nested_bitplane_option_run(before.bitplane_state,role,false,calls),
        |_:Option<Part1LegacyBitplane>,rest|part2_ht_duplicate_after_bitplane(before,role,rest),Ok(before.bitplane_state),value);
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_primary(before,role,calls),value);
    part2_decoder_plane_frames(before.plane,role,false,Ok(before.plane));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_plane_run(before.plane,role,false,calls),
        |_:Tier1RawPlane,rest|part2_ht_duplicate_after_primary(before,role,rest),Ok(before.plane),value);
}
pub(crate) proof fn part2_ht_duplicate_bitplane_error(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,error:crate::DecodeError)
    requires part2_decoder_plane_result(before.plane,role,false,Ok(before.plane)),
        part2_nested_bitplane_option_result(before.bitplane_state,role,false,Err(error)),
    ensures part2_ht_duplicate_result(before,role,Err(error)),
{
    reveal(part2_ht_duplicate_result);reveal(part2_ht_duplicate_run);reveal(part2_ht_duplicate_after_primary);
    part2_nested_option_frames(before.bitplane_state,|source,rest|part2_nested_bitplane_run(source,role,false,rest),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_nested_bitplane_option_run(before.bitplane_state,role,false,calls),
        |_:Option<Part1LegacyBitplane>,rest|part2_ht_duplicate_after_bitplane(before,role,rest),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_primary(before,role,calls),Err(error));
    part2_decoder_plane_frames(before.plane,role,false,Ok(before.plane));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_plane_run(before.plane,role,false,calls),
        |_:Tier1RawPlane,rest|part2_ht_duplicate_after_primary(before,role,rest),Ok(before.plane),Err(error));
}
pub(crate) proof fn part2_ht_duplicate_legacy_error(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,error:crate::DecodeError)
    requires part2_decoder_plane_result(before.plane,role,false,Ok(before.plane)),
        part2_nested_bitplane_option_result(before.bitplane_state,role,false,Ok(before.bitplane_state)),
        part2_nested_legacy_option_result(before.legacy_segment,role,Err(error)),
    ensures part2_ht_duplicate_result(before,role,Err(error)),
{
    reveal(part2_ht_duplicate_result);reveal(part2_ht_duplicate_run);reveal(part2_ht_duplicate_after_primary);reveal(part2_ht_duplicate_after_bitplane);
    part2_nested_option_frames(before.legacy_segment,|source,rest|part2_nested_legacy_run(source,role,rest),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_nested_legacy_option_run(before.legacy_segment,role,calls),
        |_:Option<Tier1LegacyFrame>,rest|part2_ht_duplicate_after_legacy(before,role,rest),Err(error),Err(error));
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_bitplane(before,role,calls),Err(error));
    part2_nested_option_frames(before.bitplane_state,|source,rest|part2_nested_bitplane_run(source,role,false,rest),Ok(before.bitplane_state));
    part2_tier1_storage_bind_frame(|calls|part2_nested_bitplane_option_run(before.bitplane_state,role,false,calls),
        |_:Option<Part1LegacyBitplane>,rest|part2_ht_duplicate_after_bitplane(before,role,rest),Ok(before.bitplane_state),Err(error));
    part2_tier1_storage_eta(|calls|part2_ht_duplicate_after_primary(before,role,calls),Err(error));
    part2_decoder_plane_frames(before.plane,role,false,Ok(before.plane));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_plane_run(before.plane,role,false,calls),
        |_:Tier1RawPlane,rest|part2_ht_duplicate_after_primary(before,role,rest),Ok(before.plane),Err(error));
}
pub(crate) proof fn part2_ht_duplicate_primary_error(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,error:crate::DecodeError)
    requires part2_decoder_plane_result(before.plane,role,false,Err(error)),
    ensures part2_ht_duplicate_result(before,role,Err(error)),
{
    reveal(part2_ht_duplicate_result);reveal(part2_ht_duplicate_run);
    part2_decoder_plane_frames(before.plane,role,false,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_plane_run(before.plane,role,false,calls),
        |_:Tier1RawPlane,rest|part2_ht_duplicate_after_primary(before,role,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_ht_duplicate_cleanup_error(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,error:crate::DecodeError)
    requires part2_decoder_plane_result(before.plane,role,false,Ok(before.plane)),
        part2_nested_bitplane_option_result(before.bitplane_state,role,false,Ok(before.bitplane_state)),
        part2_nested_legacy_option_result(before.legacy_segment,role,Ok(before.legacy_segment)),
        part2_decoder_cleanup_result(before.ht_cleanup_plane,role,Err(error)),
    ensures part2_ht_duplicate_result(before,role,Err(error)),
{
    reveal(part2_ht_duplicate_after_legacy);
    part2_decoder_cleanup_frames(before.ht_cleanup_plane,role,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_decoder_cleanup_run(before.ht_cleanup_plane,role,calls),
        |_:Option<Tier1RawPlane>,rest|part2_ht_duplicate_after_cleanup(before,role,rest),Err(error),Err(error));
    part2_ht_duplicate_nested_join(before,role,Err(error));
}
pub(crate) proof fn part2_ht_duplicate_normal(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_ht_duplicate_result(before,role,Ok(before)),
{
    part2_decoder_plane_normal(before.plane,role,false);
    part2_nested_bitplane_option_normal(before.bitplane_state,role,false);
    part2_nested_legacy_option_normal(before.legacy_segment,role);
    part2_decoder_cleanup_normal(before.ht_cleanup_plane,role);
    part2_ht_bytes_normal(before.ht_refinement_data,role);
    part2_ht_duplicate_observed(before,role,Ok(before.ht_refinement_data));
}
pub(crate) proof fn part2_ht_duplicate_frames(before:Tier1DecoderState,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1DecoderState,crate::DecodeError>)
    requires part2_ht_duplicate_result(before,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_ht_duplicate_run(before,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState>|
            (forall|calls| #[trigger] other(calls)==part2_ht_duplicate_run(before,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_ht_duplicate_result);part2_tier1_storage_eta(|calls|part2_ht_duplicate_run(before,role,calls),result);}
}
