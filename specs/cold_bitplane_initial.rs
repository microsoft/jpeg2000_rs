//! Actual fresh significant-before reservation and visited fill, not owner copies.
use super::*;
verus! {
pub(crate) open spec fn part2_bitplane_significant(plane:Tier1RawPlane)->Seq<bool> {
    plane.coefficients.map_values(|value:Tier1RawCoefficient|value.significant)
}
pub(crate) open spec fn part2_bitplane_capacity_run(plane:Tier1RawPlane,bitplane:u16,visited:bool,prior:Option<Seq<bool>>,
    calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=if visited{match prior{Some(values)=>values.len(),None=>0nat}}else{plane.coefficients.len()};
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0]{
        Part2Tier1StorageEvent::BitplaneInitialCapacity {plane:source,bitplane:actual,visited:field,prior:before,elements,succeeded}=>
            if source!=plane || actual!=bitplane || field!=visited || before!=prior || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_bitplane_capacity_result(plane:Tier1RawPlane,bitplane:u16,visited:bool,prior:Option<Seq<bool>>,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_bitplane_capacity_run(plane,bitplane,visited,prior,calls),result)
}
pub(crate) proof fn part2_bitplane_capacity_observed(plane:Tier1RawPlane,bitplane:u16,visited:bool,prior:Option<Seq<bool>>,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (result==Err(crate::DecodeError::AllocationFailed)
        && (if visited{match prior{Some(values)=>values.len(),None=>0nat}}else{plane.coefficients.len()})>0),
    ensures part2_bitplane_capacity_result(plane,bitplane,visited,prior,result),
{
    reveal(part2_bitplane_capacity_result);
    let count=if visited{match prior{Some(values)=>values.len(),None=>0nat}}else{plane.coefficients.len()};
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::BitplaneInitialCapacity {plane,bitplane,visited,prior,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_bitplane_capacity_run(plane,bitplane,visited,prior,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_bitplane_capacity_run(plane,bitplane,visited,prior,calls),prefix,result));
}
pub(crate) proof fn part2_bitplane_capacity_frames(plane:Tier1RawPlane,bitplane:u16,visited:bool,prior:Option<Seq<bool>>,result:Result<(),crate::DecodeError>)
    requires part2_bitplane_capacity_result(plane,bitplane,visited,prior,result),
    ensures part2_tier1_storage_framed(|calls|part2_bitplane_capacity_run(plane,bitplane,visited,prior,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()>|
            (forall|calls| #[trigger] other(calls)==part2_bitplane_capacity_run(plane,bitplane,visited,prior,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_bitplane_capacity_result);part2_tier1_storage_eta(|calls|part2_bitplane_capacity_run(plane,bitplane,visited,prior,calls),result);}
pub(crate) open spec fn part2_bitplane_initial_visited(plane:Tier1RawPlane,bitplane:u16,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyBitplane> {
    part2_tier1_storage_bind(part2_bitplane_capacity_run(plane,bitplane,true,Some(part2_bitplane_significant(plane)),calls),
        |_:(),rest|Some((part1_legacy_bitplane_initial(plane,bitplane),rest)))
}
pub(crate) open spec fn part2_bitplane_initial_run(plane:Tier1RawPlane,bitplane:u16,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyBitplane> {
    if bitplane>=crate::tier1::MAX_TIER1_BITPLANES{Some((part1_legacy_bitplane_initial(plane,bitplane),calls))}
    else{part2_tier1_storage_bind(part2_bitplane_capacity_run(plane,bitplane,false,None,calls),
        |_:(),rest|part2_bitplane_initial_visited(plane,bitplane,rest))}
}
pub closed spec fn part2_bitplane_initial_result(plane:Tier1RawPlane,bitplane:u16,result:Result<Part1LegacyBitplane,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_bitplane_initial_run(plane,bitplane,calls),result)
}
pub(crate) proof fn part2_bitplane_initial_first_error(plane:Tier1RawPlane,bitplane:u16,error:crate::DecodeError)
    requires bitplane<crate::tier1::MAX_TIER1_BITPLANES,part2_bitplane_capacity_result(plane,bitplane,false,None,Err(error)),
    ensures part2_bitplane_initial_result(plane,bitplane,Err(error)),
{
    reveal(part2_bitplane_initial_result);
    part2_bitplane_capacity_frames(plane,bitplane,false,None,Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_bitplane_capacity_run(plane,bitplane,false,None,calls),|_:(),rest|part2_bitplane_initial_visited(plane,bitplane,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_bitplane_initial_observed(plane:Tier1RawPlane,bitplane:u16,copied:Result<(),crate::DecodeError>)
    requires bitplane<crate::tier1::MAX_TIER1_BITPLANES,part2_bitplane_capacity_result(plane,bitplane,false,None,Ok(())),
        part2_bitplane_capacity_result(plane,bitplane,true,Some(part2_bitplane_significant(plane)),copied),
    ensures part2_bitplane_initial_result(plane,bitplane,match copied{Err(error)=>Err(error),Ok(())=>part1_legacy_bitplane_initial(plane,bitplane)}),
{
    reveal(part2_bitplane_initial_result);
    let value=match copied{Err(error)=>Err(error),Ok(())=>part1_legacy_bitplane_initial(plane,bitplane)};
    part2_bitplane_capacity_frames(plane,bitplane,true,Some(part2_bitplane_significant(plane)),copied);
    if copied.is_ok(){part2_tier1_storage_pure(part1_legacy_bitplane_initial(plane,bitplane));}
    part2_tier1_storage_bind_frame(|calls|part2_bitplane_capacity_run(plane,bitplane,true,Some(part2_bitplane_significant(plane)),calls),
        |_:(),rest|Some((part1_legacy_bitplane_initial(plane,bitplane),rest)),copied,value);
    part2_tier1_storage_eta(|calls|part2_bitplane_initial_visited(plane,bitplane,calls),value);
    part2_bitplane_capacity_frames(plane,bitplane,false,None,Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_bitplane_capacity_run(plane,bitplane,false,None,calls),|_:(),rest|part2_bitplane_initial_visited(plane,bitplane,rest),Ok(()),value);
}
pub(crate) proof fn part2_bitplane_initial_normal(plane:Tier1RawPlane,bitplane:u16)
    ensures part2_bitplane_initial_result(plane,bitplane,part1_legacy_bitplane_initial(plane,bitplane)),
{
    reveal(part2_bitplane_initial_result);
    if bitplane>=crate::tier1::MAX_TIER1_BITPLANES{part2_tier1_storage_pure(part1_legacy_bitplane_initial(plane,bitplane));}
    else{
        part2_bitplane_capacity_observed(plane,bitplane,false,None,Ok(()));
        part2_bitplane_capacity_observed(plane,bitplane,true,Some(part2_bitplane_significant(plane)),Ok(()));
        part2_bitplane_initial_observed(plane,bitplane,Ok(()));
    }
}
pub(crate) proof fn part2_bitplane_initial_frames(plane:Tier1RawPlane,bitplane:u16,result:Result<Part1LegacyBitplane,crate::DecodeError>)
    requires part2_bitplane_initial_result(plane,bitplane,result),
    ensures part2_tier1_storage_framed(|calls|part2_bitplane_initial_run(plane,bitplane,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyBitplane>|
            (forall|calls| #[trigger] other(calls)==part2_bitplane_initial_run(plane,bitplane,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_bitplane_initial_result);part2_tier1_storage_eta(|calls|part2_bitplane_initial_run(plane,bitplane,calls),result);}
pub(crate) open spec fn part2_legacy_ensure_run(before:Tier1DecoderState,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult> {
    if before.bitplane_state.is_some(){Some((Ok((Ok(()),before)),calls))}
    else{part2_tier1_storage_resume(part2_bitplane_initial_run(before.plane,before.bitplane,calls),
        |copied:Result<Part1LegacyBitplane,crate::DecodeError>,rest|Some((Ok(match copied{
            Err(error)=>(Err(error),before),Ok(state)=>(Ok(()),Tier1DecoderState {bitplane_state:Some(state),..before})
        }),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_ensure_result(before:Tier1DecoderState,result:Part2LegacyResult)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_ensure_run(before,calls),Ok(result))
}
pub(crate) proof fn part2_legacy_ensure_observed(before:Tier1DecoderState,copied:Result<Part1LegacyBitplane,crate::DecodeError>)
    requires before.bitplane_state.is_none(),part2_bitplane_initial_result(before.plane,before.bitplane,copied),
    ensures part2_legacy_ensure_result(before,match copied{Err(error)=>(Err(error),before),Ok(state)=>(Ok(()),Tier1DecoderState {bitplane_state:Some(state),..before})}),
{
    reveal(part2_legacy_ensure_result);
    let value=match copied{Err(error)=>(Err(error),before),Ok(state)=>(Ok(()),Tier1DecoderState {bitplane_state:Some(state),..before})};
    part2_bitplane_initial_frames(before.plane,before.bitplane,copied);part2_tier1_storage_pure(Ok(value));
    part2_tier1_resume_frame(|calls|part2_bitplane_initial_run(before.plane,before.bitplane,calls),
        |copied:Result<Part1LegacyBitplane,crate::DecodeError>,rest|Some((Ok(match copied{
            Err(error)=>(Err(error),before),Ok(state)=>(Ok(()),Tier1DecoderState {bitplane_state:Some(state),..before})
        }),rest)),copied,Ok(value));
}
pub(crate) proof fn part2_legacy_ensure_present(before:Tier1DecoderState)
    requires before.bitplane_state.is_some(),
    ensures part2_legacy_ensure_result(before,(Ok(()),before)),
{reveal(part2_legacy_ensure_result);part2_tier1_storage_pure::<Part2LegacyResult>(Ok((Ok(()),before)));}
pub(crate) proof fn part2_legacy_ensure_normal(before:Tier1DecoderState)
    ensures part2_legacy_ensure_result(before,part1_legacy_ensure_bitplane(before)),
{
    if before.bitplane_state.is_some(){part2_legacy_ensure_present(before);}
    else{part2_bitplane_initial_normal(before.plane,before.bitplane);part2_legacy_ensure_observed(before,part1_legacy_bitplane_initial(before.plane,before.bitplane));}
}
pub(crate) proof fn part2_legacy_ensure_frames(before:Tier1DecoderState,result:Part2LegacyResult)
    requires part2_legacy_ensure_result(before,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_ensure_run(before,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part2LegacyResult>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_ensure_run(before,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_ensure_result);part2_tier1_storage_eta(|calls|part2_legacy_ensure_run(before,calls),Ok(result));}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_pass_prepared(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind)->Part1LegacySegmentPassEffect {
    match before.bitplane_state{
        None=>(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before,symbols),
        Some(state)=>if (symbols is Raw) && (kind is Cleanup){(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before,symbols)}
        else{
            let pass=if kind is Cleanup{
                part1_legacy_cleanup_pass(before.plane,state,symbols,before.orientation,before.style.vertical_causal_context,before.style.segmentation_symbols)
            }else{part1_legacy_pass(before.plane,state,symbols,if kind is MagnitudeRefinement{crate::tier1::SubbandOrientation::Ll}else{before.orientation},
                before.style.vertical_causal_context,if kind is MagnitudeRefinement{1u8}else{0u8})};
            (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..before},pass.3)
        },
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_pass_after_ready(symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,ready:Part2LegacyResult)->Part1LegacySegmentPassEffect {
    match ready.0{Err(error)=>(Err(error),ready.1,symbols),Ok(())=>part2_legacy_pass_prepared(ready.1,symbols,kind)}
}
pub(crate) open spec fn part2_legacy_pass_run(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentPassEffect> {
    part2_tier1_storage_bind(part2_legacy_ensure_run(before,calls),
        |ready:Part2LegacyResult,rest|Some((Ok(part2_legacy_pass_after_ready(symbols,kind,ready)),rest)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_legacy_pass_result(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,result:Part1LegacySegmentPassEffect)->bool {
    part2_tier1_storage_framed(|calls|part2_legacy_pass_run(before,symbols,kind,calls),Ok(result))
        && (result.0!=Err(crate::DecodeError::AllocationFailed) ==> result==part1_legacy_decode_pass(before,symbols,kind))
}
pub(crate) proof fn part2_legacy_pass_observed(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,ready:Part2LegacyResult)
    requires part2_legacy_ensure_result(before,ready),
        ready.0!=Err(crate::DecodeError::AllocationFailed) ==> ready==part1_legacy_ensure_bitplane(before),
    ensures part2_legacy_pass_result(before,symbols,kind,part2_legacy_pass_after_ready(symbols,kind,ready)),
{
    reveal(part2_legacy_pass_result);reveal(part2_legacy_pass_after_ready);reveal(part2_legacy_pass_prepared);reveal(part1_legacy_decode_pass);
    let result=part2_legacy_pass_after_ready(symbols,kind,ready);
    part2_legacy_ensure_frames(before,ready);part2_tier1_storage_pure(Ok(result));
    part2_tier1_storage_bind_frame(|calls|part2_legacy_ensure_run(before,calls),
        |ready:Part2LegacyResult,rest|Some((Ok(part2_legacy_pass_after_ready(symbols,kind,ready)),rest)),Ok(ready),Ok(result));
}
pub(crate) proof fn part2_legacy_pass_normal(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind)
    ensures part2_legacy_pass_result(before,symbols,kind,part1_legacy_decode_pass(before,symbols,kind)),
{
    reveal(part1_legacy_decode_pass);reveal(part2_legacy_pass_prepared);reveal(part2_legacy_pass_after_ready);
    part2_legacy_ensure_normal(before);part2_legacy_pass_observed(before,symbols,kind,part1_legacy_ensure_bitplane(before));
}
pub(crate) proof fn part2_legacy_pass_after_ready_equation(symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,ready:Part2LegacyResult)
    ensures part2_legacy_pass_after_ready(symbols,kind,ready)==match ready.0{
        Err(error)=>(Err(error),ready.1,symbols),Ok(())=>part2_legacy_pass_prepared(ready.1,symbols,kind)},
{reveal(part2_legacy_pass_after_ready);}
pub(crate) proof fn part2_legacy_pass_prepared_equation(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind)
    ensures part2_legacy_pass_prepared(before,symbols,kind)==match before.bitplane_state{
        None=>(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before,symbols),
        Some(state)=>if (symbols is Raw) && (kind is Cleanup){(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before,symbols)}
        else{
            let pass=if kind is Cleanup{
                part1_legacy_cleanup_pass(before.plane,state,symbols,before.orientation,before.style.vertical_causal_context,before.style.segmentation_symbols)
            }else{part1_legacy_pass(before.plane,state,symbols,if kind is MagnitudeRefinement{crate::tier1::SubbandOrientation::Ll}else{before.orientation},
                before.style.vertical_causal_context,if kind is MagnitudeRefinement{1u8}else{0u8})};
            (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..before},pass.3)
        },
    },
{reveal(part2_legacy_pass_prepared);}
pub(crate) proof fn part2_legacy_pass_primary_consequence(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,result:Part1LegacySegmentPassEffect)
    requires part2_legacy_pass_result(before,symbols,kind,result),
    ensures result.0!=Err(crate::DecodeError::AllocationFailed) ==> result==part1_legacy_decode_pass(before,symbols,kind),
{reveal(part2_legacy_pass_result);}
pub(crate) proof fn part2_legacy_raw_prepared_equation(before:Tier1DecoderState,reader:Part1RawReaderState,kind:crate::tier1::Tier1PassKind)
    ensures part2_legacy_pass_prepared(before,Part1LegacySymbols::Raw(reader),kind)==match before.bitplane_state{
        None=>(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before,Part1LegacySymbols::Raw(reader)),
        Some(state)=>if kind is Cleanup{(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),before,Part1LegacySymbols::Raw(reader))}
        else{
            let pass=part1_legacy_pass(before.plane,state,Part1LegacySymbols::Raw(reader),
                if kind is MagnitudeRefinement{crate::tier1::SubbandOrientation::Ll}else{before.orientation},
                before.style.vertical_causal_context,if kind is MagnitudeRefinement{1u8}else{0u8});
            (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..before},pass.3)
        },
    },
{reveal(part2_legacy_pass_prepared);}
pub(crate) proof fn part2_legacy_raw_ready_contract(before:Tier1DecoderState,reader:Part1RawReaderState,kind:crate::tier1::Tier1PassKind,ready:Part2LegacyResult)
    requires part2_legacy_ensure_result(before,ready),
        ready.0!=Err(crate::DecodeError::AllocationFailed) ==> ready==part1_legacy_ensure_bitplane(before),
    ensures part2_legacy_pass_result(before,Part1LegacySymbols::Raw(reader),kind,part2_legacy_pass_after_ready(Part1LegacySymbols::Raw(reader),kind,ready)),
        part2_legacy_pass_after_ready(Part1LegacySymbols::Raw(reader),kind,ready).0!=Err(crate::DecodeError::AllocationFailed) ==>
            part2_legacy_pass_after_ready(Part1LegacySymbols::Raw(reader),kind,ready)==part1_legacy_decode_pass(before,Part1LegacySymbols::Raw(reader),kind),
        part2_legacy_pass_after_ready(Part1LegacySymbols::Raw(reader),kind,ready)==match ready.0{
            Err(error)=>(Err(error),ready.1,Part1LegacySymbols::Raw(reader)),Ok(())=>match ready.1.bitplane_state{
                None=>(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),ready.1,Part1LegacySymbols::Raw(reader)),
                Some(state)=>if kind is Cleanup{(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),ready.1,Part1LegacySymbols::Raw(reader))}
                else{
                    let pass=part1_legacy_pass(ready.1.plane,state,Part1LegacySymbols::Raw(reader),
                        if kind is MagnitudeRefinement{crate::tier1::SubbandOrientation::Ll}else{ready.1.orientation},
                        ready.1.style.vertical_causal_context,if kind is MagnitudeRefinement{1u8}else{0u8});
                    (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..ready.1},pass.3)
                },
            },
        },
{
    let symbols=Part1LegacySymbols::Raw(reader);
    part2_legacy_pass_observed(before,symbols,kind,ready);
    part2_legacy_pass_after_ready_equation(symbols,kind,ready);
    part2_legacy_raw_prepared_equation(ready.1,reader,kind);
    part2_legacy_pass_primary_consequence(before,symbols,kind,part2_legacy_pass_after_ready(symbols,kind,ready));
}
pub(crate) proof fn part2_legacy_pass_frames(before:Tier1DecoderState,symbols:Part1LegacySymbols,kind:crate::tier1::Tier1PassKind,result:Part1LegacySegmentPassEffect)
    requires part2_legacy_pass_result(before,symbols,kind,result),
    ensures part2_tier1_storage_framed(|calls|part2_legacy_pass_run(before,symbols,kind,calls),Ok(result)),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacySegmentPassEffect>|
            (forall|calls| #[trigger] other(calls)==part2_legacy_pass_run(before,symbols,kind,calls)) ==> #[trigger] part2_tier1_storage_framed(other,Ok(result)),
{reveal(part2_legacy_pass_result);part2_tier1_storage_eta(|calls|part2_legacy_pass_run(before,symbols,kind,calls),Ok(result));}
pub(crate) proof fn part2_legacy_mq_ready_contract(before:Tier1DecoderState,reader:Part1MqState,kind:crate::tier1::Tier1PassKind,ready:Part2LegacyResult)
    requires part2_legacy_ensure_result(before,ready),
        ready.0!=Err(crate::DecodeError::AllocationFailed) ==> ready==part1_legacy_ensure_bitplane(before),
    ensures part2_legacy_pass_result(before,Part1LegacySymbols::Mq(reader),kind,part2_legacy_pass_after_ready(Part1LegacySymbols::Mq(reader),kind,ready)),
        part2_legacy_pass_after_ready(Part1LegacySymbols::Mq(reader),kind,ready).0!=Err(crate::DecodeError::AllocationFailed) ==>
            part2_legacy_pass_after_ready(Part1LegacySymbols::Mq(reader),kind,ready)==part1_legacy_decode_pass(before,Part1LegacySymbols::Mq(reader),kind),
        part2_legacy_pass_after_ready(Part1LegacySymbols::Mq(reader),kind,ready)==match ready.0{
            Err(error)=>(Err(error),ready.1,Part1LegacySymbols::Mq(reader)),Ok(())=>match ready.1.bitplane_state{
                None=>(Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),ready.1,Part1LegacySymbols::Mq(reader)),Some(state)=>{
                    let pass=if kind is Cleanup{part1_legacy_cleanup_pass(ready.1.plane,state,Part1LegacySymbols::Mq(reader),ready.1.orientation,ready.1.style.vertical_causal_context,ready.1.style.segmentation_symbols)}
                        else{part1_legacy_pass(ready.1.plane,state,Part1LegacySymbols::Mq(reader),if kind is MagnitudeRefinement{crate::tier1::SubbandOrientation::Ll}else{ready.1.orientation},ready.1.style.vertical_causal_context,if kind is MagnitudeRefinement{1u8}else{0u8})};
                    (pass.0,Tier1DecoderState {plane:pass.1,bitplane_state:Some(pass.2),..ready.1},pass.3)
                },
            },
        },
{
    let symbols=Part1LegacySymbols::Mq(reader);
    part2_legacy_pass_observed(before,symbols,kind,ready);
    part2_legacy_pass_after_ready_equation(symbols,kind,ready);
    part2_legacy_pass_prepared_equation(ready.1,symbols,kind);
    part2_legacy_pass_primary_consequence(before,symbols,kind,part2_legacy_pass_after_ready(symbols,kind,ready));
}
}
