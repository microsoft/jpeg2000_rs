//! Shared role-aware coefficient storage and actual configured-decoder caller responses.
use super::*;
verus! {
pub enum Part2Tier1StorageEvent {
    AssemblyOwnerCapacity {context:Part2AssemblyOwnerContext,elements:nat,succeeded:bool},
    PreparedViewsCapacity {source:Seq<Part1AssemblyTile>,elements:nat,succeeded:bool},
    PreparedComponentCapacity {context:Part2PreparedComponentContext,elements:nat,succeeded:bool},
    PrepareWorkingCapacity {context:Part2PrepareWorkingContext,elements:nat,succeeded:bool},
    PrecinctContributions {context:Part2PrecinctContributionsContext,elements:nat,succeeded:bool},
    Coefficient {width:u16,height:u16,role:crate::tier1::CoefficientStorageRole,samples:usize,succeeded:bool},
    RefinementBytes {role:crate::tier1::HtRefinementCopyRole,source:Seq<u8>,elements:nat,succeeded:bool},
    DecoderPlaneCopy {source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,cleanup:bool,elements:nat,succeeded:bool},
    NestedCopy {owner:Part2NestedCopyOwner,elements:nat,succeeded:bool},
    BitplaneInitialCapacity {plane:Tier1RawPlane,bitplane:u16,visited:bool,prior:Option<Seq<bool>>,elements:nat,succeeded:bool},
    HtExponentCapacity {context:Part2HtExponentContext,current:bool,elements:nat,succeeded:bool},
    HtMetadataCapacity {context:Part2HtMetadataContext,role:Part2HtMetadataRole,elements:nat,succeeded:bool},
    RefinementScratchCapacity {context:Part2HtRefinementScratchContext,stuffed:bool,elements:usize,succeeded:bool},
    CoefficientExtractionCapacity {context:Part2CoefficientExtractionContext,elements:nat,succeeded:bool},
    CleanupSignificanceCapacity {elements:nat,succeeded:bool},
    QuantizationCapacity {owner:Part2QuantizationOwner,elements:nat,succeeded:bool},
    WaveletPlaneCapacity {owner:Part2WaveletPlaneOwner,elements:nat,succeeded:bool},
    WaveletLineCapacity {context:Part2WaveletLineContext,elements:nat,succeeded:bool},
    PrepareCopyCapacity {role:Part2PrepareCopyRole,elements:nat,succeeded:bool},
    LegacyInputExtension {source:Tier1LegacyFrame,bytes:Seq<u8>,passes:u32,elements:nat,succeeded:bool},
}
pub type Part2Tier1Run<T> = Option<(Result<T,crate::DecodeError>,Seq<Part2Tier1StorageEvent>)>;
pub(crate) open spec fn part2_tier1_storage_prefix<T>(run:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,
    prefix:Seq<Part2Tier1StorageEvent>,result:Result<T,crate::DecodeError>)->bool {
    forall|tail:Seq<Part2Tier1StorageEvent>| #[trigger] run(prefix+tail)==Some((result,tail))
}
pub(crate) open spec fn part2_tier1_storage_framed<T>(run:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,result:Result<T,crate::DecodeError>)->bool {
    exists|prefix:Seq<Part2Tier1StorageEvent>| #[trigger] part2_tier1_storage_prefix(run,prefix,result)
}
pub(crate) open spec fn part2_tier1_storage_bind<A,B>(run:Part2Tier1Run<A>,next:spec_fn(A,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>)->Part2Tier1Run<B> {
    match run {None=>None,Some((Err(error),rest))=>Some((Err(error),rest)),Some((Ok(value),rest))=>next(value,rest)}
}
pub(crate) proof fn part2_tier1_storage_at<T>(run:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,prefix:Seq<Part2Tier1StorageEvent>,
    result:Result<T,crate::DecodeError>,tail:Seq<Part2Tier1StorageEvent>)
    requires part2_tier1_storage_prefix(run,prefix,result),
    ensures run(prefix+tail)==Some((result,tail)),
{}
pub(crate) proof fn part2_tier1_storage_eta<T>(run:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,result:Result<T,crate::DecodeError>)
    requires part2_tier1_storage_framed(run,result),
    ensures forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>|
        (forall|events| #[trigger] other(events)==run(events)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    assert forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>|
        (forall|events| #[trigger] other(events)==run(events)) implies #[trigger] part2_tier1_storage_framed(other,result) by {
        assert(other =~= run);
    }
}
pub(crate) proof fn part2_tier1_storage_bind_frame<A,B>(run:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<A>,
    next:spec_fn(A,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>,first:Result<A,crate::DecodeError>,result:Result<B,crate::DecodeError>)
    requires part2_tier1_storage_framed(run,first),
        match first {Err(error)=>result==Err(error),Ok(value)=>part2_tier1_storage_framed(|events|next(value,events),result)},
    ensures part2_tier1_storage_framed(|events|part2_tier1_storage_bind(run(events),next),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>|
            (forall|events| #[trigger] other(events)==part2_tier1_storage_bind(run(events),next)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    let prefix=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,first);
    match first {
        Err(_)=>{assert(part2_tier1_storage_prefix(|events|part2_tier1_storage_bind(run(events),next),prefix,result));},
        Ok(value)=>{
            let child=|events|next(value,events);
            let second=choose|prefix| #[trigger] part2_tier1_storage_prefix(child,prefix,result);
            assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_tier1_storage_bind(run((prefix+second)+tail),next)==Some((result,tail)) by{
                assert((prefix+second)+tail =~= prefix+(second+tail));
                part2_tier1_storage_at(run,prefix,first,second+tail);
                part2_tier1_storage_at(child,second,result,tail);
            }
            assert(part2_tier1_storage_prefix(|events|part2_tier1_storage_bind(run(events),next),prefix+second,result));
        },
    }
    part2_tier1_storage_eta(|events|part2_tier1_storage_bind(run(events),next),result);
}
pub(crate) proof fn part2_tier1_storage_pure<T>(result:Result<T,crate::DecodeError>)
    ensures part2_tier1_storage_framed(|events|Some((result,events)),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>|
            (forall|events| #[trigger] other(events)==Some((result,events))) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    assert(part2_tier1_storage_prefix(|events|Some((result,events)),Seq::empty(),result));
    part2_tier1_storage_eta(|events|Some((result,events)),result);
}
pub(crate) open spec fn part2_tier1_plane_admit(width:u16,height:u16)->Result<usize,crate::DecodeError> {
    let count=width as nat*height as nat;
    if width==0 || height==0{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else if count>usize::MAX{Err(ht_reader_error(crate::MalformedKind::ArithmeticOverflow))}
    else if count>4096{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}else{Ok(count as usize)}
}
pub(crate) open spec fn part2_tier1_plane_run(width:u16,height:u16,role:crate::tier1::CoefficientStorageRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane> {
        match part2_tier1_plane_admit(width,height) {
            Err(error)=>Some((Err(error),calls)),
            Ok(count)=>if count==0{Some((tier1_empty_plane(width,height),calls))}else if calls.len()==0{None}else{
                match calls[0] {
                    Part2Tier1StorageEvent::Coefficient {width:actual_width,height:actual_height,role:actual_role,samples,succeeded}=>
                        if actual_width!=width || actual_height!=height || actual_role!=role || samples!=count{None}
                        else{Some((if succeeded{tier1_empty_plane(width,height)}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))},
                    _=>None,
                }
            },
        }
}
pub closed spec fn part1_tier1_plane_storage_result(width:u16,height:u16,role:crate::tier1::CoefficientStorageRole,result:Result<Tier1RawPlane,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_tier1_plane_run(width,height,role,calls),result)
}
pub(crate) proof fn part2_tier1_plane_normal(width:u16,height:u16,role:crate::tier1::CoefficientStorageRole)
    ensures part1_tier1_plane_storage_result(width,height,role,tier1_empty_plane(width,height)),
{
    let result=tier1_empty_plane(width,height);
    let prefix=match part2_tier1_plane_admit(width,height){
        Err(_)=>Seq::empty(),Ok(count)=>if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::Coefficient {width,height,role,samples:count,succeeded:true}]},
    };
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_tier1_plane_run(width,height,role,prefix+tail)==Some((result,tail)) by{
        if part2_tier1_plane_admit(width,height).is_ok() && part2_tier1_plane_admit(width,height).get_Ok_0()>0{
            assert((prefix+tail).drop_first() =~= tail);
        }else{assert(prefix+tail =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_tier1_plane_run(width,height,role,calls),prefix,result));
}
pub(crate) proof fn part2_tier1_plane_observed(width:u16,height:u16,role:crate::tier1::CoefficientStorageRole,count:usize,result:Result<(),crate::DecodeError>)
    requires part2_tier1_plane_admit(width,height)==Ok(count),result==Ok(()) || (count>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part1_tier1_plane_storage_result(width,height,role,if result.is_ok(){tier1_empty_plane(width,height)}else{Err(crate::DecodeError::AllocationFailed)}),
{
    let value=if result.is_ok(){tier1_empty_plane(width,height)}else{Err(crate::DecodeError::AllocationFailed)};
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::Coefficient {width,height,role,samples:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_tier1_plane_run(width,height,role,prefix+tail)==Some((value,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_tier1_plane_run(width,height,role,calls),prefix,value));
}
pub(crate) proof fn part2_tier1_plane_frames(width:u16,height:u16,role:crate::tier1::CoefficientStorageRole,result:Result<Tier1RawPlane,crate::DecodeError>)
    requires part1_tier1_plane_storage_result(width,height,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_tier1_plane_run(width,height,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane>|
            (forall|calls| #[trigger] other(calls)==part2_tier1_plane_run(width,height,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{part2_tier1_storage_eta(|calls|part2_tier1_plane_run(width,height,role,calls),result);}
pub(crate) open spec fn part2_tier1_storage_resume<A,B>(run:Part2Tier1Run<A>,next:spec_fn(Result<A,crate::DecodeError>,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>)->Part2Tier1Run<B> {
    match run {None=>None,Some((result,rest))=>next(result,rest)}
}
pub(crate) proof fn part2_tier1_resume_frame<A,B>(run:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<A>,
    next:spec_fn(Result<A,crate::DecodeError>,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>,
    first:Result<A,crate::DecodeError>,result:Result<B,crate::DecodeError>)
    requires part2_tier1_storage_framed(run,first),part2_tier1_storage_framed(|calls|next(first,calls),result),
    ensures part2_tier1_storage_framed(|calls|part2_tier1_storage_resume(run(calls),next),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>|
            (forall|calls| #[trigger] other(calls)==part2_tier1_storage_resume(run(calls),next)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{
    let prefix=choose|prefix| #[trigger] part2_tier1_storage_prefix(run,prefix,first);
    let child=|calls|next(first,calls);
    let second=choose|prefix| #[trigger] part2_tier1_storage_prefix(child,prefix,result);
    let joined=|calls|part2_tier1_storage_resume(run(calls),next);
    assert forall|tail:Seq<Part2Tier1StorageEvent>|joined((prefix+second)+tail)==Some((result,tail)) by{
        assert((prefix+second)+tail =~= prefix+(second+tail));
        part2_tier1_storage_at(run,prefix,first,second+tail);part2_tier1_storage_at(child,second,result,tail);
    }
    assert(part2_tier1_storage_prefix(joined,prefix+second,result));
    part2_tier1_storage_eta(joined,result);
}
pub(crate) open spec fn part2_tier1_phase<T>(root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,prefix:Seq<Part2Tier1StorageEvent>,
    child:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>)->bool {
    forall|tail:Seq<Part2Tier1StorageEvent>| #[trigger] root(prefix+tail)==child(tail)
}
pub(crate) proof fn part2_tier1_phase_eta<T>(root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,
    other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,prefix:Seq<Part2Tier1StorageEvent>,
    child:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>)
    requires part2_tier1_phase(root,prefix,child),
        forall|calls:Seq<Part2Tier1StorageEvent>| #[trigger] root(calls)==other(calls),
    ensures part2_tier1_phase(other,prefix,child),
{
    assert forall|tail:Seq<Part2Tier1StorageEvent>|other(prefix+tail)==child(tail) by{
        assert(root(prefix+tail)==child(tail));
    }
}
pub(crate) proof fn part2_tier1_prefix_advance<A,B>(root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>,
    child:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<A>,next:spec_fn(A,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<B>,
    prefix:Seq<Part2Tier1StorageEvent>,value:A)->(joined:Seq<Part2Tier1StorageEvent>)
    requires forall|tail:Seq<Part2Tier1StorageEvent>| #[trigger] root(prefix+tail)==part2_tier1_storage_bind(child(tail),next),
        part2_tier1_storage_framed(child,Ok(value)),
    ensures part2_tier1_phase(root,joined,|tail|next(value,tail)),
{
    let calls=choose|calls| #[trigger] part2_tier1_storage_prefix(child,calls,Ok(value));
    let joined=prefix+calls;
    assert forall|tail:Seq<Part2Tier1StorageEvent>|root(joined+tail)==next(value,tail) by{
        assert(joined+tail =~= prefix+(calls+tail));
        part2_tier1_storage_at(child,calls,Ok(value),tail);
    }
    joined
}
pub(crate) proof fn part2_tier1_prefix_finish<T>(root:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,
    prefix:Seq<Part2Tier1StorageEvent>,result:Result<T,crate::DecodeError>)
    requires part2_tier1_phase(root,prefix,|tail|Some((result,tail))),
    ensures part2_tier1_storage_framed(root,result),
{assert(part2_tier1_storage_prefix(root,prefix,result));part2_tier1_storage_eta(root,result);}
pub(crate) open spec fn part2_tier1_initial_run(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,
    style:crate::tier1::Tier1CodingStyle,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    if significant==0 || significant>crate::tier1::MAX_TIER1_BITPLANES{Some((Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock)),calls))}
    else{part2_tier1_storage_bind(part2_tier1_plane_run(width,height,crate::tier1::CoefficientStorageRole::InitialDecoder,calls),
        |_:Tier1RawPlane,rest|Some((part2_tier1_initial_decoder(width,height,significant,orientation,style),rest)))}
}
pub closed spec fn part1_tier1_initial_storage_result(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,
    style:crate::tier1::Tier1CodingStyle,result:Result<Tier1DecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_tier1_initial_run(width,height,significant,orientation,style,calls),result)
}
pub(crate) proof fn part2_tier1_initial_normal(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,style:crate::tier1::Tier1CodingStyle)
    ensures part1_tier1_initial_storage_result(width,height,significant,orientation,style,part2_tier1_initial_decoder(width,height,significant,orientation,style)),
{
    let result=part2_tier1_initial_decoder(width,height,significant,orientation,style);
    if significant==0 || significant>crate::tier1::MAX_TIER1_BITPLANES{part2_tier1_storage_pure(result);}else{
        part2_tier1_plane_normal(width,height,crate::tier1::CoefficientStorageRole::InitialDecoder);
        let plane=tier1_empty_plane(width,height);if plane.is_ok(){part2_tier1_storage_pure(result);}
        part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(width,height,crate::tier1::CoefficientStorageRole::InitialDecoder,calls),
            |_:Tier1RawPlane,rest|Some((result,rest)),plane,result);
    }
}
pub(crate) proof fn part2_tier1_initial_plane_error(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,style:crate::tier1::Tier1CodingStyle,error:crate::DecodeError)
    requires significant>0,significant<=crate::tier1::MAX_TIER1_BITPLANES,part1_tier1_plane_storage_result(width,height,crate::tier1::CoefficientStorageRole::InitialDecoder,Err(error)),
    ensures part1_tier1_initial_storage_result(width,height,significant,orientation,style,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_tier1_plane_run(width,height,crate::tier1::CoefficientStorageRole::InitialDecoder,calls),
        |_:Tier1RawPlane,rest|Some((part2_tier1_initial_decoder(width,height,significant,orientation,style),rest)),Err(error),Err(error));
}
pub(crate) open spec fn part2_tier1_configured_run(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,style:crate::tier1::Tier1CodingStyle,
    allowed:bool,bound:u8,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1DecoderState> {
    part2_tier1_storage_bind(part2_tier1_initial_run(width,height,significant,orientation,style,calls),
        |_:Tier1DecoderState,rest|Some((part2_tier1_configured_decoder(width,height,significant,orientation,style,allowed,bound),rest)))
}
pub closed spec fn part1_tier1_configured_storage_result(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,style:crate::tier1::Tier1CodingStyle,
    allowed:bool,bound:u8,result:Result<Tier1DecoderState,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_tier1_configured_run(width,height,significant,orientation,style,allowed,bound,calls),result)
}
pub(crate) proof fn part2_tier1_configured_normal(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,style:crate::tier1::Tier1CodingStyle,allowed:bool,bound:u8)
    ensures part1_tier1_configured_storage_result(width,height,significant,orientation,style,allowed,bound,part2_tier1_configured_decoder(width,height,significant,orientation,style,allowed,bound)),
{
    part2_tier1_initial_normal(width,height,significant,orientation,style);
    let initial=part2_tier1_initial_decoder(width,height,significant,orientation,style);
    let result=part2_tier1_configured_decoder(width,height,significant,orientation,style,allowed,bound);
    if initial.is_ok(){part2_tier1_storage_pure(result);}
    part2_tier1_storage_bind_frame(|calls|part2_tier1_initial_run(width,height,significant,orientation,style,calls),
        |_:Tier1DecoderState,rest|Some((result,rest)),initial,result);
}
pub(crate) proof fn part2_tier1_configured_initial_error(width:u16,height:u16,significant:u16,orientation:crate::tier1::SubbandOrientation,style:crate::tier1::Tier1CodingStyle,
    allowed:bool,bound:u8,error:crate::DecodeError)
    requires part1_tier1_initial_storage_result(width,height,significant,orientation,style,Err(error)),
    ensures part1_tier1_configured_storage_result(width,height,significant,orientation,style,allowed,bound,Err(error)),
{
    part2_tier1_storage_bind_frame(|calls|part2_tier1_initial_run(width,height,significant,orientation,style,calls),
        |_:Tier1DecoderState,rest|Some((part2_tier1_configured_decoder(width,height,significant,orientation,style,allowed,bound),rest)),Err(error),Err(error));
}
pub struct Part2Tier1CallContext {
    pub width:u16,pub height:u16,pub significant:u16,pub orientation:crate::tier1::SubbandOrientation,pub style:crate::tier1::Tier1CodingStyle,
    pub allowed:bool,pub bound:u8,pub grid:[u32;4],pub clip:[u32;4],pub block:[u32;2],pub indices:(usize,usize),pub before:Part2PlannedCodeBlocks,
}
pub(crate) open spec fn part2_tier1_call_admit(context:Part2Tier1CallContext)->Result<usize,crate::DecodeError> {
    if context.significant==0 || context.significant>crate::tier1::MAX_TIER1_BITPLANES{Err(ht_reader_error(crate::MalformedKind::InvalidCodeBlock))}
    else{part2_tier1_plane_admit(context.width,context.height)}
}
pub(crate) open spec fn part2_tier1_call_run(context:Part2Tier1CallContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Tier1DecoderState> {
    match part2_tier1_call_admit(context) {
        Err(error)=>Some((Err(error),events)),
        Ok(count)=>if count==0{Some((part2_tier1_configured_decoder(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound),events))}
        else if events.len()==0{None}else{
            match events[0] {
                Part2JpipSnapshotEvent::Tier1Initial {context:actual,calls}=>if actual!=context{None}else{
                    match part2_tier1_configured_run(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound,calls){
                        Some((result,rest))=>if rest.len()==0{Some((result,events.drop_first()))}else{None},None=>None,
                    }
                },
                _=>None,
            }
        },
    }
}
pub(crate) proof fn part2_tier1_call_observed(context:Part2Tier1CallContext,result:Result<Tier1DecoderState,crate::DecodeError>)
    requires part1_tier1_configured_storage_result(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound,result),
    ensures part2_cold_framed(|events|part2_tier1_call_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Tier1DecoderState>|
            (forall|events| #[trigger] other(events)==part2_tier1_call_run(context,events)) ==> #[trigger] part2_cold_framed(other,result),
{
    let raw=|calls|part2_tier1_configured_run(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound,calls);
    let calls=choose|prefix| #[trigger] part2_tier1_storage_prefix(raw,prefix,result);
    assert(calls+Seq::empty() =~= calls);assert(raw(calls)==Some((result,Seq::empty())));
    let prefix=match part2_tier1_call_admit(context){
        Err(_)=>Seq::empty(),Ok(count)=>if count==0{Seq::empty()}else{seq![Part2JpipSnapshotEvent::Tier1Initial {context,calls}]},
    };
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_tier1_call_run(context,prefix+tail)==Some((result,tail)) by{
        match part2_tier1_call_admit(context){Ok(count)=>if count>0{assert((prefix+tail).drop_first() =~= tail);}else{assert(prefix+tail =~= tail);},Err(_)=>{assert(prefix+tail =~= tail);}}
    }
    assert(part2_cold_prefix(|events|part2_tier1_call_run(context,events),prefix,result));
    part2_decode_eta(|events|part2_tier1_call_run(context,events),result);
}
pub(crate) proof fn part2_tier1_call_normal(context:Part2Tier1CallContext)
    ensures part2_cold_framed(|events|part2_tier1_call_run(context,events),
        part2_tier1_configured_decoder(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound)),
{
    part2_tier1_configured_normal(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound);
    part2_tier1_call_observed(context,part2_tier1_configured_decoder(context.width,context.height,context.significant,context.orientation,context.style,context.allowed,context.bound));
}
}
