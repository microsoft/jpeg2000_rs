//! Raw nested owner copies at the original checked decoder field frontiers.
use super::*;
verus! {
pub enum Part2NestedCopyOwner {
    Plane {source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole},
    Flags {source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,visited:bool,prior:Option<Seq<bool>>},
    Input {source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole},
}
pub(crate) open spec fn part2_nested_owner_count(owner:Part2NestedCopyOwner)->nat {
    match owner {
        Part2NestedCopyOwner::Plane {source,..}=>source.coefficients.len(),
        Part2NestedCopyOwner::Flags {source,visited,..}=>if visited{source.significance_visited.len()}else{source.significant_before.len()},
        Part2NestedCopyOwner::Input {source,..}=>source.input.len(),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_owner_run(owner:Part2NestedCopyOwner,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()> {
    let count=part2_nested_owner_count(owner);
    if count==0{Some((Ok(()),calls))}else if calls.len()==0{None}else{match calls[0] {
        Part2Tier1StorageEvent::NestedCopy {owner:actual,elements,succeeded}=>
            if actual!=owner || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},calls.drop_first()))
            },
        _=>None,
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_owner_result(owner:Part2NestedCopyOwner,result:Result<(),crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_nested_owner_run(owner,calls),result)
}
pub(crate) proof fn part2_nested_owner_observed(owner:Part2NestedCopyOwner,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (part2_nested_owner_count(owner)>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_nested_owner_result(owner,result),
{
    reveal(part2_nested_owner_result);reveal(part2_nested_owner_run);
    let count=part2_nested_owner_count(owner);
    let prefix=if count==0{Seq::empty()}else{seq![Part2Tier1StorageEvent::NestedCopy {owner,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2Tier1StorageEvent>|part2_nested_owner_run(owner,prefix+tail)==Some((result,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_tier1_storage_prefix(|calls|part2_nested_owner_run(owner,calls),prefix,result));
}
pub(crate) proof fn part2_nested_owner_frames(owner:Part2NestedCopyOwner,result:Result<(),crate::DecodeError>)
    requires part2_nested_owner_result(owner,result),
    ensures part2_tier1_storage_framed(|calls|part2_nested_owner_run(owner,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<()>|
            (forall|calls| #[trigger] other(calls)==part2_nested_owner_run(owner,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_nested_owner_result);part2_tier1_storage_eta(|calls|part2_nested_owner_run(owner,calls),result);}
pub(crate) open spec fn part2_nested_flags(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,visited:bool)->Part2NestedCopyOwner {
    Part2NestedCopyOwner::Flags {source,role,legacy,visited,prior:if visited{Some(source.significant_before)}else{None}}
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_bitplane_run(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyBitplane> {
    part2_tier1_storage_bind(part2_nested_owner_run(part2_nested_flags(source,role,legacy,false),calls),|_:(),rest|
        part2_tier1_storage_bind(part2_nested_owner_run(part2_nested_flags(source,role,legacy,true),rest),|_:(),tail|Some((Ok(source),tail))))
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_bitplane_result(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,result:Result<Part1LegacyBitplane,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_nested_bitplane_run(source,role,legacy,calls),result)
}
pub(crate) proof fn part2_nested_bitplane_observed(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,result:Result<(),crate::DecodeError>)
    requires part2_nested_owner_result(part2_nested_flags(source,role,legacy,false),Ok(())),
        part2_nested_owner_result(part2_nested_flags(source,role,legacy,true),result),
    ensures part2_nested_bitplane_result(source,role,legacy,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_nested_bitplane_result);reveal(part2_nested_bitplane_run);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    let after=|calls|part2_tier1_storage_bind(part2_nested_owner_run(part2_nested_flags(source,role,legacy,true),calls),|_:(),tail|Some((Ok(source),tail)));
    part2_nested_owner_frames(part2_nested_flags(source,role,legacy,true),result);
    if result.is_ok(){part2_tier1_storage_pure(Ok(source));}
    part2_tier1_storage_bind_frame(|calls|part2_nested_owner_run(part2_nested_flags(source,role,legacy,true),calls),|_:(),tail|Some((Ok(source),tail)),result,value);
    part2_tier1_storage_eta(after,value);
    part2_nested_owner_frames(part2_nested_flags(source,role,legacy,false),Ok(()));
    part2_tier1_storage_bind_frame(|calls|part2_nested_owner_run(part2_nested_flags(source,role,legacy,false),calls),|_:(),rest|after(rest),Ok(()),value);
}
pub(crate) proof fn part2_nested_bitplane_first_error(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,error:crate::DecodeError)
    requires part2_nested_owner_result(part2_nested_flags(source,role,legacy,false),Err(error)),
    ensures part2_nested_bitplane_result(source,role,legacy,Err(error)),
{
    reveal(part2_nested_bitplane_result);reveal(part2_nested_bitplane_run);
    part2_nested_owner_frames(part2_nested_flags(source,role,legacy,false),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_nested_owner_run(part2_nested_flags(source,role,legacy,false),calls),|_:(),rest|
        part2_tier1_storage_bind(part2_nested_owner_run(part2_nested_flags(source,role,legacy,true),rest),|_:(),tail|Some((Ok(source),tail))),Err(error),Err(error));
}
pub(crate) proof fn part2_nested_bitplane_normal(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool)
    ensures part2_nested_bitplane_result(source,role,legacy,Ok(source)),
{
    part2_nested_owner_observed(part2_nested_flags(source,role,legacy,false),Ok(()));
    part2_nested_owner_observed(part2_nested_flags(source,role,legacy,true),Ok(()));
    part2_nested_bitplane_observed(source,role,legacy,Ok(()));
}
pub(crate) proof fn part2_nested_bitplane_frames(source:Part1LegacyBitplane,role:crate::tier1::HtRefinementCopyRole,legacy:bool,result:Result<Part1LegacyBitplane,crate::DecodeError>)
    requires part2_nested_bitplane_result(source,role,legacy,result),
    ensures part2_tier1_storage_framed(|calls|part2_nested_bitplane_run(source,role,legacy,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Part1LegacyBitplane>|
            (forall|calls| #[trigger] other(calls)==part2_nested_bitplane_run(source,role,legacy,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_nested_bitplane_result);part2_tier1_storage_eta(|calls|part2_nested_bitplane_run(source,role,legacy,calls),result);}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_option_run<T>(source:Option<T>,child:spec_fn(T,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Option<T>> {
    match source{None=>Some((Ok(None),calls)),Some(value)=>part2_tier1_storage_bind(child(value,calls),|copied:T,rest|Some((Ok(Some(copied)),rest)))}
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_option_result<T>(source:Option<T>,child:spec_fn(T,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,result:Result<Option<T>,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_nested_option_run(source,child,calls),result)
}
pub(crate) proof fn part2_nested_option_none<T>(child:spec_fn(T,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>)
    ensures part2_nested_option_result(None,child,Ok(None)),
{reveal(part2_nested_option_result);reveal(part2_nested_option_run);part2_tier1_storage_pure::<Option<T>>(Ok(None));}
pub(crate) proof fn part2_nested_option_observed<T>(source:T,child:spec_fn(T,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,result:Result<T,crate::DecodeError>)
    requires part2_tier1_storage_framed(|calls|child(source,calls),result),
    ensures part2_nested_option_result(Some(source),child,match result{Err(error)=>Err(error),Ok(value)=>Ok(Some(value))}),
{
    reveal(part2_nested_option_result);reveal(part2_nested_option_run);
    let value=match result{Err(error)=>Err(error),Ok(value)=>Ok(Some(value))};
    if result.is_ok(){part2_tier1_storage_pure(value);}
    part2_tier1_storage_bind_frame(|calls|child(source,calls),|copied:T,rest|Some((Ok(Some(copied)),rest)),result,value);
}
pub(crate) proof fn part2_nested_option_frames<T>(source:Option<T>,child:spec_fn(T,Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<T>,result:Result<Option<T>,crate::DecodeError>)
    requires part2_nested_option_result(source,child,result),
    ensures part2_tier1_storage_framed(|calls|part2_nested_option_run(source,child,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Option<T>>|
            (forall|calls| #[trigger] other(calls)==part2_nested_option_run(source,child,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_nested_option_result);part2_tier1_storage_eta(|calls|part2_nested_option_run(source,child,calls),result);}
pub(crate) open spec fn part2_nested_bitplane_option_run(source:Option<Part1LegacyBitplane>,role:crate::tier1::HtRefinementCopyRole,legacy:bool,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Option<Part1LegacyBitplane>> {
    part2_nested_option_run(source,|value,rest|part2_nested_bitplane_run(value,role,legacy,rest),calls)
}
pub(crate) open spec fn part2_nested_bitplane_option_result(source:Option<Part1LegacyBitplane>,role:crate::tier1::HtRefinementCopyRole,legacy:bool,result:Result<Option<Part1LegacyBitplane>,crate::DecodeError>)->bool {
    part2_nested_option_result(source,|value,rest|part2_nested_bitplane_run(value,role,legacy,rest),result)
}
pub(crate) proof fn part2_nested_bitplane_option_normal(source:Option<Part1LegacyBitplane>,role:crate::tier1::HtRefinementCopyRole,legacy:bool)
    ensures part2_nested_bitplane_option_result(source,role,legacy,Ok(source)),
{
    let child=|value,rest|part2_nested_bitplane_run(value,role,legacy,rest);
    match source{None=>{part2_nested_option_none(child);},Some(value)=>{
        part2_nested_bitplane_normal(value,role,legacy);part2_nested_bitplane_frames(value,role,legacy,Ok(value));
        part2_nested_option_observed(value,child,Ok(value));
    }}
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_plane_run(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1RawPlane> {
    part2_tier1_storage_bind(part2_nested_owner_run(Part2NestedCopyOwner::Plane {source,role},calls),|_:(),rest|Some((Ok(source),rest)))
}
pub(crate) proof fn part2_nested_plane_observed(source:Tier1RawPlane,role:crate::tier1::HtRefinementCopyRole,result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (source.coefficients.len()>0 && result==Err(crate::DecodeError::AllocationFailed)),
    ensures part2_tier1_storage_framed(|calls|part2_nested_plane_run(source,role,calls),match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_nested_plane_run);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    part2_nested_owner_observed(Part2NestedCopyOwner::Plane {source,role},result);
    part2_nested_owner_frames(Part2NestedCopyOwner::Plane {source,role},result);
    if result.is_ok(){part2_tier1_storage_pure(Ok(source));}
    part2_tier1_storage_bind_frame(|calls|part2_nested_owner_run(Part2NestedCopyOwner::Plane {source,role},calls),|_:(),rest|Some((Ok(source),rest)),result,value);
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_legacy_after_plane(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1LegacyFrame> {
    part2_tier1_storage_bind(part2_nested_bitplane_option_run(source.bitplane_state,role,true,calls),|_:Option<Part1LegacyBitplane>,rest|
        part2_tier1_storage_bind(part2_nested_owner_run(Part2NestedCopyOwner::Input {source,role},rest),|_:(),tail|Some((Ok(source),tail))))
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_legacy_run(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1LegacyFrame> {
    part2_tier1_storage_bind(part2_nested_plane_run(source.plane,role,calls),|_:Tier1RawPlane,rest|part2_nested_legacy_after_plane(source,role,rest))
}
#[verifier::opaque]
pub(crate) open spec fn part2_nested_legacy_result(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1LegacyFrame,crate::DecodeError>)->bool {
    part2_tier1_storage_framed(|calls|part2_nested_legacy_run(source,role,calls),result)
}
pub(crate) proof fn part2_nested_legacy_join(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,value:Result<Tier1LegacyFrame,crate::DecodeError>)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(source.plane,role,calls),Ok(source.plane)),
        part2_tier1_storage_framed(|calls|part2_nested_legacy_after_plane(source,role,calls),value),
    ensures part2_nested_legacy_result(source,role,value),
{
    reveal(part2_nested_legacy_result);reveal(part2_nested_legacy_run);
    part2_tier1_storage_eta(|calls|part2_nested_plane_run(source.plane,role,calls),Ok(source.plane));
    part2_tier1_storage_eta(|calls|part2_nested_legacy_after_plane(source,role,calls),value);
    part2_tier1_storage_bind_frame(|calls|part2_nested_plane_run(source.plane,role,calls),|_:Tier1RawPlane,rest|part2_nested_legacy_after_plane(source,role,rest),Ok(source.plane),value);
}
pub(crate) proof fn part2_nested_legacy_plane_error(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,error:crate::DecodeError)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(source.plane,role,calls),Err(error)),
    ensures part2_nested_legacy_result(source,role,Err(error)),
{
    reveal(part2_nested_legacy_result);reveal(part2_nested_legacy_run);
    part2_tier1_storage_eta(|calls|part2_nested_plane_run(source.plane,role,calls),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_nested_plane_run(source.plane,role,calls),|_:Tier1RawPlane,rest|part2_nested_legacy_after_plane(source,role,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_nested_legacy_flags_error(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,error:crate::DecodeError)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(source.plane,role,calls),Ok(source.plane)),
        part2_nested_bitplane_option_result(source.bitplane_state,role,true,Err(error)),
    ensures part2_nested_legacy_result(source,role,Err(error)),
{
    reveal(part2_nested_legacy_after_plane);
    part2_nested_option_frames(source.bitplane_state,|value,rest|part2_nested_bitplane_run(value,role,true,rest),Err(error));
    part2_tier1_storage_bind_frame(|calls|part2_nested_bitplane_option_run(source.bitplane_state,role,true,calls),|_:Option<Part1LegacyBitplane>,rest|
        part2_tier1_storage_bind(part2_nested_owner_run(Part2NestedCopyOwner::Input {source,role},rest),|_:(),tail|Some((Ok(source),tail))),Err(error),Err(error));
    part2_nested_legacy_join(source,role,Err(error));
}
pub(crate) proof fn part2_nested_legacy_observed(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,result:Result<(),crate::DecodeError>)
    requires part2_tier1_storage_framed(|calls|part2_nested_plane_run(source.plane,role,calls),Ok(source.plane)),
        part2_nested_bitplane_option_result(source.bitplane_state,role,true,Ok(source.bitplane_state)),
        part2_nested_owner_result(Part2NestedCopyOwner::Input {source,role},result),
    ensures part2_nested_legacy_result(source,role,match result{Err(error)=>Err(error),Ok(())=>Ok(source)}),
{
    reveal(part2_nested_legacy_after_plane);
    let value=match result{Err(error)=>Err(error),Ok(())=>Ok(source)};
    let after=|calls|part2_tier1_storage_bind(part2_nested_owner_run(Part2NestedCopyOwner::Input {source,role},calls),|_:(),tail|Some((Ok(source),tail)));
    part2_nested_owner_frames(Part2NestedCopyOwner::Input {source,role},result);
    if result.is_ok(){part2_tier1_storage_pure(Ok(source));}
    part2_tier1_storage_bind_frame(|calls|part2_nested_owner_run(Part2NestedCopyOwner::Input {source,role},calls),|_:(),tail|Some((Ok(source),tail)),result,value);
    part2_tier1_storage_eta(after,value);
    part2_nested_option_frames(source.bitplane_state,|value,rest|part2_nested_bitplane_run(value,role,true,rest),Ok(source.bitplane_state));
    part2_tier1_storage_bind_frame(|calls|part2_nested_bitplane_option_run(source.bitplane_state,role,true,calls),|_:Option<Part1LegacyBitplane>,rest|after(rest),Ok(source.bitplane_state),value);
    part2_nested_legacy_join(source,role,value);
}
pub(crate) proof fn part2_nested_legacy_normal(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_nested_legacy_result(source,role,Ok(source)),
{
    part2_nested_plane_observed(source.plane,role,Ok(()));
    part2_nested_bitplane_option_normal(source.bitplane_state,role,true);
    part2_nested_owner_observed(Part2NestedCopyOwner::Input {source,role},Ok(()));
    part2_nested_legacy_observed(source,role,Ok(()));
}
pub(crate) proof fn part2_nested_legacy_frames(source:Tier1LegacyFrame,role:crate::tier1::HtRefinementCopyRole,result:Result<Tier1LegacyFrame,crate::DecodeError>)
    requires part2_nested_legacy_result(source,role,result),
    ensures part2_tier1_storage_framed(|calls|part2_nested_legacy_run(source,role,calls),result),
        forall|other:spec_fn(Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Tier1LegacyFrame>|
            (forall|calls| #[trigger] other(calls)==part2_nested_legacy_run(source,role,calls)) ==> #[trigger] part2_tier1_storage_framed(other,result),
{reveal(part2_nested_legacy_result);part2_tier1_storage_eta(|calls|part2_nested_legacy_run(source,role,calls),result);}
pub(crate) open spec fn part2_nested_legacy_option_run(source:Option<Tier1LegacyFrame>,role:crate::tier1::HtRefinementCopyRole,calls:Seq<Part2Tier1StorageEvent>)->Part2Tier1Run<Option<Tier1LegacyFrame>> {
    part2_nested_option_run(source,|value,rest|part2_nested_legacy_run(value,role,rest),calls)
}
pub(crate) open spec fn part2_nested_legacy_option_result(source:Option<Tier1LegacyFrame>,role:crate::tier1::HtRefinementCopyRole,result:Result<Option<Tier1LegacyFrame>,crate::DecodeError>)->bool {
    part2_nested_option_result(source,|value,rest|part2_nested_legacy_run(value,role,rest),result)
}
pub(crate) proof fn part2_nested_legacy_option_normal(source:Option<Tier1LegacyFrame>,role:crate::tier1::HtRefinementCopyRole)
    ensures part2_nested_legacy_option_result(source,role,Ok(source)),
{
    let child=|value,rest|part2_nested_legacy_run(value,role,rest);
    match source{None=>{part2_nested_option_none(child);},Some(value)=>{
        part2_nested_legacy_normal(value,role);part2_nested_legacy_frames(value,role,Ok(value));
        part2_nested_option_observed(value,child,Ok(value));
    }}
}
}
