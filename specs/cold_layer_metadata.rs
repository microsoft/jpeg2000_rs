//! Admitted registration records and opaque chroma-key copies with framed replies.
use super::*;
verus! {
pub struct Part2RegistrationStorageContext {
    pub input:Part2BoxReference,
    pub base:u64,
    pub limits:crate::ResourceLimits,
}
pub struct Part2OpacityStorageContext {
    pub input:Part2BoxReference,
    pub base:u64,
}
pub enum Part2LayerMetadataCapacityContext {
    Registration {context:Part2RegistrationStorageContext},
    Opacity {context:Part2OpacityStorageContext},
}
pub(crate) open spec fn part2_registration_storage_count(context:Part2RegistrationStorageContext)->nat {
    let payload=context.input.1;
    if payload.len()<10 || (payload.len()-4)%6!=0 {0}else{
        let horizontal=part2_box_u16([payload[0],payload[1]]);
        let vertical=part2_box_u16([payload[2],payload[3]]);
        let count=((payload.len()-4)/6) as nat;
        if horizontal==0 || vertical==0 ||
            count as u64>crate::limits::resource_codestream_limit(&context.limits) as u64 {0}else{count}
    }
}
pub(crate) open spec fn part2_opacity_storage_count(context:Part2OpacityStorageContext)->nat {
    let payload=context.input.1;
    if !part2_box_add_offset(context.base,context.input.0.1).is_ok() {0}
    else if payload.len()<3 {0}
    else if payload[0]==2 && payload[1]!=0 {(payload.len()-2) as nat}else{0}
}
pub(crate) open spec fn part2_layer_metadata_capacity_count(context:Part2LayerMetadataCapacityContext)->nat {
    match context {
        Part2LayerMetadataCapacityContext::Registration {context}=>part2_registration_storage_count(context),
        Part2LayerMetadataCapacityContext::Opacity {context}=>part2_opacity_storage_count(context),
    }
}
pub(crate) open spec fn part2_layer_metadata_capacity_run(context:Part2LayerMetadataCapacityContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_layer_metadata_capacity_count(context);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::LayerMetadataCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_layer_metadata_capacity_result(context:Part2LayerMetadataCapacityContext,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_layer_metadata_capacity_run(context,events),result)
}
pub(crate) proof fn part2_layer_metadata_capacity_observed(context:Part2LayerMetadataCapacityContext,
    result:Result<(),crate::DecodeError>)
    requires result==Ok(()) || (result==Err(crate::DecodeError::AllocationFailed) &&
        part2_layer_metadata_capacity_count(context)>0),
    ensures part2_layer_metadata_capacity_result(context,result),
{
    let count=part2_layer_metadata_capacity_count(context);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::LayerMetadataCapacity {context,elements:count,succeeded:result.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_layer_metadata_capacity_run(context,prefix+tail)==Some((result,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_layer_metadata_capacity_run(context,events),prefix,result));
}
pub(crate) proof fn part2_layer_metadata_capacity_frames(context:Part2LayerMetadataCapacityContext,
    result:Result<(),crate::DecodeError>)
    requires part2_layer_metadata_capacity_result(context,result),
    ensures part2_cold_framed(|events|part2_layer_metadata_capacity_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_layer_metadata_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_layer_metadata_capacity_run(context,events),result);
}
pub(crate) open spec fn part2_registration_storage_run(context:Part2RegistrationStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawRegistration> {
    part2_jpip_snapshot_bind(part2_layer_metadata_capacity_run(
        Part2LayerMetadataCapacityContext::Registration {context},events),
        |_:(),rest|Some((part2_parse_codestream_registration(context.input,context.base,&context.limits),rest)))
}
pub closed spec fn part2_registration_storage_result(context:Part2RegistrationStorageContext,
    result:Result<Part2RawRegistration,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_registration_storage_run(context,events),result)
}
pub(crate) proof fn part2_registration_storage_normal(context:Part2RegistrationStorageContext)
    ensures part2_registration_storage_result(context,part2_parse_codestream_registration(context.input,context.base,&context.limits)),
{
    let capacity=Part2LayerMetadataCapacityContext::Registration {context};
    let result=part2_parse_codestream_registration(context.input,context.base,&context.limits);
    part2_layer_metadata_capacity_observed(capacity,Ok(()));part2_layer_metadata_capacity_frames(capacity,Ok(()));
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_layer_metadata_capacity_run(capacity,events),
        |_:(),rest|Some((result,rest)),Ok(()),result);
}
pub(crate) proof fn part2_registration_storage_refused(context:Part2RegistrationStorageContext,error:crate::DecodeError)
    requires part2_registration_storage_count(context)>0,
        part2_layer_metadata_capacity_result(Part2LayerMetadataCapacityContext::Registration {context},Err(error)),
    ensures part2_registration_storage_result(context,Err(error)),
{
    let capacity=Part2LayerMetadataCapacityContext::Registration {context};
    part2_layer_metadata_capacity_frames(capacity,Err(error));
    part2_cold_bind(|events|part2_layer_metadata_capacity_run(capacity,events),
        |_:(),rest|Some((part2_parse_codestream_registration(context.input,context.base,&context.limits),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_registration_storage_frames(context:Part2RegistrationStorageContext,
    result:Result<Part2RawRegistration,crate::DecodeError>)
    requires part2_registration_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_registration_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawRegistration>|
            (forall|events| #[trigger] other(events)==part2_registration_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_registration_storage_run(context,events),result);
}
pub(crate) open spec fn part2_opacity_storage_run(context:Part2OpacityStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2SourceOpacity> {
    part2_jpip_snapshot_bind(part2_layer_metadata_capacity_run(
        Part2LayerMetadataCapacityContext::Opacity {context},events),
        |_:(),rest|Some((part2_parse_layer_opacity(context.input,context.base),rest)))
}
pub closed spec fn part2_opacity_storage_result(context:Part2OpacityStorageContext,
    result:Result<Part2SourceOpacity,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_opacity_storage_run(context,events),result)
}
pub(crate) proof fn part2_opacity_storage_normal(context:Part2OpacityStorageContext)
    ensures part2_opacity_storage_result(context,part2_parse_layer_opacity(context.input,context.base)),
{
    let capacity=Part2LayerMetadataCapacityContext::Opacity {context};
    let result=part2_parse_layer_opacity(context.input,context.base);
    part2_layer_metadata_capacity_observed(capacity,Ok(()));part2_layer_metadata_capacity_frames(capacity,Ok(()));
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_layer_metadata_capacity_run(capacity,events),
        |_:(),rest|Some((result,rest)),Ok(()),result);
}
pub(crate) proof fn part2_opacity_storage_refused(context:Part2OpacityStorageContext,error:crate::DecodeError)
    requires part2_opacity_storage_count(context)>0,
        part2_layer_metadata_capacity_result(Part2LayerMetadataCapacityContext::Opacity {context},Err(error)),
    ensures part2_opacity_storage_result(context,Err(error)),
{
    let capacity=Part2LayerMetadataCapacityContext::Opacity {context};
    part2_layer_metadata_capacity_frames(capacity,Err(error));
    part2_cold_bind(|events|part2_layer_metadata_capacity_run(capacity,events),
        |_:(),rest|Some((part2_parse_layer_opacity(context.input,context.base),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_opacity_storage_frames(context:Part2OpacityStorageContext,
    result:Result<Part2SourceOpacity,crate::DecodeError>)
    requires part2_opacity_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_opacity_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2SourceOpacity>|
            (forall|events| #[trigger] other(events)==part2_opacity_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_opacity_storage_run(context,events),result);
}
}
