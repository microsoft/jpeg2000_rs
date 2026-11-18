//! Actual PCLR and CMAP collection requests at their original parser stages.
use super::*;
verus! {
pub struct Part2PaletteStorageContext {
    pub input:Part2BoxReference,
    pub base:u64,
}
pub enum Part2PaletteStorageRole {Columns,Values}
pub struct Part2MappingStorageContext {
    pub input:Part2BoxReference,
    pub components:u16,
    pub palette_columns:u8,
    pub limits:crate::ResourceLimits,
    pub base:u64,
}
pub(crate) open spec fn part2_palette_columns_admit(context:Part2PaletteStorageContext)->Result<(),crate::DecodeError> {
    let input=context.input;let base=context.base;let payload=input.1;
    if payload.len()<3 {Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxLength))}
    else {
        let entries=part2_box_u16([payload[0],payload[1]]);let count=payload[2] as nat;
        if entries==0 || entries>1024 || count==0 {
            Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxContents))
        }else if 3+count>usize::MAX as nat {Err(part2_palette_arithmetic_error(base))}
        else if 3+count>payload.len() {Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxLength))}
        else {Ok(())}
    }
}
pub(crate) open spec fn part2_palette_values_admit(context:Part2PaletteStorageContext)->Result<(),crate::DecodeError> {
    let input=context.input;let base=context.base;let payload=input.1;
    match part2_palette_columns_admit(context) {
        Err(error)=>Err(error),
        Ok(())=>match part2_palette_descriptors(input,base,payload[2] as nat) {
            Err(error)=>Err(error),
            Ok(descriptors)=>{
                let entries=part2_box_u16([payload[0],payload[1]]) as nat;
                let sample_bytes=entries*descriptors.1 as nat;
                let expected=3+payload[2] as nat+sample_bytes;
                let count=entries*descriptors.0.len();
                if sample_bytes>usize::MAX as nat || expected>usize::MAX as nat {
                    Err(part2_palette_arithmetic_error(base))
                }else if payload.len()!=expected {
                    Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxLength))
                }else if count>usize::MAX as nat {Err(part2_palette_arithmetic_error(base))}
                else {Ok(())}
            },
        },
    }
}
pub(crate) open spec fn part2_palette_capacity_count(context:Part2PaletteStorageContext,role:Part2PaletteStorageRole)->nat {
    match role {
        Part2PaletteStorageRole::Columns=>if part2_palette_columns_admit(context).is_ok() {context.input.1[2] as nat}else{0},
        Part2PaletteStorageRole::Values=>if part2_palette_values_admit(context).is_ok() {
            let descriptors=part2_palette_descriptors(context.input,context.base,context.input.1[2] as nat).get_Ok_0();
            part2_box_u16([context.input.1[0],context.input.1[1]]) as nat*descriptors.0.len()
        }else{0},
    }
}
pub(crate) open spec fn part2_palette_capacity_run(context:Part2PaletteStorageContext,role:Part2PaletteStorageRole,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_palette_capacity_count(context,role);
    if count==0 {Some((Ok(()),events))}else if events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::PaletteCapacity {context:actual,role:actual_role,elements,succeeded}=>
            if actual!=context || actual_role!=role || elements!=count {None}
            else {Some((if succeeded {Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_palette_capacity_result(context:Part2PaletteStorageContext,role:Part2PaletteStorageRole,
    response:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_palette_capacity_run(context,role,events),response)
}
pub(crate) proof fn part2_palette_capacity_observed(context:Part2PaletteStorageContext,role:Part2PaletteStorageRole,
    response:Result<(),crate::DecodeError>)
    requires response==Ok(()) ||
        (response==Err(crate::DecodeError::AllocationFailed) && part2_palette_capacity_count(context,role)>0),
    ensures part2_palette_capacity_result(context,role,response),
{
    let count=part2_palette_capacity_count(context,role);
    let prefix=if count==0 {Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::PaletteCapacity {context,role,elements:count,succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_palette_capacity_run(context,role,prefix+tail)==Some((response,tail)) by {
        if count==0 {assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_palette_capacity_run(context,role,events),prefix,response));
}
pub(crate) proof fn part2_palette_capacity_frames(context:Part2PaletteStorageContext,role:Part2PaletteStorageRole,
    response:Result<(),crate::DecodeError>)
    requires part2_palette_capacity_result(context,role,response),
    ensures part2_cold_framed(|events|part2_palette_capacity_run(context,role,events),response),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_palette_capacity_run(context,role,events)) ==>
                #[trigger] part2_cold_framed(other,response),
{
    part2_decode_eta(|events|part2_palette_capacity_run(context,role,events),response);
}
pub(crate) open spec fn part2_palette_storage_after_columns(context:Part2PaletteStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PaletteModel> {
    match part2_palette_values_admit(context) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>part2_jpip_snapshot_bind(part2_palette_capacity_run(context,Part2PaletteStorageRole::Values,events),
            |_:(),rest|Some((part2_parse_palette(context.input,context.base),rest))),
    }
}
pub(crate) open spec fn part2_palette_storage_run(context:Part2PaletteStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PaletteModel> {
    match part2_palette_columns_admit(context) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>part2_jpip_snapshot_bind(part2_palette_capacity_run(context,Part2PaletteStorageRole::Columns,events),
            |_:(),rest|part2_palette_storage_after_columns(context,rest)),
    }
}
pub closed spec fn part2_palette_storage_result(context:Part2PaletteStorageContext,
    result:Result<Part2PaletteModel,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_palette_storage_run(context,events),result)
}
pub(crate) proof fn part2_palette_storage_normal(context:Part2PaletteStorageContext)
    ensures part2_palette_storage_result(context,part2_parse_palette(context.input,context.base)),
{
    reveal(part2_parse_palette);
    let result=part2_parse_palette(context.input,context.base);
    part2_cold_pure(result);
    if part2_palette_columns_admit(context).is_ok() {
        if part2_palette_values_admit(context).is_ok() {
            part2_palette_capacity_observed(context,Part2PaletteStorageRole::Values,Ok(()));
            part2_palette_capacity_frames(context,Part2PaletteStorageRole::Values,Ok(()));
            part2_cold_bind(|events|part2_palette_capacity_run(context,Part2PaletteStorageRole::Values,events),
                |_:(),rest|Some((result,rest)),Ok(()),result);
        }
        part2_decode_eta(|events|part2_palette_storage_after_columns(context,events),result);
        part2_palette_capacity_observed(context,Part2PaletteStorageRole::Columns,Ok(()));
        part2_palette_capacity_frames(context,Part2PaletteStorageRole::Columns,Ok(()));
        part2_cold_bind(|events|part2_palette_capacity_run(context,Part2PaletteStorageRole::Columns,events),
            |_:(),rest|part2_palette_storage_after_columns(context,rest),Ok(()),result);
    }
}
pub(crate) proof fn part2_palette_storage_columns_refused(context:Part2PaletteStorageContext,error:crate::DecodeError)
    requires part2_palette_columns_admit(context)==Ok(()),
        part2_palette_capacity_result(context,Part2PaletteStorageRole::Columns,Err(error)),
    ensures part2_palette_storage_result(context,Err(error)),
{
    part2_palette_capacity_frames(context,Part2PaletteStorageRole::Columns,Err(error));
    part2_cold_bind(|events|part2_palette_capacity_run(context,Part2PaletteStorageRole::Columns,events),
        |_:(),rest|part2_palette_storage_after_columns(context,rest),Err(error),Err(error));
}
pub(crate) proof fn part2_palette_storage_values_refused(context:Part2PaletteStorageContext,error:crate::DecodeError)
    requires part2_palette_columns_admit(context)==Ok(()),part2_palette_values_admit(context)==Ok(()),
        part2_palette_capacity_result(context,Part2PaletteStorageRole::Columns,Ok(())),
        part2_palette_capacity_result(context,Part2PaletteStorageRole::Values,Err(error)),
    ensures part2_palette_storage_result(context,Err(error)),
{
    part2_palette_capacity_frames(context,Part2PaletteStorageRole::Values,Err(error));
    part2_cold_bind(|events|part2_palette_capacity_run(context,Part2PaletteStorageRole::Values,events),
        |_:(),rest|Some((part2_parse_palette(context.input,context.base),rest)),Err(error),Err(error));
    part2_decode_eta(|events|part2_palette_storage_after_columns(context,events),Err(error));
    part2_palette_capacity_frames(context,Part2PaletteStorageRole::Columns,Ok(()));
    part2_cold_bind(|events|part2_palette_capacity_run(context,Part2PaletteStorageRole::Columns,events),
        |_:(),rest|part2_palette_storage_after_columns(context,rest),Ok(()),Err(error));
}
pub(crate) proof fn part2_palette_storage_frames(context:Part2PaletteStorageContext,
    result:Result<Part2PaletteModel,crate::DecodeError>)
    requires part2_palette_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_palette_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2PaletteModel>|
            (forall|events| #[trigger] other(events)==part2_palette_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_palette_storage_run(context,events),result);
}

pub(crate) open spec fn part2_mapping_storage_admit(context:Part2MappingStorageContext)->Result<(),crate::DecodeError> {
    let length=context.input.1.len();let count=length/4;
    if length==0 || length%4!=0 {Err(part2_image_box_error(context.base,context.input.0,crate::MalformedKind::InvalidBoxLength))}
    else if count>u16::MAX as nat {Err(part2_palette_arithmetic_error(context.base))}
    else if count>crate::limits::resource_component_limit(&context.limits) {
        Err(crate::DecodeError::LimitExceeded {resource:crate::Resource::Components,
            limit:crate::limits::resource_component_limit(&context.limits) as u64,actual:count as u64})
    }else{Ok(())}
}
pub(crate) open spec fn part2_mapping_capacity_run(context:Part2MappingStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if !part2_mapping_storage_admit(context).is_ok() {Some((Ok(()),events))}
    else if events.len()==0 {None}else{match events[0] {
        Part2JpipSnapshotEvent::ComponentMappingCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=context.input.1.len()/4 {None}
            else{Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_mapping_capacity_result(context:Part2MappingStorageContext,response:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_mapping_capacity_run(context,events),response)
}
pub(crate) proof fn part2_mapping_capacity_observed(context:Part2MappingStorageContext,response:Result<(),crate::DecodeError>)
    requires part2_mapping_storage_admit(context).is_ok(),
        response==Ok(()) || response==Err(crate::DecodeError::AllocationFailed),
    ensures part2_mapping_capacity_result(context,response),
{
    let prefix=seq![Part2JpipSnapshotEvent::ComponentMappingCapacity {
        context,elements:context.input.1.len()/4,succeeded:response.is_ok()}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_mapping_capacity_run(context,prefix+tail)==Some((response,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_mapping_capacity_run(context,events),prefix,response));
}
pub(crate) proof fn part2_mapping_capacity_frames(context:Part2MappingStorageContext,response:Result<(),crate::DecodeError>)
    requires part2_mapping_capacity_result(context,response),
    ensures part2_cold_framed(|events|part2_mapping_capacity_run(context,events),response),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_mapping_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,response),
{
    part2_decode_eta(|events|part2_mapping_capacity_run(context,events),response);
}
pub(crate) open spec fn part2_mapping_storage_run(context:Part2MappingStorageContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<crate::jp2::ComponentMapping>> {
    match part2_mapping_storage_admit(context) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>part2_jpip_snapshot_bind(part2_mapping_capacity_run(context,events),
            |_:(),rest|Some((part2_parse_component_mapping(
                context.input,context.components,context.palette_columns,&context.limits,context.base),rest))),
    }
}
pub closed spec fn part2_mapping_storage_result(context:Part2MappingStorageContext,
    result:Result<Seq<crate::jp2::ComponentMapping>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_mapping_storage_run(context,events),result)
}
pub(crate) proof fn part2_mapping_storage_normal(context:Part2MappingStorageContext)
    ensures part2_mapping_storage_result(context,part2_parse_component_mapping(
        context.input,context.components,context.palette_columns,&context.limits,context.base)),
{
    reveal(part2_parse_component_mapping);
    let result=part2_parse_component_mapping(context.input,context.components,context.palette_columns,&context.limits,context.base);
    part2_cold_pure(result);
    if part2_mapping_storage_admit(context).is_ok() {
        part2_mapping_capacity_observed(context,Ok(()));part2_mapping_capacity_frames(context,Ok(()));
        part2_cold_bind(|events|part2_mapping_capacity_run(context,events),
            |_:(),rest|Some((result,rest)),Ok(()),result);
    }
}
pub(crate) proof fn part2_mapping_storage_refused(context:Part2MappingStorageContext,error:crate::DecodeError)
    requires part2_mapping_storage_admit(context)==Ok(()),part2_mapping_capacity_result(context,Err(error)),
    ensures part2_mapping_storage_result(context,Err(error)),
{
    part2_mapping_capacity_frames(context,Err(error));
    part2_cold_bind(|events|part2_mapping_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_component_mapping(
            context.input,context.components,context.palette_columns,&context.limits,context.base),rest)),
        Err(error),Err(error));
}
pub(crate) proof fn part2_mapping_storage_frames(context:Part2MappingStorageContext,
    result:Result<Seq<crate::jp2::ComponentMapping>,crate::DecodeError>)
    requires part2_mapping_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_mapping_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<crate::jp2::ComponentMapping>>|
            (forall|events| #[trigger] other(events)==part2_mapping_storage_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_mapping_storage_run(context,events),result);
}

pub enum Part2HeaderStorageRequest {
    Channel {context:Part2ChannelStorageContext},
    Palette {context:Part2PaletteStorageContext},
    Mapping {context:Part2MappingStorageContext},
    Color {context:Part2ColorStorageContext},
    ColorGroup {context:Part2ColorGroupStorageContext},
    Registration {context:Part2RegistrationStorageContext},
    Opacity {context:Part2OpacityStorageContext},
}
pub(crate) open spec fn part2_header_storage_request_value(request:Part2HeaderStorageRequest)->Result<(),crate::DecodeError> {
    match request {
        Part2HeaderStorageRequest::Channel {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_channel_definition(context.input,context.channels,context.base)),
        Part2HeaderStorageRequest::Palette {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_palette(context.input,context.base)),
        Part2HeaderStorageRequest::Mapping {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_component_mapping(context.input,context.components,context.palette_columns,&context.limits,context.base)),
        Part2HeaderStorageRequest::Color {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_color_specification(context.input,context.base)),
        Part2HeaderStorageRequest::ColorGroup {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_color_group(context.input,context.limits,context.base)),
        Part2HeaderStorageRequest::Registration {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_codestream_registration(context.input,context.base,&context.limits)),
        Part2HeaderStorageRequest::Opacity {context}=>crate::allocation::inspection_capacity_outcome(
            part2_parse_layer_opacity(context.input,context.base)),
    }
}
pub(crate) open spec fn part2_header_storage_request_run(request:Part2HeaderStorageRequest,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    match request {
        Part2HeaderStorageRequest::Channel {context}=>part2_jpip_snapshot_bind(part2_channel_storage_run(context,events),
            |_:Seq<Part2ChannelRecord>,rest|Some((Ok(()),rest))),
        Part2HeaderStorageRequest::Palette {context}=>part2_jpip_snapshot_bind(part2_palette_storage_run(context,events),
            |_:Part2PaletteModel,rest|Some((Ok(()),rest))),
        Part2HeaderStorageRequest::Mapping {context}=>part2_jpip_snapshot_bind(part2_mapping_storage_run(context,events),
            |_:Seq<crate::jp2::ComponentMapping>,rest|Some((Ok(()),rest))),
        Part2HeaderStorageRequest::Color {context}=>part2_jpip_snapshot_bind(part2_color_storage_run(context,events),
            |_:Part2ColorSpecification,rest|Some((Ok(()),rest))),
        Part2HeaderStorageRequest::ColorGroup {context}=>part2_jpip_snapshot_bind(part2_color_group_storage_run(context,events),
            |_:Seq<Part2ColorSpecification>,rest|Some((Ok(()),rest))),
        Part2HeaderStorageRequest::Registration {context}=>part2_jpip_snapshot_bind(part2_registration_storage_run(context,events),
            |_:Part2RawRegistration,rest|Some((Ok(()),rest))),
        Part2HeaderStorageRequest::Opacity {context}=>part2_jpip_snapshot_bind(part2_opacity_storage_run(context,events),
            |_:Part2SourceOpacity,rest|Some((Ok(()),rest))),
    }
}
pub closed spec fn part2_header_storage_request_result(request:Part2HeaderStorageRequest,
    result:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_header_storage_request_run(request,events),result)
}
pub(crate) proof fn part2_header_storage_discard_frame<A>(
    run:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<A>,result:Result<A,crate::DecodeError>)
    requires part2_cold_framed(run,result),
    ensures part2_cold_framed(|events|part2_jpip_snapshot_bind(run(events),
        |_:A,rest|Some((Ok(()),rest))),crate::allocation::inspection_capacity_outcome(result)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_jpip_snapshot_bind(run(events),
                |_:A,rest|Some((Ok(()),rest)))) ==>
                    #[trigger] part2_cold_framed(other,crate::allocation::inspection_capacity_outcome(result)),
{
    let response=crate::allocation::inspection_capacity_outcome(result);
    if result.is_ok() {part2_cold_pure(Ok(()));}
    part2_cold_bind(run,|_:A,rest|Some((Ok(()),rest)),result,response);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(run(events),|_:A,rest|Some((Ok(()),rest))),response);
}
pub(crate) proof fn part2_header_storage_request_normal(request:Part2HeaderStorageRequest)
    ensures part2_header_storage_request_result(request,part2_header_storage_request_value(request)),
{
    match request {
        Part2HeaderStorageRequest::Channel {context}=>{
            let result=part2_parse_channel_definition(context.input,context.channels,context.base);
            part2_channel_storage_normal(context);part2_channel_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_channel_storage_run(context,events),result);
        },
        Part2HeaderStorageRequest::Palette {context}=>{
            let result=part2_parse_palette(context.input,context.base);
            part2_palette_storage_normal(context);part2_palette_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_palette_storage_run(context,events),result);
        },
        Part2HeaderStorageRequest::Mapping {context}=>{
            let result=part2_parse_component_mapping(context.input,context.components,context.palette_columns,&context.limits,context.base);
            part2_mapping_storage_normal(context);part2_mapping_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_mapping_storage_run(context,events),result);
        },
        Part2HeaderStorageRequest::Color {context}=>{
            let result=part2_parse_color_specification(context.input,context.base);
            part2_color_storage_normal(context);part2_color_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_color_storage_run(context,events),result);
        },
        Part2HeaderStorageRequest::ColorGroup {context}=>{
            let result=part2_parse_color_group(context.input,context.limits,context.base);
            part2_color_group_storage_normal(context);part2_color_group_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_color_group_storage_run(context,events),result);
        },
        Part2HeaderStorageRequest::Registration {context}=>{
            let result=part2_parse_codestream_registration(context.input,context.base,&context.limits);
            part2_registration_storage_normal(context);part2_registration_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_registration_storage_run(context,events),result);
        },
        Part2HeaderStorageRequest::Opacity {context}=>{
            let result=part2_parse_layer_opacity(context.input,context.base);
            part2_opacity_storage_normal(context);part2_opacity_storage_frames(context,result);
            part2_header_storage_discard_frame(|events|part2_opacity_storage_run(context,events),result);
        },
    }
}
pub(crate) proof fn part2_header_storage_request_channel_error(context:Part2ChannelStorageContext,error:crate::DecodeError)
    requires part2_channel_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::Channel {context},Err(error)),
{
    part2_channel_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_channel_storage_run(context,events),Err(error));
}
pub(crate) proof fn part2_header_storage_request_palette_error(context:Part2PaletteStorageContext,error:crate::DecodeError)
    requires part2_palette_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::Palette {context},Err(error)),
{
    part2_palette_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_palette_storage_run(context,events),Err(error));
}
pub(crate) proof fn part2_header_storage_request_mapping_error(context:Part2MappingStorageContext,error:crate::DecodeError)
    requires part2_mapping_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::Mapping {context},Err(error)),
{
    part2_mapping_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_mapping_storage_run(context,events),Err(error));
}
pub(crate) proof fn part2_header_storage_request_frames(request:Part2HeaderStorageRequest,
    result:Result<(),crate::DecodeError>)
    requires part2_header_storage_request_result(request,result),
    ensures part2_cold_framed(|events|part2_header_storage_request_run(request,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_header_storage_request_run(request,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_header_storage_request_run(request,events),result);
}
pub(crate) proof fn part2_header_storage_request_color_error(context:Part2ColorStorageContext,error:crate::DecodeError)
    requires part2_color_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::Color {context},Err(error)),
{
    part2_color_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_color_storage_run(context,events),Err(error));
}
pub(crate) proof fn part2_header_storage_request_color_group_error(context:Part2ColorGroupStorageContext,error:crate::DecodeError)
    requires part2_color_group_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::ColorGroup {context},Err(error)),
{
    part2_color_group_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_color_group_storage_run(context,events),Err(error));
}
pub(crate) proof fn part2_header_storage_request_registration_error(context:Part2RegistrationStorageContext,error:crate::DecodeError)
    requires part2_registration_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::Registration {context},Err(error)),
{
    part2_registration_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_registration_storage_run(context,events),Err(error));
}
pub(crate) proof fn part2_header_storage_request_opacity_error(context:Part2OpacityStorageContext,error:crate::DecodeError)
    requires part2_opacity_storage_result(context,Err(error)),
    ensures part2_header_storage_request_result(Part2HeaderStorageRequest::Opacity {context},Err(error)),
{
    part2_opacity_storage_frames(context,Err(error));
    part2_header_storage_discard_frame(|events|part2_opacity_storage_run(context,events),Err(error));
}
}
