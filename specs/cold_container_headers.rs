//! Actual admitted main, associated and layer header calls in container order.
use super::*;
verus! {
pub enum Part2ContainerHeaderRequest {
    Main {payload:Seq<u8>,base:u64,allow:bool},
    Associated {payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,base:u64},
    Layer {input:Part2BoxReference},
}
pub struct Part2AssociationAppendContext {
    pub input:Part2BoxReference,
    pub before:Part2RawContainerState,
    pub file_type:Part2FileType,
    pub limits:crate::ResourceLimits,
    pub parsed:Part2RawJp2Header,
}
pub(crate) open spec fn part2_association_append_admitted(context:Part2AssociationAppendContext)->bool {
    match part2_container_header_request(context.input,context.before,context.file_type,context.limits) {
        Some(Part2ContainerHeaderRequest::Associated {payload,defaults,base})=>
            part2_parse_codestream_header(payload,defaults,context.limits,base)==Ok(context.parsed),
        _=>false,
    }
}
pub(crate) open spec fn part2_association_append_capacity_run(context:Part2AssociationAppendContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    if !part2_association_append_admitted(context) || events.len()==0 {None}
    else {match events[0] {
        Part2JpipSnapshotEvent::AssociationAppendCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=1 {None}
            else {Some((if succeeded {Ok(())} else {Err(crate::DecodeError::AllocationFailed)},events.drop_first()))},
        _=>None,
    }}
}
pub closed spec fn part2_association_append_capacity_result(context:Part2AssociationAppendContext,
    response:Result<(),crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_association_append_capacity_run(context,events),response)
}
pub(crate) proof fn part2_association_append_capacity_observed(context:Part2AssociationAppendContext,
    response:Result<(),crate::DecodeError>)
    requires part2_association_append_admitted(context),
        response==Ok(()) || response==Err(crate::DecodeError::AllocationFailed),
    ensures part2_association_append_capacity_result(context,response),
{
    let prefix=seq![Part2JpipSnapshotEvent::AssociationAppendCapacity {context,elements:1,succeeded:response.is_ok()}];
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_association_append_capacity_run(context,prefix+tail)==Some((response,tail)) by {
        assert((prefix+tail).drop_first() =~= tail);
    }
    assert(part2_cold_prefix(|events|part2_association_append_capacity_run(context,events),prefix,response));
}
pub(crate) proof fn part2_association_append_capacity_frames(context:Part2AssociationAppendContext,
    response:Result<(),crate::DecodeError>)
    requires part2_association_append_capacity_result(context,response),
    ensures part2_cold_framed(|events|part2_association_append_capacity_run(context,events),response),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()>|
            (forall|events| #[trigger] other(events)==part2_association_append_capacity_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,response),
{
    part2_decode_eta(|events|part2_association_append_capacity_run(context,events),response);
}
pub(crate) open spec fn part2_container_association_append_run(context:Part2AssociationAppendContext,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawContainerState> {
    part2_jpip_snapshot_bind(part2_association_append_capacity_run(context,events),
        |_:(),rest|Some((part2_container_step(context.input,context.before,context.file_type,context.limits),rest)))
}
pub(crate) proof fn part2_container_association_append_normal(context:Part2AssociationAppendContext)
    requires part2_association_append_admitted(context),
    ensures part2_cold_framed(|events|part2_container_association_append_run(context,events),
        part2_container_step(context.input,context.before,context.file_type,context.limits)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawContainerState>|
            (forall|events| #[trigger] other(events)==part2_container_association_append_run(context,events)) ==>
                #[trigger] part2_cold_framed(other,part2_container_step(context.input,context.before,context.file_type,context.limits)),
{
    let result=part2_container_step(context.input,context.before,context.file_type,context.limits);
    part2_association_append_capacity_observed(context,Ok(()));
    part2_association_append_capacity_frames(context,Ok(()));
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_association_append_capacity_run(context,events),
        |_:(),rest|Some((result,rest)),Ok(()),result);
    part2_decode_eta(|events|part2_container_association_append_run(context,events),result);
}
pub(crate) open spec fn part2_container_header_request(input:Part2BoxReference,state:Part2RawContainerState,
    file_type:Part2FileType,limits:crate::ResourceLimits)->Option<Part2ContainerHeaderRequest> {
    if state.box_count==u64::MAX{None}else if input.0.0==crate::jp2::BoxType::JP2_HEADER{
        if state.header.is_some() || state.streams.len()>0 || state.associations.len()>0 || state.layers.len()>0 || state.composition.is_some(){None}
        else{match part2_box_payload_offset(input.0){
            Err(_)=>None,Ok(base)=>Some(Part2ContainerHeaderRequest::Main {payload:input.1,base,
                allow:part2_file_type_compatible(file_type,crate::jp2::BoxType::JPH_BRAND)}),
        }}
    }else if input.0.0==crate::jp2::BoxType::CODESTREAM_HEADER{
        if !part2_file_type_jpx(file_type) || state.header.is_none() || state.streams.len()>0{None}
        else if part2_container_next_stream_count(state.associations.len(),limits,input.0.1).is_err(){None}
        else{match part2_box_payload_offset(input.0){
            Err(_)=>None,Ok(base)=>Some(Part2ContainerHeaderRequest::Associated {payload:input.1,defaults:state.header,base}),
        }}
    }else if input.0.0==crate::jp2::BoxType::COMPOSITING_LAYER_HEADER{
        if !part2_file_type_jpx(file_type) || state.header.is_none() || state.streams.len()>0 || state.composition.is_some()
            || state.layers.len()>=usize::MAX || state.layers.len()+1>crate::limits::resource_layer_limit(&limits) as nat{None}
        else{Some(Part2ContainerHeaderRequest::Layer {input})}
    }else{None}
}
pub(crate) open spec fn part2_container_headers_run(input:Part2BoxReference,state:Part2RawContainerState,
    file_type:Part2FileType,limits:crate::ResourceLimits,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawContainerState> {
    let result=part2_container_step(input,state,file_type,limits);
    match part2_container_header_request(input,state,file_type,limits){
        None=>Some((result,events)),
        Some(Part2ContainerHeaderRequest::Main {payload,base,allow})=>
            part2_jpip_snapshot_bind(part2_jp2_header_storage_run(payload,limits,base,allow,events),
                |_:Part2RawJp2Header,rest|Some((result,rest))),
        Some(Part2ContainerHeaderRequest::Associated {payload,defaults,base})=>
            part2_jpip_snapshot_bind(part2_codestream_header_storage_run(payload,defaults,limits,base,events),
                |parsed:Part2RawJp2Header,rest|part2_container_association_append_run(
                    Part2AssociationAppendContext {input,before:state,file_type,limits,parsed},rest)),
        Some(Part2ContainerHeaderRequest::Layer {input:layer})=>
            part2_jpip_snapshot_bind(part2_layer_header_storage_run(layer,limits,events),
                |_:Part2RawCompositingLayer,rest|Some((result,rest))),
    }
}
pub(crate) proof fn part2_container_headers_normal(input:Part2BoxReference,state:Part2RawContainerState,
    file_type:Part2FileType,limits:crate::ResourceLimits)
    ensures part2_cold_framed(|events|part2_container_headers_run(input,state,file_type,limits,events),part2_container_step(input,state,file_type,limits)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawContainerState>|
            (forall|events| #[trigger] other(events)==part2_container_headers_run(input,state,file_type,limits,events)) ==>
                #[trigger] part2_cold_framed(other,part2_container_step(input,state,file_type,limits)),
{
    reveal(part2_container_step);
    crate::jp2::channel_storage_box_kinds_known();
    let result=part2_container_step(input,state,file_type,limits);part2_cold_pure(result);
    match part2_container_header_request(input,state,file_type,limits){
        None=>{},
        Some(Part2ContainerHeaderRequest::Main {payload,base,allow})=>{
            let parsed=part2_parse_jp2_header_profile(payload,limits,base,allow);
            assert(parsed.is_err() ==> result==Err(parsed.get_Err_0()));
            part2_jp2_header_storage_normal(payload,limits,base,allow);part2_jp2_header_storage_frames(payload,limits,base,allow,parsed);
            part2_cold_bind(|events|part2_jp2_header_storage_run(payload,limits,base,allow,events),
                |_:Part2RawJp2Header,rest|Some((result,rest)),parsed,result);
        },
        Some(Part2ContainerHeaderRequest::Associated {payload,defaults,base})=>{
            let parsed=part2_parse_codestream_header(payload,defaults,limits,base);
            assert(parsed.is_err() ==> result==Err(parsed.get_Err_0()));
            part2_codestream_header_storage_normal(payload,defaults,limits,base);part2_codestream_header_storage_frames(payload,defaults,limits,base,parsed);
            if let Ok(header)=parsed {
                part2_container_association_append_normal(Part2AssociationAppendContext {
                    input,before:state,file_type,limits,parsed:header});
            }
            part2_cold_bind(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),
                |header:Part2RawJp2Header,rest|part2_container_association_append_run(
                    Part2AssociationAppendContext {input,before:state,file_type,limits,parsed:header},rest),parsed,result);
        },
        Some(Part2ContainerHeaderRequest::Layer {input:layer})=>{
            let parsed=part2_parse_compositing_layer(layer,limits);
            part2_layer_header_storage_normal(layer,limits);part2_layer_header_storage_frames(layer,limits,parsed);
            part2_cold_bind(|events|part2_layer_header_storage_run(layer,limits,events),
                |_:Part2RawCompositingLayer,rest|Some((result,rest)),parsed,result);
        },
    }
    part2_decode_eta(|events|part2_container_headers_run(input,state,file_type,limits,events),result);
}
pub(crate) proof fn part2_container_main_header_error(input:Part2BoxReference,state:Part2RawContainerState,file_type:Part2FileType,
    limits:crate::ResourceLimits,payload:Seq<u8>,base:u64,allow:bool,error:crate::DecodeError)
    requires part2_container_header_request(input,state,file_type,limits)==Some(Part2ContainerHeaderRequest::Main {payload,base,allow}),
        part2_jp2_header_storage_result(payload,limits,base,allow,Err(error)),
    ensures part2_cold_framed(|events|part2_container_step_cold_run(input,state,file_type,limits,events),Err(error)),
{
    crate::jp2::channel_storage_box_kinds_known();
    assert(!part2_container_step_reserves(input,state,file_type,limits));
    part2_jp2_header_storage_frames(payload,limits,base,allow,Err(error));
    part2_cold_bind(|events|part2_jp2_header_storage_run(payload,limits,base,allow,events),
        |_:Part2RawJp2Header,rest|Some((part2_container_step(input,state,file_type,limits),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_container_associated_header_error(input:Part2BoxReference,state:Part2RawContainerState,file_type:Part2FileType,
    limits:crate::ResourceLimits,payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,base:u64,error:crate::DecodeError)
    requires part2_container_header_request(input,state,file_type,limits)==Some(Part2ContainerHeaderRequest::Associated {payload,defaults,base}),
        part2_codestream_header_storage_result(payload,defaults,limits,base,Err(error)),
    ensures part2_cold_framed(|events|part2_container_step_cold_run(input,state,file_type,limits,events),Err(error)),
{
    crate::jp2::channel_storage_box_kinds_known();
    assert(!part2_container_step_reserves(input,state,file_type,limits));
    part2_codestream_header_storage_frames(payload,defaults,limits,base,Err(error));
    part2_cold_bind(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),
        |header:Part2RawJp2Header,rest|part2_container_association_append_run(
            Part2AssociationAppendContext {input,before:state,file_type,limits,parsed:header},rest),Err(error),Err(error));
}
pub(crate) proof fn part2_container_association_append_error(context:Part2AssociationAppendContext,error:crate::DecodeError)
    requires part2_association_append_admitted(context),
        part2_codestream_header_storage_result(context.input.1,context.before.header,context.limits,
            part2_box_payload_offset(context.input.0).get_Ok_0(),Ok(context.parsed)),
        part2_association_append_capacity_result(context,Err(error)),
    ensures part2_cold_framed(|events|part2_container_step_cold_run(
        context.input,context.before,context.file_type,context.limits,events),Err(error)),
{
    let input=context.input;let state=context.before;let file_type=context.file_type;let limits=context.limits;
    let payload=input.1;let defaults=state.header;let base=part2_box_payload_offset(input.0).get_Ok_0();
    crate::jp2::channel_storage_box_kinds_known();
    assert(!part2_container_step_reserves(input,state,file_type,limits));
    part2_association_append_capacity_frames(context,Err(error));
    part2_cold_bind(|events|part2_association_append_capacity_run(context,events),
        |_:(),rest|Some((part2_container_step(input,state,file_type,limits),rest)),Err(error),Err(error));
    part2_decode_eta(|events|part2_container_association_append_run(context,events),Err(error));
    part2_codestream_header_storage_frames(payload,defaults,limits,base,Ok(context.parsed));
    part2_cold_bind(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),
        |header:Part2RawJp2Header,rest|part2_container_association_append_run(
            Part2AssociationAppendContext {input,before:state,file_type,limits,parsed:header},rest),
        Ok(context.parsed),Err(error));
}
pub(crate) proof fn part2_container_layer_header_error(input:Part2BoxReference,state:Part2RawContainerState,file_type:Part2FileType,
    limits:crate::ResourceLimits,layer:Part2BoxReference,error:crate::DecodeError)
    requires part2_container_header_request(input,state,file_type,limits)==Some(Part2ContainerHeaderRequest::Layer {input:layer}),
        part2_layer_header_storage_result(layer,limits,Err(error)),
    ensures part2_cold_framed(|events|part2_container_step_cold_run(input,state,file_type,limits,events),Err(error)),
{
    crate::jp2::channel_storage_box_kinds_known();
    assert(!part2_container_step_reserves(input,state,file_type,limits));
    part2_layer_header_storage_frames(layer,limits,Err(error));
    part2_cold_bind(|events|part2_layer_header_storage_run(layer,limits,events),
        |_:Part2RawCompositingLayer,rest|Some((part2_container_step(input,state,file_type,limits),rest)),Err(error),Err(error));
}
pub(crate) proof fn part2_parse_container_header_error(input:Seq<u8>,limits:crate::ResourceLimits,file_type:Part2FileType,
    prefix:Seq<Part2JpipSnapshotEvent>,before_reader:Part2BoxReaderState,before:Part2RawContainerState,
    reader:Part2BoxReaderState,box_ref:Part2BoxReference,error:crate::DecodeError)
    requires forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input,limits,prefix+tail)==part2_container_boxes_cold_run(input,before_reader,before,file_type,limits,tail),
        part2_box_reader_next_ref(before_reader)==(Some(Ok(box_ref)),reader),before_reader.position<reader.position<=input.len(),
        part2_cold_framed(|events|part2_container_step_cold_run(box_ref,before,file_type,limits,events),Err(error)),
    ensures part2_parse_container_cold_result(input,limits,Err(error)),
{
    let run=|events|part2_container_step_cold_run(box_ref,before,file_type,limits,events);
    let calls=part2_cold_witness(run,Err(error));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_parse_container_cold_run(input,limits,(prefix+calls)+tail)==Some((Err(error),tail)) by{
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
        part2_cold_prefix_at(run,calls,Err(error),tail);
        assert(part2_parse_container_cold_run(input,limits,prefix+(calls+tail))
            ==part2_container_boxes_cold_run(input,before_reader,before,file_type,limits,calls+tail));
        assert(part2_container_step_cold_run(box_ref,before,file_type,limits,calls+tail)==Some((Err(error),tail)));
        reveal_with_fuel(part2_container_boxes_cold_run,1);
        reveal(part2_jpip_snapshot_bind);
    }
    assert(part2_cold_prefix(|events|part2_parse_container_cold_run(input,limits,events),prefix+calls,Err(error)));
    part2_parse_container_cold_observed(input,limits,Err(error));
}

pub(crate) open spec fn part2_container_attach_storage_update(streams:Seq<Part2RawCodestream>,index:nat,
    association:Part2RawCodestreamAssociation)->Seq<Part2RawCodestream> {
    streams.update(index as int,(streams[index as int].0,streams[index as int].1,Some(association)))
}
#[verifier::opaque]
pub(crate) open spec fn part2_container_attach_storage_run(state:Part2RawContainerState,count:nat,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2RawCodestream>>
    decreases count,
{
    if count==0 {Some((Ok(state.streams),events))}
    else {part2_jpip_snapshot_bind(part2_container_attach_storage_run(state,(count-1) as nat,events),
        |streams:Seq<Part2RawCodestream>,rest|part2_jpip_snapshot_bind(
            part2_association_clone_storage_run(state.associations[count-1],rest),
            |association:Part2RawCodestreamAssociation,tail|Some((Ok(
                part2_container_attach_storage_update(streams,(count-1) as nat,association)),tail))))}
}
pub closed spec fn part2_container_attach_storage_result(state:Part2RawContainerState,count:nat,
    result:Result<Seq<Part2RawCodestream>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_container_attach_storage_run(state,count,events),result)
}
pub(crate) proof fn part2_container_attach_storage_update_normal(state:Part2RawContainerState,index:nat)
    requires index<state.associations.len(),index<state.streams.len(),
    ensures part2_container_attach_storage_update(
        part2_container_attach(state.streams,state.associations,index),index,state.associations[index as int])
            ==part2_container_attach(state.streams,state.associations,index+1),
{
    let before=part2_container_attach(state.streams,state.associations,index);
    let after=part2_container_attach_storage_update(before,index,state.associations[index as int]);
    assert forall|i:int|0<=i<state.streams.len() implies
        after[i]==part2_container_attach(state.streams,state.associations,index+1)[i] by {};
    assert(after =~= part2_container_attach(state.streams,state.associations,index+1));
}
pub(crate) proof fn part2_container_attach_storage_normal(state:Part2RawContainerState,count:nat)
    requires count<=state.associations.len(),count<=state.streams.len(),
    ensures part2_container_attach_storage_result(state,count,
        Ok(part2_container_attach(state.streams,state.associations,count))),
    decreases count,
{
    reveal_with_fuel(part2_container_attach_storage_run,1);
    let result=Ok(part2_container_attach(state.streams,state.associations,count));
    if count==0 {
        assert(part2_container_attach(state.streams,state.associations,0) =~= state.streams);
        part2_cold_pure(result);
    }
    else {
        let index=(count-1) as nat;
        let before=part2_container_attach(state.streams,state.associations,index);
        let source=state.associations[index as int];
        part2_container_attach_storage_normal(state,index);
        part2_association_clone_storage_normal(source);
        part2_association_clone_storage_frames(source,Ok(source));
        part2_container_attach_storage_update_normal(state,index);
        part2_cold_pure(result);
        part2_cold_bind(|events|part2_association_clone_storage_run(source,events),
            |association:Part2RawCodestreamAssociation,tail|Some((Ok(
                part2_container_attach_storage_update(before,index,association)),tail)),Ok(source),result);
        part2_decode_eta(|events|part2_jpip_snapshot_bind(
            part2_association_clone_storage_run(source,events),
            |association:Part2RawCodestreamAssociation,tail|Some((Ok(
                part2_container_attach_storage_update(before,index,association)),tail))),result);
        part2_cold_bind(|events|part2_container_attach_storage_run(state,index,events),
            |streams:Seq<Part2RawCodestream>,rest|part2_jpip_snapshot_bind(
                part2_association_clone_storage_run(source,rest),
                |association:Part2RawCodestreamAssociation,tail|Some((Ok(
                    part2_container_attach_storage_update(streams,index,association)),tail))),Ok(before),result);
    }
}
pub(crate) proof fn part2_container_attach_storage_error(state:Part2RawContainerState,from:nat,to:nat,error:crate::DecodeError)
    requires from<=to,part2_container_attach_storage_result(state,from,Err(error)),
    ensures part2_container_attach_storage_result(state,to,Err(error)),
    decreases to-from,
{
    if from<to {
        reveal_with_fuel(part2_container_attach_storage_run,1);
        part2_container_attach_storage_error(state,from,(to-1) as nat,error);
        part2_cold_bind(|events|part2_container_attach_storage_run(state,(to-1) as nat,events),
            |streams:Seq<Part2RawCodestream>,rest|part2_jpip_snapshot_bind(
                part2_association_clone_storage_run(state.associations[to-1],rest),
                |association:Part2RawCodestreamAssociation,tail|Some((Ok(
                    part2_container_attach_storage_update(streams,(to-1) as nat,association)),tail))),
            Err(error),Err(error));
    }
}
pub(crate) proof fn part2_container_attach_storage_stage(state:Part2RawContainerState,index:nat,
    before:Seq<Part2RawCodestream>,result:Result<Part2RawCodestreamAssociation,crate::DecodeError>)
    requires index<state.associations.len(),index<before.len(),
        part2_container_attach_storage_result(state,index,Ok(before)),
        part2_association_clone_storage_result(state.associations[index as int],result),
    ensures match result {
        Err(error)=>part2_container_attach_storage_result(state,state.associations.len(),Err(error)),
        Ok(association)=>part2_container_attach_storage_result(state,index+1,
            Ok(part2_container_attach_storage_update(before,index,association))),
    },
{
    reveal_with_fuel(part2_container_attach_storage_run,1);
    let outcome=match result {Err(error)=>Err(error),
        Ok(association)=>Ok(part2_container_attach_storage_update(before,index,association))};
    part2_association_clone_storage_frames(state.associations[index as int],result);
    if result.is_ok() {part2_cold_pure(outcome);}
    part2_cold_bind(|events|part2_association_clone_storage_run(state.associations[index as int],events),
        |association:Part2RawCodestreamAssociation,tail|Some((Ok(
            part2_container_attach_storage_update(before,index,association)),tail)),result,outcome);
    part2_decode_eta(|events|part2_jpip_snapshot_bind(
        part2_association_clone_storage_run(state.associations[index as int],events),
        |association:Part2RawCodestreamAssociation,tail|Some((Ok(
            part2_container_attach_storage_update(before,index,association)),tail))),outcome);
    part2_cold_bind(|events|part2_container_attach_storage_run(state,index,events),
        |streams:Seq<Part2RawCodestream>,rest|part2_jpip_snapshot_bind(
            part2_association_clone_storage_run(state.associations[index as int],rest),
            |association:Part2RawCodestreamAssociation,tail|Some((Ok(
                part2_container_attach_storage_update(streams,index,association)),tail))),Ok(before),outcome);
    if let Err(error)=result {
        part2_container_attach_storage_error(state,index+1,state.associations.len(),error);
    }
}
pub(crate) open spec fn part2_container_finish_storage_admit(state:Part2RawContainerState)->Result<(),crate::DecodeError> {
    if state.header.is_none() || state.streams.len()==0 {Err(part2_raw_header_missing(0))}
    else if state.associations.len()!=0 && state.associations.len()!=state.streams.len() {
        Err(part2_container_error(0,crate::MalformedKind::InvalidBoxContents))
    }else {Ok(())}
}
pub(crate) open spec fn part2_container_finish_storage_tail(state:Part2RawContainerState,file_type:Part2FileType,
    streams:Seq<Part2RawCodestream>)->Result<Part2RawJp2File,crate::DecodeError> {
    match part2_validate_layer_references(state.layers,state.streams.len() as usize) {
        Err(error)=>Err(error),
        Ok(())=>Ok(Part2RawJp2File {
            file_type,header:state.header.get_Some_0(),streams,layers:state.layers,composition:state.composition,
            metadata_boxes:state.metadata_boxes,metadata_depth:state.metadata_depth,box_count:state.box_count,
        }),
    }
}
pub(crate) open spec fn part2_container_finish_storage_run(state:Part2RawContainerState,file_type:Part2FileType,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2File> {
    match part2_container_finish_storage_admit(state) {
        Err(error)=>Some((Err(error),events)),
        Ok(())=>part2_jpip_snapshot_bind(part2_container_attach_storage_run(state,state.associations.len(),events),
            |streams:Seq<Part2RawCodestream>,rest|Some((part2_container_finish_storage_tail(state,file_type,streams),rest))),
    }
}
pub closed spec fn part2_container_finish_storage_result(state:Part2RawContainerState,file_type:Part2FileType,
    result:Result<Part2RawJp2File,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_container_finish_storage_run(state,file_type,events),result)
}
pub(crate) proof fn part2_container_finish_storage_normal(state:Part2RawContainerState,file_type:Part2FileType)
    ensures part2_container_finish_storage_result(state,file_type,part2_container_finish(state,file_type)),
{
    reveal(part2_container_finish);
    let result=part2_container_finish(state,file_type);
    part2_cold_pure(result);
    if part2_container_finish_storage_admit(state).is_ok() {
        let streams=part2_container_attach(state.streams,state.associations,state.associations.len());
        part2_container_attach_storage_normal(state,state.associations.len());
        part2_decode_eta(|events|part2_container_attach_storage_run(state,state.associations.len(),events),Ok(streams));
        part2_cold_bind(|events|part2_container_attach_storage_run(state,state.associations.len(),events),
            |streams:Seq<Part2RawCodestream>,rest|Some((part2_container_finish_storage_tail(state,file_type,streams),rest)),
            Ok(streams),result);
    }
}
pub(crate) open spec fn part2_container_finish_storage_calls(state:Part2RawContainerState,file_type:Part2FileType)
    ->Seq<Part2JpipSnapshotEvent> {
    choose|calls| #[trigger] part2_container_finish_storage_calls_prefix(state,file_type,calls)
}
pub(crate) open spec fn part2_container_finish_storage_calls_prefix(state:Part2RawContainerState,
    file_type:Part2FileType,calls:Seq<Part2JpipSnapshotEvent>)->bool {
    part2_cold_prefix(|events|part2_container_finish_storage_run(state,file_type,events),
        calls,part2_container_finish(state,file_type))
}
pub(crate) proof fn part2_container_finish_storage_prefix(state:Part2RawContainerState,file_type:Part2FileType,
    tail:Seq<Part2JpipSnapshotEvent>)
    ensures part2_container_finish_storage_run(state,file_type,
        part2_container_finish_storage_calls(state,file_type)+tail)==Some((part2_container_finish(state,file_type),tail)),
{
    part2_container_finish_storage_normal(state,file_type);
    let run=|events|part2_container_finish_storage_run(state,file_type,events);
    let result=part2_container_finish(state,file_type);
    let witness=part2_cold_witness(run,result);
    assert(part2_container_finish_storage_calls_prefix(state,file_type,witness));
    let calls=part2_container_finish_storage_calls(state,file_type);
    part2_cold_prefix_at(run,calls,result,tail);
}
pub(crate) proof fn part2_container_finish_storage_attach_error(state:Part2RawContainerState,file_type:Part2FileType,
    error:crate::DecodeError)
    requires part2_container_finish_storage_admit(state)==Ok(()),
        part2_container_attach_storage_result(state,state.associations.len(),Err(error)),
    ensures part2_container_finish_storage_result(state,file_type,Err(error)),
{
    part2_decode_eta(|events|part2_container_attach_storage_run(state,state.associations.len(),events),Err(error));
    part2_cold_bind(|events|part2_container_attach_storage_run(state,state.associations.len(),events),
        |streams:Seq<Part2RawCodestream>,rest|Some((part2_container_finish_storage_tail(state,file_type,streams),rest)),
        Err(error),Err(error));
}
pub(crate) proof fn part2_container_finish_storage_frames(state:Part2RawContainerState,file_type:Part2FileType,
    result:Result<Part2RawJp2File,crate::DecodeError>)
    requires part2_container_finish_storage_result(state,file_type,result),
    ensures part2_cold_framed(|events|part2_container_finish_storage_run(state,file_type,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2File>|
            (forall|events| #[trigger] other(events)==part2_container_finish_storage_run(state,file_type,events)) ==>
                #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_container_finish_storage_run(state,file_type,events),result);
}
pub closed spec fn part2_parse_container_finish_phase(input:Seq<u8>,limits:crate::ResourceLimits,
    file_type:Part2FileType,prefix:Seq<Part2JpipSnapshotEvent>,state:Part2RawContainerState)->bool {
    forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input,limits,prefix+tail)
            ==part2_container_finish_storage_run(state,file_type,tail)
}
pub(crate) proof fn part2_parse_container_finish_begin(input:Seq<u8>,limits:crate::ResourceLimits,
    file_type:Part2FileType,prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,state:Part2RawContainerState)
    requires forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input,limits,prefix+tail)
            ==part2_container_boxes_cold_run(input,reader,state,file_type,limits,tail),
        part2_box_reader_next_ref(reader).0.is_none(),
    ensures part2_parse_container_finish_phase(input,limits,file_type,prefix,state),
{
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input,limits,prefix+tail)
            ==part2_container_finish_storage_run(state,file_type,tail) by {
        assert(part2_parse_container_cold_run(input,limits,prefix+tail)
            ==part2_container_boxes_cold_run(input,reader,state,file_type,limits,tail));
        reveal_with_fuel(part2_container_boxes_cold_run,1);
    }
}
pub(crate) proof fn part2_parse_container_attach_error(input:Seq<u8>,limits:crate::ResourceLimits,
    file_type:Part2FileType,prefix:Seq<Part2JpipSnapshotEvent>,state:Part2RawContainerState,error:crate::DecodeError)
    requires part2_parse_container_finish_phase(input,limits,file_type,prefix,state),
        part2_container_finish_storage_admit(state)==Ok(()),
        part2_container_attach_storage_result(state,state.associations.len(),Err(error)),
    ensures part2_parse_container_cold_result(input,limits,Err(error)),
{
    part2_container_finish_storage_attach_error(state,file_type,error);
    part2_container_finish_storage_frames(state,file_type,Err(error));
    let run=|events|part2_container_finish_storage_run(state,file_type,events);
    let calls=part2_cold_witness(run,Err(error));
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|
        part2_parse_container_cold_run(input,limits,(prefix+calls)+tail)==Some((Err(error),tail)) by {
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
        assert(part2_parse_container_cold_run(input,limits,prefix+(calls+tail))
            ==part2_container_finish_storage_run(state,file_type,calls+tail));
        part2_cold_prefix_at(run,calls,Err(error),tail);
    }
    assert(part2_cold_prefix(|events|part2_parse_container_cold_run(input,limits,events),prefix+calls,Err(error)));
    part2_parse_container_cold_observed(input,limits,Err(error));
}
}
