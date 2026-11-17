//! Actual admitted main, associated and layer header calls in container order.
use super::*;
verus! {
pub enum Part2ContainerHeaderRequest {
    Main {payload:Seq<u8>,base:u64,allow:bool},
    Associated {payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,base:u64},
    Layer {input:Part2BoxReference},
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
                |_:Part2RawJp2Header,rest|Some((result,rest))),
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
            part2_cold_bind(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),
                |_:Part2RawJp2Header,rest|Some((result,rest)),parsed,result);
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
        |_:Part2RawJp2Header,rest|Some((part2_container_step(input,state,file_type,limits),rest)),Err(error),Err(error));
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
}
