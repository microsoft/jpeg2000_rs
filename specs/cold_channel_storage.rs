//! Reached CDEF collection storage and source-derived header traversals.
use super::*;
verus! {
pub struct Part2ChannelStorageContext {
    pub input:Part2BoxReference,
    pub channels:u16,
    pub base:u64,
}
pub(crate) open spec fn part2_channel_storage_count(context:Part2ChannelStorageContext)->nat {
    let payload=context.input.1;
    if payload.len()<2{0}else{
        let count=part2_box_u16([payload[0],payload[1]]) as nat;
        if count==0 || payload.len()!=2+count*6{0}else{count}
    }
}
pub(crate) open spec fn part2_channel_capacity_run(context:Part2ChannelStorageContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<()> {
    let count=part2_channel_storage_count(context);
    if count==0{Some((Ok(()),events))}else if events.len()==0{None}else{match events[0] {
        Part2JpipSnapshotEvent::ChannelDefinitionCapacity {context:actual,elements,succeeded}=>
            if actual!=context || elements!=count{None}else{
                Some((if succeeded{Ok(())}else{Err(crate::DecodeError::AllocationFailed)},events.drop_first()))
            },
        _=>None,
    }}
}
pub(crate) open spec fn part2_channel_storage_run(context:Part2ChannelStorageContext,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ChannelRecord>> {
    part2_jpip_snapshot_bind(part2_channel_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_channel_definition(context.input,context.channels,context.base),rest)))
}
pub closed spec fn part2_channel_storage_result(context:Part2ChannelStorageContext,result:Result<Seq<Part2ChannelRecord>,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_channel_storage_run(context,events),result)
}
pub(crate) proof fn part2_channel_capacity_observed(context:Part2ChannelStorageContext,response:Result<(),crate::DecodeError>)
    requires response==Ok(()) || (response==Err(crate::DecodeError::AllocationFailed) && part2_channel_storage_count(context)>0),
    ensures part2_cold_framed(|events|part2_channel_capacity_run(context,events),response),
{
    let count=part2_channel_storage_count(context);
    let prefix=if count==0{Seq::empty()}else{
        seq![Part2JpipSnapshotEvent::ChannelDefinitionCapacity {context,elements:count,succeeded:response.is_ok()}]};
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_channel_capacity_run(context,prefix+tail)==Some((response,tail)) by{
        if count==0{assert(prefix+tail =~= tail);}else{assert((prefix+tail).drop_first() =~= tail);}
    }
    assert(part2_cold_prefix(|events|part2_channel_capacity_run(context,events),prefix,response));
}
pub(crate) proof fn part2_channel_storage_normal(context:Part2ChannelStorageContext)
    ensures part2_channel_storage_result(context,part2_parse_channel_definition(context.input,context.channels,context.base)),
{
    let result=part2_parse_channel_definition(context.input,context.channels,context.base);
    part2_channel_capacity_observed(context,Ok(()));
    part2_cold_pure(result);
    part2_cold_bind(|events|part2_channel_capacity_run(context,events),
        |_:(),rest|Some((result,rest)),Ok(()),result);
}
pub(crate) proof fn part2_channel_storage_refused(context:Part2ChannelStorageContext,response:Result<(),crate::DecodeError>)
    requires response==Err(crate::DecodeError::AllocationFailed),part2_channel_storage_count(context)>0,
    ensures part2_channel_storage_result(context,Err(crate::DecodeError::AllocationFailed)),
{
    part2_channel_capacity_observed(context,response);
    part2_cold_bind(|events|part2_channel_capacity_run(context,events),
        |_:(),rest|Some((part2_parse_channel_definition(context.input,context.channels,context.base),rest)),
        response,Err(crate::DecodeError::AllocationFailed));
}
pub(crate) proof fn part2_channel_storage_frames(context:Part2ChannelStorageContext,result:Result<Seq<Part2ChannelRecord>,crate::DecodeError>)
    requires part2_channel_storage_result(context,result),
    ensures part2_cold_framed(|events|part2_channel_storage_run(context,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Seq<Part2ChannelRecord>>|
            (forall|events| #[trigger] other(events)==part2_channel_storage_run(context,events)) ==> #[trigger] part2_cold_framed(other,result),
{
    part2_decode_eta(|events|part2_channel_storage_run(context,events),result);
}

#[verifier::reject_recursive_types(S)]
pub struct Part2HeaderStorageMachine<S,T> {
    pub payload:Seq<u8>,
    pub base:u64,
    pub prepare:spec_fn(S)->Result<S,crate::DecodeError>,
    pub request:spec_fn(Part2BoxReference,S)->Option<Part2HeaderStorageRequest>,
    pub step:spec_fn(Part2BoxReference,S)->Result<S,crate::DecodeError>,
    pub finish:spec_fn(S)->Result<T,crate::DecodeError>,
}
pub(crate) open spec fn part2_header_storage_machine_valid<S,T>(machine:Part2HeaderStorageMachine<S,T>)->bool {
    forall|input,state|match #[trigger] (machine.request)(input,state) {
        None=>true,
        Some(request)=>match part2_header_storage_request_value(request) {
            Err(error)=>(machine.step)(input,state)==Err(error),Ok(_)=>true,
        },
    }
}
pub(crate) open spec fn part2_header_storage_step_run<S,T>(
    machine:Part2HeaderStorageMachine<S,T>,input:Part2BoxReference,state:S,events:Seq<Part2JpipSnapshotEvent>,
)->Part2ColdRun<S> {
    match (machine.request)(input,state) {
        None=>Some(((machine.step)(input,state),events)),
        Some(request)=>part2_jpip_snapshot_bind(part2_header_storage_request_run(request,events),
            |_:(),rest|Some(((machine.step)(input,state),rest))),
    }
}
pub(crate) proof fn part2_header_storage_step_normal<S,T>(
    machine:Part2HeaderStorageMachine<S,T>,input:Part2BoxReference,state:S,
)
    requires part2_header_storage_machine_valid(machine),
    ensures part2_cold_framed(|events|part2_header_storage_step_run(machine,input,state,events),(machine.step)(input,state)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<S>|
            (forall|events| #[trigger] other(events)==part2_header_storage_step_run(machine,input,state,events)) ==> #[trigger] part2_cold_framed(other,(machine.step)(input,state)),
{
    let result=(machine.step)(input,state);
    part2_cold_pure(result);
    if let Some(request)=(machine.request)(input,state){
        let parsed=part2_header_storage_request_value(request);
        part2_header_storage_request_normal(request);part2_header_storage_request_frames(request,parsed);
        part2_cold_bind(|events|part2_header_storage_request_run(request,events),
            |_:(),rest|Some((result,rest)),parsed,result);
    }
    part2_decode_eta(|events|part2_header_storage_step_run(machine,input,state,events),result);
}
pub(crate) proof fn part2_header_storage_step_error<S,T>(
    machine:Part2HeaderStorageMachine<S,T>,input:Part2BoxReference,state:S,request:Part2HeaderStorageRequest,error:crate::DecodeError,
)
    requires (machine.request)(input,state)==Some(request),part2_header_storage_request_result(request,Err(error)),
    ensures part2_cold_framed(|events|part2_header_storage_step_run(machine,input,state,events),Err(error)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<S>|
            (forall|events| #[trigger] other(events)==part2_header_storage_step_run(machine,input,state,events)) ==> #[trigger] part2_cold_framed(other,Err(error)),
{
    part2_header_storage_request_frames(request,Err(error));
    part2_cold_bind(|events|part2_header_storage_request_run(request,events),
        |_:(),rest|Some(((machine.step)(input,state),rest)),Err(error),Err(error));
    part2_decode_eta(|events|part2_header_storage_step_run(machine,input,state,events),Err(error));
}
#[verifier::opaque]
pub(crate) open spec fn part2_header_storage_boxes_run<S,T>(
    machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S,events:Seq<Part2JpipSnapshotEvent>,
)->Part2ColdRun<T>
    decreases machine.payload.len() as int-reader.position as int,
{
    let next=part2_box_reader_next_ref(reader);
    match next.0 {
        None=>Some(((machine.finish)(state),events)),
        Some(result)=>if next.1.position<=reader.position || next.1.position>machine.payload.len(){
            Some((Err(part2_resolution_progress_error(machine.base,reader.position)),events))
        }else{match result {
            Err(error)=>Some((Err(part2_box_rebase_error(error,machine.base)),events)),
            Ok(input)=>match (machine.prepare)(state) {
                Err(error)=>Some((Err(error),events)),
                Ok(prepared)=>part2_jpip_snapshot_bind(part2_header_storage_step_run(machine,input,prepared,events),
                    |updated:S,rest|part2_header_storage_boxes_run(machine,next.1,updated,rest)),
            },
        }},
    }
}
#[verifier::opaque]
pub(crate) open spec fn part2_header_storage_boxes_value<S,T>(
    machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S,
)->Result<T,crate::DecodeError>
    decreases machine.payload.len() as int-reader.position as int,
{
    let next=part2_box_reader_next_ref(reader);
    match next.0 {
        None=>(machine.finish)(state),
        Some(result)=>if next.1.position<=reader.position || next.1.position>machine.payload.len(){
            Err(part2_resolution_progress_error(machine.base,reader.position))
        }else{match result {
            Err(error)=>Err(part2_box_rebase_error(error,machine.base)),
            Ok(input)=>match (machine.prepare)(state) {
                Err(error)=>Err(error),
                Ok(prepared)=>match (machine.step)(input,prepared) {
                    Err(error)=>Err(error),Ok(updated)=>part2_header_storage_boxes_value(machine,next.1,updated),
                },
            },
        }},
    }
}
pub(crate) proof fn part2_header_storage_boxes_normal<S,T>(machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S)
    requires part2_header_storage_machine_valid(machine),
    ensures part2_cold_framed(|events|part2_header_storage_boxes_run(machine,reader,state,events),part2_header_storage_boxes_value(machine,reader,state)),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T>|
            (forall|events| #[trigger] other(events)==part2_header_storage_boxes_run(machine,reader,state,events)) ==> #[trigger] part2_cold_framed(other,part2_header_storage_boxes_value(machine,reader,state)),
    decreases machine.payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_header_storage_boxes_run,1);
    reveal_with_fuel(part2_header_storage_boxes_value,1);
    let result=part2_header_storage_boxes_value(machine,reader,state);
    let next=part2_box_reader_next_ref(reader);
    part2_cold_pure(result);
    if let Some(Ok(input))=next.0{
        if reader.position<next.1.position && next.1.position<=machine.payload.len(){
            if let Ok(prepared)=(machine.prepare)(state){
                let stepped=(machine.step)(input,prepared);
                part2_header_storage_step_normal(machine,input,prepared);
                if let Ok(updated)=stepped{part2_header_storage_boxes_normal(machine,next.1,updated);}
                part2_cold_bind(|events|part2_header_storage_step_run(machine,input,prepared,events),
                    |updated:S,rest|part2_header_storage_boxes_run(machine,next.1,updated,rest),stepped,result);
            }
        }
    }
    part2_decode_eta(|events|part2_header_storage_boxes_run(machine,reader,state,events),result);
}
pub(crate) open spec fn part2_header_storage_advance_prefix<S,T>(machine:Part2HeaderStorageMachine<S,T>,
    reader:Part2BoxReaderState,state:S,updated:S,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    forall|tail:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_header_storage_boxes_run(machine,reader,state,prefix+tail)
        ==part2_header_storage_boxes_run(machine,part2_box_reader_next_ref(reader).1,updated,tail)
}
pub(crate) proof fn part2_header_storage_advance<S,T>(machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S,
    input:Part2BoxReference,updated:S)
    requires part2_header_storage_machine_valid(machine),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=machine.payload.len(),
        (machine.prepare)(state).is_ok(),
        (machine.step)(input,(machine.prepare)(state).get_Ok_0())==Ok(updated),
    ensures exists|prefix:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_header_storage_advance_prefix(machine,reader,state,updated,prefix),
{
    let prepared=(machine.prepare)(state).get_Ok_0();
    part2_header_storage_step_normal(machine,input,prepared);
    let prefix=part2_cold_witness(|events|part2_header_storage_step_run(machine,input,prepared,events),Ok(updated));
    reveal_with_fuel(part2_header_storage_boxes_run,1);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_header_storage_boxes_run(machine,reader,state,prefix+tail)
        ==part2_header_storage_boxes_run(machine,part2_box_reader_next_ref(reader).1,updated,tail) by{
        part2_cold_prefix_at(|events|part2_header_storage_step_run(machine,input,prepared,events),prefix,Ok(updated),tail);
    }
    assert(part2_header_storage_advance_prefix(machine,reader,state,updated,prefix));
}
pub(crate) proof fn part2_header_storage_reached_error<S,T>(machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S,
    input:Part2BoxReference,request:Part2HeaderStorageRequest,error:crate::DecodeError)
    requires part2_box_reader_next_ref(reader).0==Some(Ok(input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=machine.payload.len(),
        (machine.prepare)(state).is_ok(),
        (machine.request)(input,(machine.prepare)(state).get_Ok_0())==Some(request),
        part2_header_storage_request_result(request,Err(error)),
    ensures part2_cold_framed(|events|part2_header_storage_boxes_run(machine,reader,state,events),Err(error)),
{
    let prepared=(machine.prepare)(state).get_Ok_0();
    part2_header_storage_step_error(machine,input,prepared,request,error);
    part2_cold_bind(|events|part2_header_storage_step_run(machine,input,prepared,events),
        |updated:S,rest|part2_header_storage_boxes_run(machine,part2_box_reader_next_ref(reader).1,updated,rest),Err(error),Err(error));
    reveal_with_fuel(part2_header_storage_boxes_run,1);
}
pub(crate) proof fn part2_header_storage_root_advance<S,T>(root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T>,
    prefix:Seq<Part2JpipSnapshotEvent>,machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S,
    input:Part2BoxReference,updated:S)->(extended:Seq<Part2JpipSnapshotEvent>)
    requires part2_cold_phase(root,prefix,|events|part2_header_storage_boxes_run(machine,reader,state,events)),
        part2_header_storage_machine_valid(machine),part2_box_reader_next_ref(reader).0==Some(Ok(input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=machine.payload.len(),
        (machine.prepare)(state).is_ok(),(machine.step)(input,(machine.prepare)(state).get_Ok_0())==Ok(updated),
    ensures part2_cold_phase(root,extended,|events|part2_header_storage_boxes_run(machine,part2_box_reader_next_ref(reader).1,updated,events)),
{
    part2_header_storage_advance(machine,reader,state,input,updated);
    let calls=choose|prefix:Seq<Part2JpipSnapshotEvent>| #[trigger] part2_header_storage_advance_prefix(machine,reader,state,updated,prefix);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|root((prefix+calls)+tail)
        ==part2_header_storage_boxes_run(machine,part2_box_reader_next_ref(reader).1,updated,tail) by{
        assert((prefix+calls)+tail =~= prefix+(calls+tail));
    }
    prefix+calls
}
pub(crate) proof fn part2_header_storage_root_error<S,T>(root:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<T>,
    prefix:Seq<Part2JpipSnapshotEvent>,machine:Part2HeaderStorageMachine<S,T>,reader:Part2BoxReaderState,state:S,
    input:Part2BoxReference,request:Part2HeaderStorageRequest,error:crate::DecodeError)
    requires part2_cold_phase(root,prefix,|events|part2_header_storage_boxes_run(machine,reader,state,events)),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),
        reader.position<part2_box_reader_next_ref(reader).1.position<=machine.payload.len(),
        (machine.prepare)(state).is_ok(),(machine.request)(input,(machine.prepare)(state).get_Ok_0())==Some(request),
        part2_header_storage_request_result(request,Err(error)),
    ensures part2_cold_framed(root,Err(error)),
{
    part2_header_storage_reached_error(machine,reader,state,input,request,error);
    part2_cold_prefix_result(root,|events|part2_header_storage_boxes_run(machine,reader,state,events),prefix,Err(error));
}

pub(crate) open spec fn part2_main_header_storage_machine(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool)
    ->Part2HeaderStorageMachine<Part2RawHeaderState,Part2RawJp2Header> {
    Part2HeaderStorageMachine {
        payload,base,
        prepare:|state:Part2RawHeaderState|if state.nested==u32::MAX{Err(part2_palette_arithmetic_error(base))}
            else{Ok(Part2RawHeaderState {nested:(state.nested+1) as u32,..state})},
        request:|input:Part2BoxReference,state:Part2RawHeaderState|{
            let count=if state.mappings.len()==0{state.image.components as nat}else{state.mappings.len()};
            let palette_columns=match state.palette {None=>0,Some(palette)=>palette.1.len()};
            if input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION && state.definitions.len()==0 && count<=u16::MAX{
                Some(Part2HeaderStorageRequest::Channel {context:Part2ChannelStorageContext {input,channels:count as u16,base}})
            }else if input.0.0==crate::jp2::BoxType::PALETTE && state.palette.is_none() {
                Some(Part2HeaderStorageRequest::Palette {context:Part2PaletteStorageContext {input,base}})
            }else if input.0.0==crate::jp2::BoxType::COMPONENT_MAPPING && state.mappings.len()==0 && palette_columns<=u8::MAX {
                Some(Part2HeaderStorageRequest::Mapping {context:Part2MappingStorageContext {
                    input,components:state.image.components,palette_columns:palette_columns as u8,limits,base}})
            }else if input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION && state.color.is_none() {
                Some(Part2HeaderStorageRequest::Color {context:Part2ColorStorageContext {input,base}})
            }else{None}},
        step:|input,state|part2_raw_header_step(input,state,limits,base),
        finish:|state|part2_raw_header_finish(state,base,allow),
    }
}
pub(crate) open spec fn part2_associated_header_storage_machine(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64)
    ->Part2HeaderStorageMachine<Part2AssociatedHeaderState,Part2RawJp2Header> {
    Part2HeaderStorageMachine {
        payload,base,
        prepare:|state:Part2AssociatedHeaderState|if state.nested==u32::MAX{Err(part2_palette_arithmetic_error(base))}
            else{Ok(Part2AssociatedHeaderState {nested:(state.nested+1) as u32,..state})},
        request:|input:Part2BoxReference,state:Part2AssociatedHeaderState|{
            let count=if state.header.mappings.len()==0{state.header.image.components as nat}else{state.header.mappings.len()};
            let palette_columns=match state.header.palette {None=>0,Some(palette)=>palette.1.len()};
            if input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION && !state.definition_override && count<=u16::MAX{
                Some(Part2HeaderStorageRequest::Channel {context:Part2ChannelStorageContext {input,channels:count as u16,base}})
            }else if input.0.0==crate::jp2::BoxType::PALETTE && !state.palette_override && !state.mapping_override && !state.definition_override {
                Some(Part2HeaderStorageRequest::Palette {context:Part2PaletteStorageContext {input,base}})
            }else if input.0.0==crate::jp2::BoxType::COMPONENT_MAPPING && !state.mapping_override && !state.definition_override
                && palette_columns<=u8::MAX {
                Some(Part2HeaderStorageRequest::Mapping {context:Part2MappingStorageContext {
                    input,components:state.header.image.components,palette_columns:palette_columns as u8,limits,base}})
            }else if input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION && !state.color_override {
                Some(Part2HeaderStorageRequest::Color {context:Part2ColorStorageContext {input,base}})
            }else{None}},
        step:|input,state|part2_associated_header_step(input,state,limits,base),
        finish:|state|part2_associated_header_finish(state,base),
    }
}
pub(crate) open spec fn part2_layer_header_storage_machine(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64)
    ->Part2HeaderStorageMachine<Part2RawLayerState,Part2RawCompositingLayer> {
    Part2HeaderStorageMachine {
        payload,base,prepare:|state:Part2RawLayerState|Ok(state),
        request:|input:Part2BoxReference,state:Part2RawLayerState|
            if input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION && state.layer.definitions.len()==0 && state.layer.opacity.is_none(){
                Some(Part2HeaderStorageRequest::Channel {context:Part2ChannelStorageContext {input,channels:u16::MAX,base}})
            }else if input.0.0==crate::jp2::BoxType::COLOR_GROUP && state.layer.colors.len()==0 {
                match part2_box_payload_offset(input.0) {
                    Err(_)=>None,Ok(relative)=>match part2_box_add_offset(base,relative) {
                        Err(_)=>None,Ok(nested_base)=>Some(Part2HeaderStorageRequest::ColorGroup {
                            context:Part2ColorGroupStorageContext {input,limits,base:nested_base}}),
                    },
                }
            }else{None},
        step:|input,state|part2_raw_layer_step(input,state,limits,base),
        finish:|state:Part2RawLayerState|Ok(state.layer),
    }
}
pub(crate) proof fn part2_header_storage_machines_valid(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool)
    ensures part2_header_storage_machine_valid(part2_main_header_storage_machine(payload,limits,base,allow)),
        part2_header_storage_machine_valid(part2_associated_header_storage_machine(payload,limits,base)),
        part2_header_storage_machine_valid(part2_layer_header_storage_machine(payload,limits,base)),
{
    reveal(part2_raw_header_step);reveal(part2_associated_header_step);reveal(part2_raw_layer_step);
    crate::jp2::channel_storage_box_kinds_known();
    let main=part2_main_header_storage_machine(payload,limits,base,allow);
    assert forall|input:Part2BoxReference,state:Part2RawHeaderState|match #[trigger] (main.request)(input,state){
        None=>true,Some(request)=>match part2_header_storage_request_value(request){
            Err(error)=>(main.step)(input,state)==Err(error),Ok(_)=>true,
        },
    } by {
        if let Some(request)=(main.request)(input,state){
            match request {
                Part2HeaderStorageRequest::Channel {context}=>{
                    assert(input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION);
                    assert(state.definitions.len()==0);
                    let count=if state.mappings.len()==0{state.image.components as nat}else{state.mappings.len()};
                    assert(count<=u16::MAX);
                    assert(context==(Part2ChannelStorageContext {input,channels:count as u16,base}));
                },
                Part2HeaderStorageRequest::Palette {context}=>{
                    assert(input.0.0==crate::jp2::BoxType::PALETTE);
                    assert(state.palette.is_none());
                    assert(context==(Part2PaletteStorageContext {input,base}));
                },
                Part2HeaderStorageRequest::Mapping {context}=>{
                    let count=match state.palette {None=>0,Some(palette)=>palette.1.len()};
                    assert(input.0.0==crate::jp2::BoxType::COMPONENT_MAPPING);
                    assert(state.mappings.len()==0 && count<=u8::MAX);
                    assert(context==(Part2MappingStorageContext {
                        input,components:state.image.components,palette_columns:count as u8,limits,base}));
                },
                Part2HeaderStorageRequest::Color {context}=>{
                    assert(input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION && state.color.is_none());
                    assert(context==(Part2ColorStorageContext {input,base}));
                },
                Part2HeaderStorageRequest::ColorGroup {context}=>{assert(false);},
            }
        }
    }
    let associated=part2_associated_header_storage_machine(payload,limits,base);
    assert forall|input:Part2BoxReference,state:Part2AssociatedHeaderState|match #[trigger] (associated.request)(input,state){
        None=>true,Some(request)=>match part2_header_storage_request_value(request){
            Err(error)=>(associated.step)(input,state)==Err(error),Ok(_)=>true,
        },
    } by {
        if let Some(request)=(associated.request)(input,state){
            match request {
                Part2HeaderStorageRequest::Channel {context}=>{
                    assert(input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION);
                    assert(!state.definition_override);
                    let count=if state.header.mappings.len()==0{state.header.image.components as nat}else{state.header.mappings.len()};
                    assert(count<=u16::MAX);
                    assert(context==(Part2ChannelStorageContext {input,channels:count as u16,base}));
                },
                Part2HeaderStorageRequest::Palette {context}=>{
                    assert(input.0.0==crate::jp2::BoxType::PALETTE);
                    assert(!state.palette_override && !state.mapping_override && !state.definition_override);
                    assert(context==(Part2PaletteStorageContext {input,base}));
                },
                Part2HeaderStorageRequest::Mapping {context}=>{
                    let count=match state.header.palette {None=>0,Some(palette)=>palette.1.len()};
                    assert(input.0.0==crate::jp2::BoxType::COMPONENT_MAPPING);
                    assert(!state.mapping_override && !state.definition_override && count<=u8::MAX);
                    assert(context==(Part2MappingStorageContext {
                        input,components:state.header.image.components,palette_columns:count as u8,limits,base}));
                },
                Part2HeaderStorageRequest::Color {context}=>{
                    assert(input.0.0==crate::jp2::BoxType::COLOR_SPECIFICATION && !state.color_override);
                    assert(context==(Part2ColorStorageContext {input,base}));
                },
                Part2HeaderStorageRequest::ColorGroup {context}=>{assert(false);},
            }
        }
    }
}
pub(crate) proof fn part2_main_header_storage_value(payload:Seq<u8>,reader:Part2BoxReaderState,state:Part2RawHeaderState,
    limits:crate::ResourceLimits,base:u64,allow:bool)
    ensures part2_header_storage_boxes_value(part2_main_header_storage_machine(payload,limits,base,allow),reader,state)
        ==part2_raw_header_boxes(payload,reader,state,limits,base,allow),
    decreases payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_header_storage_boxes_value,1);reveal_with_fuel(part2_raw_header_boxes,1);
    let next=part2_box_reader_next_ref(reader);
    if let Some(Ok(input))=next.0{
        if reader.position<next.1.position && next.1.position<=payload.len() && state.nested<u32::MAX{
            let prepared=Part2RawHeaderState {nested:(state.nested+1) as u32,..state};
            if let Ok(updated)=part2_raw_header_step(input,prepared,limits,base){
                part2_main_header_storage_value(payload,next.1,updated,limits,base,allow);
            }
        }
    }
}
pub(crate) proof fn part2_associated_header_storage_value(payload:Seq<u8>,reader:Part2BoxReaderState,state:Part2AssociatedHeaderState,
    limits:crate::ResourceLimits,base:u64)
    ensures part2_header_storage_boxes_value(part2_associated_header_storage_machine(payload,limits,base),reader,state)
        ==part2_associated_header_boxes(payload,reader,state,limits,base),
    decreases payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_header_storage_boxes_value,1);reveal_with_fuel(part2_associated_header_boxes,1);
    let next=part2_box_reader_next_ref(reader);
    if let Some(Ok(input))=next.0{
        if reader.position<next.1.position && next.1.position<=payload.len() && state.nested<u32::MAX{
            let prepared=Part2AssociatedHeaderState {nested:(state.nested+1) as u32,..state};
            if let Ok(updated)=part2_associated_header_step(input,prepared,limits,base){
                part2_associated_header_storage_value(payload,next.1,updated,limits,base);
            }
        }
    }
}
pub(crate) proof fn part2_layer_header_storage_value(payload:Seq<u8>,reader:Part2BoxReaderState,state:Part2RawLayerState,
    limits:crate::ResourceLimits,base:u64)
    ensures part2_header_storage_boxes_value(part2_layer_header_storage_machine(payload,limits,base),reader,state)
        ==part2_raw_layer_boxes(payload,reader,state,limits,base),
    decreases payload.len() as int-reader.position as int,
{
    reveal_with_fuel(part2_header_storage_boxes_value,1);reveal_with_fuel(part2_raw_layer_boxes,1);
    let next=part2_box_reader_next_ref(reader);
    if let Some(Ok(input))=next.0{
        if reader.position<next.1.position && next.1.position<=payload.len(){
            if let Ok(updated)=part2_raw_layer_step(input,state,limits,base){
                part2_layer_header_storage_value(payload,next.1,updated,limits,base);
            }
        }
    }
}
pub(crate) open spec fn part2_jp2_header_storage_start(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64)
    ->Result<(Part2BoxReaderState,Part2RawHeaderState),crate::DecodeError> {
    match part2_box_reader_from_input(payload,limits) {
        Err(error)=>Err(error),
        Ok(reader)=>{
            let required=part2_box_reader_required(reader,0);
            match required.0{
                Err(error)=>Err(part2_box_rebase_error(error,base)),
                Ok(input)=>if input.0.0!=crate::jp2::BoxType::IMAGE_HEADER{
                    Err(part2_image_box_error(base,input.0,crate::MalformedKind::InvalidBoxOrder))
                }else{match part2_parse_image_header(input,&limits,base){
                    Err(error)=>Err(error),
                    Ok(image)=>Ok((required.1,Part2RawHeaderState {image,color:None,saw_bpcc:false,palette:None,
                        mappings:Seq::empty(),definitions:Seq::empty(),capture:None,display:None,nested:1})),
                }},
            }
        },
    }
}
pub(crate) open spec fn part2_jp2_header_storage_run(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header> {
    match part2_jp2_header_storage_start(payload,limits,base){
        Err(error)=>Some((Err(error),events)),
        Ok((reader,state))=>part2_header_storage_boxes_run(part2_main_header_storage_machine(payload,limits,base,allow),reader,state,events),
    }
}
pub closed spec fn part2_jp2_header_storage_result(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool,
    result:Result<Part2RawJp2Header,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_jp2_header_storage_run(payload,limits,base,allow,events),result)
}
pub(crate) proof fn part2_jp2_header_storage_normal(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool)
    ensures part2_jp2_header_storage_result(payload,limits,base,allow,part2_parse_jp2_header_profile(payload,limits,base,allow)),
{
    let result=part2_parse_jp2_header_profile(payload,limits,base,allow);
    part2_cold_pure(result);
    if let Ok((reader,state))=part2_jp2_header_storage_start(payload,limits,base){
        part2_header_storage_machines_valid(payload,limits,base,allow);
        part2_main_header_storage_value(payload,reader,state,limits,base,allow);
        part2_header_storage_boxes_normal(part2_main_header_storage_machine(payload,limits,base,allow),reader,state);
    }
}
pub(crate) proof fn part2_jp2_header_storage_observed(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool,
    result:Result<Part2RawJp2Header,crate::DecodeError>)
    requires part2_cold_framed(|events|part2_jp2_header_storage_run(payload,limits,base,allow,events),result),
    ensures part2_jp2_header_storage_result(payload,limits,base,allow,result),
{}
pub(crate) proof fn part2_jp2_header_storage_frames(payload:Seq<u8>,limits:crate::ResourceLimits,base:u64,allow:bool,
    result:Result<Part2RawJp2Header,crate::DecodeError>)
    requires part2_jp2_header_storage_result(payload,limits,base,allow,result),
    ensures part2_cold_framed(|events|part2_jp2_header_storage_run(payload,limits,base,allow,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header>|
            (forall|events| #[trigger] other(events)==part2_jp2_header_storage_run(payload,limits,base,allow,events)) ==> #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_jp2_header_storage_run(payload,limits,base,allow,events),result);}

pub(crate) open spec fn part2_layer_header_storage_start(input:Part2BoxReference,limits:crate::ResourceLimits)
    ->Result<(u64,Part2BoxReaderState,Part2RawLayerState),crate::DecodeError> {
    match part2_box_payload_offset(input.0){
        Err(error)=>Err(error),
        Ok(base)=>match part2_box_reader_from_input(input.1,limits){
            Err(error)=>Err(error),Ok(reader)=>Ok((base,reader,Part2RawLayerState {
                layer:Part2RawCompositingLayer {header:input.0,payload:input.1,horizontal:1,vertical:1,
                    registrations:Seq::empty(),colors:Seq::empty(),definitions:Seq::empty(),opacity:None,nested_metadata:0},
                has_registration:false})),
        },
    }
}
pub(crate) open spec fn part2_layer_header_storage_run(input:Part2BoxReference,limits:crate::ResourceLimits,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawCompositingLayer> {
    match part2_layer_header_storage_start(input,limits){
        Err(error)=>Some((Err(error),events)),
        Ok((base,reader,state))=>part2_header_storage_boxes_run(part2_layer_header_storage_machine(input.1,limits,base),reader,state,events),
    }
}
pub closed spec fn part2_layer_header_storage_result(input:Part2BoxReference,limits:crate::ResourceLimits,
    result:Result<Part2RawCompositingLayer,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_layer_header_storage_run(input,limits,events),result)
}
pub(crate) proof fn part2_layer_header_storage_normal(input:Part2BoxReference,limits:crate::ResourceLimits)
    ensures part2_layer_header_storage_result(input,limits,part2_parse_compositing_layer(input,limits)),
{
    let result=part2_parse_compositing_layer(input,limits);
    part2_cold_pure(result);
    if let Ok((base,reader,state))=part2_layer_header_storage_start(input,limits){
        part2_header_storage_machines_valid(input.1,limits,base,false);
        part2_layer_header_storage_value(input.1,reader,state,limits,base);
        part2_header_storage_boxes_normal(part2_layer_header_storage_machine(input.1,limits,base),reader,state);
    }
}
pub(crate) proof fn part2_layer_header_storage_observed(input:Part2BoxReference,limits:crate::ResourceLimits,
    result:Result<Part2RawCompositingLayer,crate::DecodeError>)
    requires part2_cold_framed(|events|part2_layer_header_storage_run(input,limits,events),result),
    ensures part2_layer_header_storage_result(input,limits,result),
{}
pub(crate) proof fn part2_layer_header_storage_frames(input:Part2BoxReference,limits:crate::ResourceLimits,
    result:Result<Part2RawCompositingLayer,crate::DecodeError>)
    requires part2_layer_header_storage_result(input,limits,result),
    ensures part2_cold_framed(|events|part2_layer_header_storage_run(input,limits,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawCompositingLayer>|
            (forall|events| #[trigger] other(events)==part2_layer_header_storage_run(input,limits,events)) ==> #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_layer_header_storage_run(input,limits,events),result);}

pub(crate) open spec fn part2_header_storage_resume<A,B>(run:Part2ColdRun<A>,
    next:spec_fn(Result<A,crate::DecodeError>,Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<B>)->Part2ColdRun<B> {
    match run{None=>None,Some((result,rest))=>next(result,rest)}
}
pub(crate) proof fn part2_header_storage_resume_frame<A,B>(run:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<A>,
    next:spec_fn(Result<A,crate::DecodeError>,Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<B>,
    first:Result<A,crate::DecodeError>,result:Result<B,crate::DecodeError>)
    requires part2_cold_framed(run,first),part2_cold_framed(|events|next(first,events),result),
    ensures part2_cold_framed(|events|part2_header_storage_resume(run(events),next),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<B>|
            (forall|events| #[trigger] other(events)==part2_header_storage_resume(run(events),next)) ==> #[trigger] part2_cold_framed(other,result),
{
    let before=part2_cold_witness(run,first);
    let after=part2_cold_witness(|events|next(first,events),result);
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_header_storage_resume(run((before+after)+tail),next)==Some((result,tail)) by{
        assert((before+after)+tail =~= before+(after+tail));
        part2_cold_prefix_at(run,before,first,after+tail);
        part2_cold_prefix_at(|events|next(first,events),after,result,tail);
    }
    assert(part2_cold_prefix(|events|part2_header_storage_resume(run(events),next),before+after,result));
    part2_decode_eta(|events|part2_header_storage_resume(run(events),next),result);
}
pub(crate) open spec fn part2_codestream_header_storage_start(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64)
    ->Result<(Part2BoxReaderState,Part2AssociatedHeaderState),crate::DecodeError> {
    match defaults{
        None=>Err(part2_raw_header_missing(base)),
        Some(header)=>match part2_box_reader_from_input(payload,limits){
            Err(error)=>Err(error),
            Ok(reader)=>Ok((reader,Part2AssociatedHeaderState {header,image_override:false,color_override:false,
                saw_bpcc:false,palette_override:false,mapping_override:false,definition_override:false,resolution_override:false,nested:0})),
        },
    }
}
pub(crate) open spec fn part2_codestream_header_storage_cloned(payload:Seq<u8>,header:Part2RawJp2Header,
    limits:crate::ResourceLimits,base:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header> {
    match part2_codestream_header_storage_start(payload,Some(header),limits,base) {
        Err(error)=>Some((Err(error),events)),
        Ok((reader,state))=>part2_header_storage_boxes_run(part2_associated_header_storage_machine(payload,limits,base),reader,state,events),
    }
}
pub(crate) open spec fn part2_codestream_header_storage_after(first:Result<Part2RawJp2Header,crate::DecodeError>,
    payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header> {
    match first{
        Ok(header)=>Some((Ok(header),events)),
        Err(crate::DecodeError::AllocationFailed)=>Some((Err(crate::DecodeError::AllocationFailed),events)),
        Err(_)=>match defaults{
            None=>Some((Err(part2_raw_header_missing(base)),events)),
            Some(header)=>part2_jpip_snapshot_bind(part2_header_clone_storage_run(header,events),
                |cloned:Part2RawJp2Header,rest|part2_codestream_header_storage_cloned(payload,cloned,limits,base,rest)),
        },
    }
}
pub(crate) open spec fn part2_codestream_header_storage_run(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    events:Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header> {
    part2_header_storage_resume(part2_jp2_header_storage_run(payload,limits,base,false,events),
        |first,rest|part2_codestream_header_storage_after(first,payload,defaults,limits,base,rest))
}
pub closed spec fn part2_codestream_header_storage_result(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    result:Result<Part2RawJp2Header,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),result)
}
pub(crate) proof fn part2_codestream_header_storage_normal(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64)
    ensures part2_codestream_header_storage_result(payload,defaults,limits,base,part2_parse_codestream_header(payload,defaults,limits,base)),
{
    let first=part2_parse_jp2_header(payload,limits,base);
    let result=part2_parse_codestream_header(payload,defaults,limits,base);
    part2_jp2_header_semantic_errors(payload,limits,base,false);
    part2_jp2_header_storage_normal(payload,limits,base,false);part2_jp2_header_storage_frames(payload,limits,base,false,first);
    part2_cold_pure(result);
    if first.is_err(){
        if let Some(header)=defaults{
            if let Ok((reader,state))=part2_codestream_header_storage_start(payload,defaults,limits,base){
                part2_header_storage_machines_valid(payload,limits,base,false);
                part2_associated_header_storage_value(payload,reader,state,limits,base);
                part2_header_storage_boxes_normal(part2_associated_header_storage_machine(payload,limits,base),reader,state);
            }
            part2_decode_eta(|events|part2_codestream_header_storage_cloned(payload,header,limits,base,events),result);
            part2_header_clone_storage_normal(header);
            part2_header_clone_storage_frames(header,Ok(header));
            part2_cold_bind(|events|part2_header_clone_storage_run(header,events),
                |cloned:Part2RawJp2Header,rest|part2_codestream_header_storage_cloned(payload,cloned,limits,base,rest),
                Ok(header),result);
        }
    }
    part2_decode_eta(|events|part2_codestream_header_storage_after(first,payload,defaults,limits,base,events),result);
    part2_header_storage_resume_frame(|events|part2_jp2_header_storage_run(payload,limits,base,false,events),
        |first,rest|part2_codestream_header_storage_after(first,payload,defaults,limits,base,rest),first,result);
}
pub(crate) proof fn part2_codestream_header_storage_first(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    first:Result<Part2RawJp2Header,crate::DecodeError>)
    requires part2_jp2_header_storage_result(payload,limits,base,false,first),
    ensures first.is_ok() || first==Err(crate::DecodeError::AllocationFailed) ==>
        part2_codestream_header_storage_result(payload,defaults,limits,base,first),
{
    if first.is_ok() || first==Err(crate::DecodeError::AllocationFailed){
        part2_jp2_header_storage_frames(payload,limits,base,false,first);part2_cold_pure(first);
        part2_header_storage_resume_frame(|events|part2_jp2_header_storage_run(payload,limits,base,false,events),
            |first,rest|part2_codestream_header_storage_after(first,payload,defaults,limits,base,rest),first,first);
    }
}
pub(crate) proof fn part2_codestream_header_storage_clone_error(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,
    limits:crate::ResourceLimits,base:u64,first:Result<Part2RawJp2Header,crate::DecodeError>,
    header:Part2RawJp2Header,error:crate::DecodeError)
    requires part2_jp2_header_storage_result(payload,limits,base,false,first),
        first.is_err(),first!=Err(crate::DecodeError::AllocationFailed),defaults==Some(header),
        part2_header_clone_storage_result(header,Err(error)),
    ensures part2_codestream_header_storage_result(payload,defaults,limits,base,Err(error)),
{
    part2_header_clone_storage_frames(header,Err(error));
    part2_cold_bind(|events|part2_header_clone_storage_run(header,events),
        |cloned:Part2RawJp2Header,rest|part2_codestream_header_storage_cloned(payload,cloned,limits,base,rest),
        Err(error),Err(error));
    part2_decode_eta(|events|part2_codestream_header_storage_after(first,payload,defaults,limits,base,events),Err(error));
    part2_jp2_header_storage_frames(payload,limits,base,false,first);
    part2_header_storage_resume_frame(|events|part2_jp2_header_storage_run(payload,limits,base,false,events),
        |first,rest|part2_codestream_header_storage_after(first,payload,defaults,limits,base,rest),first,Err(error));
}
pub closed spec fn part2_codestream_header_storage_at(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    reader:Part2BoxReaderState,state:Part2AssociatedHeaderState,prefix:Seq<Part2JpipSnapshotEvent>)->bool {
    part2_cold_phase(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),prefix,
        |events|part2_header_storage_boxes_run(part2_associated_header_storage_machine(payload,limits,base),reader,state,events))
}
pub(crate) proof fn part2_codestream_header_storage_prefix(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    first:Result<Part2RawJp2Header,crate::DecodeError>,reader:Part2BoxReaderState,state:Part2AssociatedHeaderState)->(prefix:Seq<Part2JpipSnapshotEvent>)
    requires part2_jp2_header_storage_result(payload,limits,base,false,first),first.is_err(),first!=Err(crate::DecodeError::AllocationFailed),
        part2_codestream_header_storage_start(payload,defaults,limits,base)==Ok((reader,state)),
        match defaults {None=>true,Some(header)=>part2_header_clone_storage_result(header,Ok(header))},
    ensures part2_codestream_header_storage_at(payload,defaults,limits,base,reader,state,prefix),
{
    part2_jp2_header_storage_frames(payload,limits,base,false,first);
    let before=part2_cold_witness(|events|part2_jp2_header_storage_run(payload,limits,base,false,events),first);
    let header=defaults.get_Some_0();
    part2_header_clone_storage_frames(header,Ok(header));
    let copied=part2_cold_witness(|events|part2_header_clone_storage_run(header,events),Ok(header));
    let prefix=before+copied;
    assert forall|tail:Seq<Part2JpipSnapshotEvent>|part2_codestream_header_storage_run(payload,defaults,limits,base,prefix+tail)
        ==part2_header_storage_boxes_run(part2_associated_header_storage_machine(payload,limits,base),reader,state,tail) by{
        assert((before+copied)+tail =~= before+(copied+tail));
        part2_cold_prefix_at(|events|part2_jp2_header_storage_run(payload,limits,base,false,events),before,first,copied+tail);
        part2_cold_prefix_at(|events|part2_header_clone_storage_run(header,events),copied,Ok(header),tail);
    }
    prefix
}
pub(crate) proof fn part2_codestream_header_storage_advance(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,state:Part2AssociatedHeaderState,input:Part2BoxReference,
    updated:Part2AssociatedHeaderState)->(extended:Seq<Part2JpipSnapshotEvent>)
    requires part2_codestream_header_storage_at(payload,defaults,limits,base,reader,state,prefix),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),reader.position<part2_box_reader_next_ref(reader).1.position<=payload.len(),
        state.nested<u32::MAX,
        part2_associated_header_step(input,Part2AssociatedHeaderState {nested:(state.nested+1) as u32,..state},limits,base)==Ok(updated),
    ensures part2_codestream_header_storage_at(payload,defaults,limits,base,part2_box_reader_next_ref(reader).1,updated,extended),
{
    part2_header_storage_machines_valid(payload,limits,base,false);
    part2_header_storage_root_advance(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),prefix,
        part2_associated_header_storage_machine(payload,limits,base),reader,state,input,updated)
}
pub(crate) proof fn part2_codestream_header_storage_error(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,state:Part2AssociatedHeaderState,input:Part2BoxReference,
    channels:u16,error:crate::DecodeError)
    requires part2_codestream_header_storage_at(payload,defaults,limits,base,reader,state,prefix),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),reader.position<part2_box_reader_next_ref(reader).1.position<=payload.len(),
        state.nested<u32::MAX,input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION,!state.definition_override,
        (if state.header.mappings.len()==0{state.header.image.components as nat}else{state.header.mappings.len()})==channels as nat,
        part2_channel_storage_result(Part2ChannelStorageContext {input,channels,base},Err(error)),
    ensures part2_codestream_header_storage_result(payload,defaults,limits,base,Err(error)),
{
    let context=Part2ChannelStorageContext {input,channels,base};
    part2_header_storage_request_channel_error(context,error);
    part2_header_storage_root_error(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),prefix,
        part2_associated_header_storage_machine(payload,limits,base),reader,state,input,Part2HeaderStorageRequest::Channel {context},error);
}
pub open spec fn part2_associated_header_box_outcome(result:Result<(),crate::DecodeError>,state:Part2AssociatedHeaderState)
    ->Result<Part2AssociatedHeaderState,crate::DecodeError> {
    match result{Err(error)=>Err(error),Ok(())=>Ok(state)}
}
pub closed spec fn part2_associated_header_box_storage_result(input:Part2BoxReference,state:Part2AssociatedHeaderState,
    limits:crate::ResourceLimits,base:u64,result:Result<Part2AssociatedHeaderState,crate::DecodeError>)->bool {
    part2_cold_framed(|events|part2_header_storage_step_run(part2_associated_header_storage_machine(Seq::empty(),limits,base),input,state,events),result)
}
pub(crate) proof fn part2_associated_header_box_storage_normal(input:Part2BoxReference,state:Part2AssociatedHeaderState,limits:crate::ResourceLimits,base:u64)
    ensures part2_associated_header_box_storage_result(input,state,limits,base,part2_associated_header_step(input,state,limits,base)),
{
    part2_header_storage_machines_valid(Seq::empty(),limits,base,false);
    part2_header_storage_step_normal(part2_associated_header_storage_machine(Seq::empty(),limits,base),input,state);
}
pub(crate) proof fn part2_associated_header_box_storage_error(input:Part2BoxReference,state:Part2AssociatedHeaderState,
    limits:crate::ResourceLimits,base:u64,channels:u16,error:crate::DecodeError)
    requires input.0.0==crate::jp2::BoxType::CHANNEL_DEFINITION,!state.definition_override,
        (if state.header.mappings.len()==0{state.header.image.components as nat}else{state.header.mappings.len()})==channels as nat,
        part2_channel_storage_result(Part2ChannelStorageContext {input,channels,base},Err(error)),
    ensures part2_associated_header_box_storage_result(input,state,limits,base,Err(error)),
{
    let context=Part2ChannelStorageContext {input,channels,base};
    part2_header_storage_request_channel_error(context,error);
    part2_header_storage_step_error(part2_associated_header_storage_machine(Seq::empty(),limits,base),input,state,
        Part2HeaderStorageRequest::Channel {context},error);
}
pub(crate) proof fn part2_associated_header_box_storage_request_error(input:Part2BoxReference,state:Part2AssociatedHeaderState,
    limits:crate::ResourceLimits,base:u64,request:Part2HeaderStorageRequest,error:crate::DecodeError)
    requires (part2_associated_header_storage_machine(Seq::empty(),limits,base).request)(input,state)==Some(request),
        part2_header_storage_request_result(request,Err(error)),
    ensures part2_associated_header_box_storage_result(input,state,limits,base,Err(error)),
{
    part2_header_storage_step_error(part2_associated_header_storage_machine(Seq::empty(),limits,base),
        input,state,request,error);
}
pub(crate) proof fn part2_associated_header_box_storage_frames(input:Part2BoxReference,state:Part2AssociatedHeaderState,
    limits:crate::ResourceLimits,base:u64,payload:Seq<u8>,result:Result<Part2AssociatedHeaderState,crate::DecodeError>)
    requires part2_associated_header_box_storage_result(input,state,limits,base,result),
    ensures part2_cold_framed(|events|part2_header_storage_step_run(part2_associated_header_storage_machine(payload,limits,base),input,state,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2AssociatedHeaderState>|
            (forall|events| #[trigger] other(events)==part2_header_storage_step_run(part2_associated_header_storage_machine(payload,limits,base),input,state,events))
                ==> #[trigger] part2_cold_framed(other,result),
{
    part2_cold_framed_extensional(
        |events|part2_header_storage_step_run(part2_associated_header_storage_machine(Seq::empty(),limits,base),input,state,events),
        |events|part2_header_storage_step_run(part2_associated_header_storage_machine(payload,limits,base),input,state,events),result);
}
pub(crate) proof fn part2_codestream_header_storage_box_error(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    prefix:Seq<Part2JpipSnapshotEvent>,reader:Part2BoxReaderState,state:Part2AssociatedHeaderState,input:Part2BoxReference,error:crate::DecodeError)
    requires part2_codestream_header_storage_at(payload,defaults,limits,base,reader,state,prefix),
        part2_box_reader_next_ref(reader).0==Some(Ok(input)),reader.position<part2_box_reader_next_ref(reader).1.position<=payload.len(),
        state.nested<u32::MAX,
        part2_associated_header_box_storage_result(input,Part2AssociatedHeaderState {nested:(state.nested+1) as u32,..state},limits,base,Err(error)),
    ensures part2_codestream_header_storage_result(payload,defaults,limits,base,Err(error)),
{
    let machine=part2_associated_header_storage_machine(payload,limits,base);
    let prepared=Part2AssociatedHeaderState {nested:(state.nested+1) as u32,..state};
    part2_associated_header_box_storage_frames(input,prepared,limits,base,payload,Err(error));
    part2_cold_bind(|events|part2_header_storage_step_run(machine,input,prepared,events),
        |updated:Part2AssociatedHeaderState,rest|part2_header_storage_boxes_run(machine,part2_box_reader_next_ref(reader).1,updated,rest),Err(error),Err(error));
    reveal_with_fuel(part2_header_storage_boxes_run,1);
    part2_cold_prefix_result(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),
        |events|part2_header_storage_boxes_run(machine,reader,state,events),prefix,Err(error));
}
pub(crate) proof fn part2_codestream_header_storage_observed(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    result:Result<Part2RawJp2Header,crate::DecodeError>)
    requires part2_cold_framed(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),result),
    ensures part2_codestream_header_storage_result(payload,defaults,limits,base,result),
{}
pub(crate) proof fn part2_codestream_header_storage_frames(payload:Seq<u8>,defaults:Option<Part2RawJp2Header>,limits:crate::ResourceLimits,base:u64,
    result:Result<Part2RawJp2Header,crate::DecodeError>)
    requires part2_codestream_header_storage_result(payload,defaults,limits,base,result),
    ensures part2_cold_framed(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),result),
        forall|other:spec_fn(Seq<Part2JpipSnapshotEvent>)->Part2ColdRun<Part2RawJp2Header>|
            (forall|events| #[trigger] other(events)==part2_codestream_header_storage_run(payload,defaults,limits,base,events)) ==> #[trigger] part2_cold_framed(other,result),
{part2_decode_eta(|events|part2_codestream_header_storage_run(payload,defaults,limits,base,events),result);}
}
